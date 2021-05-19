from LexicalAnalysis import *
from Constants import *
import numpy as np

class Boolean:
    def __init__(self,val):
        self.val=val
    def Not(self):
        return Boolean(not(self.val))
    def toString(self):
        return str(self.val)

class Factor:
    def __init__(self, var=None, const=1):
        self.var=var
        self.const=const
    def toString(self):
        if(self.var==None):
            return str(self.const)
        elif(self.const!=0):
            return str(self.const) + str(self.var)
        else:
            return "0"
    def isZero(self):
        return self.const==0
    def isConstant(self):
        return self.var==None
    def isNegative(self):
        return self.const<0
    def inverse(self):
        return Factor(var=self.var,const=-self.const)
    def toZ3(self):
        if(self.var!=None):
            return self.const*z3.Int(self.var)
        return self.const

class Sum:
    def __init__(self,factorSet):
        self.factorSet=factorSet
    def toString(self):
        if(len(self.factorSet)==0):
            return "0"
        res=self.factorSet[0].toString()
        for f in self.factorSet[1:]:
            if(f.isNegative()):
                res+= " - " + f.inverse().toString()
            else:
                res+= " + " + f.toString()
        return res
    def addFactor(self,f):
        self.factorSet.append(f)
        return self
    def inverse(self):
        for i in range(len(self.factorSet)):
            self.factorSet[i]=self.factorSet[i].inverse()
        return self
    def isConstant(self):
        return len(self.factorSet)==1 and self.factorSet[0].isConstant()
    def isZero(self):
        return len(self.factorSet)==1 and self.factorSet[0].isZero()
    def containsX(self,x):
        for f in self.factorSet:
            if f.var==x:
                return True
        return False
    def add(self,f):
        fs=list(self.factorSet)
        fs.append(f)
        return Sum(fs)
    def toZ3(self):
        res=0
        for f in self.factorSet:
            if res==0:
                res=f.toZ3()
            else:
                res+=f.toZ3()
        return res
class LinearConstraint:
    def __init__(self,cmp,sumSet):
        self.cmp=cmp
        self.sumSet=sumSet
    def toString(self):
        cmp=self.cmp
        if(cmp==EQ):
            strCmp=" = "
        elif(cmp==NE):
            strCmp=" != "
        elif(cmp==LT):
            strCmp=" < "
        elif(cmp==LE):
            strCmp=" <= "
        elif(cmp==GT):
            strCmp=" > "
        elif(cmp==GE):
            strCmp=" >= "
        else:
            return ""
        res=self.sumSet[0].toString()
        for s in self.sumSet[1:]:
            res += strCmp + s.toString()
        return res
    def Not(self):
        cmp=self.cmp
        if(cmp==EQ):
            return LinearConstraint(NE,self.sumSet)
        elif(cmp==NE):
            return LinearConstraint(EQ,self.sumSet)
        elif(cmp==LT):
            return LinearConstraint(GE,self.sumSet)
        elif(cmp==LE):
            return LinearConstraint(GT,self.sumSet)
        elif(cmp==GT):
            return LinearConstraint(LE,self.sumSet)
        elif(cmp==GE):
            return LinearConstraint(LT,self.sumSet)
        return None
    def minfp(self,x):
        #We assume the cmp in ax cmp t is either < or >
        if(self.cmp==LT):
            return Boolean(True)
        else:
            return Boolean(False)
    def divisors(self,x):
        return []
    def coefficients(self,x):
        #print(self.sumSet[0].factorSet[0].var)
        if(self.sumSet[0].factorSet[0].var==x and self.cmp==LT):
            return [self.sumSet[0].factorSet[0].const]
        return []
    def isolate(self,x):
        sumSet=self.sumSet
        #A < B < C replaced with A < B and B < C
        if(len(self.sumSet)>2):
            constSet=[]
            for i in range(len(self.sumSet)-1):
                constSet.append(LinearConstraint( self.cmp , [ self.sumSet[i], self.sumSet[i+1] ] ) ) 
            simplifiedLinearConstraint=Junction(AND,constSet)
            return simplifiedLinearConstraint.isolate(x)

        #a = b replaced with a <= b and a >= b
        if(self.cmp==EQ):
            return Junction(AND, [LinearConstraint(LE,self.sumSet), LinearConstraint(GE,self.sumSet)]).isolate(x)
        #a != b replaced with a < b or a > b
        if(self.cmp==NE):
            return Junction(OR, [LinearConstraint(LT,self.sumSet), LinearConstraint(GT,self.sumSet)]).isolate(x)
        #a <= b replaced with a < b + 1
        if(self.cmp==LE):
            return LinearConstraint(LT, [ sumSet[0],sumSet[1].add(Factor()) ] ).isolate(x)
        #a >= b replaced with a + 1 > b
        if(self.cmp==GE):
            return LinearConstraint(GT, [ sumSet[0].add(Factor()),sumSet[1] ]).isolate(x)
        A = []
        B = []

        #Pass all the factors containing x to the left, and the rest to the right.
        #Result ax < t or ax > t
        for f in self.sumSet[0].factorSet:
            if(f.var==x):
                A.append(f)
            else:
                B.append(f.inverse())

        for f in self.sumSet[1].factorSet:
            if(f.var==x):
                A.append(f.inverse())
            else:
                B.append(f)        
        a=0
        for f in A:
            a+=f.const
        if(a<0):
            a=-a
            for i in range(len(B)):
                B[i]=B[i].inverse()
        ax=Sum([Factor(var=x,const=a)])
        t=Sum(B)
        return LinearConstraint(self.cmp,[ax,t])
    def getterms(self):
        if(self.cmp==GT):
            return [self.sumSet[1]]
        return []
  
    def isExists(self):
        return False
    def replaceax(self,t):
        return LinearConstraint(self.cmp,[t,self.sumSet[1]])
    def toZ3(self):
        cmp=self.cmp
        if(cmp==EQ):
            return self.sumSet[0].toZ3() == self.sumSet[1].toZ3()
        elif(cmp==NE):
            return self.sumSet[0].toZ3() != self.sumSet[1].toZ3()
        elif(cmp==LT):
            return self.sumSet[0].toZ3() < self.sumSet[1].toZ3()
        elif(cmp==LE):
            return self.sumSet[0].toZ3() <= self.sumSet[1].toZ3()
        elif(cmp==GT):
            return self.sumSet[0].toZ3() > self.sumSet[1].toZ3()
        elif(cmp==GE):
            return self.sumSet[0].toZ3() >= self.sumSet[1].toZ3()



class Junction:
    def __init__(self, op, constSet):
        self.constSet=constSet
        self.op=op
    def toString(self):
        op=self.op
        if(len(self.constSet)==0):
            return ""
        if(op==AND):
            strOp=" and "
        if(op==OR):
            strOp=" or "
        res=self.constSet[0].toString()
        for c in self.constSet[1:]:
            res+= strOp + c.toString()
        return res
    def Not(self):
        if(self.op==AND):
            self.op=OR
        else:
            self.op=AND
        for i in range(len(self.constSet)):
            self.constSet[i]=self.constSet[i].Not()
        return self
    def minfp(self,x):
        T=[]
        for c in self.constSet:
            v=c.minfp(x)
            if v != None:
                T.append(v)
        j=Junction(self.op,T)
        return j
    def divisors(self,x):
        D=[]
        for c in self.constSet:
            D+=c.divisors(x)
        return D
    def coefficients(self,x):
        A=[]
        for c in self.constSet:
            A+=c.coefficients(x)
        return A
    def isolate(self,x):
        return Junction(self.op,[c.isolate(x) for c in self.constSet])
    def getterms(self):
        T=[]
        for c in self.constSet:
            T+=c.getterms()
        return T    
    def isExists(self):
        return False
    def replaceax(self,t):
        C=[]
        for c in self.constSet:
            r=c.replaceax(t)
            if(r!=None):
                C.append(r)
        return Junction(self.op,C)
    def toZ3(self):
        if self.op==AND:
            op=z3.And
        else:
            op=z3.Or
        res=None
        for c in self.constSet:
            if res==None:
                res=c.toZ3()
            else:
                res=op(c.toZ3(),res)
        return res
class Exists:
    def __init__(self,varList,constraint,isNot=False):
        self.varList=varList
        self.constraint=constraint
        self.isNot=isNot
    def toString(self):
        if(self.isNot):
            return "Not( Exists( " + str(self.varList) + ", " + self.constraint.toString() + " ) )"
        else:
            return "Exists( " + str(self.varList) + ", " + self.constraint.toString() + " ) "
    def Not(self):
        self.isNot=not(self.isNot)
        return self
    def cooper(self,x=None):

        if(self.constraint.isExists()):
            self.constraint=self.constraint.cooper()
        #Replace Exists( [x0, ..., xn], P(x) ) with Exists([x0], Exists([x1], ... Exists( [xn], P(x) ) ) ... )
        if(len(self.varList)>1):
            res=self.constraint
            for v in self.varList[::-1]:
                res=Exists([v],res).cooper()
            return res


        if(x==None):
            x=self.varList[-1]

        #Restrain the constraints to ax < t, ax > t and x % d = 0 
        self=self.isolate(x)
        print(self.toString())

        #Get the formula : P(x)[ T \ ax < t, F \ ax > t ]  (-inf projection)
        f=self.constraint.minfp(x)
        print(f.toString())
        #Get the set of all divisors ( the set of d such that P contains a constraint x % d = 0 )
        D=self.constraint.divisors(x)

        #Get all the coefficients of x in ax < t ( the set of a such that P contains a constraint ax < t )
        A=self.constraint.coefficients(x)

        #Get all the terms in ax > t (the set of t such that P contains a constraint ax > t)
        T=self.constraint.getterms()
        #print(D)
        #print(A)
        d=None
        dp=None

        if(len(D)!=0):
            d=np.lcm.reduce(D)
            #print(d)
            if d==0:
                return f
        
        if(len(A)!=0):
            dp=np.lcm.reduce(A)
            print("dp: ", dp)
            if dp==0:
                return f
        print(A)

        if d==None:
            d=1
        if dp==None:
            dp=1
        
        S=[]
        for i in range(1,d+1):
            for t in T:
                #Compute P[t+i \ ax] and dp | t+i for each i from 1 to d, and for each ax in such that P(x) contains ax < t
                t=t.add(Factor(var=None,const=i))
                r=self.constraint.replaceax(t)
                if r!=None:
                    S.append( Junction( AND , [ r, DivConstraint( Sum ( [ Factor ( const=dp, var=None) ] ), t ) ] ) )
        f=Junction(OR,[f] + S)
        
        return f

    def isolate(self,x):
        return Exists(self.varList,self.constraint.isolate(x),self.isNot)

    def replaceax(self,term):
        return Exists(self.varList,self.constraint.replaceax(term))
    def isExists(self):
        return True
    def toZ3(self):
        return z3.Exists(self.varList,self.constraint.toZ3())


class DivConstraint:
    def __init__(self, diviseur, dividende, isNot=False):
        self.diviseur=diviseur
        self.dividende=dividende
        self.isNot=isNot
    def toString(self):
        return self.dividende.toString() + " % " + self.diviseur.toString() + " = 0"
    def Not(self):
        self.isNot=not(self.isNot)
        return self
    def divisors(self,x):
        print(self.diviseur.factorSet[0].const)
        if self.dividende.factorSet[0].var==x and len(self.dividende.factorSet)==1:
            return [self.diviseur.factorSet[0].const*self.dividende.factorSet[0].const]
        return []
    def minfp(self,x):
        return None
    def coefficients(self,x):
        return []
    def isolate(self,x):
        return self
    def getterms(self):
        return []
    def isExists(self):
        return False
    def replaceax(self,t):
        return None
    def toZ3(self):
        return self.dividende.toZ3() % self.diviseur.toZ3() == 0
