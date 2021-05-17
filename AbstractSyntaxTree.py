from LexicalAnalysis import *
from Constants import *

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
        self.factorSet.append(f)
        return self
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
    def cooper(self,x):


        sumSet=self.sumSet
        #A < B < C replaced with A < B and B < C
        if(len(self.sumSet)>2):
            constSet=[]
            for i in range(len(self.sumSet)-1):
                constSet.append(LinearConstraint( self.cmp , [ self.sumSet[i], self.sumSet[i+1] ] ) ) 
            simplifiedLinearConstraint=Junction(AND,constSet)
            return simplifiedLinearConstraint.cooper(x)

        #a = b replaced with a <= b and a >= b
        if(self.cmp==EQ):
            return Junction(AND, [LinearConstraint(LE,self.sumSet), LinearConstraint(GE,self.sumSet)]).cooper(x)
        #a != b replaced with a < b or a > b
        if(self.cmp==NE):
            return Junction(OR, [LinearConstraint(LT,self.sumSet), LinearConstraint(GT,self.sumSet)]).cooper(x)
        #a <= b replaced with a < b + 1
        if(self.cmp==LE):
            return LinearConstraint(LT, [ sumSet[0],sumSet[1].add(Factor()) ] ).cooper(x)
        #a >= b replaced with a + 1 > b
        if(self.cmp==GE):
            return LinearConstraint(GT, [ sumSet[0].add(Factor()),sumSet[1] ]).cooper(x)
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

        #We assume the cmp in ax cmp t is either < or >
        if(self.cmp==LT):
            return Boolean(True)
        else:
            return Boolean(False)
        




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
    def cooper(self,x):
        j=Junction(self.op,[c.cooper(x) for c in self.constSet])
        return j
       
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
        if(x==None):
            x=self.varList[0]
        f=self.constraint.cooper(x)
        return f

class DivConstraint:
    def __init__(self, diviseur, dividende, isNot=False):
        self.diviseur=diviseur
        self.dividende=dividende
    def toString(self):
        return str(self.dividende) + " % " + self.diviseur.toString() + " = 0"
    def Not(self):
        self.isNot=not(self.isNot)
        return self