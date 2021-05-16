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
    def __init__(self, var=None, const=0):
        self.var=var
        self.const=const
    def toString(self):
        if(var!=None):
            return str(self.const)
        elif(const!=0):
            return str(self.const) + str(self.var)
        else:
            return "0"
    def isZero(self):
        return self.const==0
    def isConst(self):
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

class Comparison:
    def __init__(self,cmp,sumSet):
        self.cmp=cmp
        self.sumSet
    def toString(self):
        
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
        for s in sumSet[1:]:
            res += strCmp + s.toString()
        return res
    def Not(self):
        if(cmp==EQ):
            return Comparison(NE,self.sumSet)
        elif(cmp==NE):
            return Comparison(EQ,self.sumSet)
        elif(cmp==LT):
            return Comparison(GE,self.sumSet)
        elif(cmp==LE):
            return Comparison(GT,self.sumSet)
        elif(cmp==GT):
            return Comparison(LE,self.sumSet)
        elif(cmp==GE):
            return Comparison(LT,self.sumSet)
        return None

class Junction:
    def __init__(self, op, constSet):
        self.constSet=constSet
        self.op=op
    def toString(self):
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
       
class Exists:
    def __init__(self,varList,constraint,isNot=False):
        self.var=varList
        self.constraint=constraint
        self.isNot=isNot
    def toString(self):
        if(self.isNot):
            return "Not( Exists( " + str(varList) + ", " + self.const.toString() + " ) )"
        else:
            return "Exists( " + str(varList) + ", " + self.const.toString() + " ) "
    def Not(self):
        self.isNot=not(self.isNot)
        return self
