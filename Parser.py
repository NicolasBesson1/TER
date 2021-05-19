import z3
from LexicalAnalysis import *
from Constants import *
from AbstractSyntaxTree import *
'''
F -> exists(VL, F) | J | C
VL -> x, | x,VL
J -> J and J | J or J | C
C -> S cmp S
S -> F + S 
F -> a | ax | -ax


F -> exists(VL P)  |  P and P  | P or P  | E cmp E | not P | And(P,P) | Or(P,P)
VL -> x, | x,VL
E -> E + T | E - T  | T  | E mod E
T -> T * F  | F
F -> x | n | ( E )  | -F
'''



def Parse(L):
	global i
	i=0
	return P(L)


#Variable List : x0, ..., xn, or x0, ..., xn :  
def VL(L):
	global i
	VarList=[]
	cond=False
	if(L[i].typ==OB):
		cond=True
		#print(L[i].val)
		i+=1
	while(L[i].typ==VAR and L[i+1].typ==COMA):
		VarList.append(L[i].val)
		#print(L[i].val)
		#print(L[i+1].val)
		i+=2
	if(L[i].typ!=VAR):
		#print(L[i].val)
		return False
	VarList.append(L[i].val)
	
	for v in VarList:
		pass
		#print(v.Val.val)
	
	i+=1
	if(cond):
		if(L[i].typ!=CB):
			return False
		#print(L[i].val)
		i+=1
	if(L[i].typ!=ST and L[i].typ!=COMA):
		#print("B")
		return False
	#print(L[i].val)
	i+=1
	#print(VarList)

	#print(VarList)
	return VarList


#P -> exists(VL P)  | P and P | P or P | not P



def P(L):
	global i
	if(i==len(L)):
		return True
	elif(L[i].typ==OP):
		#print(L[i].val)
		i+=1
		F1=P(L)
		if(F1==False):
			#print("C")
			return False
		if(not(L[i].typ==CP)):
			#print("D")
			return False
		#print(L[i].val)
		i+=1
		return F1
	elif(L[i].typ==AND or L[i].typ==OR):
		Operator=L[i]
		#print(L[i].val)
		i+=1
		if(L[i].typ!=OP):
			#print("E")
			return False
		#print(L[i].val)
		i+=1			
		F1=P(L)
		if(L[i].typ!=COMA):
			#print(L[i].val)
			#print("F")
			return False
		#print(L[i].val)
		i+=1			
		F2=P(L)
		if(L[i].typ!=CP):
			#print("G")
			return False
		#print(L[i].val)
		i+=1	
		return Junction(Operator,[F1,F2])	

	elif(L[i].typ==EXQ):
		#print(L[i].val)
		i+=1
		if(not L[i].typ==OP):
			#print("Z")
			return False
		#print(L[i].val)
		i+=1
		VarList=VL(L)
		if(VarList==False):
			#print("F2")
			return False
		F1=P(L)
		if(F1==False):
			#print("G2")
			return False
		F1=Exists(VarList,F1)
		if(L[i].typ!=CP):
			#print("H")
			return False	
		#print(L[i].val)	
		i+=1
		return F1
	elif(L[i].typ==NOT):
		#print(L[i].val)
		i+=1
		if(L[i].typ!=OP):
			#print("I")
			return False
		#print(L[i].val)
		i+=1
		F1=P(L)
		if(F1==False):
			#print("J")
			return False
		F1=F1.Not()
		if(not L[i].typ==CP):
			#print("K")
			return False
		#print(L[i].val)
		i+=1
		return F1
	else:
		F1=D(L)
		if(F1==False):
			#print("L")
			return False
		return F1
		
	
	return F1

def D(L):
	global i
	c=C(L)
	if(c==False):
		#print("NN")
		return False
	conjunctionSet=[c]
	while(L[i].typ == OR):
		#print(L[i].val)
		i+=1
		c=C(L)
		if(c==False):
			#print("OO")
			return False
		conjunctionSet.append(c)
	return Junction(OR,conjunctionSet)

def C(L):
	global i
	c=CONSTRAINT(L)
	if(c==False):
		#print("LL")
		return False
	constraintSet=[c]
	while(L[i].typ == AND):
		#print(L[i].val)
		i+=1
		c=CONSTRAINT(L)
		if(c==False):
			#print("MM")
			return False
		constraintSet.append(c)
	return Junction(AND,constraintSet)


#SEQCMP -> E <= E | E = E | E < E ...

def CONSTRAINT(L):
	global i
	sumSet=[]
	sumi=S(L)
	if(sumi==False):
		print("AA")
		return False
	if(L[i].typ==MOD):
		#print(L[i].val)
		i+=1
		dividende=sumi
		diviseur=S(L)
		if(diviseur==False or (L[i].typ != EQ and L[i].typ != NE) or not(diviseur.isConstant())):
			print("PP")
			return False
		#print(L[i].val)
		cmp=L[i].typ
		i+=1
		res=S(L)
		if(not res.isZero()):
			#print("QQ")
			return False
		return DivConstraint(diviseur,dividende,isNot=(cmp==NE))

	sumSet.append(sumi)
	if(not L[i].IsCmpOperator()):
		#print("CC")
		return False
	cmp=L[i].typ

	while(L[i].IsCmpOperator()):
		if(L[i].typ!=cmp):
			#print("DD")
			return False
		#print(L[i].val)
		i+=1
		sumi=S(L)
		if(sumi==False):
			#print("BB")
			return False
		sumSet.append(sumi)
	return LinearConstraint(cmp,sumSet)
	

		
		
#S -> F + S | F - S

def S(L):
	global i
	isMinus=False
	if(L[i].typ==MINUS):
		isMinus=True
		#print(L[i].val)
		i+=1

	if(L[i].typ!=INT and L[i].typ!=VAR):
		#print("EE")
		return False
	if(L[i].typ==VAR):
		if(isMinus):
			f=Factor(var=L[i].val,const=-1)
		else:
			f=Factor(var=L[i].val, const=1)
		#print(L[i].val)
		i+=1
	else:
		if(isMinus):
			constf=-int(L[i].val)
		else:
			constf=int(L[i].val)
		varf=None
		#print(L[i].val)
		i+=1
		if(L[i].typ==VAR):
			varf=str(L[i].val)
			#print(L[i].val)
			i+=1
		f=Factor(var=varf,const=constf)
	F=[]
	F.append(f)
	while(L[i].typ==PLUS or L[i].typ==MINUS):
		isMinus=False
		if(L[i].typ==MINUS):
			isMinus=True
		#print(L[i].val)
		i+=1
		if(L[i].typ!=INT and L[i].typ!=VAR):
			#print("GG")
			return False
		if(L[i].typ==VAR):
			if(isMinus):
				f=Factor(var=L[i].val,const=-1)
			else:
				f=Factor(var=L[i].val,const=1)
			i+=1
		else:
			if(isMinus):
				constf=-int(L[i].val)
			else:
				constf=int(L[i].val)
			varf=None
			#print(L[i].val)
			i+=1
			if(L[i].typ==VAR):
				varf=str(L[i].val)
				#print(L[i].val)
				i+=1
			f=Factor(var=varf,const=constf)
		F.append(f)
	return Sum(F)

#T -> T * F  | TF | F

test = "Exists(x: 8x > 5 and 30x < 798 and x % 4 == 0)"
'''test = "exists (e0: 12x1 <= 93 - 90x2 + 35x3 -  68x4 + 87x5 - 92x6 - 3e0 and 79x1 >= -73 + 99x2 + 34x3 - 76x4 - 6x5 + 92x6 - 5e0 and \
81x1 >= -21 - 67x2 - 40x3 + 19x4 + 72x5 - x6 - 92e0 and 95x1 >= -54 + 16x2 + 62x3 - 73x4 - 44x5 - 4x6 + 89e0 or \
5x2 + 8x3 + 3x4 + e0 <= 0 and e0 % 45 == 0 and 2e0 % 13 == 0 )"'''
LL=get_lexema_list(test)

F1 = Parse(LL)

#print(test)
#print(F1.toString())
F2=F1.cooper()

#print(F2.toString())
#print(F1.ASTtoZ3())
 
Int=z3.Int
x=Int("x")
y=Int("y")
z=Int("z")
Lal = z3.Exists([x], z3.And(z3.And(8*x > 5, 30*x < 798), x % 4 == 0) )

So=z3.Solver()


Lol = F2.toZ3()
print(Lol)
So.add(Lal)
res=So.check()
print(res)
if(str(res)=="sat"):
    print(So.model())
    
  
#print(So.model())

#test2 = "exists(e0: exists (e1,e2,e3 : not ( e0 = e1 + e2 + e3 ) and exists ( e4 : lol <= e1 - e2 + e3 ) ) ) "

lex_list=get_lexema_list(test)

'''for l in lex_list:
	print (l.val)'''
	
F1=Parse(lex_list)
#F2=F1.cooper()
#F1=Parse(lex_list).toString()

#print(test)
#print(F1.toString())
#print(F2.toString())

#lex_list=get_lexema_list(A)
#print(A)
for l in lex_list:
	#print (l.val)
	pass





'''
Formula= correctZ3String(str(Not(Exists([x,y], Not(Or(Not(And(x+3<y,x-3==y)), Not(And(x+0==x,y+x>y))))))))
print(Formula)
lex_list=get_lexema_list(Formula)
A=Parse(lex_list)
print(A.ASTtoZ3())
A=A.NNF()
print(A.ASTtoZ3())
'''
