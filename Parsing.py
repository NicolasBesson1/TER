from LexicalAnalysis import *
from constants import *
from AbstractSyntaxTree import *
'''
P -> exists(VL P)  |  P and P  | P or P  | E cmp E | not P
VL -> x, | x,VL
E -> E + T | E - T  | T  | E mod E
T -> T * F  | F
F -> x | n | ( E )  | -F
'''


i=0

#VL -> x, | x,VL
#VL (or variable list) is a sequence of the form v1, v2, ..., vN



def VL(L):
	global i
	VarList=[]
		
	while(L[i].typ==VAR and L[i+1].typ==COMA):
		VarList.append(AST(L[i],[]))
		#print(L[i].val)
		#print(L[i+1].val)
		i+=2
	if(L[i].typ!=VAR):
		return False
	VarList.append(AST(L[i],[]))
	#print(L[i].val)
	i+=1
	if(L[i].typ!=ST):
		#print("B")
		return False
	#print(L[i].val)
	i+=1
	#print(VarList)
	return VarList


#P -> exists(VL P)  | P and P | P or P | not P



def P(L):
	global i
	if(i==len(L)):
		return None
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
	elif(L[i].typ==EXQ):
		#print(L[i].val)
		i+=1
		if(not L[i].typ==OP):
			#print("E")
			return False
		#print(L[i].val)
		i+=1
		VarList=VL(L)
		
		if(VarList==False):
			#print("F")
			return False
		F1=P(L)
		if(F1==False):
			#print("G")
			return False
		VarList.append(F1)
		F1=AST(Lexema(EXQ,"exists"),VarList)
		if(L[i].typ!=CP):
			#print("H")
			return False	
		#print(L[i].val)	
		i+=1
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
		F1=AST(Lexema(NOT,"not"),[F1])
		if(not L[i].typ==CP):
			#print("K")
			return False
		#print(L[i].val)
		i+=1
	else:
		F1=SEQCMP(L)
		if(F1==False):
			#print("L")
			return False
		
		
	if(i==len(L)):
		return F1
	if(L[i].IsBoolOperator()):
		Operator=L[i]
		#print(L[i].val)
		i+=1
		F2=P(L)
		if(F2==False):
			#print("M")
			return False
		return AST(Operator,[F1,F2])
	
	return F1

#SEQCMP -> E <= E | E = E | E < E ...

def SEQCMP(L):
	global i
	F1=E(L,False)
	if(F1==False):
		#print("O")
		return False
	Operator=L[i]
	if(not L[i].IsCmpOperator()):
		#print("P")
		return False
	#print(L[i].val)
	i+=1
	F2=E(L,False)
	if(F2==False):
		#print("Q")
		return False
	return AST(Operator,[F1,F2])

		
		
#E -> T + E | T - E  | T 

def E(L, isNegative):
	global i
	F1=T(L,isNegative)
	if(F1==False):
		#print("R")
		return False
		
	
	if(i==len(L)):
		return F1
	
	if(L[i].typ==PLUS or L[i].typ==MINUS):
		Operator=L[i]
		#print(L[i].val)
		i+=1	
		F2=E(L,Operator.typ==MINUS)
		if(F2==False):
			#print("S")
			return False
		return AST(Lexema(PLUS,"+"),[F1,F2])
	return F1

#T -> T * F  | TF | F

def T(L,isNegative):
	global i
	F1=F(L,isNegative)
	if(F1==False):
		#print("T")
		return False
	if(i==len(L)):
		return F1
	if(L[i].typ == MULT):
		Operator=L[i]
		#print(L[i].val)
		i+=1
		F2=F(L,False)
		if(F2==False):
			#print("U")
			return False
		return AST(Operator,[F1,F2])
	if(i==len(L)):
		return F1
	if(L[i].typ == VAR):
		F2=F(L,False)
		if(F2==False):
			#print("V")
			return False
		return AST(Lexema(MULT,"*"),[F1,F2])
	return F1


def F(L,isNegative):
	global i
	if(L[i].typ==MINUS):
		i+=1
		F1=F(L,isNegative)	
		return AST(Lexema(MINUS,"-"),[F1])
	if(L[i].typ==OP):
		#print(L[i].val)
		i+=1
		F1=E(L)
		if(F1==False):
			#print("W")
			return False
		#print(L[i].val)
		i+=1
		if(L[i-1].typ!=CP):
			#print("X")
			return False
		if(isNegative):
			return AST(Lexema(MINUS,"-"),[F1])
		return F1
	if(L[i].typ==VAR or L[i].typ==INT):
		#print(L[i].val)
		i+=1
		if(isNegative):
			return AST(Lexema(MINUS,"-"),[AST(L[i-1],[])])
		return AST(L[i-1],[])
	print("Y", L[i].val)
	return False
		

test = "exists (e0, e1: 12e1 <= 93 - 90x2 + 35x3 -  68x4 + 87x5 - 92x6 - 3e0 and 79e1 >= -73 + 99x2 + 34x3 - 76x4 - 6x5 + 92x6 - 5e0 and 81e1 >= -21 - 67x2 - 40x3 + 19x4 + 72x5 - x6 - 92e0 and 95e1 >= -54 + 16x2 + 62x3 - 73x4 - 44x5 - 4x6 + 89e0)"

test2 = "exists(e0, lol: exists (e1,e2,e3 : not ( e0 = e1 + e2 + e3 ) and exists ( e4 : lol <= e1 - e2 + e3 ) ) ) "


lex_list=get_lexema_list(test2)
'''
lol=""
for l in lex_list:
	lol+=str(l.val)+" "
print(lol)
print("End")'''
	
F1=P(lex_list)
F1.DepthWalk()
print(F1.ASTtoZ3())
