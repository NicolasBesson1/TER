from LexicalAnalysis import *
from constants import *

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
	
	if( not(L[i].typ==VAR and L[i+1].typ==COMA) ):
		return False
	while(L[i].typ==VAR and L[i+1].typ==COMA):
		print(L[i].val)
		print(L[i+1].val)
		i+=2
	print(L[i].val)
	i+=1
	if(L[i].typ!=ST):
		return False
	print(L[i].val)
	i+=1
	return True
		
		
#P -> exists(VL P)  | P and P | P or P | not P



def P(L):
	global i
	if(i==len(L)):
		return True
	elif(L[i].typ==OP):
		print(L[i].val)
		i+=1
		if(not P(L)):
			return False
		if(not(L[i].typ==CP)):
			return False
		print(L[i].val)
		i+=1
	elif(L[i].typ==EXQ):
		print(L[i].val)
		i+=1
		if(not L[i].typ==OP):
			return False
		print(L[i].val)
		i+=1
		if(not VL(L)):
			return False
		if(not P(L)):
			return False
		if(L[i].typ!=CP):
			return False	
		print(L[i].val)	
		i+=1
	elif(L[i].typ==NOT):
		print(L[i].val)
		i+=1
		if(L[i].typ!=OP):
			return False
		print(L[i].val)
		i+=1
		if(not P(L)):
			return False
		if(not L[i].typ==CP):
			return False
		print(L[i].val)
		i+=1
	elif( not(SEQCMP(L)) ):
		return False
	if(i==len(L)):
		return True
	if(L[i].IsBoolOperator()):
		print(L[i].val)
		i+=1
		return P(L) 
	return i==len(L)

#SEQCMP -> E <= E | E = E | E < E ...

def SEQCMP(L):
	global i
	if(not E(L)):
		return False
	if(not L[i].IsCmpOperator()):
		return False
	print(L[i].val)
	i+=1
	if(not E(L)):
		return False
	if L[i].IsCmpOperator():
		print(L[i].val)
		i+=1
		return SEQCMP(L)
	return True

#SEQBOOL -> SEQCMP | SEQCMP or SEQBOOL | SEQCMP and SEQBOOL
	

def SEQP(L):
	global i
	if(not P(L)):
		return False
	if(i==len(L)):
		return True
	if(L[i].typ==AND or L[i].typ==OR):
		print(L[i].val)
		i+=1
	
	return SEQCMP(L)
	
		
		
#E -> T + E | T - E  | T 

def E(L):
	global i
	
	if(not T(L)):
		return False
		
	
	if(i==len(L)):
		return True
		
	if(L[i].typ==PLUS or L[i].typ==MINUS):
		print(L[i].val)
		i+=1	
		if(not E(L)):
			return False
	return True

#T -> T * F  | TF | F

def T(L):
	global i
	if(not F(L)):
		return False
	if(i==len(L)):
		return True
	if(L[i].typ == MULT):
		print(L[i].val)
		i+=1
		if(not F(L)):
			return False
	if(i==len(L)):
		return True
	if(L[i].typ == VAR):
		return F(L)
	return True


def F(L):
	global i
	if(L[i].typ==MINUS):
		i+=1
		return F(L)
	if(L[i].typ==OP):
		print(L[i].val)
		i+=1
		if(not E(L)):
			return False
		print(L[i].val)
		i+=1
		return L[i-1].typ==CP
	if(L[i].typ==VAR or L[i].typ==INT):
		print(L[i].val)
		i+=1
		return True
	return False
		

test = "exists (e0, e1: 12e1 <= 93 - 90x2 + 35x3 -  68x4 + 87x5 - 92x6 - 3e0 and 79e1 >= >= -73 + 99x2 + 34x3 - 76x4 - 6x5 + 92x6 - 5e0 and 81e1 >= -21 - 67x2 - 40x3 + 19x4 + 72x5 - x6 - 92e0 and 95e1 >= -54 + 16x2 + 62x3 - 73x4 - 44x5 - 4x6 + 89e0)"

test2 = "exists(e0, lol: exists (e1,e2,e3: not ( e0 = e1 + e2 + e3 ) and exists (e4, e4 : lol <= e1 - e2 + e3 ) ) ) "


lex_list=get_lexema_list(test2)
'''
lol=""
for l in lex_list:
	lol+=str(l.val)+" "
print(lol)
print("End")'''
	

	
print(P(lex_list))
		
