from LexicalAnalysis import *


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
		i+=2
	return True
		
		

def P(L):
	global i
	if(L[i].typ==EXQ):
		i+=1
		if(L[i].typ==OP):
			i+=1
		if(!VL(L)):
			return False
		if(!P(L)):
			return False
		return L[i].typ==CP
		
	if(L[i].typ==NOT):
		i+=1
		return P(L)
	
	if(!E(L)):
		return False
	
	
		

test = "exists (e0, e1: 12e1 <= 93 - 90x2 + 35x3 - 68x4 + 87x5 - 92x6 - 3e0 and 79e1 >= -73 + 99x2 + 34x3 - 76x4 - 6x5 + 92x6 - 5e0 and 81e1 >= -21 - 67x2 - 40x3 + 19x4 + 72x5 - x6 - 92e0 and 95e1 >= -54 + 16x2 + 62x3 - 73x4 - 44x5 - 4x6 + 89e0)"

lex_list=get_lexema_list(test)
