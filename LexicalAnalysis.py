

from constants import *

class Lexema():
	def __init__(self, typ, val):
		self.typ=typ
		self.val=val
	def PrintVal(self):
		print(self.val)
	
	

def IsLetter(c):
	nc=ord(c)
	na=ord('a')
	nz=ord('z')
	nA=ord('A')
	nZ=ord('Z')
	return ((na<=nc) and (nc <= nz)) or ((nA<=nc) and (nc<=nZ))
	
def IsNumber(c):
	nc=ord(c)
	n0=ord('0')
	n9=ord('9')
	return ((n0<=nc) and (nc<=n9))

def IsSeparator(c):
	nc=ord(c)
	nspace=ord(' ')
	ntab=ord('	')
	return nc==nspace or nc==ntab

def IsOpPar(c):
	return c=='('

def IsClosePar(c):
	return c==')'
	
def IsIntOperator(c):
	return c=='+' or c=='-' or c=='*' or c=='/'


def IsCmpOperator(c):
	return c=='<' or c=='>' or c=='=' or c=='!'

def IsComa(c):
	return c==','

def IsSuchThat(c):
	return c==':'

i=0

def next_lexema(formula):
	global i
	
	
	#if no lexemas to read
	if(i>=len(formula)):
		return None
	#jump all the separators
	while(IsSeparator(formula[i])):
		i+=1
		if(i>=len(formula)):
			return None
			
	#if it is an opening parenthesis, a closing parenthesis or an integer operator, a coma or ':' (such that)
	if(IsOpPar(formula[i])):
		i+=1
		return Lexema(OP,'(')
	if(IsClosePar(formula[i])):
		i+=1
		return Lexema(CP,')')
	if(formula[i]=='+'):
		i+=1
		return Lexema(PLUS,'+')
	if(formula[i]=='-'):
		i+=1
		return Lexema(MINUS,'-')	
	if(formula[i]=='*'):
		i+=1
		return Lexema(MULT,'*')
	if(IsSuchThat(formula[i])):
		i+=1
		return Lexema(ST,':')
	if(IsComa(formula[i])):
		i+=1
		return Lexema(COMA,',')
		
	lex=""
	
	#Variable names can be written with format l1 ... lN n1 ... nM with li being a letter and ni being a number
	if(IsLetter(formula[i])):
		while(IsLetter(formula[i])):
			lex+=formula[i]
			i+=1
			if(i>=len(formula)):
				return Lexema(VAR,lex)
				
		#If the sequence of letters form a boolean operator or an existential quantifier (variables cannot be named like these)
		if( (lex=="and") and IsSeparator(formula[i]) ):
			return Lexema(AND,"and")
		if( (lex=="or") and IsSeparator(formula[i]) ):
			return Lexema(OR,"or")
		if( (lex=="not") and IsSeparator(formula[i]) ):
			return Lexema(NOT,"not")
		if( (lex=="exists") and IsSeparator(formula[i]) ):
			return Lexema(EXQ,"exists")
			
		while(IsNumber(formula[i])):
			lex+=formula[i]
			i+=1
			if(i>=len(formula)):
				return Lexema(VAR,lex)
		return Lexema(VAR,lex)
	
	#If the next lexema is composed by numbers
	if(IsNumber(formula[i])):
		while(IsNumber(formula[i])):
			lex+=formula[i]
			i+=1
			if(i>=len(formula)):
				return Lexema(INT,lex)
		return Lexema(INT,lex)
	
	#If the next lexema is the comparator '!=' :
	if(formula[i]=='!'):
		i+=1
		if(formula[i]=='='):
			i+=1
			return Lexema(NE,"!=")
		return None
		
	#If the next lexema is either a ">=" or a "<="
	lex=""
	if(formula[i]=='<'):
		lex+=formula[i]
		i+=1
		if(formula[i]=='='):
			lex+=formula[i]
			i+=1
			return Lexema(LE,"<=")
		return Lexema(LT,"<")
	if(formula[i]=='>'):
		lex+=formula[i]
		i+=1
		if(formula[i]=='='):
			lex+=formula[i]
			i+=1
			return Lexema(GE,"<=")
		return Lexema(GT,"<")
	#If the lexema is an equality
	if(formula[i]=='='):
		i+=1
		return Lexema(EQ,"=")
	
	

	
	
def get_lexema_list(formula):
	global i
	lex_list=[]
	while(True):
		lex=next_lexema(formula)
		if lex==None:
			return lex_list
		else:
			lex_list.append(lex)
	return lex_list
	
		
		
