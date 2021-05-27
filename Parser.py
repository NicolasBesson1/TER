import z3
from LexicalAnalysis import *
from Constants import *
from AbstractSyntaxTree import *
from ISLandZ3Testing import *
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
	if(len(L)==0):
		return Boolean(True)
	if(len(L)==2):
		if(L[0].typ==OP and L[1].typ==CP):
			return Boolean(True)
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
		
	if(cond):
		if(L[i].typ==VAR):
			if(L[i+1].typ!=CB):
				print("bad")
				return False
			VarList.append(L[i].val)
			i+=2
			if(L[i].typ!=ST and L[i].typ!=COMA):
				print("worse")
				return False
			return VarList
		else:
			print("bader")
			return False
	if(L[i].typ==VAR and L[i+1].typ==ST):
		VarList.append(L[i].val)
		i+=2
		#print(L[i].val)
		return VarList
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
			print("C")
			return False
		if(not(L[i].typ==CP)):
			print("D")
			return False
		#print(L[i].val)
		i+=1
		return F1
	elif(L[i].typ==AND or L[i].typ==OR):
		Operator=L[i].typ
		#print(L[i].val)
		i+=1
		if(L[i].typ!=OP):
			print("E")
			return False
		#print(L[i].val)
		i+=1			
		F1=P(L)
		if(L[i].typ!=COMA):
			print(L[i].val)
			print("F")
			return False
		#print(L[i].val)
		i+=1			
		F2=P(L)
		if(L[i].typ!=CP):
			print("G")
			return False
		#print(L[i].val)
		i+=1	
		return Junction(Operator,[F1,F2])	

	elif(L[i].typ==EXQ):
		#print(L[i].val)
		i+=1
		if(not L[i].typ==OP):
			print("Z")
			return False
		#print(L[i].val)
		i+=1
		VarList=VL(L)
		if(VarList==False):
			print("F2")
			return False
		F1=P(L)
		if(F1==False):
			print("G2")
			return False
		F1=Exists(VarList,F1)
		if(L[i].typ!=CP):
			print("H")
			return False	
		#print(L[i].val)	
		i+=1
		return F1
	elif(L[i].typ==NOT):
		print(L[i].val)
		i+=1
		if(L[i].typ!=OP):
			print("I")
			return False
		#print(L[i].val)
		i+=1
		F1=P(L)
		if(F1==False):
			print("J")
			return False
		F1=F1.Not()
		if(not L[i].typ==CP):
			print("K")
			return False
		#print(L[i].val)
		i+=1
		return F1
	else:
		F1=D(L)
		if(F1==False):
			print("L")
			return False
		return F1
		
	
	return F1

def D(L):
	global i
	c=C(L)
	if(c==False):
		print("NN")
		return False
	conjunctionSet=[c]
	while(L[i].typ == OR):
		#print(L[i].val)
		i+=1
		c=C(L)
		if(c==False):
			print("OO")
			return False
		conjunctionSet.append(c)
	return Junction(OR,conjunctionSet)

def C(L):
	global i
	c=CONSTRAINT(L)
	if(c==False):
		print("LL")
		return False
	constraintSet=[c]
	while(L[i].typ == AND):
		#print(L[i].val)
		i+=1
		c=CONSTRAINT(L)
		if(c==False):
			print("MM")
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
			print("QQ")
			return False
		return DivConstraint(diviseur,dividende,isNot=(cmp==NE))

	sumSet.append(sumi)
	if(not L[i].IsCmpOperator()):
		print("CC")
		return False
	cmp=L[i].typ

	while(L[i].IsCmpOperator()):
		if(L[i].typ!=cmp):
			print("DD")
			return False
		#print(L[i].val)
		i+=1
		sumi=S(L)
		if(sumi==False):
			print("BB")
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
	#print("AQUITA")
	if(L[i].typ==VAR):
		if(isMinus):
			f=Factor(var=L[i].val,const=-1)
		else:
			f=Factor(var=L[i].val, const=1)
		#print(L[i].val)
		i+=1
	else:
		#print(L[i].val)
		if(isMinus):
			constf=-int(L[i].val)
			i+=1
		else:
			constf=int(L[i].val)
			i+=1
		varf=None
		if(L[i].typ==MULT):
			#print("Yes good sir", L[i].val)
			i+=1
		
		
		#print("NE",L[i].val)
		#print(L[i].typ)
		if(L[i].typ==VAR):
			varf=str(L[i].val)
			#print(L[i].val)
			i+=1
		f=Factor(var=varf,const=constf)
	F=[]
	F.append(f)
	#print(f.toString())
	while(L[i].typ==PLUS or L[i].typ==MINUS):
		#print("SISA")
		isMinus=False
		if(L[i].typ==MINUS):
			isMinus=True
			
		#print("A",L[i].val)
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
			#print(L[i].val)
			if(isMinus):
				constf=-int(L[i].val)
			else:
				constf=int(L[i].val)
			varf=None
			#print(L[i].val)
			i+=1
			if(L[i].typ==MULT):
				#print(L[i].val)
				i+=1
			if(L[i].typ==VAR):
				varf=str(L[i].val)
				#print(L[i].val)
				i+=1
			f=Factor(var=varf,const=constf)
		F.append(f)
		#print(f.toString())
	return Sum(F)

		

#T -> T * F  | TF | F

def projection_test(n=5,m=7):
	P=polyedre(n=n,m=m)
	F1=conjunction(P)
	print("Random polyhedron", F1)
	E1=z3.Exists(z3.Int("x0"),F1)
	#print("Expected formula after projection", E1)
	#t=z3.Tactic("qe")
	#Formula1 = t(E1)
	#print("Expected formula after projection, with z3 quantifier elimination", Formula1)
	a=Parse(get_lexema_list(str(E1))).cooper().toZ3()
	#print("Expected formula after projection, with my implementation of quantifier elimination", a)
	
	F2=isl_intersection(P)
	Fp=project(F2)
	Str="(" + get_formula(Fp) + ")"
	
	
	LL=get_lexema_list(Str)
	E2=Parse(LL)
	#print("Formula given by ISL after projection", E2.toZ3())
	#Formula2=t(E2.toZ3())
	
	#print("Formula given by ISL after projection, after z3 quantifier elimination", Formula2)
	b=E2.cooper().toZ3()
	#print("Formula given by ISL after projection, after my implementation of quantifier elimination", b)	

	my_solver = z3.Solver()
	
	my_solver.add(z3.Xor(a,b))
	r=my_solver.check()==z3.unsat
	print("Result with my implementation of quantifier elimination", r)
	return r
	
	
	
	
	
	#z3_solver = z3.Then("smt","qe").solver()
	#z3_solver.add(z3.Xor(E1,E2.toZ3()))
	#print("Result with z3 quantifier elimination", z3_solver.check()==z3.unsat)
	
	#z3_solver = z3.Then("smt","qe").solver()
	#z3_solver.add(z3.Not(z3.Implies(E1,E2.toZ3())))
	#print("A => B", z3_solver.check()==z3.unsat)
	#z3_solver = z3.Then("smt", "qe").solver()
	#z3_solver.add(z3.Not(z3.Implies(E2.toZ3(),E1)))
	#print("B => A", z3_solver.check()==z3.unsat)
	
	
	'''SE=str(E)
	LLE=get_lexema_list(SE)
	Lol = Parse(LLE)
	print(Lol.toString())
	Unch = Lol.cooper()
	print("unch",Unch.toString())'''
	
	'''Fp=isl_intersection(P)
	Fp=project(Fp)
	Str="(" + get_formula(Fp) +")"
	print(Str)
	LL=get_lexema_list(Str) 
	Ep=Parse(LL)
	Anch = Ep.cooper()
	
	#print(E)
	#print(Ep.toString())
	print("Anch ", Anch.toString())
	Sol=z3.Solver()
	Sol.add(z3.Xor(Unch.toZ3(),Anch.toZ3()))
	print(Sol.check()==z3.unsat)'''
	
	
	

#print(test)
'''test = "exists (e0: 12x1 <= 93 - 90x2 + 35x3 -  68x4 + 87x5 - 92x6 - 3e0 and 79x1 >= -73 + 99x2 + 34x3 - 76x4 - 6x5 + 92x6 - 5e0 and \
81x1 >= -21 - 67x2 - 40x3 + 19x4 + 72x5 - x6 - 92e0 and 95x1 >= -54 + 16x2 + 62x3 - 73x4 - 44x5 - 4x6 + 89e0 or \
5x2 + 8x3 + 3x4 + e0 <= 0 and e0 % 45 == 0 and 2e0 % 13 == 0 )"'''
#LL=get_lexema_list(test)

#print("YES",test)

#F1 = Parse(LL)
#print(F1.toString())
#E = F1.toZ3()
#print(E)
#LE = get_lexema_list(str(E))
#print(LE)
#print(Parse(LE).toString())



#print(test)
#print(F1.toString())
#F2=F1
#print(F2.toString())
#print(F2.toString())
#print(F1.ASTtoZ3())
 
#print(res)
#if(str(res)=="sat"):
    #print(So.model())


  
#print(So.model())

#test2 = "exists(e0: exists (e1,e2,e3 : not ( e0 = e1 + e2 + e3 ) and exists ( e4 : lol <= e1 - e2 + e3 ) ) ) "

#lex_list=get_lexema_list(test)

'''for l in lex_list:
	print (l.val)'''
	
#F1=Parse(lex_list)
#F2=F1.cooper()
#F1=Parse(lex_list).toString()

#print(test)
#print(F1.toString())
#print(F2.toString())

#lex_list=get_lexema_list(A)
#print(A)
r=projection_test()
while(r):
    projection_test()





'''
Formula= correctZ3String(str(Not(Exists([x,y], Not(Or(Not(And(x+3<y,x-3==y)), Not(And(x+0==x,y+x>y))))))))
print(Formula)
lex_list=get_lexema_list(Formula)
A=Parse(lex_list)
print(A.ASTtoZ3())
A=A.NNF()
print(A.ASTtoZ3())
'''
