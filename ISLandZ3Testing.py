from z3 import *
from islpy import *
from random import *



#Input: a list of strings
#Output: a string corresponding to the concatanation of al the strings in the list
def concat(T):
        result = ""
        for i in T:
                result+=i
        return result

a=Set("{ [x0,x1,x2] : (x1 + 3x2 >= x0 and x0 > x2 and 2x1 + 3 >= 7x0 + x2) or (x1 > x2 +3 and x2 + x0 <= 14 and 13 + 3x0 >=7) } ")

print(a) 

bsets = a.get_basic_sets()
print("Printing basic sets")
for bset in bsets:
	print(bset)
	
	



N = 8
M = 3

#Renvoit une liste d'inegalites en Z3 correspondant a un polyedre convexe
def polyedre(n=N,m=M):
        satisfaisable=False

        # Tant que l'ensemble n'est pas satisfaisable
        # donc tant que le polyedre soit vide
        while(not(satisfaisable)):
        #Declaration de variables
                S=Solver()
                #A est une matrice de n*m, X est un vecteur de dimension n et B de m
                #n est le nombre d'inconnues du systeme d'innequations
                #m est le nombre d'inegalites du systeme
                #A[i] correspond aux coefficients des variables a l'inegalite i
                A=[[randint(-100,100) for i in range(n)] for j in range(m)]
                #X est l'ensemble des variables
                X=[Int("x"+str(i)) for i in range(n)]
                #B correspond aux membres de droite de chaque inegalite
                B=[randint(-100,100) for i in range(m)]
                polyedre=[]
                

                for i in range(len(A)):
                        #Termes contient le membre de gauche de l'inegalite:
                        
                        termes=[]
                        for j in range(len(X)):
                                termes+=[A[i][j]*X[j]]


                        #On ajoute a S l'inegalite:
                        # sum(A[i][j]*X[j]) <= B[i]
                        S.add(sum(termes)<=B[i])
                        polyedre.append(sum(termes)<=B[i])
                #print(S.check()==sat)
                '''for x in X:
                        S.add(x>=0)
                        polyedre.append(x>=0)'''
                satisfaisable=S.check()==sat
        #print(S.check())

        return polyedre
   
def print_list(L):
	for l in L:
		print(l)
   


#Input: An array T containing formulas
#Output: the conjunction of every formula
def conjunction(T):
        if(len(T)>0):
                result=T[0]
                for i in T[1:]:
                        result=And(result,i)
                return result
        return True

P=polyedre(7,4)
F=conjunction(P)


#Input: a Z3 formula
#Output: an ISL set defined by the formula
def inequality_to_set(formula):
        #Assuming the variables in "formula" have the format x0,x1, ... xN
        arguments = concat( [concat(["x",str(i),","]) for i in range(N-1) ]) + str("x") + str(N-1)
        return Set("{ ["+arguments+"] : " + str(formula) + "}" )


#Input: poly is an array with z3 inequalities
#Output: The intersection of the m sets created with polyedre()
def isl_intersection(poly):
        isl_poly=inequality_to_set(poly[0])
        for i in poly:
                isl_poly=isl_poly.intersect(inequality_to_set(i))
        return isl_poly


S=isl_intersection(P)
print(S)

print("After projection :")

res=S.project_out(dim_type.out,first=0,n=1).project_out(dim_type.out,first=0,n=1)
print(res)

S=Set("{ [x,y] : 3x != y }")
Z=S.project_out(dim_type.out,first=1,n=1)
print(S)

