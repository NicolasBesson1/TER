from LexicalAnalysis import *
from constants import *

class AST():
	def __init__(self, Val, Children):
		self.Val=Val
		self.Children=Children
	def GetValue(self):
		return self.Value
	def DepthWalk(self):
		if(self==None):
			return
		print(self.Val.val)
		for c in self.Children:
			c.DepthWalk()

Example=AST(Lexema(EXQ,"exists"),[AST(Lexema(VAR,"x"),[]),AST(Lexema(VAR,"y"),[]), AST(Lexema(EQ,"="),[AST(Lexema(PLUS,"+"),[AST(Lexema(VAR,"x"),[]),AST(Lexema(VAR,"y"),[])]), AST(Lexema(VAR,"z"),[])]) ] )
		

Example.DepthWalk()
