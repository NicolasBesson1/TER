from LexicalAnalysis import *
from constants import *
from z3 import *

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
	def AddChild(self,Child):
		self.Children.append(Child)
	def ASTtoZ3(self):
		if(self.Val.typ==EXQ):
			l=len(self.Children)
			A=self.Children[l-1].ASTtoZ3()
			return Exists([Int(self.Children[i].Val.val) for i in range(l-2)],A)
		if(self.Val.typ==NOT):
			return Not(self.Children[0].ASTtoZ3())
		if(self.Val.typ==PLUS):
			return self.Children[0].ASTtoZ3() + self.Children[1].ASTtoZ3()
		if(self.Val.typ==MINUS):
			if(len(self.Children)==2):
				return self.Children[0].ASTtoZ3() - self.Children[1].ASTtoZ3()
			else:
				return -self.Children[0].ASTtoZ3()
		if(self.Val.typ==MULT):
			return self.Children[0].ASTtoZ3() * self.Children[1].ASTtoZ3()
		if(self.Val.typ==EQ):
			return self.Children[0].ASTtoZ3() == self.Children[1].ASTtoZ3()
		if(self.Val.typ==NE):
			return self.Children[0].ASTtoZ3() != self.Children[1].ASTtoZ3()
		if(self.Val.typ==LT):
			return self.Children[0].ASTtoZ3() < self.Children[1].ASTtoZ3()
		if(self.Val.typ==GT):
			return self.Children[0].ASTtoZ3() > self.Children[1].ASTtoZ3()
		if(self.Val.typ==LE):
			return self.Children[0].ASTtoZ3() <= self.Children[1].ASTtoZ3()
		if(self.Val.typ==GE):
			return self.Children[0].ASTtoZ3() >= self.Children[1].ASTtoZ3()
		if(self.Val.typ==AND):
			return And(self.Children[0].ASTtoZ3(),self.Children[1].ASTtoZ3())
		if(self.Val.typ==OR):
			return Or(self.Children[0].ASTtoZ3(),self.Children[1].ASTtoZ3())
		if(self.Val.typ==INT):
			return int(self.Val.val)
		if(self.Val.typ==VAR):
			return Int(self.Val.val)
		
