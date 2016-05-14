#!/usr/bin/python


import pdb

import math


__doc__='''Intermediate Representation
Could be improved by relying less on class hierarchy and more on string tags and/or duck typing
Includes lowering and flattening functions'''


class TempNameFactory(object):

	def __init__(self):
		self.current=1

	def getName(self):
		retString=str(self.current)+"TEMP"
		self.current=self.current+1
		return retString

class TempSymbolTable(object):
	def __init__(self):
		self.symtab=SymbolTable()

	def append(self, elem):
		if not isinstance(elem, Temp): 
			print repr(elem), "is not a Temp"
			return
		self.symtab.append(elem)

	def __repr__(self):
		res='TempSymbolTable:\n'
		for s in self.symtab :
			res+=repr(s)+'\n'
		return res


CONST_SIZE = 32

WORD_SIZE = 32

TEMP_NAME_FACTORY = TempNameFactory()


class SymbolWithOffset(object):
	def __init__(self,symbol=None, offset=0):
		self.symbol=symbol
		self.offset=offset

	def __repr__(self):
		return repr(self.symbol) + " offset: " + str(self.offset)


#SYMBOLS AND TYPES
basetypes = [ 'Int', 'Float', 'Label', 'Struct', 'Function' ]
qualifiers = [ 'unsigned' ]


class Type(object):
	def __init__(self, name, size, basetype, qualifiers=None):
		self.name=name
		self.size=size
		self.basetype=basetype
		self.qual_list=qualifiers

class ArrayType(Type):
	def __init__(self, name, size, basetype):
		self.name=name
		self.size=size
		self.basetype=basetype
		self.qual_list=[]

class StructType(Type):
	def __init__(self, name, size, fields):
		self.name=name
		self.fields=fields
		self.size=self.getSize()
		self.basetype='Struct'
		self.qual_list=[]
		
	def getSize(self):
		return sum([ f.size for f in self.fields])
		
class LabelType(Type):
	def __init__(self):
		self.name='label'
		self.size=0
		self.basetype='Label'
		self.qual_list=[]
		self.ids=0
	
	def __call__(self,target=None):
		self.ids+=1
		return Symbol(name='label'+`self.ids`, stype=self, value=target)


class FunctionType(Type):
	def __init__(self):
		self.name='function'
		self.size=0
		self.basetype='Function'
		self.qual_list=[]

standard_types = {
	'int'  : Type('int',   32, 'Int'),
	'short': Type('short', 16, 'Int'),
	'char' : Type('char',   8, 'Int'),
	'uchar': Type('uchar',  8, 'Int', ['unsigned']),
	'uint' : Type('uint',  32, 'Int', ['unsigned']),
	'ushort': Type('ushort',16,'Int', ['unsigned']),
	'float': Type('float', 32, 'Float'),
	'label': LabelType(),
	'function' : FunctionType(),
}

class Symbol(object):
	def __init__(self, name, stype, value=None):
		self.name=name
		self.stype=stype
		self.value=value # if not None, it is a constant

	def __repr__(self):
		return self.stype.name+' '+self.name + ( self.value if type(self.value)==str else '')

class Temp(Symbol):
	pass

class SymbolTable(list):
	def find(self, name):
		print 'Looking up', name
		for s in self :
			if s.name==name : return s
		print 'Looking up of failed!'
		return None

	def __repr__(self):
		res='SymbolTable:\n'
		for s in self :
			res+=repr(s)+'\n'
		return res
		
	def exclude(self, barred_types):
		return [ symb for symb in self if symb.stype not in barred_types ]


#IRNODE
class IRNode(object):
	def __init__(self,parent=None, children=None, symtab=None):
		self.parent=parent
		if children :	self.children=children
		else : self.children=[]
		self.symtab=symtab
	
	def __repr__(self):
		from string import split, join
		attrs = set(['body','cond', 'value','thenpart','elsepart', 'symbol', 'call', 'step', 'expr', 'target', 'defs', 'global_symtab', 'local_symtab','init','operands','operator', 'source', 'label' ]) & set(dir(self))

		res=`type(self)`+' '+`id(self)`+' {\n'
		try :
			label=self.getLabel()
			res=label.name+': '+res
		except Exception, e :
			pass
		if 'children' in dir(self) and len(self.children) :
			res+='\tchildren:\n'
			for node in self.children :
				rep=repr(node)
				res+=join([ '\t'+s for s in rep.split('\n') ],'\n')+'\n'
		for d in attrs :
			node=getattr(self,d)
			rep=repr(node)
			res+='\t'+d+': '+join([ '\t'+s for s in rep.split('\n') ],'\n')+'\n'		
		res+='}'
		return res

	def navigate(self, action):
		action(self)
		attrs = set(['body','cond', 'value','thenpart','elsepart', 'symbol', 'call', 'step', 'expr', 'target', 'defs', 'global_symtab', 'local_symtab', 'init' ]) & set(dir(self))
		if 'children' in dir(self) and len(self.children) :
			print 'navigating children of', type(self), id(self), len(self.children)
			for node in self.children :
				try : node.navigate(action)
				except Exception : pass
		for d in attrs :
			try : getattr(self,d).navigate(action)
			except Exception : pass
	
	def replace(self, old, new):
		try:
			if 'children' in dir(self) and len(self.children) and old in self.children:
				self.children[self.children.index(old)]=new
				return True
			attrs = set(['body','cond', 'value','thenpart','elsepart', 'symbol', 'call', 'step', 'expr', 'target', 'defs', 'global_symtab', 'local_symtab', 'init' ]) & set(dir(self))
			for d in attrs :
				try :
					if getattr(self,d)==old :
						setattr(self,d,new)
						return True			
				except Exception, e :
					print Exception, e 
			return False
		except Exception, e: 
			print "CANNOT DO REPLACEMENT BETWEEN", old, "AND", new
			raise Exception

			

#CONST and VAR	
class Const(IRNode):
	def __init__(self,parent=None, value=0, symb=None, symtab=None):
		self.parent=parent
		self.value=value
		self.symbol=symb
		self.symtab=symtab
		
class Var(IRNode):
	def __init__(self,parent=None, var=None, symtab=None):
		self.parent=parent
		self.symbol=var
		self.symtab=symtab

	def lowerAndAppendToStatList(self, stat_list):
		print "LOWERING VAR:", self
		temp_type = None
		source = None
		try:
			if self.symbol is None :
				temp_type = standard_types['int']
			else:
				temp_type = self.symbol.stype
			dest_symbol= Temp(name=TEMP_NAME_FACTORY.getName(), stype=temp_type)
			self.symtab.append(dest_symbol)
			load_stat=LoadStat(parent=self.parent, symbol=dest_symbol, source=self.symbol, symtab=self.symtab)
			stat_list.append(load_stat)
		except Exception, e: print "VAR ERROR:", Exception, e

	def collect_uses(self):
		return [self.symbol] if isinstance(self.symbol, Temp) else []

#EXPRESSIONS
class Expr(IRNode):
	def getOperator(self):
		return self.children[0]

	def collect_uses(self):
		raise RuntimeError

	def lowerAndAppendToStatList(self, stat_list):
		operand_list=[]
		try:
			for ch in self.children[1:]:
				if isinstance(ch, Expr) or  isinstance(ch, Var):
					try:
						ch.lowerAndAppendToStatList(stat_list)
						operand_list.append(stat_list.children[-1].symbol)
					except Exception, e: raise Exception, e
				elif isinstance(ch, Const):
					operand_list.append(ch)
				else:
					operand_list.append(ch)
			bin_stat=BinStat(parent=self, operands=operand_list, operator=self.getOperator(), symtab=self.symtab)
			stat_list.append(bin_stat)
		except Exception, e: print "EXPR LOWER ERROR:", Exception, e
		

	#the dirty work is done by the lowerAndAppendToStatList method. The lower method just
	#does the replacement
	def lower(self):
		try:
			stat_list = StatList(self.parent, [], self.symtab)
			self.lowerAndAppendToStatList(stat_list)
			return self.parent.replace(self, stat_list)
		except Exception,e : print "IRNODE LOWER ERROR:", Exception, e

class BinExpr(Expr):
	def getOperands(self):
		return self.children[1:]



class UnExpr(Expr):
	def getOperand(self):
		return self.children[1]


class CallExpr(Expr):
	def __init__(self, parent=None, function=None, parameters=None, symtab=None):
		self.parent=parent
		self.symbol=function
		if parameters : self.children=parameters[:]
		else : self.children=[]


#STATEMENTS
class Stat(IRNode):
	def setLabel(self, label):
		self.label=label
		label.value=self # set target
	
	def getLabel(self):
		return self.label

	def getFunction(self):
		if not self.parent : return 'global'
		elif type(self.parent)== FunctionDef :
			return self.parent
		else :
			return self.parent.getFunction()

class BinStat(Stat):

	def __init__(self, parent=None, operands=None, operator=None, symtab=None):
		self.parent=parent
		self.operands=operands
		self.operator=operator
		self.symtab=symtab
		operand_size_array=self.getOperandSize()
		#the type of the temp will be equal to the type of the operand with the greater size
		temp_type = None
		try:
			if (operand_size_array[0] > operand_size_array[1]):
				temp_type = self.operands[0].stype
			else:
				temp_type = self.operands[1].stype
		except: temp_type=standard_types['int']
		#insert temp into symtab
		self.symbol = Temp(name=TEMP_NAME_FACTORY.getName(), stype=temp_type)
		#self.symbol = Symbol(name=TEMP_NAME_FACTORY.getName(), stype=temp_type)
		self.symtab.append( self.symbol )


	def getOperandSize(self):
		op_size = []
		for op in self.operands:
			if isinstance(op,Const):
				op_size.append(CONST_SIZE)
			elif isinstance(op, Symbol):
				op_size.append(op.stype.size)
			else:
				op_size.append(op.symbol.stype.size)
		return op_size

	def collect_uses(self):
		ret_list = []
		for el in self.operands:
			if isinstance(el, Temp): ret_list.append(el)  
		return ret_list
			

class CallStat(Stat):	
	'''Procedure call (non returning)'''
	def __init__(self, parent=None, call_expr=None, symtab=None):
		self.parent=parent
		self.call=call_expr
		self.call.parent=self
		self.symtab=symtab
	
	def collect_uses(self):
		return []

class IfStat(Stat):
	def __init__(self, parent=None, cond=None, thenpart=None, elsepart=None, symtab=None):
		self.parent=parent
		self.cond=cond
		self.thenpart=thenpart
		self.elsepart=elsepart
		self.cond.parent=self
		self.thenpart.parent=self
		if self.elsepart : self.elsepart.parent=self
		self.symtab=symtab

	def lower(self):
		try:
			#self.cond.lower()
			#self.thenpart.lower()
			exit_label = standard_types['label']()
			exit_stat = EmptyStat(self.parent,symtab=self.symtab)
			exit_stat.setLabel(exit_label)
			if self.elsepart :
				self.elsepart.lower()
				then_label = standard_types['label']()
				self.thenpart.setLabel(else_label)
				branch_to_then = BranchStat(None,self.cond,then_label,self.symtab)
				branch_to_exit = BranchStat(None,None,exit_label,self.symtab)
				stat_list = StatList(self.parent, [branch_to_then,self.elsepart,branch_to_exit,self.thenpart,exit_stat], self.symtab)
				branch_to_then.parent=stat_list
				branch_to_then.lower()
				branch_to_exit.parent=stat_list
				branch_to_exit.lower()
				print "END IF LOWER ELSECOND"
				return self.parent.replace(self,stat_list)
			else :
				branch_to_exit = BranchStat(None,UnExpr(None,['not', self.cond]),exit_label,self.symtab)
				stat_list = StatList(self.parent, [branch_to_exit,self.thenpart,exit_stat], self.symtab)
				branch_to_exit.parent=stat_list
				branch_to_exit.lower()
				print "END IF LOWER COND"
				return self.parent.replace(self,stat_list)
		except Exception, e: print "IFSTAT LOWER ERROR",Exception,e

	def collect_uses(self):
		raise RuntimeError
						
	
class WhileStat(Stat):
	def __init__(self, parent=None, cond=None, body=None, symtab=None):
		self.parent=parent
		self.cond=cond
		self.body=body
		self.cond.parent=self
		self.body.parent=self
		self.symtab=symtab
	
	def lower(self):
		entry_label = standard_types['label']()
		exit_label = standard_types['label']()
		exit_stat = EmptyStat(self.parent,symtab=self.symtab)
		exit_stat.setLabel(exit_label)
		branch = BranchStat(None,self.cond,exit_label,self.symtab)
		branch.setLabel(entry_label)
		loop = BranchStat(None,Const(None, 1),entry_label,self.symtab)
		stat_list = StatList(self.parent, [branch,self.body,loop,exit_stat], self.symtab)
		return self.parent.replace(self,stat_list)
	
class ForStat(Stat):
	def __init__(self, parent=None, init=None, cond=None, step=None, body=None, symtab=None):
		self.parent=parent
		self.init=init
		self.init.parent=self
		self.cond=cond
		self.cond.parent=self
		self.step=step
		self.step.parent=self
		self.body=body
		self.body.parent=self
		self.symtab=symtab

	def lower(self):
		stat_list=StatList(self.parent,[], self.symtab)
		print "FOR LOWERING"
		try:
			#generate labels
			cond_label = standard_types['label']()
			exit_label = standard_types['label']()
			#bind exit condition
			exit_stat = EmptyStat(self.parent,symtab=self.symtab)
			exit_stat.setLabel(exit_label)
			stat_list.append(self.init)
			self.cond = UnExpr(self, ['!', self.cond], self.symtab)
			self.cond.lower()
			self.cond.children[0].setLabel(cond_label)
			exit_jump=JumpStat(parent=self.parent, symbol=self.cond.children[-1].symbol, target=exit_label, symtab=self.symtab ) 
			cond_jump=JumpStat(parent=self.parent, symbol=None, target=cond_label, symtab=self.symtab)
			stat_list.append(self.cond)
			stat_list.append(exit_jump)
			stat_list.append(self.body)
			stat_list.append(self.step)
			stat_list.append(cond_jump)
			stat_list.append(exit_stat)
			print "END FOR LOWERING"
		except Exception, e : print "FOR ERROR:", Exception, e
		return self.parent.replace(self, stat_list)

	def collect_uses(self):
		raise RuntimeError

class AssignStat(Stat):
	def __init__(self, parent=None, target=None, expr=None, symtab=None):
		self.parent=parent
		self.symbol=target
		self.expr=expr
		try:
			self.expr.parent = self
		except Exception, e: 
			print Exception, e
		self.symtab=symtab

	def lower(self):
		print "LOWERING AssignStat"
		stat_list=StatList(self.parent, [], self.symtab)
		if isinstance(self.expr, Const):
			try:
				store_stat = StoreStat(parent=self.parent, symbol=self.symbol, source=self.expr, symtab=self.symtab)
				return self.parent.replace(self, store_stat)
			except Exception, e: print Exception, e
		else:
			self.expr.lowerAndAppendToStatList(stat_list)
			source_symbol=stat_list.children[-1].symbol
			store_stat=StoreStat(parent=self.parent, symbol=self.symbol, source=source_symbol, symtab=self.symtab)
			stat_list.append(store_stat)
			return self.parent.replace(self, stat_list)

	def collect_uses(self):
		raise RuntimeError

class BranchStat(Stat):
	def __init__(self, parent=None, cond=None, target=None, symtab=None):
		self.parent=parent
		self.cond=cond # cond == None -> True
		self.target=target
		if self.cond is not None:
			self.cond.parent=self
		self.target.parent=self
		self.symtab=symtab

	def lower(self):
		print "LOWERING BranchStat"
		try:
			stat_list=StatList(self.parent, [], self.symtab)
			dest_symbol=None
			if self.cond is not None:
				self.cond.lowerAndAppendToStatList(stat_list)
				dest_symbol=stat_list.children[-1].symbol
			stat_list.append(JumpStat(stat_list,dest_symbol, self.target, self.symtab))
			return self.parent.replace(self, stat_list)
		except Exception, e: print "BRANCHSTAT LOWER ERROR:", Exception, e


	def collect_uses(self):
		try : return self.cond.collect_uses()
		except AttributeError : return []

	def is_unconditional(self):	
		try :
			check=self.cond.value
			return True
		except AttributeError :
			return False

class JumpStat(Stat):
	def __init__(self, parent=None, symbol=None, target=None, symtab=None):
		self.parent=parent
		self.symbol=symbol #check result contained in simbol. If None is unconditional
		self.target=target
		self.symtab=symtab

	def is_unconditional(self):
		return self.symbol is None

	def collect_uses(self):
		return [self.symbol] if isinstance(self.symbol, Temp) else []

class EmptyStat(Stat):
	pass

	def collect_uses(self):
		return []

class StoreStat(Stat):
	def __init__(self, parent=None, symbol=None, source=None, symtab=None):
		self.parent=parent
		#destination of the store
		self.symbol=symbol
		self.symtab=symtab
		#source. value that will be stored at symbol
		self.source=source
		
	def collect_uses(self):
		return [self.symbol] if isinstance(self.symbol, Temp) else []

class LoadStat(Stat):
	def __init__(self, parent=None, symbol=None, source=None, symtab=None):
		self.parent=parent
		self.symbol=symbol
		self.source=source
		self.symtab=symtab

	def collect_uses(self):
		return []

class StatList(Stat):
	def __init__(self,parent=None, children=None, symtab=None):
		print 'StatList : new', id(self)
		self.parent=parent
		if children : 
			self.children=children[:]
			for c in self.children :
				c.parent=self
		else : self.children=[]
		self.symtab=symtab

	def lower(self):
		print "STATLIST LOWERING"
		for ch in self.children:
			try:
				ch.lower()
			except Exception, e: pass
		print "END STATLIST LOWERING"
		return True

		
	def append(self, elem):
		elem.parent=self
		print 'StatList: appending', id(elem), 'of type', type(elem), 'to', id(self)
		self.children.append(elem)

	def collect_uses(self):
		try:
			return sum([ c.collect_uses() for c in self.children ],[])
		except Exception, e : print "STATLIST COLLECT USES ERROR:", Exception, e

	def print_content(self):
			print 'StatList', id(self), ': [',
			for n in self.children :
				print id(n),
			print ']'

	def flatten(self):
		'''Remove nested StatLists'''
		if type(self.parent)==StatList :
			print 'Flattening', id(self), 'into', id(self.parent)
			for c in self.children :
				c.parent=self.parent
			try : 
				label = self.getLabel()
				self.children[0].setLabel(label)
			except Exception : pass
			i = self.parent.children.index(self)
			self.parent.children=self.parent.children[:i]+self.children+self.parent.children[i+1:]
			return True
		else :
			print 'Not flattening', id(self), 'into', id(self.parent), 'of type', type(self.parent)
			return False

class Block(Stat):
	def __init__(self, parent=None, gl_sym=None, lc_sym=None, defs=None, body=None):
		self.parent=parent
		self.global_symtab=gl_sym
		self.local_symtab=lc_sym
		self.body=body
		self.defs=defs
		self.body.parent=self
		self.defs.parent=self

class PrintStat(Stat):
	def __init__(self, parent=None, symbol=None, symtab=None):	
		self.parent=parent
		self.symbol=symbol
		self.symtab=symtab

	def collect_uses(self):
		return [self.symbol] if isinstance(self.symbol, Temp) else []
	

#DEFINITIONS
class Definition(IRNode):
	def __init__(self, parent=None, symbol=None):
		self.parent=parent
		self.symbol=symbol

class FunctionDef(Definition):
	def __init__(self, parent=None, symbol=None, body=None):
		self.parent=parent
		self.symbol=symbol
		self.body=body
		self.body.parent=self
		self.symtabWithOffset=SymbolTable()
		self.tempSymTab=TempSymbolTable()

	def lower():
		body.lower()
		self.parent.replace(self, body)

	def getGlobalSymbols(self):
		return self.body.global_symtab.exclude([standard_types['function'],standard_types['label']])

	def genOffset(self):
		try:
			print "genOffset for", id(self)
			fp = 0
			oldFp=0
			for entry in self.body.local_symtab:
				try:
					self.symtabWithOffset.append(SymbolWithOffset(symbol=entry, offset=fp-oldFp))
					oldFp=fp
					fp = fp + int ( math.ceil( entry.stype.size / WORD_SIZE ) )
				except Exception, e: print "GENOFFSET ERROR:",Exception, e
				print "symtabWithOffset:", self.symtabWithOffset

			print "selecting temps from", self.body.body.symtab

			for tempEntry in self.body.body.symtab:
				if isinstance(tempEntry, Temp):
					self.tempSymTab.append(tempEntry)

			print "generated tempSymTab:", self.tempSymTab

			return True
		except Exception, e: 
			print "MAIN GENOFFSET ERROR:", Exception, e
			return False

class DefinitionList(IRNode):
	def __init__(self,parent=None, children=None):
		self.parent=parent
		if children :	self.children=children
		else : self.children=[]
		
	def append(self, elem):
		elem.parent=self
		self.children.append(elem)
		

def print_stat_list(node):
	'''Navigation action: print'''
	print type(node), id(node)
	if type(node)==StatList :
		print 'StatList', id(node), ': [',
		for n in node.children :
			print id(n),
		print ']'
	
