
"""
 * @author nhphung
"""
from AST import * 
from Visitor import *
from Utils import Utils
from StaticError import *
from functools import reduce
from itertools import permutations

class MType:
    def __init__(self,partype,rettype):
        self.partype = partype
        self.rettype = rettype
    def __str__(self):
        return 'MType(['+','.join(str(x) for x in self.partype)+'],'+str(self.rettype)+')'

class Symbol:
    def __init__(self,name,mtype,value = None):
        self.name = name
        self.mtype = mtype
        self.value = value
    def __str__(self):
        return 'Symbol('+self.name+','+str(self.mtype)+')'

class RetType:
    def __init__(self,t):
        ''' t: Return type '''
        self.t = t
    def __str__(self): 
        return 'Return(' + type(t) + ')' 

class GlobalEnv(BaseVisitor,Utils):
    global_envi = [Symbol("getInt",MType([],IntType())),
    			   Symbol("putIntLn",MType([IntType()],VoidType()))]

    def __init__(self,ast):
        self.ast = ast
  
    def check(self,ast):
        return self.visit(ast,GlobalEnv.global_envi)
                

    def checkRedecl(self,sym,kind,env):
        if self.lookup(sym.name.lower(),env,lambda x: x.name.lower()):
            raise Redeclared(kind,sym.name)
        else:
            return sym

    def visitProgram(self,ast,c):
        return reduce(lambda x,y: [self.visit(y,x+c)]+x,ast.decl,[])

    def visitVarDecl(self,ast,c):
        return self.checkRedecl(Symbol(ast.variable.name,ast.varType),Variable(),c)

    def visitFuncDecl(self,ast,c):
        kind = Procedure() if type(ast.returnType) is VoidType else Function()
        return self.checkRedecl(Symbol(ast.name.name,MType([x.varType for x in ast.param],ast.returnType)),kind,c)

class StaticChecker(BaseVisitor,Utils):

    def __init__(self,ast):
        self.ast = ast
        self.global_env = GlobalEnv(ast)

    def comb(self,lst1,lst2):
        return lst1+list(filter(lambda x: x.name not in list(map(lambda x: x.name,lst1)),lst2))

    def intCoerce(self,left,right):
        if type(left) is FloatType and type(right) is IntType:
            return True
        else:
            return False

    def checkRedecl(self,sym,kind,env):
        if self.lookup(sym.name.lower(),env,lambda x: x.name.lower()):
            raise Redeclared(kind,sym.name)
        else:
            return sym

    def checkRetPath(self,lst):
        res = []
        for x in lst:
            if type(x) is tuple:
                res.append(self.checkRetPath(x[0]) and self.checkRetPath(x[1]))
            elif type(x) is list:
                res.append(self.checkRetPath(x))
            elif type(x) is RetType:
                res.append(True)
            else:
                res.append(False)
        return any(res)

    def checkUnreachableStmt(self,lst):
        try:
            i = list(map(lambda x: type(x),lst)).index(Return)
            if i != len(list(map(lambda x: type(x),lst))) - 1:
                raise UnreachableStatement(lst[i+1])
        except ValueError:
            pass

    def checkType(self,x,y):
        if type(x) is IntType and type(y) is FloatType:
            return True
        elif type(x) != type(y):
            return False
        elif type(x) is ArrayType and type(y) is ArrayType:
            if x.upper == y.upper and x.lower == y.lower and type(x.eleType) == type(y.eleType):
                return True
            else:
                return False
        else:
            return True               

    def check(self):
        global_envi = self.global_env.check(self.ast) + self.global_env.global_envi
        main = self.lookup(str(Symbol('main',MType([],VoidType()))).lower(),global_envi,lambda x: str(x).lower())
        if main is None:
            raise NoEntryPoint()
        return self.visit(self.ast,global_envi)

    def visitProgram(self,ast,c):
        return [self.visit(x,c) for x in ast.decl if type(x) is FuncDecl]

    def visitVarDecl(self,ast,c):
        return self.checkRedecl(Symbol(ast.variable.name,ast.varType),Variable(),c)

    def visitFuncDecl(self,ast,c):
        try:
            tmp = reduce(lambda x,y: [self.visit(y,x)]+x,ast.param,[])
        except Redeclared as e:
            raise Redeclared(Parameter(),e.n)
        local_env = reduce(lambda x,y: [self.visit(y,x)]+x,ast.param+ast.local,[])
        rettype = self.visit(ast.returnType,local_env+c)
        '''
        for x in ast.body:
            if type(x) is For:
                self.visit(x.id,local_env)
        '''
        sl = [self.visit(x,(local_env+c,False,rettype)) for x in ast.body]
        if not self.checkRetPath(sl) and not type(rettype) is VoidType:
            raise FunctionNotReturn(ast.name.name)
        self.checkUnreachableStmt(ast.body)

        '''
        if type(rettype) is not VoidType and not Return in list(map(lambda x: type(x),ast.body)):
            try:
                sl = [self.visit(x,(scope_var,rettype,False)) for x in ast.body]
            except Exception:
                raise FunctionNotReturn(ast.name.name)
        else:
            stmt = [self.visit(x,(scope_var,rettype,False)) for x in list(filter(lambda x: type(x) is not Return,ast.body))]
            return [self.visit(x,(scope_var,rettype)) for x in list(filter(lambda x: type(x) is Return,ast.body))]'''

    def visitIntType(self,ast,c):
        return IntType()
    
    def visitFloatType(self,ast,c):
        return FloatType()
    
    def visitBoolType(self,ast,c):
        return BoolType()
    
    def visitStringType(self,ast,c):
        return StringType()
    
    def visitVoidType(self,ast,c):
        return VoidType()

    def visitArrayType(self,ast,c):
        return ArrayType(ast.lower,ast.upper,self.visit(ast.eleType,c[0]))

    def visitBinaryOp(self,ast,c):
        ltype = self.visit(ast.left,c)
        rtype = self.visit(ast.right,c)
        if ast.op.lower() in ['div','mod']:
            if type(ltype) is IntType and type(rtype) is IntType:
                return IntType()
            else:
                raise TypeMismatchInExpression(ast)
        elif ast.op == '/':
            if type(ltype) in [IntType,FloatType] and type(rtype) in [IntType,FloatType]:
                return FloatType()
            else:
                raise TypeMismatchInExpression(ast)
        elif ast.op in ['<','<=','=','>=','>','<>']:
            if type(ltype) in [IntType,FloatType] and type(rtype) in [IntType,FloatType]:
                return BoolType()
            else:
                raise TypeMismatchInExpression(ast)
        elif ast.op.lower() in ['andthen','orelse','and','or']:
            if type(ltype) is BoolType and type(rtype) is BoolType:
                return BoolType()
            else:
                raise TypeMismatchInExpression(ast)
        else:
            if type(ltype) in [IntType,FloatType] and type(rtype) in [IntType,FloatType]:
                if type(ltype) is IntType and type(rtype) is IntType:
                    return IntType()
                else:
                    return FloatType()
            else:
                raise TypeMismatchInExpression(ast)

    def visitUnaryOp(self,ast,c):
        body = self.visit(ast.body,c)
        if ast.op == 'not' and type(body) is not BoolType:
            raise TypeMismatchInExpression(ast)
        elif ast.op == '-' and not type(body) in [IntType,FloatType]:
            raise TypeMismatchInExpression(ast)
        else:
            return body

    def visitId(self,ast,c):
        res = self.lookup(ast.name,c,lambda x: x.name)
        if res is None or type(res.mtype) is MType:
            raise Undeclared(Identifier(),ast.name)
        else:
            return res.mtype

    def visitCallExpr(self,ast,c):
        par = [self.visit(x,c) for x in ast.param]
        res = self.lookup(ast.method.name.lower(),c,lambda x: x.name.lower())
        if res is None or not type(res.mtype) is MType or type(res.mtype.rettype) is VoidType:
            raise Undeclared(Function(),ast.method.name)
        elif len(res.mtype.partype) != len(par):
            raise TypeMismatchInExpression(ast)
        elif any([not self.checkType(x,y) for (x,y) in zip(par,res.mtype.partype)]):
            raise TypeMismatchInExpression(ast)
        else:
            return res.mtype.rettype

    def visitArrayCell(self,ast,c):
        arr = self.visit(ast.arr,c)
        idx = self.visit(ast.idx,c)
        if type(arr) is ArrayType and type(idx) is IntType:
            return arr.eleType 
        else:
            raise TypeMismatchInExpression(ast)    

    def visitAssign(self,ast,c):
        lhs = self.visit(ast.lhs,c[0])
        rhs = self.visit(ast.exp,c[0])
        if type(lhs) is StringType or type(rhs) is ArrayType:
            raise TypeMismatchInStatement(ast)
        elif self.intCoerce(lhs,rhs):
            return FloatType()
        elif type(lhs) == type(rhs):
            return lhs
        elif type(lhs) is ArrayType and type(lhs.eleType) == type(rhs):
            return lhs
        else:
            raise TypeMismatchInStatement(ast)

    def visitWith(self,ast,c):
        block_env = reduce(lambda x,y: [self.visit(y,x)]+x,ast.decl,[])
        return [self.visit(x,(block_env+c[0],c[1],c[2])) for x in ast.stmt]

    def visitIf(self,ast,c):
        cond = self.visit(ast.expr,c[0])
        if not type(cond) is BoolType:
            raise TypeMismatchInStatement(ast)
        else:
            tl = [self.visit(x,c) for x in ast.thenStmt]
            el = [self.visit(x,c) for x in ast.elseStmt]
            self.checkUnreachableStmt(ast.thenStmt)
            self.checkUnreachableStmt(ast.elseStmt)
            return [self.visit(x,c) for x in ast.thenStmt],[self.visit(x,c) for x in ast.elseStmt]

    def visitFor(self,ast,c):
        id = self.visit(ast.id,c[0])
        exp1 = self.visit(ast.expr1,c[0])
        exp2 = self.visit(ast.expr2,c[0])
        if type(exp1) is IntType and type(exp2) is IntType and type(id) is IntType:
            return [self.visit(x,(c[0],True,c[2])) for x in ast.loop]
        else:
            raise TypeMismatchInStatement(ast)

    def visitContinue(self,ast,c):
        if c[1] == False:
            raise ContinueNotInLoop()
        else:
            return Continue()

    def visitBreak(self,ast,c):
        if c[1] == False:
            raise BreakNotInLoop()
        else:
            return Break()

    def visitReturn(self,ast,c):
        if ast.expr is None:
            if type(c[2]) is not VoidType:
                raise TypeMismatchInStatement(ast)
            else:
                return RetType(VoidType())
        else:
            extype = self.visit(ast.expr,c[0])
            if self.intCoerce(c[2],extype):
                return RetType(FloatType())
            elif type(c[2]) is ArrayType and type(extype) is ArrayType:
                if (c[2].upper,c[2].lower) == (extype.upper,extype.lower) and type(c[2].eleType) == type(extype.eleType):
                    return RetType(type(c[2]))
                else:
                    raise TypeMismatchInStatement(ast)
            elif type(c[2]) == type(extype):
                return RetType(c[2])
            else:
                raise TypeMismatchInStatement(ast)

    def visitWhile(self,ast,c):
        exp = self.visit(ast.exp,c[0])
        if not type(exp) is BoolType:
            raise TypeMismatchInStatement(ast)
        else:
            return [self.visit(x,(c[0],True,c[2])) for x in ast.sl]

    def visitCallStmt(self,ast,c):
        par = [self.visit(x,c[0]) for x in ast.param]
        res = self.lookup(ast.method.name.lower(),c[0],lambda x: x.name.lower())
        if res is None or not type(res.mtype) is MType or not type(res.mtype.rettype) is VoidType:
            raise Undeclared(Procedure(),ast.method.name)
        elif len(res.mtype.partype) != len(par):
            raise TypeMismatchInStatement(ast)
        elif any([not self.checkType(x,y) for (x,y) in zip(par,res.mtype.partype)]):
            raise TypeMismatchInStatement(ast)
        else:
            return res.mtype.rettype

    def visitIntLiteral(self,ast,c):
        return IntType()
    
    def visitFloatLiteral(self,ast,c):
        return FloatType()

    def visitBooleanLiteral(self,ast,c):
        return BoolType()
    
    def visitStringLiteral(self,ast,c):
        return StringType()

'''
    
    def visitProgram(self,ast,c): 
        reduce(lambda x,y: [self.visit(y,x+c)]+x,ast.decl,[])
        return

    def visitVarDecl(self,ast,c):
        return self.checkReDecl(Symbol(ast.variable.name),Variable(),c)

    def visitFuncDecl(self,ast,c):
        stmt = [self.visit(x,c+param+local) for x in ast.body]
        kind = Procedure() if type(ast.returnType) is VoidType else Function()
        param = self.checkReDecl(Symbol(ast.name.name,MType([x.varType for x in ast.param],ast.returnType)),kind,c)
        local = 

        return

    def visitIfStmt(self,ast,c):
        condtype = self.visit(ast.expr)
        if type(condtype) is not BoolType():
            raise TypeMismatchInStatement(ast)
        list(map(lambda x: self.visit(x,c), ast.thenStmt))
        list(map(lambda x: self.visit(x,c), ast.elseStmt))

    
    def visitCallStmt(self,ast,c):
        at = [self.visit(x,c) for x in ast.param]
        res = self.lookup(ast.method.name,c,lambda x: x.name)
        if res is None or not type(res.mtype) is MType or not type(res.mtype.rettype) is VoidType:
            raise Undeclared(Procedure(),ast.method.name)
        elif len(res.mtype.partype) != len(at) or not all([type(x) == type(y) for (x,y) in zip(at,res.mtype.partype)]):
            raise TypeMismatchInStatement(ast)       
        else:
            return res.mtype.rettype

    def visitId(self,ast,c):


    def visitIntLiteral(self,ast, c): 
        return IntType()

'''