from MPVisitor import MPVisitor
from MPParser import MPParser
from AST import *
from functools import reduce

class ASTGeneration(MPVisitor):
    def visitProgram(self, ctx: MPParser.ProgramContext):
        return Program(reduce(lambda a, x: a + x, [self.visit(x) for x in ctx.decl()], []))

    def visitDecl(self, ctx: MPParser.DeclContext):
        if ctx.vardecl():
            return self.visit(ctx.vardecl())
        else:
            return [self.visit(ctx.getChild(0))]

    def visitFuncdecl(self, ctx: MPParser.FuncdeclContext):
        rtype = self.visit(ctx.idtype())
        cpstmt = self.visit(ctx.body())
        return FuncDecl(Id(ctx.ID().getText()),
                        self.visit(ctx.plist()) if ctx.plist() else [],
                        self.visit(ctx.vardecl()) if ctx.vardecl() else [],
                        cpstmt,
                        rtype)
  
    def visitProcdecl(self, ctx: MPParser.ProcdeclContext):
        cpstmt = self.visit(ctx.body())
        return FuncDecl(Id(ctx.ID().getText()),
                        self.visit(ctx.plist()) if ctx.plist() else [],
                        self.visit(ctx.vardecl()) if ctx.vardecl() else [],
                        cpstmt)

    def visitVardecl(self, ctx: MPParser.VardeclContext):
        lst = [self.visit(x) for x in ctx.vargroup()]
        return reduce(lambda a, x: a + x, lst)

    def visitVargroup(self, ctx: MPParser.VargroupContext):
        idtype = self.visit(ctx.idtype())
        return [VarDecl(id, idtype) for id in self.visit(ctx.idlist())]

    def visitBody(self, ctx: MPParser.BodyContext):
        return reduce(lambda a, x: a + x, [self.flatten(self.visit(x)) for x in ctx.stmt()], [])

    def visitStmt(self, ctx: MPParser.StmtContext):
        if ctx.breakstmt():
            return Break()
        elif ctx.continuestmt():
            return Continue()
        else:
            return self.visit(ctx.getChild(0))

    def visitAssign(self, ctx: MPParser.AssignContext):
        lhs = len(ctx.variable())
        assign_lst = []
        if lhs > 1:
            assign_lst = [Assign(self.visit(ctx.variable(x)),self.visit(ctx.variable(x+1))) for x in range(lhs-1)]
        assign_lst += [Assign(self.visit(ctx.variable(lhs-1)), self.visit(ctx.expr()))]
        return list(assign_lst.__reversed__())

    def visitVariable(self, ctx: MPParser.VariableContext):
        if ctx.ID():
            return Id(ctx.ID().getText())
        if ctx.arraycell():
            return self.visit(ctx.arraycell())

    def visitIfstmt(self, ctx: MPParser.IfstmtContext):
        return If(self.visit(ctx.expr()),
                  self.flatten(self.visit(ctx.stmt(0))),
                  self.flatten(self.visit(ctx.stmt(1)) if ctx.stmt(1) else []))

    def visitWhilestmt(self, ctx: MPParser.WhilestmtContext):
        return While(self.visit(ctx.expr()),
                     self.flatten(self.visit(ctx.stmt())))

    def visitReturnstmt(self, ctx: MPParser.ReturnstmtContext):
        if not ctx.expr():
            return Return()
        else:
            return Return(self.visit(ctx.expr()))

    def visitForstmt(self, ctx: MPParser.ForstmtContext):
        return For(Id(ctx.ID().getText()),
                   self.visit(ctx.expr(0)),
                   self.visit(ctx.expr(1)),
                   True if ctx.TO() else False,
                   self.flatten(self.visit(ctx.stmt())))

    def visitWithstmt(self, ctx: MPParser.WithstmtContext):
        return With(reduce(lambda a, x: a + x, [self.visit(x) for x in ctx.vargroup()], []),
                    self.flatten(self.visit(ctx.stmt())))

    def visitCallstmt(self, ctx: MPParser.CallstmtContext):
        return CallStmt(Id(ctx.ID().getText()),
                        [self.visit(x) for x in ctx.expr()])

    def visitFuncall(self, ctx: MPParser.FuncallContext):
        return CallExpr(Id(ctx.ID().getText()),
                        [self.visit(x) for x in ctx.expr()])

    def visitExpr(self, ctx: MPParser.ExprContext):
        if ctx.getChildCount() == 1:
            return self.visit(ctx.exp1())
        if ctx.AND():
            return BinaryOp('andthen',
                            self.visit(ctx.expr()),
                            self.visit(ctx.exp1()))
        if ctx.OR():
            return BinaryOp('orelse',
                            self.visit(ctx.expr()),
                            self.visit(ctx.exp1()))

    def visitExp1(self, ctx: MPParser.Exp1Context):
        if ctx.getChildCount() == 1:
            return self.visit(ctx.exp2(0))
        else:
            return BinaryOp(ctx.getChild(1).getText(),
                            self.visit(ctx.exp2(0)),
                            self.visit(ctx.exp2(1)))

    def visitExp2(self, ctx: MPParser.Exp2Context):
        if ctx.getChildCount() == 1:
            return self.visit(ctx.exp3())
        else:
            return BinaryOp(ctx.getChild(1).getText(),
                            self.visit(ctx.exp2()),
                            self.visit(ctx.exp3()))

    def visitExp3(self, ctx: MPParser.Exp3Context):
        if ctx.getChildCount() == 1:
            return self.visit(ctx.exp4())
        else:
            return BinaryOp(ctx.getChild(1).getText(),
                            self.visit(ctx.exp3()),
                            self.visit(ctx.exp4()))
    
    def visitExp4(self, ctx: MPParser.Exp4Context):
        if ctx.getChildCount() == 1:
            return self.visit(ctx.exp5())
        if ctx.SUB():
            return UnaryOp(ctx.SUB().getText(), self.visit(ctx.exp4()))
        if ctx.NOT():
            return UnaryOp(ctx.NOT().getText(), self.visit(ctx.exp4()))

    def visitExp5(self, ctx: MPParser.Exp5Context):
        if ctx.getChildCount() == 1:
            return self.visit(ctx.exp6())
        else:
            return ArrayCell(self.visit(ctx.exp6()), self.visit(ctx.expr()))

    def visitExp6(self, ctx: MPParser.Exp5Context):
        if ctx.op():
            return self.visit(ctx.op())
        else:
            return self.visit(ctx.expr())

    def visitOp(self, ctx: MPParser.OpContext):
        if ctx.ID():
            return Id(ctx.ID().getText())
        if ctx.INTLIT():
            return IntLiteral(int(ctx.INTLIT().getText()))
        if ctx.FLOATLIT():
            return FloatLiteral(float(ctx.FLOATLIT().getText()))
        if ctx.STRINGLIT():
            return StringLiteral(ctx.STRINGLIT().getText())
        if ctx.boollit():
            return BooleanLiteral(self.visit(ctx.boollit()))
        if ctx.funcall():
            return self.visit(ctx.funcall())
        if ctx.arraycell():
            return self.visit(ctx.arraycell())

    def visitBoollit(self, ctx: MPParser.BoollitContext):
        if ctx.TRUE():
            return True
        else:
            return False
    
    def visitArraycell(self, ctx: MPParser.ArraycellContext):
        return ArrayCell(self.visit(ctx.exp6()), self.visit(ctx.expr()))

    def visitPlist(self, ctx: MPParser.PlistContext):
        grp = [self.visit(x) for x in ctx.pgroup()]
        return reduce(lambda a, x: a + x, grp, [])

    def visitPgroup(self, ctx: MPParser.PgroupContext):
        idtype = self.visit(ctx.idtype())
        return [VarDecl(id, idtype) for id in self.visit(ctx.idlist())]

    def visitIdlist(self, ctx: MPParser.IdlistContext):
        return [Id(x.getText()) for x in ctx.ID()]

    def visitIdtype(self, ctx: MPParser.IdtypeContext):
        return self.visit(ctx.getChild(0))

    def visitPrimtype(self, ctx: MPParser.PrimtypeContext):
        if ctx.BOOLEAN():
            return BoolType()
        if ctx.INTEGER():
            return IntType()
        if ctx.REAL():
            return FloatType()
        if ctx.STRING():
            return StringType()

    def visitArraytype(self, ctx: MPParser.ArraytypeContext):
        return ArrayType(self.visit(ctx.signedInt()[0]),
                        self.visit(ctx.signedInt(1)),
                        self.visit(ctx.primtype()))

    def visitSignedInt(self, ctx: MPParser.SignedIntContext):
        return int(ctx.INTLIT().getText())*(-1 if ctx.SUB() else 1)

    def flatten(self, target):
        if isinstance(target, list):
            return target
        else:
            return [target]