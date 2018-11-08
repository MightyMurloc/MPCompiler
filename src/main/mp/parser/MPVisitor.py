# Generated from main/mp/parser/MP.g4 by ANTLR 4.7.1
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .MPParser import MPParser
else:
    from MPParser import MPParser

# This class defines a complete generic visitor for a parse tree produced by MPParser.

class MPVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by MPParser#program.
    def visitProgram(self, ctx:MPParser.ProgramContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#decl.
    def visitDecl(self, ctx:MPParser.DeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#vardecl.
    def visitVardecl(self, ctx:MPParser.VardeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#vargroup.
    def visitVargroup(self, ctx:MPParser.VargroupContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#idlist.
    def visitIdlist(self, ctx:MPParser.IdlistContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#idtype.
    def visitIdtype(self, ctx:MPParser.IdtypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#primtype.
    def visitPrimtype(self, ctx:MPParser.PrimtypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#arraytype.
    def visitArraytype(self, ctx:MPParser.ArraytypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#signedInt.
    def visitSignedInt(self, ctx:MPParser.SignedIntContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#funcdecl.
    def visitFuncdecl(self, ctx:MPParser.FuncdeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#plist.
    def visitPlist(self, ctx:MPParser.PlistContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#pgroup.
    def visitPgroup(self, ctx:MPParser.PgroupContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#procdecl.
    def visitProcdecl(self, ctx:MPParser.ProcdeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#body.
    def visitBody(self, ctx:MPParser.BodyContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#stmt.
    def visitStmt(self, ctx:MPParser.StmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#cpstmt.
    def visitCpstmt(self, ctx:MPParser.CpstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#assign.
    def visitAssign(self, ctx:MPParser.AssignContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#variable.
    def visitVariable(self, ctx:MPParser.VariableContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#ifstmt.
    def visitIfstmt(self, ctx:MPParser.IfstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#whilestmt.
    def visitWhilestmt(self, ctx:MPParser.WhilestmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#forstmt.
    def visitForstmt(self, ctx:MPParser.ForstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#breakstmt.
    def visitBreakstmt(self, ctx:MPParser.BreakstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#continuestmt.
    def visitContinuestmt(self, ctx:MPParser.ContinuestmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#returnstmt.
    def visitReturnstmt(self, ctx:MPParser.ReturnstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#withstmt.
    def visitWithstmt(self, ctx:MPParser.WithstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#callstmt.
    def visitCallstmt(self, ctx:MPParser.CallstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#expr.
    def visitExpr(self, ctx:MPParser.ExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#exp1.
    def visitExp1(self, ctx:MPParser.Exp1Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#exp2.
    def visitExp2(self, ctx:MPParser.Exp2Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#exp3.
    def visitExp3(self, ctx:MPParser.Exp3Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#exp4.
    def visitExp4(self, ctx:MPParser.Exp4Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#exp5.
    def visitExp5(self, ctx:MPParser.Exp5Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#exp6.
    def visitExp6(self, ctx:MPParser.Exp6Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#op.
    def visitOp(self, ctx:MPParser.OpContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#funcall.
    def visitFuncall(self, ctx:MPParser.FuncallContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#arraycell.
    def visitArraycell(self, ctx:MPParser.ArraycellContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by MPParser#boollit.
    def visitBoollit(self, ctx:MPParser.BoollitContext):
        return self.visitChildren(ctx)



del MPParser