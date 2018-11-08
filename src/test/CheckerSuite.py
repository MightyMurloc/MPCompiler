import unittest
from TestUtils import TestChecker
from AST import *
from StaticError import *

class CheckerSuite(unittest.TestCase):
    def test_redecl_1(self):
        input = """
                var i: integer;
                procedure main();
                begin end
                procedure foo();
                begin
                end
                procedure i();
                begin
                    return;
                end
                """
        expect = 'Redeclared Procedure: i'
        self.assertTrue(TestChecker.test(input,expect,401))
    def test_redecl_2(self):
        input = """
                var i: integer;
                procedure main();
                begin end
                procedure foo();
                begin
                end
                function foo():integer;
                begin
                    return 1+5;
                end
                """
        expect = 'Redeclared Function: foo'
        self.assertTrue(TestChecker.test(input,expect,402))
    def test_redecl_3(self):
        input = """
                var i: integer;
                var i: real;
                procedure main();
                begin end
                procedure foo();
                begin
                end
                """
        expect = 'Redeclared Variable: i'
        self.assertTrue(TestChecker.test(input,expect,403))
    def test_redecl_4(self):
        input = """
                var i,j: real; k,j: integer;
                procedure main();
                begin end
                procedure foo();
                begin
                end
                """
        expect = 'Redeclared Variable: j'
        self.assertTrue(TestChecker.test(input,expect,404))
    def test_redecl_5(self):
        input = """
                procedure main();
                begin end
                procedure foo(a,b,a: integer);
                begin
                end
                """
        expect = 'Redeclared Parameter: a'
        self.assertTrue(TestChecker.test(input,expect,405))
    def test_redecl_6(self):
        input = """
                procedure main();
                begin end
                procedure foo(i: boolean;j:real);
                begin
                    with a,b:real;i:integer;b:real; do
                    begin end
                end
                """
        expect = 'Redeclared Variable: b'
        self.assertTrue(TestChecker.test(input,expect,406))
    def test_redecl_7(self):
        input = """
                procedure main();
                begin end
                procedure foo(foo: boolean;j:real);
                var J: array [1 .. 5] of real;
                begin
                end
                """
        expect = 'Redeclared Variable: J'
        self.assertTrue(TestChecker.test(input,expect,407))
    def test_redecl_8(self):
        input = """
                procedure main();
                begin end
                procedure foo(i: boolean;j:real;i: string);
                begin
                    putIntLn(4);
                end
                """
        expect = 'Redeclared Parameter: i'
        self.assertTrue(TestChecker.test(input,expect,408))
    def test_redecl_9(self):
        input = """
                var getint: real;
                procedure main();
                begin end
                procedure foo(i: boolean;j:real);
                begin
                    getInt();
                end
                """
        expect = 'Redeclared Variable: getint'
        self.assertTrue(TestChecker.test(input,expect,409))
    def test_redecl_10(self):
        input = """
                procedure main();
                begin end
                procedure foo(i: boolean;j:real);
                begin
                    putIntLn(4);
                end
                var putintLN: integer;
                """
        expect = 'Redeclared Variable: putintLN'
        self.assertTrue(TestChecker.test(input,expect,410))
    def test_undecl_1(self):
        input = """
                procedure main();
                begin
                    x := 1;
                end
                procedure foo(i: boolean;j:real);
                begin
                    putIntLn(4);
                end
                """
        expect = 'Undeclared Identifier: x'
        self.assertTrue(TestChecker.test(input,expect,411))
    def test_undecl_2(self):
        input = """
                procedure main();
                begin
                    foo(true,2.0);
                    foo(false,a);
                end
                procedure foo(i: boolean;j:real);
                begin
                    putIntLn(4);
                end
                """
        expect = 'Undeclared Identifier: a'
        self.assertTrue(TestChecker.test(input,expect,412))
    def test_undecl_3(self):
        input = """
                var a: real;
                procedure main();
                begin
                    a := 1 * b/2;
                end
                procedure b(i: boolean;j:real);
                begin
                    putIntLn(4);
                    a:=a+1;
                end
                """
        expect = 'Undeclared Identifier: b'
        self.assertTrue(TestChecker.test(input,expect,413))
    def test_undecl_4(self):
        input = """
                var a: real;
                procedure main();
                begin
                    foo(false,a);
                end
                procedure foo(i: boolean;j:real);
                begin
                    putIntLn(4);
                    goo();
                    a:=a+1;
                end
                """
        expect = 'Undeclared Procedure: goo'
        self.assertTrue(TestChecker.test(input,expect,414))
    def test_undecl_5(self):
        input = """
                var a: real;
                var f: integer;
                procedure main();
                begin
                    foo(false,a);
                end
                procedure foo(i: boolean;j:real);
                begin
                    putIntLn(4);
                    f();
                    a:=a+1;
                end
                """
        expect = 'Undeclared Procedure: f'
        self.assertTrue(TestChecker.test(input,expect,415))
    def test_undecl_6(self):
        input = """
                var a: real; b: array[1 .. 2] of integer;
                procedure main();
                begin
                    foo(false,a);
                end
                procedure foo(i: boolean;j:real);
                begin
                    putIntLn(4);
                    foo(True,1e2);
                    a:= a - 1;
                    a:= b[1] + b[x];
                end
                """
        expect = 'Undeclared Identifier: x'
        self.assertTrue(TestChecker.test(input,expect,416))
    def test_undecl_7(self):
        input = """
                var a: integer;
                procedure main();
                var foo: real;
                begin
                    foo(false,1.0);
                end
                procedure foo(i: boolean;j:real);
                begin
                    putIntLn(4);
                    foo(True,1e2);
                end
                """
        expect = 'Undeclared Procedure: foo'
        self.assertTrue(TestChecker.test(input,expect,417))
    def test_undecl_8(self):
        input = """
                var a: integer;
                procedure main();
                begin
                    foo(false,1.0);
                    a := g(1,2e-1,true);
                end
                procedure foo(i: boolean;j:real);
                begin
                    putIntLn(4);
                    foo(True,1e2);
                end
                """
        expect = 'Undeclared Function: g'
        self.assertTrue(TestChecker.test(input,expect,418))
    def test_undecl_9(self):
        input = """
                var a: integer;
                procedure main();
                begin
                    foo(false,1.0);
                    a := g(1);
                end
                procedure foo(i: boolean;j:real);
                begin
                    putIntLn(4);
                    foo(True,1e2);
                end
                procedure g(a: integer);
                begin end
                """
        expect = 'Undeclared Function: g'
        self.assertTrue(TestChecker.test(input,expect,419))
    def test_undecl_10(self):
        input = """
                var a: integer;
                var g: real;
                var c: real;
                procedure main();
                begin
                    foo(false,1.0);
                    g := C := a := g(1) ;
                end
                procedure foo(i: boolean;j:real);
                begin
                    putIntLn(4);
                    foo(True,1e2);
                end
                """
        expect = 'Undeclared Function: g'
        self.assertTrue(TestChecker.test(input,expect,420))
    def test_tp_mismtch_in_stmt_1(self):
        input = """
                var a,b: integer;
                procedure main();
                begin
                    foo(false,1.0);
                    if (a < b) then
                    begin
                        if (a) then
                        begin end
                    end
                end
                procedure foo(i: boolean;j:real);
                begin
                    putIntLn(4);
                    foo(True,1e2);
                end
                """
        expect = 'Type Mismatch In Statement: If(Id(a),[],[])'
        self.assertTrue(TestChecker.test(input,expect,421))
    def test_tp_mismtch_in_stmt_2(self):
        input = """
                var a,b: integer; c: boolean;
                procedure main();
                begin
                    if (c) then
                    begin
                        if (a*b) then
                        begin end
                    end
                end
                """
        expect = 'Type Mismatch In Statement: If(BinaryOp(*,Id(a),Id(b)),[],[])'
        self.assertTrue(TestChecker.test(input,expect,422))
    def test_tp_mismtch_in_stmt_3(self):
        input = """
                var a,b: integer; c: boolean;
                procedure main();
                begin
                    if (1 + 2) then
                    begin
                        if (c) then
                        begin end
                    end
                end
                """
        expect = 'Type Mismatch In Statement: If(BinaryOp(+,IntLiteral(1),IntLiteral(2)),[If(Id(c),[],[])],[])'
        self.assertTrue(TestChecker.test(input,expect,423))
    def test_tp_mismtch_in_stmt_4(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                begin
                    if ("the sun") then
                    begin
                        if (c) then
                        begin end
                    end
                end
                """
        expect = 'Type Mismatch In Statement: If(StringLiteral(the sun),[If(Id(c),[],[])],[])'
        self.assertTrue(TestChecker.test(input,expect,424))
    def test_tp_mismtch_in_stmt_5(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                begin
                    if (false) then
                    begin
                        if (foo()) then
                        begin end
                    end
                    else
                        return;
                end
                function foo():integer;
                begin
                    return 1;
                end
                """
        expect = 'Type Mismatch In Statement: If(CallExpr(Id(foo),[]),[],[])'
        self.assertTrue(TestChecker.test(input,expect,425))
    def test_tp_mismtch_in_stmt_6(self):
        input = """
                var b: integer;
                procedure main();
                var a: integer;
                begin
                    for a := 1 to 7 do
                    begin end
                    for a := 1 to 5.0 do
                    begin
                        putIntLn(1);
                    end
                end
                function foo():integer;
                begin
                    return 1;
                end
                """
        expect = 'Type Mismatch In Statement: For(Id(a)IntLiteral(1),FloatLiteral(5.0),True,[CallStmt(Id(putIntLn),[IntLiteral(1)])])'
        self.assertTrue(TestChecker.test(input,expect,426))
    def test_tp_mismtch_in_stmt_7(self):
        input = """
                var c: boolean; d: string;
                procedure main();
                var a,b: integer;
                begin
                    for a:= -1/2 to 5 do
                    begin
                        putIntLn(1);
                    end
                end
                function foo():integer;
                begin
                    return 1;
                end
                """
        expect = 'Type Mismatch In Statement: For(Id(a)BinaryOp(/,UnaryOp(-,IntLiteral(1)),IntLiteral(2)),IntLiteral(5),True,[CallStmt(Id(putIntLn),[IntLiteral(1)])])'
        self.assertTrue(TestChecker.test(input,expect,427))
    def test_tp_mismtch_in_stmt_8(self):
        input = """
                var b: integer; c: boolean; d: string;
                procedure main();
                var c: string; a: integer;
                begin
                    for a:= 8 downto c do
                    begin
                        putIntLn(1);
                    end
                end
                function foo():integer;
                begin
                    return 1;
                end
                """
        expect = 'Type Mismatch In Statement: For(Id(a)IntLiteral(8),Id(c),False,[CallStmt(Id(putIntLn),[IntLiteral(1)])])'
        self.assertTrue(TestChecker.test(input,expect,428))
    def test_tp_mismtch_in_stmt_9(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: string; a: integer;
                begin
                    for a:= foo(8) downto 2 do
                    begin
                        putIntLn(1);
                    end
                end
                function foo(x:integer):real;
                begin
                    return 1;
                end
                """
        expect = 'Type Mismatch In Statement: For(Id(a)CallExpr(Id(foo),[IntLiteral(8)]),IntLiteral(2),False,[CallStmt(Id(putIntLn),[IntLiteral(1)])])'
        self.assertTrue(TestChecker.test(input,expect,429))
    def test_tp_mismtch_in_stmt_10(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var a: string; e: integer;
                begin
                    for e:= 1 to 5 do
                    begin
                        for a:= 7 downto 2 do
                        begin
                            putIntLn(1);
                        end
                    end
                end
                function foo(x:integer):real;
                begin
                    return 1;
                end
                """
        expect = 'Type Mismatch In Statement: For(Id(a)IntLiteral(7),IntLiteral(2),False,[CallStmt(Id(putIntLn),[IntLiteral(1)])])'
        self.assertTrue(TestChecker.test(input,expect,430))
    def test_tp_mismtch_in_stmt_11(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var a: string;
                begin
                    while 1 do
                    begin 
                        putIntln(7);
                    end
                end
                function foo(x:integer):real;
                begin
                    return 1;
                end
                """
        expect = 'Type Mismatch In Statement: While(IntLiteral(1),[CallStmt(Id(putIntln),[IntLiteral(7)])])'
        self.assertTrue(TestChecker.test(input,expect,431))
    def test_tp_mismtch_in_stmt_12(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: string;
                begin
                    while c do
                    begin 
                        putIntln(7);
                    end
                end
                function foo(x:integer):real;
                begin
                    return 1;
                end
                """
        expect = 'Type Mismatch In Statement: While(Id(c),[CallStmt(Id(putIntln),[IntLiteral(7)])])'
    
        self.assertTrue(TestChecker.test(input,expect,432))
    
    def test_tp_mismtch_in_stmt_13(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: string;
                begin
                    while a < b do
                    begin 
                        putIntln(7);
                        while a + b do
                            a := foo();
                    end
                    break;
                end
                function foo(x:integer):real;
                begin
                    return 1;
                end
                """
        expect = 'Type Mismatch In Statement: While(BinaryOp(+,Id(a),Id(b)),[AssignStmt(Id(a),CallExpr(Id(foo),[]))])'
    
        self.assertTrue(TestChecker.test(input,expect,433))

    def test_tp_mismtch_in_stmt_14(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                begin
                    while foo(12) do
                    begin
                        while "long" do
                            break;
                    end
                end
                function foo(x:integer):boolean;
                begin
                    return 1;
                end
                """
        expect = 'Type Mismatch In Statement: While(StringLiteral(long),[Break])'
    
        self.assertTrue(TestChecker.test(input,expect,434))

    def test_tp_mismtch_in_stmt_15(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: string;
                begin
                    while foo(7) do
                    begin 
                        putIntln(7);
                    end
                    break;
                end
                function foo(x:integer):real;
                begin
                    return 1;
                end
                """
        expect = 'Type Mismatch In Statement: While(CallExpr(Id(foo),[IntLiteral(7)]),[CallStmt(Id(putIntln),[IntLiteral(7)])])'
    
        self.assertTrue(TestChecker.test(input,expect,435))

    def test_tp_mismtch_in_stmt_16(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: string;
                begin
                    a := 1.5;
                end
                function foo(x:integer):real;
                begin
                    return 1;
                end
                """
        expect = 'Type Mismatch In Statement: AssignStmt(Id(a),FloatLiteral(1.5))'
    
        self.assertTrue(TestChecker.test(input,expect,436))

    def test_tp_mismtch_in_stmt_17(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: string;
                begin
                    c := "long";
                end
                function foo(x:integer):real;
                begin
                    return 1;
                end
                """
        expect = 'Type Mismatch In Statement: AssignStmt(Id(c),StringLiteral(long))'
    
        self.assertTrue(TestChecker.test(input,expect,437))

    def test_tp_mismtch_in_stmt_18(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real;
                begin
                    a := c := 1;
                end
                function foo(x:integer):real;
                begin
                    return 1;
                end
                """
        expect = 'Type Mismatch In Statement: AssignStmt(Id(a),Id(c))'
    
        self.assertTrue(TestChecker.test(input,expect,438))

    def test_tp_mismtch_in_stmt_19(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real;
                begin
                    a := foo(2);
                end
                function foo(x:integer):real;
                begin
                    return 1.5;
                end
                """
        expect = 'Type Mismatch In Statement: AssignStmt(Id(a),CallExpr(Id(foo),[IntLiteral(2)]))'
    
        self.assertTrue(TestChecker.test(input,expect,439))

    def test_tp_mismtch_in_stmt_20(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real;
                begin
                    c := foo(2);
                    a := b := goo(5.5)[4] := 7.5;
                end
                function foo(x:integer):real;
                begin
                    return 1.5;
                end
                function goo(y:real):array[1 .. 5] of real;
                var res: array [1 .. 5] of real;
                begin
                    return res;
                end
                """
        expect = 'Type Mismatch In Statement: AssignStmt(Id(b),ArrayCell(CallExpr(Id(goo),[FloatLiteral(5.5)]),IntLiteral(4)))'
    
        self.assertTrue(TestChecker.test(input,expect,440))

    def test_tp_mismtch_in_stmt_21(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real;
                begin
                    proc(1e2,"good");
                end
                function foo(x:integer):real;
                begin
                    return 1.5;
                end
                procedure proc(x:real;y:string);
                begin
                    return 7;
                end
                """
        expect = 'Type Mismatch In Statement: Return(Some(IntLiteral(7)))'
    
        self.assertTrue(TestChecker.test(input,expect,441))

    def test_tp_mismtch_in_stmt_22(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real;
                begin
                    proc(1e2,"good");
                end
                function foo(x:integer):real;
                begin
                    return "goo\\tn";
                end
                procedure proc(x:real;y:string);
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Statement: Return(Some(StringLiteral(goo\\tn)))'
    
        self.assertTrue(TestChecker.test(input,expect,442))

    def test_tp_mismtch_in_stmt_23(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real;
                begin
                    proc(1e2,"good");
                end
                function foo(x:integer):real;
                begin
                    return a < (b+9);
                end
                procedure proc(x:real;y:string);
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Statement: Return(Some(BinaryOp(<,Id(a),BinaryOp(+,Id(b),IntLiteral(9)))))'
    
        self.assertTrue(TestChecker.test(input,expect,443))

    def test_tp_mismtch_in_stmt_24(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real;
                begin
                    proc(1e2,"good");
                end
                function foo(x:integer):array[1 .. 5] of integer;
                var a: array[1 .. 5] of boolean;
                begin
                    return a;
                end
                procedure proc(x:real;y:string);
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Statement: Return(Some(Id(a)))'
    
        self.assertTrue(TestChecker.test(input,expect,444))

    def test_tp_mismtch_in_stmt_25(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real;
                begin
                    proc(1e2,"good");
                end
                function foo(x:integer):array[1 .. 5] of integer;
                var a: array[1 .. 3] of integer;
                begin
                    return a;
                end
                procedure proc(x:real;y:string);
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Statement: Return(Some(Id(a)))'
    
        self.assertTrue(TestChecker.test(input,expect,445))

    def test_tp_mismtch_in_stmt_26(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real;
                begin
                    proc(1e2,7);
                end
                procedure proc(x:real;y:string);
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Statement: CallStmt(Id(proc),[FloatLiteral(100.0),IntLiteral(7)])'
    
        self.assertTrue(TestChecker.test(input,expect,446))

    def test_tp_mismtch_in_stmt_27(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array [1 .. 3] of string;
                begin
                    proc(c,d);
                end
                procedure proc(x:real;y:array[1 .. 3] of real);
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Statement: CallStmt(Id(proc),[Id(c),Id(d)])'
    
        self.assertTrue(TestChecker.test(input,expect,447))

    def test_tp_mismtch_in_stmt_28(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real;
                begin
                    proc(1e2,"long",12);
                end
                procedure proc(x:real;y:string);
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Statement: CallStmt(Id(proc),[FloatLiteral(100.0),StringLiteral(long),IntLiteral(12)])'
    
        self.assertTrue(TestChecker.test(input,expect,448))

    def test_tp_mismtch_in_stmt_29(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[1 .. 2] of real;
                begin
                    proc(1.5,d);
                end
                procedure proc(x:real;y:array[1 .. 3] of real);
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Statement: CallStmt(Id(proc),[FloatLiteral(1.5),Id(d)])'
    
        self.assertTrue(TestChecker.test(input,expect,449))
    
    def test_tp_mismtch_in_stmt_30(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[1 .. 2] of real;
                begin
                    proc(1.5,2);
                    proc(1.5,a/b);
                end
                procedure proc(x:real;y:integer);
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Statement: CallStmt(Id(proc),[FloatLiteral(1.5),BinaryOp(/,Id(a),Id(b))])'
    
        self.assertTrue(TestChecker.test(input,expect,450))

    def test_tp_mismtch_in_expr_1(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[1 .. 2] of real;
                begin
                    proc(1.5,2);
                    c := d[b] := d[c];
                end
                procedure proc(x:real;y:integer);
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Expression: ArrayCell(Id(d),Id(c))'
    
        self.assertTrue(TestChecker.test(input,expect,451))

    def test_tp_mismtch_in_expr_2(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[1 .. 2] of real;
                begin
                    proc(1.5,2);
                    d[a] := 1.5;
                    c[2] := 0.2;
                end
                procedure proc(x:real;y:integer);
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Expression: ArrayCell(Id(c),IntLiteral(2))'
    
        self.assertTrue(TestChecker.test(input,expect,452))

    def test_tp_mismtch_in_expr_3(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[1 .. 2] of real;
                begin
                    proc(1.5,2);
                    d[1] := 0e-2;
                    d[a/b] := 1.5;
                end
                procedure proc(x:real;y:integer);
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Expression: ArrayCell(Id(d),BinaryOp(/,Id(a),Id(b)))'
    
        self.assertTrue(TestChecker.test(input,expect,453))

    def test_tp_mismtch_in_expr_4(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[1 .. 2] of real;
                begin
                    proc(7)[12] := b;
                    proc(8)[proc(1)[2]+c] := 1;
                end
                function proc(x:integer):array[1 .. 100] of integer;
                var a: array[1 .. 100] of integer; i: integer;
                begin
                    for i := 1 to 100 do
                        a[i] := i;
                    return a;
                end
                """
        expect = 'Type Mismatch In Expression: ArrayCell(CallExpr(Id(proc),[IntLiteral(8)]),BinaryOp(+,ArrayCell(CallExpr(Id(proc),[IntLiteral(1)]),IntLiteral(2)),Id(c)))'
    
        self.assertTrue(TestChecker.test(input,expect,454))

    def test_tp_mismtch_in_expr_5(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[1 .. 2] of real;
                begin
                    proc(7)[2+d[1]] := b;
                end
                function proc(x:integer):array[1 .. 100] of integer;
                var a: array[1 .. 100] of integer; i: integer;
                begin
                    for i := 1 to 100 do
                        a[i] := i;
                    return a;
                end
                """
        expect = 'Type Mismatch In Expression: ArrayCell(CallExpr(Id(proc),[IntLiteral(7)]),BinaryOp(+,IntLiteral(2),ArrayCell(Id(d),IntLiteral(1))))'
    
        self.assertTrue(TestChecker.test(input,expect,455))

    def test_tp_mismtch_in_expr_6(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[1 .. 2] of real; e: real;
                begin
                    e := c + d[1] - a;
                    e := c + d[1] * d;
                end
                function proc(x:integer):array[1 .. 100] of integer;
                var a: array[1 .. 100] of integer; i: integer;
                begin
                    for i := 1 to 100 do
                        a[i] := i;
                    return a;
                end
                """
        expect = 'Type Mismatch In Expression: BinaryOp(*,ArrayCell(Id(d),IntLiteral(1)),Id(d))'
    
        self.assertTrue(TestChecker.test(input,expect,456))

    def test_tp_mismtch_in_expr_7(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[1 .. 2] of real; e: real;
                begin
                    e := c + d[1] - a;
                    e := (proc(7)[12] - 2.5) div 15;
                end
                function proc(x:integer):array[1 .. 100] of integer;
                var a: array[1 .. 100] of integer; i: integer;
                begin
                    for i := 1 to 100 do
                        a[i] := i;
                    return a;
                end
                """
        expect = 'Type Mismatch In Expression: BinaryOp(div,BinaryOp(-,ArrayCell(CallExpr(Id(proc),[IntLiteral(7)]),IntLiteral(12)),FloatLiteral(2.5)),IntLiteral(15))'
    
        self.assertTrue(TestChecker.test(input,expect,457))

    def test_tp_mismtch_in_expr_8(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[1 .. 2] of real; e: real;
                begin
                    e := c + d[1] - a;
                    e := (proc(7)[12] - 2) / "alo";
                end
                function proc(x:integer):array[1 .. 100] of integer;
                var a: array[1 .. 100] of integer; i: integer;
                begin
                    for i := 1 to 100 do
                        a[i] := i;
                    return a;
                end
                """
        expect = 'Type Mismatch In Expression: BinaryOp(/,BinaryOp(-,ArrayCell(CallExpr(Id(proc),[IntLiteral(7)]),IntLiteral(12)),IntLiteral(2)),StringLiteral(alo))'
    
        self.assertTrue(TestChecker.test(input,expect,458))

    def test_tp_mismtch_in_expr_9(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var d: array[1 .. 2] of real; e: real;
                begin
                    if (true and then c) then
                    begin
                        while (c and a) do
                        begin end
                    end
                end
                function proc(x:integer):array[1 .. 100] of integer;
                var a: array[1 .. 100] of integer; i: integer;
                begin
                    for i := 1 to 100 do
                        a[i] := i;
                    return a;
                end
                """
        expect = 'Type Mismatch In Expression: BinaryOp(and,Id(c),Id(a))'
    
        self.assertTrue(TestChecker.test(input,expect,459))

    def test_tp_mismtch_in_expr_10(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var d: array[1 .. 2] of real; e: real;
                begin
                    if (c and not a) then
                    begin
                        while (c and c) do
                        begin end
                    end
                end
                function proc(x:integer):array[1 .. 100] of integer;
                var a: array[1 .. 100] of integer; i: integer;
                begin
                    for i := 1 to 100 do
                        a[i] := i;
                    return a;
                end
                """
        expect = 'Type Mismatch In Expression: UnaryOp(not,Id(a))'
    
        self.assertTrue(TestChecker.test(input,expect,460))

    def test_tp_mismtch_in_expr_11(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var d: array[1 .. 2] of real; e: real;
                begin
                    log(1.5/2,proc(1)[b],e mod d[0]);
                end
                function proc(x:integer):array[1 .. 100] of integer;
                var a: array[1 .. 100] of integer; i: integer;
                begin
                    for i := 1 to 100 do
                        a[i] := i;
                    return a;
                end
                procedure log(x:real;y:real;z:integer);
                var y: boolean;
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Expression: BinaryOp(mod,Id(e),ArrayCell(Id(d),IntLiteral(0)))'
    
        self.assertTrue(TestChecker.test(input,expect,461))

    def test_tp_mismtch_in_expr_12(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var d: array[1 .. 2] of real; e: real;
                begin
                    log(1.5/2,not proc(1)[b],b mod d[0]);
                end
                function proc(x:integer):array[1 .. 100] of integer;
                var a: array[1 .. 100] of integer; i: integer;
                begin
                    for i := 1 to 100 do
                        a[i] := i;
                    return a;
                end
                procedure log(x:real;y:real;z:integer);
                var y: boolean;
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Expression: UnaryOp(not,ArrayCell(CallExpr(Id(proc),[IntLiteral(1)]),Id(b)))'
    
        self.assertTrue(TestChecker.test(input,expect,462))

    def test_tp_mismtch_in_expr_13(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var d: array[1 .. 2] of integer; e: real;
                begin
                    log(1.5/2,proc(1)[b],b mod d[0]);
                end
                function proc(x:integer):array[1 .. 100] of integer;
                var a: array[1 .. 100] of integer; i: integer;
                begin
                    for i := 1 to 100 do
                        if a > not c then
                            a[i] := i;
                    return a;
                end
                procedure log(x:real;y:real;z:integer);
                var y: boolean;
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Expression: BinaryOp(>,Id(a),UnaryOp(not,Id(c)))'
    
        self.assertTrue(TestChecker.test(input,expect,463))

    def test_tp_mismtch_in_expr_14(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var d: array[1 .. 2] of integer; e: real;
                begin
                    log(1.5/2,proc(1)[b],b mod d[0]);
                end
                function proc(x:integer):array[1 .. 100] of integer;
                var a: array[1 .. 100] of integer; i: integer;
                begin
                    for i := 1 to 100 do
                        if not (i>b) then
                            a[i] := i;
                        else
                            a[-c] := 4;
                    return a;
                end
                procedure log(x:real;y:real;z:integer);
                var y: boolean;
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Expression: UnaryOp(-,Id(c))'
    
        self.assertTrue(TestChecker.test(input,expect,464))

    def test_tp_mismtch_in_expr_15(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var d: array[1 .. 2] of integer; e: real;
                begin
                    e := 1 mod (15 + -b);
                    log(1.5/2,.15,b mod d[0]);
                end
                function proc(x:integer):integer;
                var a: array[1 .. 100] of integer; i: integer;
                begin
                    return a[5] + proc(i)*a;
                end
                procedure log(x:real;y:real;z:integer);
                var y: boolean;
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Expression: BinaryOp(*,CallExpr(Id(proc),[Id(i)]),Id(a))'
    
        self.assertTrue(TestChecker.test(input,expect,465))

    def test_tp_mismtch_in_expr_16(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real;
                begin
                    c := proc(1e2,7);
                end
                function proc(x:real;y:string):real;
                begin
                    return 1.2;
                end
                """
        expect = 'Type Mismatch In Expression: CallExpr(Id(proc),[FloatLiteral(100.0),IntLiteral(7)])'
    
        self.assertTrue(TestChecker.test(input,expect,466))

    def test_tp_mismtch_in_expr_17(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array [1 .. 3] of string;y:array[1 .. 3] of real;
                begin
                    c := proc(c,y);
                    c := proc(c,d);
                end
                function proc(x:real;y:array[1 .. 3] of real):real;
                begin
                    return;
                end
                """
        expect = 'Type Mismatch In Expression: CallExpr(Id(proc),[Id(c),Id(d)])'
    
        self.assertTrue(TestChecker.test(input,expect,467))

    def test_tp_mismtch_in_expr_18(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real;
                begin
                    c := proc(1e2,"long",12);
                end
                function proc(x:real;y:string):real;
                begin
                    return 1;
                end
                """
        expect = 'Type Mismatch In Expression: CallExpr(Id(proc),[FloatLiteral(100.0),StringLiteral(long),IntLiteral(12)])'
    
        self.assertTrue(TestChecker.test(input,expect,468))

    def test_tp_mismtch_in_expr_19(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[1 .. 2] of real;
                begin
                    c := 1.5 * proc(1.5,d);
                end
                function proc(x:real;y:array[1 .. 3] of real):real;
                begin
                    return 2;
                end
                """
        expect = 'Type Mismatch In Expression: CallExpr(Id(proc),[FloatLiteral(1.5),Id(d)])'
    
        self.assertTrue(TestChecker.test(input,expect,469))

    def test_tp_mismtch_in_expr_20(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    c := 1.5 * proc(1.5,d);
                end
                function proc(x:real;y:array[1 .. 3] of real):real;
                begin
                    return 2;
                end
                """
        expect = 'Type Mismatch In Expression: CallExpr(Id(proc),[FloatLiteral(1.5),Id(d)])'
    
        self.assertTrue(TestChecker.test(input,expect,470))

    def test_func_not_ret_1(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    c := 1.5 * proc(1.5,2.2);
                end
                function proc(x,y:real):real;
                begin
                    putIntLn(15);
                end
                """
        expect = 'Function proc Not Return '
    
        self.assertTrue(TestChecker.test(input,expect,471))

    def test_func_not_ret_2(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    c := 1.5 * proc(1.5,2.2);
                end
                function f(x:integer):boolean;
                begin
                    return x < 5;
                end
                function proc(x,y:real):real;
                begin
                    if a <> b then
                        return 8e12;
                end
                """
        expect = 'Function proc Not Return '
    
        self.assertTrue(TestChecker.test(input,expect,472))

    def test_func_not_ret_3(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    c := 1.5 * proc(1.5,2.2);
                end
                function f(x:integer):boolean;
                begin
                    return x < 5;
                end
                function proc(x,y:real):real;
                begin
                    if a <> b then
                        putIntLn(15);
                    else
                        return a/2;
                end
                """
        expect = 'Function proc Not Return '
    
        self.assertTrue(TestChecker.test(input,expect,473))

    def test_func_not_ret_4(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    c := 1.5 * proc(1.5,2.2);
                end
                function f(x:integer):boolean;
                begin
                    return x < 5;
                end
                function proc(x,y:real):real;
                begin
                    if a <> b then
                        return 8e12;
                    else
                        putIntLn(15);
                end
                """
        expect = 'Function proc Not Return '
    
        self.assertTrue(TestChecker.test(input,expect,474))

    def test_func_not_ret_5(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    c := 1.5 * proc(1.5,2.2);
                end
                function f(x:integer):boolean;
                begin
                    return x < 5;
                end
                function proc(x,y:real):real;
                begin
                    if a <> b then
                        if a + b > 15 then
                            putIntLn(7);
                        else begin
                            putIntLn(6);
                            return -6.1;
                        end
                    else
                        return 1;
                end
                """
        expect = 'Function proc Not Return '
    
        self.assertTrue(TestChecker.test(input,expect,475))

    def test_func_not_ret_6(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    c := 1.5 * proc(1.5,2.2);
                end
                function f(x:integer):boolean;
                begin
                    return x < 5;
                end
                function proc(x,y:real):real;
                var i: integer;
                begin
                    i := 0;
                    if a <> b then
                        return 7;
                    while i < 5 do
                    begin
                        if i mod 3 = 0 then
                            return 1;
                        i := i + 1;
                    end
                end
                """
        expect = 'Function proc Not Return '
    
        self.assertTrue(TestChecker.test(input,expect,476))

    def test_func_not_ret_7(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    c := 1.5 * proc(1.5,2.2);
                end
                function proc(x,y:real):real;
                var i: integer;
                begin
                    i := 0;
                    if a <> b then
                        return 7;
                    return 5;
                end
                function f(x:integer):boolean;
                begin
                    with a,b: integer; x: boolean; do
                    begin
                        if x then
                            return x;
                    end
                end
                """
        expect = 'Function f Not Return '
    
        self.assertTrue(TestChecker.test(input,expect,477))

    def test_func_not_ret_8(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    c := 1.5 * proc(1.5,2.2);
                end
                function proc(x,y:real):real;
                var i: integer;
                begin
                    i := 0;
                    if a <> b then
                        return 7;
                    return 5;
                end
                function f(x:integer):boolean;
                begin
                    if a < b then
                        return 2 < x;
                    else
                        with x: boolean; do
                            if a >= b then
                                return x;
                    putIntLn(22);
                end
                """
        expect = 'Function f Not Return '
    
        self.assertTrue(TestChecker.test(input,expect,478))

    def test_func_not_ret_9(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    c := 1.5 * proc(1.5,2.2);
                    return;
                end
                function proc(x,y:real):real;
                var i: integer;
                begin
                    i := 0;
                    if f(2) then
                        return 7;
                    return 5;
                end
                function f(x:integer):boolean;
                begin
                    if a < b then
                        return 2 < x;
                    else
                        if (a <> b) and false then
                            return 212 > x + 2;
                        else
                            putIntLn(2);
                end
                """
        expect = 'Function f Not Return '
    
        self.assertTrue(TestChecker.test(input,expect,479))

    def test_func_not_ret_10(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    c := 1.5 * proc(1.5,2.2);
                    return;
                end
                function proc(x,y:real):real;
                var i: integer;
                begin
                    i := 0;
                    if f(2) then
                        return 7;
                    return 5;
                end
                function f(x:integer):boolean;
                var a: real;
                begin
                    if a < b then
                        if a*2/3 <> b + proc(1,2.2) then
                            a := proc(1,1);
                        else
                            return 11 <> a;
                    else
                        if (a <> b) and false then
                            return 212 > x + 2;
                        else
                            putIntLn(2);
                end
                """
        expect = 'Function f Not Return '
    
        self.assertTrue(TestChecker.test(input,expect,480))

    def test_break_not_in_loop_1(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    c := 1.5 * proc(1.5,2.2);
                    return;
                end
                function proc(x,y:real):real;
                var i: integer;
                begin
                    i := 0;
                    if f(2) > 1 then
                        return 7;
                    else
                        return 5;
                end
                function f(x:integer):real;
                var a: real; i: integer;
                begin
                    for i := 1 to 15 do
                    begin
                        if a <> b then
                            a := i mod b;
                        else
                            break;
                        putIntLn(12);
                    end
                    break;
                    return 1.2;
                end
                """
        expect = 'Break Not In Loop'
    
        self.assertTrue(TestChecker.test(input,expect,481))

    def test_break_not_in_loop_2(self):
        input = """
                function f(x:integer):real;
                var a: real; i: integer;
                begin
                    for i := 1 to 15 do
                    begin
                        if a <> b then
                            a := i mod b;
                        else
                            break;
                        putIntLn(12);
                    end
                    return 1.2;
                end
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    break;
                end

                function proc(x,y:real):real;
                var i: integer;
                begin
                    i := 0;
                    if f(2) > 1 then
                        return 7;
                    else
                        return 5;
                end
                
                """
        expect = 'Break Not In Loop'
    
        self.assertTrue(TestChecker.test(input,expect,482))

    def test_break_not_in_loop_2(self):
        input = """
                function f(x:integer):real;
                var a: real; i: integer;
                begin
                    for i := 1 to 15 do
                    begin
                        if a <> b then
                            a := i mod b;
                        else
                            break;
                        putIntLn(12);
                    end
                    return 1.2;
                end
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    break;
                end

                function proc(x,y:real):real;
                var i: integer;
                begin
                    i := 0;
                    if f(2) > 1 then
                        return 7;
                    else
                        return 5;
                end
                
                """
        expect = 'Break Not In Loop'
    
        self.assertTrue(TestChecker.test(input,expect,482))

    def test_break_not_in_loop_3(self):
        input = """
                function f(x:integer):real;
                var a: real; i: integer;
                begin
                    for i := 1 to 15 do
                    begin
                        if a <> b then
                            a := i mod b;
                        else
                            break;
                        putIntLn(12);
                    end
                    return 1.2;
                end
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    return;
                end

                function proc(x,y:real):real;
                var i: integer;
                begin
                    i := 0;
                    if f(2) > 1 then
                        return 7;
                    else begin
                        while i < 2 do
                            break;
                        break;
                    end
                end
                
                """
        expect = 'Break Not In Loop'
    
        self.assertTrue(TestChecker.test(input,expect,483))

    def test_break_not_in_loop_4(self):
        input = """
                function f(x:integer):real;
                var a: real; i: integer;
                begin
                    for i := 1 to 15 do
                    begin
                        if a <> b then
                            a := i mod b;
                        else
                            break;
                        putIntLn(12);
                    end
                    return 1.2;
                end
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    return;
                end

                function proc(x,y:real):real;
                var i,j: integer;
                begin
                    for i := 1 to 100 do
                        for j:= 99 downto i do
                            if i = j then break;
                        break;
                end
                
                """
        expect = 'Break Not In Loop'
    
        self.assertTrue(TestChecker.test(input,expect,484))

    def test_break_not_in_loop_5(self):
        input = """
                function f(x:integer):real;
                var a: real; i: integer;
                begin
                    for i := 1 to 15 do
                    begin
                        if a <> b then
                            a := i mod b;
                        else
                            break;
                        putIntLn(12);
                    end
                    return 1.2;
                end
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    return;
                end

                function proc(x,y:real):real;
                var i,j: integer;
                begin
                    for i := 1 to 100 do
                        for j:= 99 downto i do
                            if i = j then break;
                    with j,i: real; do
                        if i <> j then break;
                end
                
                """
        expect = 'Break Not In Loop'
    
        self.assertTrue(TestChecker.test(input,expect,485))

    def test_cont_not_in_loop_1(self):
        input = """
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    c := 1.5 * proc(1.5,2.2);
                    return;
                end
                function proc(x,y:real):real;
                var i: integer;
                begin
                    i := 0;
                    if f(2) > 1 then
                        return 7;
                    else
                        return 5;
                end
                function f(x:integer):real;
                var a: real; i: integer;
                begin
                    for i := 1 to 15 do
                    begin
                        if a <> b then begin
                            a := i mod b;
                            break;
                        end
                        else
                            continue;
                        putIntLn(12);
                    end
                    continue;
                    return 1.2;
                end
                """
        expect = 'Continue Not In Loop'
    
        self.assertTrue(TestChecker.test(input,expect,486))

    def test_cont_not_in_loop_2(self):
        input = """
                function f(x:integer):real;
                var a: real; i: integer;
                begin
                    for i := 1 to 15 do
                    begin
                        if a <> b then begin
                            a := i mod b;
                            continue;
                        end
                        else
                            break;
                        putIntLn(12);
                    end
                    return 1.2;
                end
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    putIntLn(75);
                    continue;
                end

                function proc(x,y:real):real;
                var i: integer;
                begin
                    i := 0;
                    if f(2) > 1 then
                        return 7;
                    else
                        return 5;
                end
                """
        expect = 'Continue Not In Loop'
    
        self.assertTrue(TestChecker.test(input,expect,487))

    def test_cont_not_in_loop_3(self):
        input = """
                function f(x:integer):real;
                var a: real; i: integer;
                begin
                    for i := 1 to 15 do
                    begin
                        if a <> b then
                            a := i mod b;
                        else
                            break;
                        putIntLn(12);
                    end
                    return 1.2;
                end
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    return;
                end

                function proc(x,y:real):real;
                var i: integer;
                begin
                    i := 0;
                    if f(2) > 1 then
                        return 7;
                    else begin
                        while i < 2 do
                            continue;
                        continue;
                    end
                end
                """
        expect = 'Continue Not In Loop'
    
        self.assertTrue(TestChecker.test(input,expect,488))

    def test_cont_not_in_loop_4(self):
        input = """
                function f(x:integer):real;
                var a: real; i: integer;
                begin
                    for i := 1 to 15 do
                    begin
                        if a <> b then
                            a := i mod b;
                        else
                            break;
                        putIntLn(12);
                    end
                    return 1.2;
                end
                var a,b: integer; c: boolean; d: string;
                procedure main();
                var c: real; d: array[-1 .. 3] of real;
                begin
                    return;
                end

                function proc(x,y:real):real;
                var i,j: integer;
                begin
                    for i := 1 to 100 do
                        for j:= 99 downto i do
                            if i = j then break;
                        continue;
                end
                """
        expect = 'Continue Not In Loop'
    
        self.assertTrue(TestChecker.test(input,expect,489))
    
    '''
    def test_undeclared_function(self):
        """Simple program: int main() {} """
        input = """procedure main(); begin foo();end"""
        expect = "Undeclared Procedure: foo"
        self.assertTrue(TestChecker.test(input,expect,400))

    def test_diff_numofparam_stmt(self):
        """More complex program"""
        input = """procedure main (); begin
            putIntLn();
        end"""
        expect = "Type Mismatch In Statement: CallStmt(Id(putIntLn),[])"
        self.assertTrue(TestChecker.test(input,expect,401))

    def test_undeclared_function_use_ast(self):
        """Simple program: int main() {} """
        input = Program([FuncDecl(Id("main"),[],[],[
            CallStmt(Id("foo"),[])])])
        expect = "Undeclared Procedure: foo"
        self.assertTrue(TestChecker.test(input,expect,402))

    def test_diff_numofparam_expr_use_ast(self):
        """More complex program"""
        input = Program([
                FuncDecl(Id("main"),[],[],[
                    CallStmt(Id("putIntLn"),[])])])
                        
        expect = "Type Mismatch In Statement: CallStmt(Id(putIntLn),[])"
        self.assertTrue(TestChecker.test(input,expect,403))
    '''