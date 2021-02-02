#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"

extern int semant_debug;
extern char *curr_filename;

static ostream& error_stream = cerr;
static int semant_errors = 0;
static Decl curr_decl = 0;
Symbol return_type;


SymbolTable<Symbol, Symbol> *func_table = new SymbolTable<Symbol, Symbol>();
SymbolTable<Symbol, Variables> *funcparam_table = new SymbolTable<Symbol, Variables>();
SymbolTable<Symbol, Symbol> *formalparam_table = new SymbolTable<Symbol, Symbol>();
SymbolTable<Symbol, Symbol> *var_table = new SymbolTable<Symbol, Symbol>();
SymbolTable<Symbol, Symbol> *localvar_table = new SymbolTable<Symbol, Symbol>();
///////////////////////////////////////////////
// helper func
///////////////////////////////////////////////


static ostream& semant_error() {
    semant_errors++;
    return error_stream;
}

static ostream& semant_error(tree_node *t) {
    error_stream << t->get_line_number() << ": ";
    return semant_error();
}

static ostream& internal_error(int lineno) {
    error_stream << "FATAL:" << lineno << ": ";
    return error_stream;
}

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////

static Symbol 
    Int,
    Float,
    String,
    Bool,
    Void,
    Main,
    print
    ;

bool isValidCallName(Symbol type) {
    return type != (Symbol)print;
}

bool isValidTypeName(Symbol type) {
    return type != Void;
}

//
// Initializing the predefined symbols.
//
int curr_stmtBlock_level = 0;
int loop_stmtBlock_level = 0;  
int callDecl_level = 0;
bool ifExistReturnStmt = false;
static void initialize_constants(void) {
    // 4 basic types and Void type
    Bool        = idtable.add_string("Bool");
    Int         = idtable.add_string("Int");
    String      = idtable.add_string("String");
    Float       = idtable.add_string("Float");
    Void        = idtable.add_string("Void");  
    // Main function
    Main        = idtable.add_string("main");

    // classical function to print things, so defined here for call.
    print        = idtable.add_string("printf");
}

/*
    TODO :
    you should fill the following function defines, so that semant() can realize a semantic 
    analysis in a recursive way. 
    Of course, you can add any other functions to help.
*/

static bool sameType(Symbol name1, Symbol name2) {
    return strcmp(name1->get_string(), name2->get_string()) == 0;
}

static void install_calls(Decls decls) {
	func_table->enterscope();
	funcparam_table->enterscope();
	//printf initialization
	func_table->addid(print, new Symbol(Void));
	
	for (int i = decls->first();decls->more(i);i = decls->next(i))
	{
		if (decls->nth(i)->isCallDecl())
		{
			if (decls->nth(i)->getName() == print)
			{
				semant_error(decls->nth(i))<<" Function printf cannot be redifined.\n";
				continue;
			}
			if (func_table->lookup(decls->nth(i)->getName()) == NULL)
			{
				func_table->addid(decls->nth(i)->getName(),new Symbol(decls->nth(i)->getType()));
				CallDecl callDecl_para = CallDecl(decls->nth(i));
				Variables *var_para = new Variables(callDecl_para->getVariables());				
				funcparam_table->addid(decls->nth(i)->getName(),var_para);
			}
			else
				semant_error(decls->nth(i))<<"Function "<<decls->nth(i)->getName()<<" has been defined.\n";
		}
	}
}

static void install_globalVars(Decls decls) {
	var_table->enterscope();
	for (int i = decls->first(); decls->more(i);i = decls->next(i))
	{
		if (!(decls->nth(i)->isCallDecl()))
		{
			if (decls->nth(i)->getType() == Void)
			{
				semant_error(decls->nth(i))<<"var "<<decls->nth(i)->getName()<<" cannot be void type.\n";
				continue;
			}
			if (var_table->lookup(decls->nth(i)->getName()) == NULL)
			{
				var_table->addid(decls->nth(i)->getName(),new Symbol(decls->nth(i)->getType()));
			}
			else
				semant_error(decls->nth(i))<<"glovar var "<<(decls->nth(i)->getName())
                     			 <<" cannot be redefined.\n";
		}
	}
}

static void check_calls(Decls decls) {
	for (int i = decls->first();decls->more(i);i = decls->next(i))
	{
		curr_decl = decls->nth(i);
		if (curr_decl->isCallDecl())
		{
			curr_decl->check();
		}
	}

}

static void check_main() {
	//check for existence
	if (func_table->lookup(Main) == NULL)
	{
		semant_error()<<"Main function is not defined.\n";
	}
}

void VariableDecl_class::check() {
	if (getType() == Void)
		semant_error(this)<<"var "<<getName()<<" cannot be void.\n";
}

void CallDecl_class::check() {
	callDecl_level++;
	if (getType() != Void && getType() != Int && getType() != String && getType() != Float && getType() != Bool)
		semant_error(this)<<"Incorrect return type:"<<getType()<<"\n";
	if (getName() == Main)
	{
		if (getType() != Void)
			semant_error(this)<<"func Main should return void type.\n";
		if (getVariables()->len() != 0)
			semant_error(this)<<"func Main should have no parameters.\n";
	}
	
	//check formal parameters
	Variables vars = getVariables();
	formalparam_table->enterscope();
	
	for (int i = vars->first();vars->more(i);i = vars->next(i))
	{
		//no formal_param of type void
		if (vars->nth(i)->getType() == Void)
		{
			semant_error(this)<<"func "<<getName()<<" has formal parameters of type void.\n";
			continue;
		}
		if (formalparam_table->probe(vars->nth(i)->getName()) == NULL)
		{
			formalparam_table->addid(vars->nth(i)->getName(),new Symbol(vars->nth(i)->getType()));
		}
		else
			semant_error(this)<<"func "<<getName()
		                      <<" formal param cannot have repeat name.\n";
	}
	if (vars->len() > 6)
		semant_error(this)<<"func "<<getName()
	                      <<" has more than 6 parameters.\n";
	
	ifExistReturnStmt = false;
	return_type = getType();
	//check stmtBlock
	getBody()->check(Int);
	
	//check if return exists
	if(!ifExistReturnStmt)
		semant_error(this)<<"func "<<getName()
	                      <<" should have a return Before the end of the outermost logic.\n";
	
	callDecl_level--;
}

void StmtBlock_class::check(Symbol type) {
	curr_stmtBlock_level++;
	//check local variables declaration
	VariableDecls varDecl = getVariableDecls();
	localvar_table->enterscope();
	for (int i = varDecl->first(); varDecl->more(i);i = varDecl->next(i))
	{
		varDecl->nth(i)->check();
		if (varDecl->nth(i)->getType() == Void)
			continue;
		if (localvar_table->probe(varDecl->nth(i)->getName()) == NULL)
			localvar_table->addid(varDecl->nth(i)->getName(), new Symbol(varDecl->nth(i)->getType()));
		else
			semant_error(varDecl->nth(i))<<"var "<<varDecl->nth(i)->getName()<<" previously defined.\n";
	}
	
	//check stmts;
	Stmts stmts = getStmts();
	for (int i = stmts->first();stmts->more(i);i = stmts->next(i))
	{	 
        stmts->nth(i)->check(Int);
	}
	curr_stmtBlock_level--;
	localvar_table->exitscope();
}

void IfStmt_class::check(Symbol type)
{
    getCondition()->checkType();
    if (getCondition()->getType() != Bool)
        {
            semant_error(this) << "Condition must return a Bool, but got " << getCondition()->getType() << '\n';
        }
    getThen()->check(Int);
    getElse()->check(Int);
}

void WhileStmt_class::check(Symbol type) {
	loop_stmtBlock_level = curr_stmtBlock_level + 1;
	getCondition()->checkType();
	if (getCondition()->getType() != Bool)
		semant_error(this)<<"Condition must return a Bool,but got " <<getCondition()->getType()<<'\n';
    getBody()->check(Int);
	loop_stmtBlock_level = 0;
}

void ForStmt_class::check(Symbol type) {
	loop_stmtBlock_level = curr_stmtBlock_level + 1;
	getInit()->checkType();
	getCondition()->checkType();
	if (getCondition()->is_empty_Expr() == false)
	{
		if (getCondition()->getType() != Bool)
			semant_error(this)<<"for Condition must return a Bool,but got "<<getCondition()->getType()<<'\n';
	}
	getLoop()->check(Int);
	getBody()->check(Int);
	loop_stmtBlock_level = 0;
}

void ReturnStmt_class::check(Symbol type) {
	if (curr_stmtBlock_level == callDecl_level)
		ifExistReturnStmt = true;
	getValue()->checkType();
	if (return_type != getValue()->getType())
		semant_error(this)<<"Return type should be "<<return_type
	                      <<" in fact is "<<getValue()->getType()<<".\n";
}

void ContinueStmt_class::check(Symbol type) {
	if (curr_stmtBlock_level < loop_stmtBlock_level || loop_stmtBlock_level == 0)
		semant_error(this)<<"continue cannot be outside loop statement.\n";
}

void BreakStmt_class::check(Symbol type) {
	if (curr_stmtBlock_level < loop_stmtBlock_level || loop_stmtBlock_level == 0)
		semant_error(this) << "break cannot be outside a loop statement.\n";
}

Symbol Call_class::checkType(){
	//printf call
	if (getName() == print)
	{
		Actuals acts = getActuals();
		if (acts->len() < 1)
		{
			semant_error(this)<<"printf() should have at least one parameter of String.\n";
			setType(Void);
			return type;
		}
		acts->nth(0)->checkType();
		if (acts->nth(0)->getType() != String)
			semant_error(this)<<"printf() first param must be String.\n";
		else
		{
			for (int i = acts->first();acts->more(i);i = acts->next(i))
				acts->nth(i)->checkType();
		}
		setType(Void);
		return type;
	}
	if (func_table->lookup(getName()) == NULL)
	{
		semant_error(this)<<"func "<<getName()<<" not defined.\n";
		setType(Void);
		return type;
	}
	else
	{   //check actuals
		if (funcparam_table->lookup(getName())!=NULL)
		{
			Variables  v = *funcparam_table->lookup(getName());
			int acts_len = v->len();
			if(getActuals()->len() != acts_len)
				semant_error(this)<<"func "<<getName()
			                      <<" call with incorrect number of parameters.\n";
			else
			{
                Actuals acts = getActuals();
                for (int i = acts->first();acts->more(i);i = acts->next(i))
				{
					acts->nth(i)->checkType();
					if (acts->nth(i)->getType() != v->nth(i)->getType())
					{
						semant_error(this)<<"func "<<getName()<<", the "<<i+1
						                  <<"th param should be "<<v->nth(i)->getType()
										  <<" but actually a "<<acts->nth(i)->getType()<<".\n";
						break;
					}
				}
			}
		}
	    Symbol ty = *func_table->lookup(getName());
		setType(ty);
		return type;
	}
}

Symbol Actual_class::checkType(){
	expr->checkType();
	setType(expr->getType());
	return type;
}

Symbol Assign_class::checkType()
{
    value->checkType();
    Symbol s;
    // check left value
    if (localvar_table->lookup(lvalue) == NULL && formalparam_table->probe(lvalue) == NULL && var_table->lookup(lvalue) == NULL)
    {
        semant_error(this) << "left value " << lvalue << " not defined.\n";
        setType(Void);
        return type;
    }
    // check right value
    else if (localvar_table->lookup(lvalue) != NULL)
    {
        s = *localvar_table->lookup(lvalue);
        if (s != value->getType())
            semant_error(this) << "Right value should be type " << s
                               << " , actually " << value->getType() << " instead.\n";
    }
    else if (formalparam_table->probe(lvalue) != NULL)
    {
        s = *formalparam_table->probe(lvalue);
        if (s != value->getType())
            semant_error(this) << "Right value should be type " << s
                               << " , actually " << value->getType() << " instead.\n";
    }
    else if (var_table->lookup(lvalue) != NULL)
    {
        s = *var_table->lookup(lvalue);
        if (s != value->getType())
            semant_error(this) << "Right value should be type " << s
                               << " , actually " << value->getType() << " instead.\n";
    }
    setType(s);
    return type;
}

Symbol Add_class::checkType()
{
    e1->checkType();
    e2->checkType();
    // Int and Float, or Float and Float
    if ((e1->getType() == Int && e2->getType() == Float) ||
        (e1->getType() == Float && e2->getType() == Int) ||
        (e1->getType() == Float && e2->getType() == Float))
    {
        setType(Float);
        return type;
    }
    // Int and Int
    else if (e1->getType() == Int && e2->getType() == Int)
    {
        setType(Int);
        return type;
    }
    else
    {
        semant_error(this) << "invalid addition between a " << e1->getType()
                           << " and a " << e2->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol Minus_class::checkType()
{
    e1->checkType();
    e2->checkType();
    // Int and Float, or Float and Float
    if ((e1->getType() == Int && e2->getType() == Float) ||
        (e1->getType() == Float && e2->getType() == Int) ||
        (e1->getType() == Float && e2->getType() == Float))
    {
        setType(Float);
        return type;
    }
    // Int and Int
    else if (e1->getType() == Int && e2->getType() == Int)
    {
        setType(Int);
        return type;
    }
    else
    {
        semant_error(this) << "invalic subtraction between a " << e1->getType()
                           << " and a " << e2->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol Multi_class::checkType()
{
    e1->checkType();
    e2->checkType();
    // Int and Float, or Float and Float
    if ((e1->getType() == Int && e2->getType() == Float) ||
        (e1->getType() == Float && e2->getType() == Int) ||
        (e1->getType() == Float && e2->getType() == Float))
    {
        setType(Float);
        return type;
    }
    // Int and Int
    else if (e1->getType() == Int && e2->getType() == Int)
    {
        setType(Int);
        return type;
    }
    else
    {
        semant_error(this) << "invalid multiplication between a " << e1->getType()
                           << " and a " << e2->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol Divide_class::checkType()
{
    e1->checkType();
    e2->checkType();
    // Int and Float, or Float and Float
    if ((e1->getType() == Int && e2->getType() == Float) ||
        (e1->getType() == Float && e2->getType() == Int) ||
        (e1->getType() == Float && e2->getType() == Float))
    {
        setType(Float);
        return type;
    }
    // Int and Int
    else if (e1->getType() == Int && e2->getType() == Int)
    {
        setType(Int);
        return type;
    }
    else
    {
        semant_error(this) << "invalid division between a " << e1->getType()
                           << " and a " << e2->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol Mod_class::checkType()
{
    e1->checkType();
    e2->checkType();
    // Int and Int
    if (e1->getType() == Int && e2->getType() == Int)
    {
        setType(Int);
        return type;
    }
    else
    {
        semant_error(this) << "invalid mod between a " << e1->getType()
                           << " and a " << e2->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol Neg_class::checkType()
{
    e1->checkType();
    if (e1->getType() == Int || e1->getType() == Float)
    {
        setType(e1->getType());
        return type;
    }
    else
    {
        semant_error(this) << "A " << e1->getType()
                           << " doesn't have a negative.\n";
        setType(Void);
        return type;
    }
}

Symbol Lt_class::checkType()
{
    e1->checkType();
    e2->checkType();
    // Int and Float, or Float and Float, or Int and Int
    if ((e1->getType() == Int && e2->getType() == Float) ||
        (e1->getType() == Float && e2->getType() == Int) ||
        (e1->getType() == Float && e2->getType() == Float) ||
        (e1->getType() == Int && e2->getType() == Int))
    {
        setType(Bool);
        return type;
    }
    else
    {
        semant_error(this) << "invalid comparison between a " << e1->getType()
                           << " and a " << e2->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol Le_class::checkType()
{
    e1->checkType();
    e2->checkType();
    // Int and Float, or Float and Float, or Int and Int
    if ((e1->getType() == Int && e2->getType() == Float) ||
        (e1->getType() == Float && e2->getType() == Int) ||
        (e1->getType() == Float && e2->getType() == Float) ||
        (e1->getType() == Int && e2->getType() == Int))
    {
        setType(Bool);
        return type;
    }
    else
    {
        semant_error(this) << "invalid comparison a " << e1->getType()
                           << " and a " << e2->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol Equ_class::checkType()
{
    e1->checkType();
    e2->checkType();
    // Int and Float, or Float and Float, or Int and Int, or Bool and Bool
    if ((e1->getType() == Int && e2->getType() == Float) ||
        (e1->getType() == Float && e2->getType() == Int) ||
        (e1->getType() == Float && e2->getType() == Float) ||
        (e1->getType() == Int && e2->getType() == Int) ||
        (e1->getType() == Bool && e2->getType() == Bool))
    {
        setType(Bool);
        return type;
    }
    else
    {
        semant_error(this) << "invalid comparison between a " << e1->getType()
                           << " and a " << e2->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol Neq_class::checkType()
{
    e1->checkType();
    e2->checkType();
    // Int and Float, or Float and Float, or Int and Int, or Bool and Bool
    if ((e1->getType() == Int && e2->getType() == Float) ||
        (e1->getType() == Float && e2->getType() == Int) ||
        (e1->getType() == Float && e2->getType() == Float) ||
        (e1->getType() == Int && e2->getType() == Int) ||
        (e1->getType() == Bool && e2->getType() == Bool))
    {
        setType(Bool);
        return type;
    }
    else
    {
        semant_error(this) << "invalid comparison between a " << e1->getType()
                           << " and a " << e2->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol Ge_class::checkType()
{
    e1->checkType();
    e2->checkType();
    // Int and Float, or Float and Float, or Int and Int
    if ((e1->getType() == Int && e2->getType() == Float) ||
        (e1->getType() == Float && e2->getType() == Int) ||
        (e1->getType() == Float && e2->getType() == Float) ||
        (e1->getType() == Int && e2->getType() == Int))
    {
        setType(Bool);
        return type;
    }
    else
    {
        semant_error(this) << "invalid comparison between a " << e1->getType()
                           << " and a " << e2->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol Gt_class::checkType()
{
    e1->checkType();
    e2->checkType();
    // Int and Float, or Float and Float, or Int and Int
    if ((e1->getType() == Int && e2->getType() == Float) ||
        (e1->getType() == Float && e2->getType() == Int) ||
        (e1->getType() == Float && e2->getType() == Float) ||
        (e1->getType() == Int && e2->getType() == Int))
    {
        setType(Bool);
        return type;
    }
    else
    {
        semant_error(this) << "invalid comparison between a " << e1->getType()
                           << " and a " << e2->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol And_class::checkType()
{
    e1->checkType();
    e2->checkType();
    // Bool and Bool
    if (e1->getType() == Bool && e2->getType() == Bool)
    {
        setType(Bool);
        return type;
    }
    else
    {
        semant_error(this) << "Cannot use && between " << e1->getType()
                           << " and " << e2->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol Or_class::checkType()
{
    e1->checkType();
    e2->checkType();
    // Bool and Bool
    if (e1->getType() == Bool && e2->getType() == Bool)
    {
        setType(Bool);
        return type;
    }
    else
    {
        semant_error(this) << "Cannot use || between " << e1->getType()
                           << " and " << e2->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol Xor_class::checkType()
{
    e1->checkType();
    e2->checkType();
    // Bool and Bool, or Int and Int
    if ((e1->getType() == Bool && e2->getType() == Bool) ||
        (e1->getType() == Int && e2->getType() == Int))
    {
        setType(e1->getType());
        return type;
    }
    else
    {
        semant_error(this) << "Cannot use ^ between " << e1->getType()
                           << " and " << e2->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol Not_class::checkType()
{
    e1->checkType();
    // Bool 
    if (e1->getType() == Bool)
    {
        setType(Bool);
        return type;
    }
    else
    {
        semant_error(this) << "Cannot use ! upon " << e1->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol Bitand_class::checkType()
{
    e1->checkType();
    e2->checkType();
    // Int and Int
    if (e1->getType() == Int && e2->getType() == Int)
    {
        setType(Int);
        return type;
    }
    else
    {
        semant_error(this) << "Cannot use & between " << e1->getType()
                           << " and " << e2->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol Bitor_class::checkType()
{
    e1->checkType();
    e2->checkType();
    // Int and Int
    if (e1->getType() == Int && e2->getType() == Int)
    {
        setType(Int);
        return type;
    }
    else
    {
        semant_error(this) << "Cannot use | between " << e1->getType()
                           << " and " << e2->getType() << ".\n";
        setType(Void);
        return type;
    }
}

Symbol Bitnot_class::checkType()
{
    e1->checkType();
    // Int and Int
    if (e1->getType() == Int)
    {
        setType(Int);
        return type;
    }
    else
    {
        semant_error(this) << "Cannot use unary op ~ upon " << e1->getType() << ".\n";
        setType(Void);
        return type;
    }
}


Symbol Const_int_class::checkType(){
    setType(Int);
    return type;
}

Symbol Const_string_class::checkType(){
    setType(String);
    return type;
}

Symbol Const_float_class::checkType(){
    setType(Float);
    return type;
}

Symbol Const_bool_class::checkType(){
    setType(Bool);
    return type;
}

Symbol Object_class::checkType(){
	Symbol obj;
	if (localvar_table->lookup(var) == NULL && formalparam_table->probe(var) == NULL && var_table->lookup(var) == NULL)
	{
		semant_error(this)<<"Object "<< var <<" not defined.\n";
		setType(Void);
		return Void;
	}
	else if (localvar_table->lookup(var)!= NULL)
		obj = *localvar_table->lookup(var);
	else if (formalparam_table->probe(var)!=NULL)
		obj = *formalparam_table->probe(var);
	else if (var_table->lookup(var)!=NULL)
		obj = *var_table->lookup(var);
	setType(obj);
	return type;
}

Symbol No_expr_class::checkType(){
    setType(Void);
    return getType();
}

void Program_class::semant() {
    initialize_constants();
    install_calls(decls);
    check_main();
    install_globalVars(decls);
    check_calls(decls);
    
    if (semant_errors > 0) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}



