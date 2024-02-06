#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/StandardInstrumentations.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Scalar/Reassociate.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "KaleidoscopeJIT.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <vector>

using namespace llvm;
using namespace llvm::orc;

/**
 *
 *
# Logical unary not.
def unary!(v)
  if v then
    0
  else
    1;

# Define > with the same precedence as <.
def binary> 10 (LHS RHS)
  RHS < LHS;

# Binary "logical or", (note that it does not "short circuit")
def binary| 5 (LHS RHS)
  if LHS then
    1
  else if RHS then
    1
  else
    0;

# Define = with slightly lower precedence than relationals.
def binary= 9 (LHS RHS)
  !(LHS < RHS | LHS > RHS);


 */

///===----------------------------------------------------------------------===//
/// Lexer
///===----------------------------------------------------------------------===//

/// The lexer returns tokens [0-255] if it is an unknown character, otherwise one
/// of these for known things.
enum Token
{
    tok_eof = -1,

    /// commands
    tok_def = -2,
    tok_extern = -3,

    /// primary
    tok_identifier = -4,
    tok_number = -5,

    /// control
    tok_if = -6,
    tok_then = -7,
    tok_else = -8,
    tok_for = -9,
    tok_in = -10,

    /// operators
    tok_binary = -11,
    tok_unary = -12
};

static std::string identifier_str;    /// Filed in if tok_identifier
static double num_val;                /// Filed in if tok_number

/// gettok - Return the next token from standard input.
static int gettok()
{
    static int last_char = ' ';

    /// Skip any whitespace
    while (isspace(last_char))
        last_char = getchar();

    if (isalpha(last_char)) /// identifier: [a-zA-Z][a-zA-Z0-9]*
    {
        identifier_str = last_char;
        while (isalnum(last_char = getchar()))
            identifier_str += last_char;

        if (identifier_str == "def")
            return tok_def;
        else if (identifier_str == "extern")
            return tok_extern;
        else if (identifier_str == "if")
            return tok_if;
        else if (identifier_str == "then")
            return tok_then;
        else if (identifier_str == "else")
            return tok_else;
        else if (identifier_str == "for")
            return tok_for;
        else if (identifier_str == "in")
            return tok_in;
        else if (identifier_str == "binary")
            return tok_binary;
        else if (identifier_str == "unary")
            return tok_unary;
        else
            return tok_identifier;
    }

    if (isdigit(last_char) || last_char == '.') /// Number: [0-9.]+
    {
        std::string num_str;
        do
        {
            num_str += last_char;
            last_char = getchar();
        }
        while (isdigit(last_char) || last_char == '.');

        num_val = strtod(num_str.c_str(), 0);
        return tok_number;
    }

    if (last_char == '#')
    {
        /// Comment until end of line.
        do
        {
            last_char = getchar();
        }
        while (last_char != EOF && last_char != '\n' && last_char != '\r');

        if (last_char != EOF)
            return gettok();
    }

    /// Check for end of line. Don't eat the EOF
    if (last_char == EOF)
        return tok_eof;

    /// Otherwise, just return the character as its ascii value.
    int this_char = last_char;
    last_char = getchar();
    return this_char;
}


///===----------------------------------------------------------------------===//
/// Abstract Syntax Tree (aka Parse Tree)
///===----------------------------------------------------------------------===//

namespace
{

/// ExprAST - Base class for all expression nodes.
class ExprAST {
public:
    virtual ~ExprAST() = default;
    virtual Value * codegen() = 0;
};

using ExprASTPtr = std::unique_ptr<ExprAST>;

/// NumberExprAST - Expression class for numeric literals like "1.0".
class NumberExprAST : public ExprAST
{
    double val;
public:
    NumberExprAST(double val_)
    : val(val_) {}
    Value * codegen() override;
};

/// VariableExprAST - Expression class for referencing a variable, like "a"
class VariableExprAST : public ExprAST
{
    std::string name;

public:
    VariableExprAST(const std::string & name_)
            : name(name_) {}
    Value * codegen() override;
};

/// BinaryExprAST - Expression class for a binary operator.
class BinaryExprAST : public ExprAST
{
    char op;
    std::unique_ptr<ExprAST> lhs;
    std::unique_ptr<ExprAST> rhs;

public:
    BinaryExprAST(char op_, std::unique_ptr<ExprAST> lhs_, std::unique_ptr<ExprAST> rhs_)
            : op(op_), lhs(std::move(lhs_)), rhs(std::move(rhs_)) {}
    Value * codegen() override;
};

/// CallExprAST - Expression class for function calls;
class CallExprAST : public ExprAST
{
    std::string callee;
    std::vector<std::unique_ptr<ExprAST>> args;

public:
    CallExprAST(const std::string & callee_, std::vector<std::unique_ptr<ExprAST>> args_)
            : callee(callee_), args(std::move(args_)) {}
    Value * codegen() override;
};


/// IfExprAST - Expression class for if/then/else.
class IfExprAST : public ExprAST
{
    std::unique_ptr<ExprAST> cond_expr;
    std::unique_ptr<ExprAST> then_expr;
    std::unique_ptr<ExprAST> else_expr;
public:
    IfExprAST(std::unique_ptr<ExprAST> cond_expr_,
              std::unique_ptr<ExprAST> then_expr_,
              std::unique_ptr<ExprAST> else_expr_)
    : cond_expr(std::move(cond_expr_))
    , then_expr(std::move(then_expr_))
    , else_expr(std::move(else_expr_))
    {}

    Value * codegen() override;
};

/// ForExprAST -
class ForExprAST : public ExprAST
{
    std::string var_name;
    std::unique_ptr<ExprAST> start;
    std::unique_ptr<ExprAST> end;
    std::unique_ptr<ExprAST> step;
    std::unique_ptr<ExprAST> body;

public:
    ForExprAST(std::string & var_name_,
               std::unique_ptr<ExprAST> start_,
               std::unique_ptr<ExprAST> end_,
               std::unique_ptr<ExprAST> step_,
               std::unique_ptr<ExprAST> body_)
    : var_name(var_name_)
    , start(std::move(start_))
    , end(std::move(end_))
    , step(std::move(step_))
    , body(std::move(body_))
    {}

    Value * codegen() override;
};

/// UnaryExprAST - Expression class for a unary operator.
class UnaryExprAST : public ExprAST
{
    char op_code;
    std::unique_ptr<ExprAST> operand;

public:
    UnaryExprAST(char op_code_, std::unique_ptr<ExprAST> operand_)
    : op_code(op_code_), operand(std::move(operand_))
    {}

    Value * codegen() override;
};

/// PrototypeAST - This class represents the "prototype" for a function,
/// which captures its name, and its argument names (thus implicitly the number
/// of arguments the function takes).
class PrototypeAST
{
    std::string name;
    std::vector<std::string> args;
    bool is_operator;
    unsigned precedence; /// precedence if a binary op.
public:
    PrototypeAST(std::string & name_,
                 std::vector<std::string> args_,
                 bool is_operator_ = false,
                 unsigned precedence_ = 0)
    : name(name_)
    , args(args_)
    , is_operator(is_operator_)
    , precedence(precedence_)
    {}

    Function * codegen();
    std::string & getName()
    {
        return name;
    }

    bool isUnaryOp() const
    {
        return is_operator && args.size() == 1;
    }

    bool isBinaryOp() const
    {
        return is_operator && args.size() == 2;
    }

    char getOperatorName() const
    {
        assert(isUnaryOp() || isBinaryOp());
        return name[name.size() - 1];
    }

    unsigned getBinaryPrecedence() const
    {
        return precedence;
    }
};

/// Function AST - This class represents a function definition itself.
class FunctionAST
{
    std::unique_ptr<PrototypeAST> proto;
    std::unique_ptr<ExprAST> body;

public:
    FunctionAST(std::unique_ptr<PrototypeAST> proto_, std::unique_ptr<ExprAST> body_)
            : proto(std::move(proto_)), body(std::move(body_)) {}
    Function * codegen();
};

}

///===----------------------------------------------------------------------===//
/// Parser
///===----------------------------------------------------------------------===//

/// cur_tok/getNextToken - Provide a simple token buffer. cur_tok is the current
/// token the parser is looking at. getNextToken reads another token form the
/// lexer and updates cur_tok with its results.
static int cur_tok;
static int getNextToken()
{
    return cur_tok = gettok();
}

/// bin_op_precedence - This holds the precedence for each binary operator that is default.
static std::map<char, int> bin_op_precedence;

/// getTokPrecedence - Get the precedence of the pending binary operator token.
static int getTokPrecedence()
{
    if (!isascii(cur_tok))
        return -1;

    // Make sure it's a declared binop.
    int tok_prec = bin_op_precedence[cur_tok];
    if (tok_prec <= 0)
        return -1;

    return tok_prec;
}

/// LogError* - These are little helper functions for error handling.
std::unique_ptr<ExprAST> LogError(const char * str)
{
    fprintf(stderr, "Error: %s\n", str);
    return nullptr;
}
std::unique_ptr<PrototypeAST> LogErrorP(const char * str)
{
    LogError(str);
    return nullptr;
}

/// declare
static std::unique_ptr<ExprAST> parseExpression();

/// numberexpr ::= number
static std::unique_ptr<NumberExprAST> parseNumberExpr()
{
    auto result = std::make_unique<NumberExprAST>(num_val);
    getNextToken(); // consume the number
    return std::move(result);
}

/// parenexpr ::= '('expression')'
static std::unique_ptr<ExprAST> parseParenExpr()
{
    getNextToken(); /// eat '('
    auto expression = parseExpression();
    if (!expression)
        return nullptr;

    if (cur_tok != ')')
        return LogError("expected ')'");

    getNextToken(); /// eat ')'
    return std::move(expression);
}

/// identifierexpr
///     ::= identifier
///     ::= identifier'('expression')'
static std::unique_ptr<ExprAST> parseIdentifier()
{
    std::string id_name = identifier_str;

    getNextToken(); /// eat identifier

    if (cur_tok != '(') /// Simple variable ref.
        return std::make_unique<VariableExprAST>(id_name);

    /// Call.
    getNextToken(); /// eat '('
    std::vector<std::unique_ptr<ExprAST>> args;
    if (cur_tok != ')') {
        while (true) {
            if (auto arg = parseExpression())
                args.push_back(std::move(arg));
            else
                return nullptr;

            if (cur_tok == ')')
                break;

            if (cur_tok != ',')
                return LogError("expected ')' or ',' in argument list");

            getNextToken();
        }
    }

    /// Eat the ')'
    getNextToken();
    return std::make_unique<CallExprAST>(id_name, std::move(args));
}

/// ifexpr ::= 'if' expression 'then' expression 'else' expression
static std::unique_ptr<ExprAST> parseIfExpr()
{
    getNextToken(); /// eat the if.

    /// condition
    std::unique_ptr<ExprAST> cond_expr = parseExpression();
    if (!cond_expr)
        return nullptr;

    if (cur_tok != tok_then)
        return LogError("expected then");

    getNextToken(); /// eat the then.

    std::unique_ptr<ExprAST> then_expr = parseExpression();
    if (!then_expr)
        return nullptr;

    if (cur_tok != tok_else)
        return LogError("expected else");

    getNextToken(); /// eat the else.

    std::unique_ptr<ExprAST> else_expr = parseExpression();
    if (!else_expr)
        return nullptr;

    return std::make_unique<IfExprAST>(std::move(cond_expr), std::move(then_expr), std::move(else_expr));
}

/// forexpr ::= 'for' identifier '=' expr ',' expr (',' expr)? 'in' expr
static std::unique_ptr<ExprAST> parseForExpr()
{
    getNextToken(); /// eat 'for'.

    if (cur_tok != tok_identifier)
        return LogError("expected identifier after for");

    std::string var_name = identifier_str;
    getNextToken(); /// eat identifier.

    if (cur_tok != '=')
        return LogError("expected identifier after for");

    getNextToken(); /// eat '='.

    std::unique_ptr<ExprAST> start = parseExpression();
    if (!start)
        return nullptr;

    if (cur_tok != ',')
        return LogError("expected ',' after for start value");

    getNextToken(); /// eat ','

    std::unique_ptr<ExprAST> end = parseExpression();
    if (!end)
        return nullptr;

    /// the step value is optional.
    std::unique_ptr<ExprAST> step;
    if (cur_tok == ',')
    {
        getNextToken(); /// eat ','
        step = parseExpression();
        if (!step)
            return nullptr;
    }

    if (cur_tok != tok_in)
        return LogError("expected 'in' after for");

    getNextToken(); /// eat 'in'.

    std::unique_ptr<ExprAST> body = parseExpression();
    if (!body)
        return nullptr;

    return std::make_unique<ForExprAST>(var_name, std::move(start), std::move(end), std::move(step), std::move(body));
}


/// primary
///     ::= identifierexpr
///     ::= numberexpr
///     ::= parenexpr
static std::unique_ptr<ExprAST> parsePrimary()
{
    switch (cur_tok)
    {
        case tok_identifier:
            return parseIdentifier();
        case tok_number:
            return parseNumberExpr();
        case '(':
            return parseParenExpr();
        case tok_if:
            return parseIfExpr();
        case tok_for:
            return parseForExpr();
        default:
            return LogError("unknown token when expecting an expression");
    }
}

/// unary
///     ::= primary
///     ::= `!` unary
static std::unique_ptr<ExprAST> parseUnary()
{
    /// If the current token is not an operator, it must be a primary expr.
    if (!isascii(cur_tok) || cur_tok == '(' || cur_tok == ',')
        return parsePrimary();

    /// If this is a unary operator, read it.
    int opc = cur_tok;
    getNextToken();
    if (auto operand = parseUnary())
        return std::make_unique<UnaryExprAST>(opc, std::move(operand));

    return nullptr;
}


/// binoprhs
///   ::= ('+' primary)*
static std::unique_ptr<ExprAST> parseBinOpRHS(int expr_prec,
                                              std::unique_ptr<ExprAST> lhs)
{
    /// If this is a binop, find its precedence.
    while (true)
    {
        int tok_prec = getTokPrecedence();

        /// If this is a binop that binds at least as tightly as the current binop,
        /// consume it, otherwise we are done.
        if (tok_prec < expr_prec)
            return lhs;

        /// Okay, we know this is a binop.
        char bin_op = cur_tok;
        getNextToken(); /// eat binop

        /// Parse the unary expression after the binary operator.
        auto rhs = parseUnary();

        /// If bin_op binds less tightly with rhs than the operator after rhs, let
        /// the pending operator take rhs as its lhs.
        int next_prec = getTokPrecedence();
        if (tok_prec < next_prec)
        {
            rhs = parseBinOpRHS(tok_prec + 1, std::move(rhs));
            if (!rhs)
                return nullptr;
        }
        /// Merge LHS/RHS.
        lhs = std::make_unique<BinaryExprAST>(bin_op, std::move(lhs), std::move(rhs));
    }
}

/// expression
///   ::= primary binoprhs
///
static std::unique_ptr<ExprAST> parseExpression()
{
    auto lhs = parseUnary();
    if (!lhs)
        return nullptr;

    return parseBinOpRHS(0, std::move(lhs));
}

/// Prototype
///     :== id'('id*')
static std::unique_ptr<PrototypeAST> parsePrototype()
{
    std::string fn_name;

    unsigned kind = 0; /// 0 = identifier, 1 = unary, 2 = binary.
    unsigned binary_precedence = 30;

    switch (cur_tok)
    {
        case tok_identifier:
            fn_name = identifier_str;
            kind = 0;
            getNextToken();
            break;
        case tok_unary:
            getNextToken();
            if (!isascii(cur_tok))
                return LogErrorP("Expected unary operator");
            fn_name = "unary";
            fn_name += (char)cur_tok;
            kind = 1;
            getNextToken();
            break;
        case tok_binary:
            getNextToken();
            if (!isascii(cur_tok))
                return LogErrorP("Expected binary operator");
            fn_name = "binary";
            fn_name += (char)cur_tok;
            kind = 2;
            getNextToken();

            /// Read the precedence if present
            if (cur_tok == tok_number)
            {
                if (num_val < 1 || num_val > 100)
                    return LogErrorP("Invalid precedence: must be 1..100");

                binary_precedence = (unsigned)num_val;
                getNextToken();
            }
            break;
        default:
            return LogErrorP("Expected function name in prototype");
    }

    if (cur_tok != '(')
        return LogErrorP("Expected '(' in prototype.");

    /// Read the list of argument names.
    std::vector<std::string> arg_names;
    while (getNextToken() == tok_identifier)
        arg_names.push_back(identifier_str);

    if (cur_tok != ')')
        return LogErrorP("Expected ')' in prototype.");

    /// success
    getNextToken(); // eat ')'.

    return std::make_unique<PrototypeAST>(fn_name, std::move(arg_names), kind != 0, binary_precedence);
}

/// definition
///     ::= 'def' prototype expression
static std::unique_ptr<FunctionAST> parseDefinition()
{
    getNextToken(); /// eat 'def'
    auto proto = parsePrototype();
    if (!proto)
        return nullptr;

    auto expression = parseExpression();
    if (!expression)
        return nullptr;

    return std::make_unique<FunctionAST>(std::move(proto), std::move(expression));
}

/// external
///     ::= 'extern' prototype
static std::unique_ptr<PrototypeAST> parseExtern()
{
    getNextToken(); /// eat extern
    return parsePrototype();
}

/// toplevelexpr
///     ::= expression
static std::unique_ptr<FunctionAST> parseTopLevelExpr()
{
    auto expression = parseExpression();
    if (!expression)
        return nullptr;

    static std::string name = "__anon_expr";
    auto proto = std::make_unique<PrototypeAST>(name, std::vector<std::string>());
    return std::make_unique<FunctionAST>(std::move(proto), std::move(expression));
}



///===----------------------------------------------------------------------===//
/// Code Generation
///===----------------------------------------------------------------------===//

static std::unique_ptr<LLVMContext> llvm_context;
static std::unique_ptr<Module> llvm_module;
static std::unique_ptr<IRBuilder<>> llvm_builder;
static std::map<std::string, Value *> named_values;

static std::unique_ptr<KaleidoscopeJIT> kaleidoscope_jit;
static std::unique_ptr<FunctionPassManager> function_pass_manager;
static std::unique_ptr<LoopAnalysisManager> loop_analysis_manager;
static std::unique_ptr<FunctionAnalysisManager> function_analysis_manager;
static std::unique_ptr<CGSCCAnalysisManager> cgscc_analysis_manager;
static std::unique_ptr<ModuleAnalysisManager> module_analysis_manager;
static std::unique_ptr<PassInstrumentationCallbacks> pass_instrumentation_callbacks;
static std::unique_ptr<StandardInstrumentations> standard_instrumentations;
static std::map<std::string, std::unique_ptr<PrototypeAST>> function_protos;
static ExitOnError ExitOnErr;

Value * LogErrorV(const char * str)
{
    LogError(str);
    return nullptr;
}

Function * getFunction(std::string name)
{
    /// First, see if the function has already been added to the current module.
    if (auto * func = llvm_module->getFunction(name))
        return func;

    /// If not, check whether we can codegen the declaration form some existing prototype.
    auto proto = function_protos.find(name);
    if (proto != function_protos.end())
        return proto->second->codegen();

    /// If not existing prototype exists, return null.
    return nullptr;
}

Value *NumberExprAST::codegen()
{
    return ConstantFP::get(*llvm_context, APFloat(val));
}

Value *VariableExprAST::codegen()
{
    /// Look this variable up in the function.
    Value * v = named_values[name];
    if (!v)
        LogErrorV("Unknown variable name");

    return v;
}

Value *BinaryExprAST::codegen()
{
    Value * l = lhs->codegen();
    Value * r = rhs->codegen();
    if (!l || !r)
        return nullptr;

    switch (op)
    {
        case '+':
            return llvm_builder->CreateFAdd(l, r, "addtmp");
        case '-':
            return llvm_builder->CreateFSub(l, r, "subtmp");
        case '*':
            return llvm_builder->CreateFMul(l, r, "multmp");
        case '<':
            l = llvm_builder->CreateFCmpULT(l, r, "cmptmp");
            /// Convert bool 0/1 to double 0.0 or 1.0
            return llvm_builder->CreateUIToFP(l, Type::getDoubleTy(*llvm_context), "booltmp");
        default:
            break;
    }

    Function * func = getFunction(std::string("binary") + op);
    Value * ops[2] = {l, r};
    return llvm_builder->CreateCall(func, ops, "binop");
}

Value *CallExprAST::codegen()
{
    /// Look up the name in the global module table
    Function * callee_fun = getFunction(callee);
    if (!callee_fun)
        return LogErrorV("Unknown function referenced");

    if (callee_fun->arg_size() != args.size())
        return LogErrorV("Incorrect # arguments passed");

    std::vector<Value *> argsv;
    for (unsigned i = 0, e = args.size(); i != e; ++i)
    {
        argsv.push_back(args[i]->codegen());
        if (!argsv.back())
            return nullptr;
    }

    return llvm_builder->CreateCall(callee_fun, argsv, "calltmp");
}

Function * PrototypeAST::codegen()
{
    /// Make the function type: double(double, double) etc.
    std::vector<Type *> doubles(args.size(), Type::getDoubleTy(*llvm_context));

    FunctionType * func_type = FunctionType::get(Type::getDoubleTy(*llvm_context), doubles, false);
    Function * func = Function::Create(func_type, Function::ExternalLinkage, name, llvm_module.get());

    /// Set names for all arguments.
    unsigned idx = 0;
    for (auto & arg : func->args())
        arg.setName(args[idx++]);

    return func;
}

Value *UnaryExprAST::codegen() {
    Value *OperandV = operand->codegen();
    if (!OperandV)
        return nullptr;

    Function *F = getFunction(std::string("unary") + op_code);
    if (!F)
        return LogErrorV("Unknown unary operator");

    return llvm_builder->CreateCall(F, OperandV, "unop");
}

Function * FunctionAST::codegen()
{
    auto & p = *proto;
    function_protos[proto->getName()] = std::move(proto);
    Function * function = getFunction(p.getName());
    if (!function)
        return nullptr;

    /// If this is an operator, install it.
    if (p.isBinaryOp())
        bin_op_precedence[p.getOperatorName()] = p.getBinaryPrecedence();

    /// Create a new basic block to start insertion into.
    BasicBlock * block = BasicBlock::Create(*llvm_context, "entry", function);
    llvm_builder->SetInsertPoint(block);

    /// Record the function arguments in the named_values map.
    named_values.clear();
    for (auto & arg : function->args())
        named_values[std::string(arg.getName())] = &arg;

    if (Value * ret_val = body->codegen())
    {
        /// Finish off the function.
        llvm_builder->CreateRet(ret_val);

        /// variable the generated code, checking for consistency.
        verifyFunction(*function);

        /// Optimize the function.
        function_pass_manager->run(*function, *function_analysis_manager);

        return function;
    }

    /// Error reading body, remove function.
    function->eraseFromParent();
    return nullptr;
}

Value * IfExprAST::codegen()
{
    Value * condv = cond_expr->codegen();
    if (!condv)
        return nullptr;

    /// Convert condition to a bool by comparing non-equal to 0.0.
    condv = llvm_builder->CreateFCmpONE(
            condv, ConstantFP::get(*llvm_context, APFloat(0.0)), "ifcond");

    Function * function = llvm_builder->GetInsertBlock()->getParent();

    /// Create blocks for the then and else cases.  Insert the 'then' block at the
    /// end of the function.
    BasicBlock * then_block = BasicBlock::Create(*llvm_context, "then", function);
    BasicBlock * else_block = BasicBlock::Create(*llvm_context, "else");
    BasicBlock * merge_block = BasicBlock::Create(*llvm_context, "ifcont");

    llvm_builder->CreateCondBr(condv, then_block, else_block);

    /// Emit then value.
    llvm_builder->SetInsertPoint(then_block);

    Value * thenv = then_expr->codegen();
    if (!thenv)
        return nullptr;

    llvm_builder->CreateBr(merge_block);
    /// Codegen of 'Then' can change the current block, update ThenBB for the PHI.
    then_block = llvm_builder->GetInsertBlock();

    /// Emit else block.
    function->insert(function->end(), else_block);
    llvm_builder->SetInsertPoint(else_block);

    Value * elsev = else_expr->codegen();
    if (!elsev)
        return nullptr;

    llvm_builder->CreateBr(merge_block);
    /// Codegen of 'Else' can change the current block, update ElseBB for the PHI.
    else_block = llvm_builder->GetInsertBlock();

    /// Emit merge block.
    function->insert(function->end(), merge_block);
    llvm_builder->SetInsertPoint(merge_block);
    PHINode *PN = llvm_builder->CreatePHI(Type::getDoubleTy(*llvm_context), 2, "iftmp");

    PN->addIncoming(thenv, then_block);
    PN->addIncoming(elsev, else_block);
    return PN;
}

Value * ForExprAST::codegen()
{
    /// Emit the start code first, without 'variable' in scope.
    Value * start_val = start->codegen();
    if (!start_val)
        return nullptr;

    /// Make the new basic block for the loop header, inserting after current block.
    Function * function = llvm_builder->GetInsertBlock()->getParent();
    BasicBlock * preheader_block = llvm_builder->GetInsertBlock();
    BasicBlock * loop_block = BasicBlock::Create(*llvm_context, "loop", function);

    /// Insert an explicit fall through form the current block to the loop_block.
    llvm_builder->CreateBr(loop_block);

    /// Start insertion in loop_block.
    llvm_builder->SetInsertPoint(loop_block);

    /// Start the PHI node with an entry for Start
    PHINode * variable = llvm_builder->CreatePHI(Type::getDoubleTy(*llvm_context), 2, var_name);

    variable->addIncoming(start_val, preheader_block);

    /// Within the loop, the variable is defined equal to the PHI node.
    /// If it shadows an existing variable, we have to restore it, so save it now.
    Value * old_val = named_values[var_name];
    named_values[var_name] = variable;

    /// Emit the body of the loop.  This, like any other expr, can change the
    /// current BB.  Note that we ignore the value computed by the body, but don't allow an error.
    if (!body->codegen())
        return nullptr;

    /// Emit the step value.
    Value * step_val = nullptr;
    if (step)
    {
        step_val = step->codegen();
        if (!step_val)
            return nullptr;
    }
    else
    {
        /// If not specified, use 1.0.
        step_val = ConstantFP::get(*llvm_context, APFloat(1.0));
    }

    Value * next_var = llvm_builder->CreateFAdd(variable, step_val, "nextvar");

    /// Compute the end condition.
    Value * end_cond = end->codegen();
    if (!end_cond)
        return nullptr;

    /// Convert condition to a bool by comparing non-equal to 0.0.
    end_cond = llvm_builder->CreateFCmpONE(
            end_cond, ConstantFP::get(*llvm_context, APFloat(0.0)), "loopcond");

    /// Create the "after loop" block and insert it.
    BasicBlock * loop_end_block = llvm_builder->GetInsertBlock();
    BasicBlock * after_block = BasicBlock::Create(*llvm_context, "afterloop", function);

    /// Insert the conditional branch into the end of LoopEndBB.
    llvm_builder->CreateCondBr(end_cond, loop_block, after_block);

    /// Any new code will be inserted in AfterBB.
    llvm_builder->SetInsertPoint(after_block);

    /// Add a new entry to the PHI node for the backedge.
    variable->addIncoming(next_var, loop_end_block);

    /// Restore the unshadowed variable.
    if (old_val)
        named_values[var_name] = old_val;
    else
        named_values.erase(var_name);

    /// for expr always returns 0.0.
    return Constant::getNullValue(Type::getDoubleTy(*llvm_context));
}

///===----------------------------------------------------------------------===//
/// Top-Level parsing and JIT Driver
///===----------------------------------------------------------------------===//

static void initializeModuleAndManagers()
{
    /// Open a new context and module.
    llvm_context = std::make_unique<LLVMContext>();
    llvm_module = std::make_unique<Module>("KaleidoscopeJIT", *llvm_context);
    llvm_module->setDataLayout(kaleidoscope_jit->getDataLayout());

    /// Create a new builder for the module
    llvm_builder = std::make_unique<IRBuilder<>>(*llvm_context);

    /// Create new pass and analysis managers.
    function_pass_manager = std::make_unique<FunctionPassManager>();
    loop_analysis_manager = std::make_unique<LoopAnalysisManager>();
    function_analysis_manager = std::make_unique<FunctionAnalysisManager>();
    cgscc_analysis_manager = std::make_unique<CGSCCAnalysisManager>();
    module_analysis_manager = std::make_unique<ModuleAnalysisManager>();
    pass_instrumentation_callbacks = std::make_unique<PassInstrumentationCallbacks>();
    standard_instrumentations = std::make_unique<StandardInstrumentations>(*llvm_context, /*DebugLogging*/ true);

    standard_instrumentations->registerCallbacks(*pass_instrumentation_callbacks, module_analysis_manager.get());

    /// Add transform passes.
    /// Do simple `peephole` optimizations and bit-twiddling optzns.
    function_pass_manager->addPass(InstCombinePass());
    /// Reassociate expressions.
    function_pass_manager->addPass(ReassociatePass());
    /// Eliminate Common SubExpressions
    function_pass_manager->addPass(GVNPass());
    /// Simplify the control flow graph (deleting unreachable blocks, etc).
    function_pass_manager->addPass(SimplifyCFGPass());

    /// Register analysis pass used in these transform passes.
    PassBuilder pass_builder;
    pass_builder.registerModuleAnalyses(*module_analysis_manager);
    pass_builder.registerFunctionAnalyses(*function_analysis_manager);
    pass_builder.crossRegisterProxies(*loop_analysis_manager, *function_analysis_manager, *cgscc_analysis_manager, *module_analysis_manager);
}

static void handleDefinition()
{
    if (auto function_ast = parseDefinition())
    {
        if (auto * func_ir = function_ast->codegen())
        {
            fprintf(stderr, "Read function definition: \n");
            func_ir->print(errs());
            fprintf(stderr, "\n");
            ExitOnErr(kaleidoscope_jit->addModule(
                    ThreadSafeModule(std::move(llvm_module), std::move(llvm_context))));
            initializeModuleAndManagers();
        }
    }
    else
    {
        /// Skip token for error recover.
        getNextToken();
    }
}

static void handleExtern()
{
    if (auto proto_ast = parseExtern())
    {
        if (auto * func_ir = proto_ast->codegen())
        {
            fprintf(stderr, "Read extern: \n");
            func_ir->print(errs());
            fprintf(stderr, "\n");
            function_protos[proto_ast->getName()] = std::move(proto_ast);
        }
    }
    else
    {
        /// Skip token for error recovery.
        getNextToken();
    }
}

static void handleTopLevelExpression()
{
    /// Evaluate a top-level expression into an anonymous function
    if (auto expr_ast = parseTopLevelExpr())
    {
        if (auto * expr_ir = expr_ast->codegen())
        {
            fprintf(stderr, "Read top-level expression: \n");
            expr_ir->print(errs());
            fprintf(stderr, "\n");

            /// Create a ResourceTracker to track JIT`d memory allocated to our
            /// anonymous expression -- that way we can free it after executing.
            auto resource_tracker = kaleidoscope_jit->getMainJITDylib().createResourceTracker();

            auto thread_safe_module = ThreadSafeModule(std::move(llvm_module), std::move(llvm_context));
            ExitOnErr(kaleidoscope_jit->addModule(std::move(thread_safe_module), resource_tracker));
            initializeModuleAndManagers();

            /// Search the JIT for the __anon_expr symbol.
            auto expr_symbol = ExitOnErr(kaleidoscope_jit->lookup("__anon_expr"));
//            assert(expr_symbol && "Function not found");

            /// Get the symbol`s address and cast it to the right type (takes no
            /// arguments, return a double) so we can call it as a native function.
            double (*func_ptr)() = expr_symbol.getAddress().toPtr<double (*)()>();
            fprintf(stderr, "Evaluated to %f\n", func_ptr());
            ExitOnErr(resource_tracker->remove());
        }
    }
    else
    {
        /// Skip token for error recovery.
        getNextToken();
    }
}

/// top ::= definition | external | expression | ';'
static void mainLoop()
{
    while (true)
    {
        fprintf(stderr, "ready> ");
        switch (cur_tok)
        {
            case tok_eof:
                return;
            case ';':   /// ignore top-level semicolons.
                getNextToken();
                break;
            case tok_def:
                handleDefinition();
                break;
            case tok_extern:
                handleExtern();
                break;
            default:
                handleTopLevelExpression();
                break;
        }
    }
}


///===----------------------------------------------------------------------===//
/// "Library" functions that can be "extern'd" from user code.
///===----------------------------------------------------------------------===//

#ifdef _WIN32
#define DLLEXPORT __declspec(dllexport)
#else
#define DLLEXPORT
#endif

/// putchard - putchar that takes a double and returns 0.
extern "C" DLLEXPORT double putchard(double X) {
    fputc((char)X, stderr);
    return 0;
}

/// printd - printf that takes a double prints it as "%f\n", returning 0.
extern "C" DLLEXPORT double printd(double X) {
    fprintf(stderr, "%f\n", X);
    return 0;
}

///===----------------------------------------------------------------------===//
/// Main driver code.
///===----------------------------------------------------------------------===//



int main() {
    InitializeNativeTarget();
    InitializeNativeTargetAsmPrinter();
    InitializeNativeTargetAsmParser();

    /// Install standard binary operators.
    /// 1 is lowest precedence.
    bin_op_precedence['<'] = 10;
    bin_op_precedence['+'] = 20;
    bin_op_precedence['-'] = 20;
    bin_op_precedence['*'] = 40; /// highest.

    /// Prime the first token.
    fprintf(stderr, "ready> ");
    getNextToken();

    kaleidoscope_jit = ExitOnErr(KaleidoscopeJIT::Create());

    /// Make the module, which holds all the code.
    initializeModuleAndManagers();

    /// Run the main "interpreter loop" now.
    mainLoop();

    /// Print out all of the generated code.
    llvm_module->print(errs(), nullptr);

    return 0;
}
