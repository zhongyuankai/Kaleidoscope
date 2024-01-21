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

/// PrototypeAST - This class represents the "prototype" for a function,
/// which captures its name, and its argument names (thus implicitly the number
/// of arguments the function takes).
class PrototypeAST
{
    std::string name;
    std::vector<std::string> args;
public:
    PrototypeAST(std::string & name_, std::vector<std::string> args_)
            : name(name_), args(args_) {}

    Function * codegen();
    std::string & getName()
    {
        return name;
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
        default:
            return LogError("unknown token when expecting an expression");
    }
}


/// binoprhs
///   ::= ('+' primary)*
static std::unique_ptr<ExprAST> parseBinOpRHS(int expr_prec, std::unique_ptr<ExprAST> lhs)
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

        /// Parse the primary expression after the binary operator.
        auto rhs = parsePrimary();

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
    auto lhs = parsePrimary();
    if (!lhs)
        return nullptr;

    return parseBinOpRHS(0, std::move(lhs));
}

/// Prototype
///     :== id'('id*')
static std::unique_ptr<PrototypeAST> parsePrototype()
{
    if (cur_tok != tok_identifier)
        return LogErrorP("Expected function name in prototype.");

    std::string name = identifier_str;
    getNextToken();
    if (cur_tok != '(')
        return LogErrorP("Expected '(' in prototype.");

    /// Read the list of argument names.
    std::vector<std::string> args;
    while (getNextToken() == tok_identifier)
        args.push_back(identifier_str);

    if (cur_tok != ')')
        return LogErrorP("Expected ')' in prototype.");

    /// success
    getNextToken(); // eat ')'.

    return std::make_unique<PrototypeAST>(name, std::move(args));
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
            return LogErrorV("invaild binary operator");
    }
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

Function * FunctionAST::codegen()
{
    auto & p = *proto;
    function_protos[proto->getName()] = std::move(proto);
    Function * function = getFunction(p.getName());
    if (!function)
        return nullptr;

    if (!function->empty())
        return (Function *) LogErrorV("Function cannot be redefined.");

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
