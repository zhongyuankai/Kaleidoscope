#include <iostream>
#include <map>

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
    };

/// NumberExprAST - Expression class for numeric literals like "1.0".
    class NumberExprAST : public ExprAST
    {
        double val;
    public:
        NumberExprAST(double val_)
                : val(val_) {}
    };

/// VariableExprAST - Expression class for referencing a variable, like "a"
    class VariableExprAST : public ExprAST
    {
        std::string name;

    public:
        VariableExprAST(const std::string & name_)
                : name(name_) {}
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
    };

/// CallExprAST - Expression class for function calls;
    class CallExprAST : public ExprAST
    {
        std::string callee;
        std::vector<std::unique_ptr<ExprAST>> args;

    public:
        CallExprAST(const std::string & callee_, std::vector<std::unique_ptr<ExprAST>> args_)
                : callee(callee_), args(std::move(args_)) {}
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
/// Top-Level parsing
///===----------------------------------------------------------------------===//

static void handleDefinition()
{
    if (parseDefinition())
        fprintf(stderr, "Parsed a function definition.\n");
    else
        getNextToken(); /// Skip token for error recover.
}

static void handleExtern()
{
    if (parseExtern())
        fprintf(stderr, "Parsed an extern\n");
    else
        getNextToken(); /// Skip token for error recovery.
}

static void handleTopLevelExpression()
{
    /// Evaluate a top-level expression into an anonymous function
    if (parseTopLevelExpr())
        fprintf(stderr, "Parsed a top-level expr\n");
    else
        getNextToken(); /// Skip token for error recovery.
}

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



int main() {
//    std::cout << "Hello, World!" << std::endl;

    bin_op_precedence['<'] = 10;
    bin_op_precedence['+'] = 20;
    bin_op_precedence['-'] = 20;
    bin_op_precedence['*'] = 40;

    fprintf(stderr, "ready> ");
    getNextToken();

    // Run the main "interpreter loop" now.
    mainLoop();

    return 0;
}
