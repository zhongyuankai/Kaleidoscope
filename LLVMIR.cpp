#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include <algorithm>
#include <cassert>
#include <memory>
#include <vector>


/**
 * LLVM IR(Intermediate code generation)
 * https://zhuanlan.zhihu.com/p/200613850
 */
using namespace llvm;
int main() {
    LLVMContext Context;
    // Create some module to put our function into it.
    std::unique_ptr<Module> Owner = std::make_unique<Module>("test", Context);
    Module *M = Owner.get();

    // Create the add1 function entry and insert this entry into module M.  The
    // function will have a return type of "int" and take an argument of "int".
    Function *Add1F =
            Function::Create(FunctionType::get(Type::getInt32Ty(Context),
                                               {Type::getInt32Ty(Context)}, false),
                             Function::ExternalLinkage, "add1", M);


    // Add a basic block to the function. As before, it automatically inserts
    // because of the last argument.
    BasicBlock *BB = BasicBlock::Create(Context, "EntryBlock", Add1F);


    // Create a basic block builder with default parameters.  The builder will
    // automatically append instructions to the basic block `BB'.
    IRBuilder<> builder(BB);
    // Get pointers to the constant `1'.
    Value *One = builder.getInt32(1);
    // Get pointers to the integer argument of the add1 function...
    assert(Add1F->arg_begin() != Add1F->arg_end()); // Make sure there's an arg
    Argument *ArgX = &*Add1F->arg_begin();          // Get the arg
    ArgX->setName("AnArg");            // Give it a nice symbolic name for fun.


    // Create the add instruction, inserting it into the end of BB.
    Value *Add = builder.CreateAdd(One, ArgX);
    // Create the return instruction and add it to the basic block
    builder.CreateRet(Add);
    // Now, function add1 is ready.
    // Now we're going to create function `foo', which returns an int and takes no
    // arguments.
    Function *FooF =
            Function::Create(FunctionType::get(Type::getInt32Ty(Context), {}, false),
                             Function::ExternalLinkage, "foo", M);
    // Add a basic block to the FooF function.
    BB = BasicBlock::Create(Context, "EntryBlock", FooF);
    // Tell the basic block builder to attach itself to the new basic block
    builder.SetInsertPoint(BB);
    // Get pointer to the constant `10'.
    Value *Ten = builder.getInt32(10);
    // Pass Ten to the call to Add1F
    CallInst *Add1CallRes = builder.CreateCall(Add1F, Ten);
    Add1CallRes->setTailCall(true);
    // Create the return instruction and add it to the basic block.
    builder.CreateRet(Add1CallRes);


    outs() << "We just constructed this LLVM module:\n\n" << *M;
    outs().flush();
    std::error_code error_code;
    std::unique_ptr<ToolOutputFile> Out(new ToolOutputFile(
            "./test.bc", error_code, sys::fs::OF_None));

    if (errorCodeToError(error_code)) {
        errs() << errorCodeToError(error_code) << '\n';
        return -1;
    }
    //write bitcode
    WriteBitcodeToFile(*M, Out->os());
    Out->keep(); // Declare success
    return 0;
}
