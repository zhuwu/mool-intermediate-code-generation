# mOOL Intermediate Code Generation

This is the intermediate code generation assignment in NUS compiler course. A Java-like language with a limited set of object oriented features called mOOL is defined in this course. This assignment is implemented in Ocaml. Static type checking is performed over the parse tree, and then the corresponding intermediate code is generated.

## Static Type Checking

#### 1. Unique class name check

A function `type_check_unique_class_name` is implemented to loop through all the class names (including main class name). If duplicated class name is detected, exception is thrown out.

#### 2. Cyclic inheritance check

A function `type_check_acyclic_hierachy` is implemented. It loops through all the classes (not including main class), and add an entry with key = class name and value = parent class name to a hash table. Then it loops through the hash table defined previously, and looks up all the ancestors from the hash table. If there is an entry with key equals to some class name accessed before, then cyclic inheritance is detected and exception is thrown out. The inheritance hash table built in this step is returned for later use.

#### 3. Checking for variable types, method return types, unique same scope identifiers, method overloading and method overriding

A function `type_check_identifers_and_methods` is implemented to do the following checkings:

1) Variable types and method return types check

It checks whether the declared variable types and return types are valid. If the type is object, it is checked against the inheritance hashtable to see whether the class is defined or not. Exception thrown out if unknown type is detected.

2) Unique class attribute names

It loops through each class and checks whether the class attributes in each class have unique names. If duplicated attribute names in each class are detected, exception is thrown out.

3) Unique method parameter/local variable names 

It loop through each method and checks whether the method parameter names and local variable names are unique. If duplication is detected, exception is thrown out.

4) Method overloading check

In each class, a list of method signatures is generated. If there is any duplicated entry in method signature list, exception is thrown out. A hash table with key = class name and value = method signatures of this class is built for overriding check. Ir3 ID is computed for each method also after the checking.

5) Method overriding check

For each class, get the list of method signatures of current class and list of method signatures of its parent class. Loop through each entry of current class method signature list, and compare it with each entry of parent class method signature list: if two methods have same signature but different return type, exception is thrown out. After checking is passed, check the list of method signatures of current class against method signatures of its parent class' parent class, until it reaches the top.

#### 4. Type annotation

1) Annotate main class

Function `transform_main` is implemented. It returns the tuple with class name and anotated main method.

2) Annotate normal class

Function `transform_classes` is implemented. It loops through every class, and for each class, it transforms each method, and returns (class name, parent, attribute list, transformed method list).

3) Annotate method

Function `type_check_method` is implemented. For each method, it transforms the statement list of the method, and checks whether the type of the statement list matches with method return type.

4) Annotate statment list

Function `type_check_statement_list` is implemented. It goes through each statement, and checks whether the expressions/inner statment list matches the correct type.

5) Annotate expressions

Function `type_check_expression` is implemented to look up variables/methods, and derive type for each expression.

##### 5. Shadowing policy

A list of variables which follow the following sequence:

*method local variables, method parameters, current class attributes, parent class attributes, parent of parent class attributes ...*

is built in each method. When looking up for a variable by name, the variable list is iterated from beginning and returns the first hit.

#### 6. Private modifier

1) For attributes, when building the variable list mentioned in shadowing policy, only use public attributes of ancestor classes.

2) For methods, if the method is called by referencing to an object (like `a.method1()`), search it from the public method from the object's class and its ancestor classes; it the method is called by using method name only (like `method1()`), search it from all methods of current class, and public methods from its ancestor classes.

## IR3 Generation

#### 1. Converting annotated tree to ir3 tree

1) Convert class into record. Each record has information of class name, parent class, attribute list (including current class attributes and parent class public attributes), method table (including all current class methods and public methods of ancestor classes) in key = method signature, value = global function name format.

2) Convert each method to a global function. Function name is the 1r3 id generated during method overloading check. Pass this object of the belonging class as first parameter of function. Generate ir3 tree according to the grammar, and create temp variables when necessary.

#### 2. Boolean short circuiting

No more `&&` or `||` in generated ir3 code after boolean short circuiting is applied. When `a && b` or `a || b` is encountered, the value of a is evaluated, and determine whether to evaluate value of b depending on evaluated value of a. An ir3 if statement is used here.


## Compilation and Running

Compilation: run `make` at this directory  
Running: `./mOOL_ir3_Gen <directory of test program>`
