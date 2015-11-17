/* This test contains debugger statement parser tests. */

next_statement;

a = eval("string");

next_statement;

eval(arg1, arg2);

next_statement;

for ( ; ; eval(arg1, arg2)) { nothing; }

next_statement;

function f()
{
next_statement;

a = eval("string");

next_statement;

eval(arg1, arg2);

next_statement;
}

next_statement;

