include "globals.mzn";
include "minisearch.mzn";
var -2147483646.0..2147483646.0 : x;
var -2147483646.0..2147483646.0 : y;
var bool:a;
var bool:b;
var bool:c;
var bool:d;
var bool:e;
var -2147483646.0..2147483646.0 : opt_var_1;
var -2147483646.0..2147483646.0 : opt_var_0;
array[int] of var float: obj_array;
constraint ((0.0 < (x + y)) <-> a);
constraint ((((2.0 * x) + (3.0 * y)) < -10.0) <-> c);
constraint ((a \/ b) /\ (c \/ d));
constraint (e -> (10.0 < x));
constraint ((10.0 < x) -> e);
constraint (x <= 100.0);
constraint (y <= 100.0);
constraint (opt_var_0=-(x));
constraint (opt_var_1=-(y));
obj_array=[opt_var_0,opt_var_1];
%use minisearch
solve search minimize_lex_float(obj_array);


function ann : minimize_lex_float(array[int] of var float : objs) =
    next () /\ commit () /\ print () /\
    repeat(
        scope(
            post(lex_less(objs,[sol(objs[i]) | i in index_set (objs)])) /\
            if next() then commit () /\ print () else break endif
    ));
