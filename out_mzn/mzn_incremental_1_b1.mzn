include "globals.mzn";
var -2147483646.0..2147483646.0 : x;
var -2147483646.0..2147483646.0 : opt_var_0;
constraint (5.0 <= x);
constraint (opt_var_0=x);
solve minimize opt_var_0;
