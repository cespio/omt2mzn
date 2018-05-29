include "globals.mzn";
var -2147483646.0..2147483646.0 : x;
var -2147483646.0..2147483646.0 : opt_var_0;
constraint (opt_var_0=x);
solve maximize opt_var_0;
