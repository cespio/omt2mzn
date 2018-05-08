var -2147483646.0..2147483646.0 : x;
var -2147483646.0..2147483646.0 : y;
var -2147483646.0..2147483646.0 : z;
var float:obj_temp_var;
constraint ((42.0 <= x) /\ (y <= x));
constraint (obj_temp_var=y);
solve maximize obj_temp_var;
