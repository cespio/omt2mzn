include "globals.mzn";
include "minisearch.mzn";
var -2147483646.0..2147483646.0 : q1;
var -2147483646.0..2147483646.0 : q0;
var -2147483646.0..2147483646.0 : q3;
var -2147483646.0..2147483646.0 : q2;
var -2147483646.0..2147483646.0 : opt_var_1;
var -2147483646.0..2147483646.0 : opt_var_0;
var -2147483646.0..2147483646.0 : used_machines;
var -2147483646.0..2147483646.0 : production_cost;
var bool:m0;
var bool:m3;
var bool:m2;
var bool:m1;
array[int] of var float: obj_array;
constraint (1100.0 <= (q0 + q1 + q2 + q3));
constraint (((0.0 <= q0) /\ (q0 <= 800.0)) /\ ((0.0 <= q1) /\ (q1 <= 500.0)) /\ ((0.0 <= q2) /\ (q2 <= 600.0)) /\ ((0.0 <= q3) /\ (q3 <= 200.0)));
constraint (((0.0 < q0) -> m0) /\ ((0.0 < q1) -> m1) /\ ((0.0 < q2) -> m2) /\ ((0.0 < q3) -> m3));
constraint (production_cost = ((q0 * 8.0) + (q1 * 9.0) + (q2 * 9.0) + (q3 * 5.0)));
var bool:used_machines_0;
constraint (used_machines_0=not(m0));
var bool:used_machines_1;
constraint (used_machines_1=not(m1));
var bool:used_machines_2;
constraint (used_machines_2=not(m2));
var bool:used_machines_3;
constraint (used_machines_3=not(m3));
constraint (used_machines=not(used_machines_2)*1+not(used_machines_3)*1+not(used_machines_0)*1+not(used_machines_1)*1);
constraint ( 0 <= used_machines /\ used_machines <= (1+1+1+1));
constraint (opt_var_0=production_cost);
constraint (opt_var_1=used_machines);
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
