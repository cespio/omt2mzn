include "globals.mzn";
array[1..8] of var bool:opt_var_1;
array[1..8] of var bool:x;
array[1..8] of var bool:opt_var_0;
function var int: toNum(array[1..8] of var bool: a) = -ceil(pow(2,8-1))*a[1]+sum([ceil(pow(2,8-i)) * a[i]| i in 2..8]);
constraint (((120 <= toNum(x)) /\ (toNum(x) <= 120)) \/ ((97 <= toNum(x)) /\ (toNum(x) <= 97)) \/ ((54 <= toNum(x)) /\ (toNum(x) <= 54)) \/ ((32 <= toNum(x)) /\ (toNum(x) <= 32)) \/ ((22 <= toNum(x)) /\ (toNum(x) <= 22)) \/ ((11 <= toNum(x)) /\ (toNum(x) <= 11)) \/ ((8 <= toNum(x)) /\ (toNum(x) <= 8)) \/ ((-7 <= toNum(x)) /\ (toNum(x) <= -7)) \/ ((-16 <= toNum(x)) /\ (toNum(x) <= -16)) \/ ((-105 <= toNum(x)) /\ (toNum(x) <= -105)));
constraint (opt_var_0=x);
constraint (toNum(opt_var_1)>=-100);
solve minimize toNum(opt_var_0);
