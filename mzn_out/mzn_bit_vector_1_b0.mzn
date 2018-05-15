array[1..8] of var 0..1:x;
array[1..8] of var 0..1:obj_temp_var;
function var int: toNum(array[1..8] of var int: a) = sum([ceil(pow(2,8-i)) * a[i]| i in 1..8]);
constraint (((120 <= toNum(x)) /\ (toNum(x) <= 120)) \/ ((97 <= toNum(x)) /\ (toNum(x) <= 97)) \/ ((54 <= toNum(x)) /\ (toNum(x) <= 54)) \/ ((32 <= toNum(x)) /\ (toNum(x) <= 32)) \/ ((22 <= toNum(x)) /\ (toNum(x) <= 22)) \/ ((11 <= toNum(x)) /\ (toNum(x) <= 11)) \/ ((8 <= toNum(x)) /\ (toNum(x) <= 8)) \/ ((135 <= toNum(x)) /\ (toNum(x) <= 135)) \/ ((144 <= toNum(x)) /\ (toNum(x) <= 144)) \/ ((233 <= toNum(x)) /\ (toNum(x) <= 233)));
constraint (obj_temp_var=x);
solve minimize toNum(obj_temp_var);
