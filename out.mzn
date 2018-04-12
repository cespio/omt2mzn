include "minisearch.mzn";
array[int] of var int: obj_array;
var int:x;
var int:y;
var bool:a;
var bool:b;
var bool:c;
var bool:d;
var bool:e;
constraint ((0 < (x + y)) <-> a);
constraint ((((2 * x) + (3 * y)) < -10) <-> c);
constraint ((a \/ b) /\ (c \/ d));
constraint (e -> (10 < x));
constraint ((10 < x) -> e);
constraint (x <= 100);
constraint (y <= 100);
function var int: sign(var int: x)=-1*x;
obj_array=[sign(x),y];
solve search minimize_lex(obj_array)