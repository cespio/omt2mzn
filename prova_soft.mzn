var int:obj;
var bool:a;
var bool:b;
constraint (obj=not(a)*2+not(b)*4);
solve maximize obj;