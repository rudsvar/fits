type I = { x: Int };
fn test(i: I): I = i;
let x = { x: 3, y: "String" };
let y = test(x);
println(y);
