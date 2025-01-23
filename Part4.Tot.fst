module Part4.Tot

// # The Effect of Total Computations

let id (a:Type) (x:a) : a = x

// is a shorthand for
let id' (a:Type) (x:a) : Tot a = x
