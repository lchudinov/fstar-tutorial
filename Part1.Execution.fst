module Part1.Execution

// # Executing programs

// # Interpreting F* programs

// F* includes an engine (called the `normalizer`) that can symbolically reduce F* computations.
// The reduction strategy may include:
// - beta: means that functions were applied
// - delta: means that definitions were unfolded
// - iota: means that patterns were matched
// - zeta: means that recursive functions were unrolled


// # Compiling to OCaml

// ## Producing an OCaml library

// To extract OCaml code from a F* program use the command-line options, as shown below:
// `fstar --codegen OCaml --extract Part1.Quicksort --odir out Part1.Quicksort.Generic.fst`

// ## Compiling an OCaml library

// `OCAMLPATH=$FSTAR_HOME/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Part1_Quicksort_Generic.cmxa`

// The compilation with OCaml doesn't work on my system.