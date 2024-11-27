module Part2.Merkle


// # Merkle Trees
// ## Setting
// ## Preliminaries
open FStar.String

// length-indexed strings
let lstring (n:nat) = s:string{String.length s == n}

// Concatenating strings sums their lengths
let concat #n #m (s0:lstring n) (s1:lstring m)
  : lstring (n + m)
  = FStar.String.concat_length s0 s1;
    s0 ^ s1

// A parameter, length of the hash in characters,
// e.g., this would be 32, if a character is 1 byte
// and we're using SHA-256
assume
val hash_size:nat 

// The type of of a hashed value
let hash_t = lstring hash_size

// The hash function itself
assume
val hash (m:string) : hash_t

// The type of resources stored in the tree
let resource = string

// ## Defining the Merkle tree

type mtree: nat -> hash_t -> Type =
  | L:
      res:resource ->
      mtree 0 (hash res)
  | N: #n:nat ->
       #hl:hash_t ->
       #hr:hash_t ->
       left:mtree n hl -> 
       right:mtree n hr ->
       mtree (n + 1) (hash (concat hl hr))
       
// ## Accessing an element in the tree

// A resource identifier resource_id is a path in the tree from the root to the leaf storing that resource.
// A path is just a list of booleans describing whether to descend left or right from a node.

// ## Exercise

// Implement a function to access an element in a mtree in given a rid : list bool.
// Figuring out its type, including its decreases clause, is the most interesting part.
// The function itself is straightforward.

let resource_id = list bool

module L = FStar.List.Tot

// let rec get #h
//             (ri:resource_id)
//             (tree:mtree (L.length ri) h)
//   : Tot resource
//   = match tree with
//     | 