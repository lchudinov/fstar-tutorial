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

let rec get #h
            (ri:resource_id)
            (tree:mtree (L.length ri) h)
  : Tot resource
    (decreases ri)
  = match ri with
    | [] -> L?.res tree
    | hd::tl -> if hd then get tl (N?.left tree) else get tl (N?.right tree)
    
// ## The Prover

type resource_with_evidence : nat -> Type =
  | RES:
      res:resource ->
      ri:resource_id ->
      hashes:list hash_t {L.length ri == L.length hashes } ->
      resource_with_evidence (L.length ri)
      
/// Retrieves data references by the path, together with the hashes
/// of the sibling nodes along that path
let rec get_with_evidence (#h:_)
                          (rid:resource_id)
                          (tree:mtree (L.length rid) h)
  : Tot (resource_with_evidence (L.length rid))
        (decreases rid)
  = match rid with
    | [] -> RES (L?.res tree) [] []
    | bit::rid' -> 
      let N #_ #hl #hr left right = tree in
        if bit then
          let p = get_with_evidence rid' left in
          RES p.res rid (hr :: p.hashes)
        else
          let p = get_with_evidence rid' right in
          RES p.res rid (hl :: p.hashes)

// ## The Verifier

let tail #n (p:resource_with_evidence n { n > 0 })
  : resource_with_evidence (n - 1)
  = RES p.res (L.tail p.ri) (L.tail p.hashes)
  
let rec compute_root_hash (#n:nat)
                          (p:resource_with_evidence n)
  : hash_t
  = let RES d ri hashes = p in
    match ri with
    | [] -> hash p.res
    | bit::ri' -> 
      let h' = compute_root_hash (tail p) in
      if bit then
        hash (concat h' (L.hd hashes))
      else
        hash (concat (L.hd hashes) h')

let verify #h #n (p:resource_with_evidence n) 
                 (tree:mtree n h)
  : bool
  = compute_root_hash p = h
  
// ## Correctness

let rec  correctness (#h:hash_t)
                     (rid:resource_id)
                     (tree:mtree (L.length rid) h)
  : Lemma (ensures (verify (get_with_evidence rid tree) tree))
          (decreases rid)
  = match rid with
    | [] -> ()
    | bit::rid' ->
      let N left right = tree in
      if bit then correctness rid' left
      else correctness rid' right
      
// ## Security

type hash_collision =
  | Collision :
      s1:string ->
      s2:string {hash s1 = hash s2 /\ not (s1 = s2)} ->
      hash_collision
      
(* 
 * If [verify] can be tricked into accepting the evidence of [p] when
 * [p.res] is not actually present in the tree at [p.ri], then
 * we can exhibit a hash collision
 *)
let rec security (#n:nat) (#h:hash_t)
                 (tree:mtree n h)
                 (p:resource_with_evidence n {
                   verify p tree /\
                   not (get p.ri tree = p.res)
                 })
  : hash_collision
  = match p.ri with
    | [] -> Collision p.res (L?.res tree)
    | bit::rid' ->
      let N #_ #h1 #h2 left right = tree in
      let h' = compute_root_hash (tail p) in
      let hd :: _ = p.hashes in
      if bit then
	      if h' = h1 then
	        security left (tail p)
	      else (
                String.concat_injective h1 h' h2 hd;
                Collision (concat h1 h2) (concat h' hd)
              )
      else
	      if h' = h2 then
	        security right (tail p)
	      else (
                String.concat_injective h1 hd h2 h';
	              Collision (concat h1 h2) (concat hd h')
              )
// ## Exercise

type mtree' (n:nat) =
  | MTree : h:hash_t -> mtree n h -> mtree' n

let rec update_mtree'  (#h:hash_t)
                       (rid:resource_id)
                       (res:resource) 
                       (tree:mtree (L.length rid) h)
   : Tot(mtree' (L.length rid))
     (decreases rid)
   = match rid with
   | [] -> MTree _ (L res)
   | hd::rid' ->
     if hd then (
      let MTree _ t = update_mtree' rid' res (N?.left tree) in
      MTree _ (N t (N?.right tree))
     )
     else (
      let MTree _ t = update_mtree' rid' res (N?.right tree) in
      MTree _ (N (N?.left tree) t)
     )