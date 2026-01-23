/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Vector.Snoc
import VCVio.OracleComp.QueryTracking.CachingOracle
import ArkLib.ToVCVio.Oracle

/-!
  # Merkle Trees as a vector commitment

  ## Notes & TODOs

  We want this treatment to be as comprehensive as possible. In particular, our formalization
  should (eventually) include all complexities such as the following:

  - Multi-instance extraction & simulation
  - Dealing with arbitrary trees (may have arity > 2, or is not complete)
  - Path pruning optimization
-/

namespace MerkleTree

open List OracleSpec OracleComp

variable (α : Type)

/-- Define the domain & range of the (single) oracle needed for constructing a Merkle tree with
    elements from some type `α`.

  We may instantiate `α` with `BitVec n` or `Fin (2 ^ n)` to construct a Merkle tree for boolean
  vectors of length `n`. -/
@[reducible]
def spec : OracleSpec Unit := fun _ => (α × α, α)

@[simp]
lemma domain_def : (spec α).domain () = (α × α) := rfl

@[simp]
lemma range_def : (spec α).range () = α := rfl

section

variable [DecidableEq α] [Inhabited α] [Fintype α]

/-- Example: a single hash computation -/
def singleHash (left : α) (right : α) : OracleComp (spec α) α := do
  let out ← query (spec := spec α) () ⟨left, right⟩
  return out

/-- Cache for Merkle tree. Indexed by `j : Fin (n + 1)`, i.e. `j = 0, 1, ..., n`. -/
def Cache (n : ℕ) := (layer : Fin (n + 1)) → List.Vector α (2 ^ layer.val)

/-- Add a base layer to the cache -/
def Cache.cons (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) (cache : Cache α n) :
    Cache α (n + 1) :=
  Fin.snoc cache leaves

/-- Removes the leaves layer to the cache, returning only the layers of the tree above this -/
def Cache.upper (n : ℕ) (cache : Cache α (n + 1)) :
    Cache α n :=
  Fin.init cache

/-- Returns the leaves of the cache -/
def Cache.leaves (n : ℕ) (cache : Cache α (n + 1)) :
    List.Vector α (2 ^ (n + 1)) := cache (Fin.last _)

omit [DecidableEq α] [Inhabited α] [Fintype α] in
@[simp]
lemma Cache.upper_cons (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) (cache : Cache α n) :
    Cache.upper α n (Cache.cons α n leaves cache) = cache := by
  simp [Cache.upper, Cache.cons]

omit [DecidableEq α] [Inhabited α] [Fintype α] in
@[simp]
lemma Cache.leaves_cons (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) (cache : Cache α n) :
    Cache.leaves α n (Cache.cons α n leaves cache) = leaves := by
  simp [Cache.leaves, Cache.cons]

/-- Compute the next layer of the Merkle tree -/
def buildLayer (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) :
    OracleComp (spec α) (List.Vector α (2 ^ n)) := do
  let leaves : List.Vector α (2 ^ n * 2) := by rwa [pow_succ] at leaves
  -- Pair up the leaves to form pairs
  let pairs : List.Vector (α × α) (2 ^ n) :=
    List.Vector.ofFn (fun i =>
      (leaves.get ⟨2 * i, by omega⟩, leaves.get ⟨2 * i + 1, by omega⟩))
  -- Hash each pair to get the next layer
  let hashes : List.Vector α (2 ^ n) ←
    List.Vector.mmap (fun ⟨left, right⟩ => query (spec := spec α) () ⟨left, right⟩) pairs
  return hashes

/-- Build the full Merkle tree, returning the cache -/
def buildMerkleTree (α) (n : ℕ) (leaves : List.Vector α (2 ^ n)) :
    OracleComp (spec α) (Cache α n) := do
  match n with
  | 0 => do
    return fun j => (by
      rw [Fin.val_eq_zero j]
      exact leaves)
  | n + 1 => do
    let lastLayer ← buildLayer α n leaves
    let cache ← buildMerkleTree α n lastLayer
    return Cache.cons α n leaves cache

/-- Get the root of the Merkle tree -/
def getRoot {n : ℕ} (cache : Cache α n) : α :=
  (cache 0).get ⟨0, by simp⟩

/-- Figure out the indices of the Merkle tree nodes that are needed to
recompute the root from the given leaf -/
def findNeighbors {n : ℕ} (i : Fin (2 ^ n)) (layer : Fin n) :
    Fin (2 ^ (layer.val + 1)) :=
  -- `finFunctionFinEquiv.invFun` gives the little-endian order, e.g. `6 = 011 little`
  -- so we need to reverse it to get the big-endian order, e.g. `6 = 110 big`
  let bits := (Vector.ofFn (finFunctionFinEquiv.invFun i)).reverse
  -- `6 = 110 big`, `j = 1`, we get `neighbor = 10 big`
  let neighbor := (bits.set layer (bits.get layer + 1)).take (layer.val + 1)
  have : min (layer.val + 1) n = layer.val + 1 := by omega
  -- `10 big` => `01 little` => `2`
  finFunctionFinEquiv.toFun (this ▸ neighbor.reverse.get)

/-- Sibling index in a perfect binary tree layer indexed by `Fin (2 ^ (n + 1))`. -/
def siblingIndex {n : ℕ} (i : Fin (2 ^ (n + 1))) : Fin (2 ^ (n + 1)) :=
  if h : i.val % 2 = 0 then
    ⟨i.val + 1, by
      have hi : i.val < 2 ^ (n + 1) := i.isLt
      have hEven : Even (2 ^ (n + 1)) := by
        exact (Nat.even_pow).2 ⟨by simpa using (even_two : Even (2 : ℕ)), Nat.succ_ne_zero n⟩
      have hmod : (2 ^ (n + 1)) % 2 = 0 := (Nat.even_iff).1 hEven
      have hle : i.val + 1 ≤ 2 ^ (n + 1) := Nat.succ_le_of_lt hi
      have hne : i.val + 1 ≠ 2 ^ (n + 1) := by
        intro hEq
        have hiVal : i.val = 2 ^ (n + 1) - 1 := by omega
        have hpos : 0 < 2 ^ (n + 1) := by
          exact pow_pos (by decide : 0 < (2 : ℕ)) _
        have hle1 : 1 ≤ 2 ^ (n + 1) := Nat.succ_le_of_lt hpos
        have hmodPred : (2 ^ (n + 1) - 1) % 2 = 1 := by
          have : (2 ^ (n + 1) - 1 + 1) % 2 = 0 := by
            simpa [Nat.sub_add_cancel hle1] using hmod
          exact (Nat.succ_mod_two_eq_zero_iff (m := 2 ^ (n + 1) - 1)).1 this
        have : i.val % 2 = 1 := by simpa [hiVal] using hmodPred
        omega
      exact lt_of_le_of_ne hle hne⟩
  else
    ⟨i.val - 1, by
      have hi : i.val < 2 ^ (n + 1) := i.isLt
      omega⟩

end

@[simp]
theorem getRoot_trivial (a : α) : getRoot α <$> (buildMerkleTree α 0 ⟨[a], rfl⟩) = pure a := by
  simp [getRoot, buildMerkleTree, List.Vector.head]

@[simp]
theorem getRoot_single (a b : α) :
    getRoot α <$> buildMerkleTree α 1 ⟨[a, b], rfl⟩ = (query (spec := spec α) () (a, b)) := by
  simp [buildMerkleTree, buildLayer, List.Vector.ofFn, List.Vector.get]
  unfold Cache.cons getRoot
  simp [Fin.snoc]

section

variable [DecidableEq α] [Inhabited α] [Fintype α]

/-- Generate a Merkle proof that a given leaf at index `i` is in the Merkle tree. The proof consists
  of the Merkle tree nodes that are needed to recompute the root from the given leaf. -/
def generateProof {n : ℕ} (i : Fin (2 ^ n)) (cache : Cache α n) :
    List.Vector α n :=
  match n with
  | 0 => List.Vector.nil
  | n + 1 =>
      List.Vector.cons ((cache.leaves).get (siblingIndex i))
        (generateProof ⟨i.val / 2, by omega⟩ (cache.upper))

/--
Given a leaf index, a leaf at that index, and putative proof,
returns the hash that would be the root of the tree if the proof was valid.
i.e. the hash obtained by combining the leaf in sequence with each member of the proof,
according to its index.
-/
def getPutativeRoot {n : ℕ} (i : Fin (2 ^ n)) (leaf : α) (proof : List.Vector α n) :
    OracleComp (spec α) α := do
  match h : n with
  | 0 => do
    -- When we have an empty proof, the root is just the leaf
    return leaf
  | n + 1 => do
    -- Get the sign bit of `i`
    let signBit := i.val % 2
    -- Show that `i / 2` is in `Fin (2 ^ (n - 1))`
    let i' : Fin (2 ^ n) := ⟨i.val / 2, by omega⟩
    if signBit = 0 then
      -- `i` is a left child
      let newLeaf ← query (spec := spec α) () ⟨leaf, proof.head⟩
      getPutativeRoot i' newLeaf proof.tail
    else
      -- `i` is a right child
      let newLeaf ← query (spec := spec α) () ⟨proof.head, leaf⟩
      getPutativeRoot i' newLeaf proof.tail

/-- Verify a Merkle proof `proof` that a given `leaf` at index `i` is in the Merkle tree with given
  `root`.
  Works by computing the putative root based on the branch, and comparing that to the actual root.
  Outputs `failure` if the proof is invalid. -/
def verifyProof {n : ℕ} (i : Fin (2 ^ n)) (leaf : α) (root : α) (proof : List.Vector α n) :
    OracleComp (spec α) Unit := do
  let putative_root ← getPutativeRoot α i leaf proof
  guard (putative_root = root)

/-! ## Functional versions for proving neverFails -/

/-- Functional version of buildLayer that takes an explicit hash function -/
def buildLayer_with_hash (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) (hashFn : α × α → α) :
    List.Vector α (2 ^ n) :=
  let leaves : List.Vector α (2 ^ n * 2) := by rwa [pow_succ] at leaves
  let pairs : List.Vector (α × α) (2 ^ n) :=
    List.Vector.ofFn (fun i =>
      (leaves.get ⟨2 * i, by omega⟩, leaves.get ⟨2 * i + 1, by omega⟩))
  pairs.map hashFn

/-- Functional version of buildMerkleTree that takes an explicit hash function -/
def buildMerkleTree_with_hash (n : ℕ) (leaves : List.Vector α (2 ^ n)) (hashFn : α × α → α) :
    Cache α n :=
  match n with
  | 0 => fun j => (by rw [Fin.val_eq_zero j]; exact leaves)
  | n + 1 =>
    let lastLayer := buildLayer_with_hash α n leaves hashFn
    let cache := buildMerkleTree_with_hash n lastLayer hashFn
    Cache.cons α n leaves cache

/-- Functional version of getPutativeRoot that takes an explicit hash function -/
def getPutativeRoot_with_hash {n : ℕ} (i : Fin (2 ^ n)) (leaf : α) (proof : List.Vector α n)
    (hashFn : α × α → α) : α :=
  match n with
  | 0 => leaf
  | n + 1 =>
    let signBit := i.val % 2
    let i' : Fin (2 ^ n) := ⟨i.val / 2, by omega⟩
    if signBit = 0 then
      let newLeaf := hashFn (leaf, proof.head)
      getPutativeRoot_with_hash i' newLeaf proof.tail hashFn
    else
      let newLeaf := hashFn (proof.head, leaf)
      getPutativeRoot_with_hash i' newLeaf proof.tail hashFn

/-- Running buildLayer with an oracle function returns some value -/
lemma runWithOracle_buildLayer_isSome (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1)))
    (f : (spec α).FunctionType) :
    (runWithOracle f (buildLayer α n leaves)).isSome = true := by
  -- This follows from the fact that mmap with query always succeeds
  have h_mmap :
      ∀ {m : ℕ} (xs : List.Vector (α × α) m),
        (runWithOracle f
            (List.Vector.mmap (fun x => liftM (query (spec := spec α) () x)) xs)).isSome = true := by
    intro m xs
    induction xs using List.Vector.inductionOn with
    | nil =>
      simp only [List.Vector.mmap_nil, runWithOracle_pure, Option.isSome_some]
    | @cons m x xs ih =>
      have hq : (runWithOracle f (liftM (query (spec := spec α) () x))).isSome = true := by
        unfold runWithOracle OracleComp.construct'
        simp
      simp only [List.Vector.mmap_cons, runWithOracle_bind, Option.bind_eq_bind]
      obtain ⟨val, h1⟩ := Option.isSome_iff_exists.mp hq
      rw [h1, Option.some_bind]
      obtain ⟨rest, h2⟩ := Option.isSome_iff_exists.mp ih
      rw [h2, Option.some_bind, runWithOracle_pure, Option.isSome_some]
  simp [buildLayer, h_mmap]

/-- Helper: mmap with query equals map with function under runWithOracle -/
lemma runWithOracle_mmap_query {m : ℕ} (xs : List.Vector (α × α) m)
    (f : (spec α).FunctionType) :
    (runWithOracle f
        (List.Vector.mmap (fun x => liftM (query (spec := spec α) () x)) xs)) =
    some (List.Vector.map (fun x => f () x) xs) := by
  induction xs using List.Vector.inductionOn with
  | nil =>
    simp only [List.Vector.mmap_nil, runWithOracle_pure, List.Vector.map_nil]
  | @cons m x xs ih =>
    have hq : (runWithOracle f (liftM (query (spec := spec α) () x))) = some (f () x) := by
      unfold runWithOracle OracleComp.construct'
      simp
    simp only [List.Vector.mmap_cons, runWithOracle_bind, ih, hq, Option.bind_eq_bind,
      Option.bind_some, List.Vector.map_cons, runWithOracle_pure]

/-- Running buildLayer with an oracle function is equivalent to buildLayer_with_hash -/
lemma runWithOracle_buildLayer (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1)))
    (f : (spec α).FunctionType) :
    runWithOracle f (buildLayer α n leaves) =
    some (buildLayer_with_hash α n leaves (fun x => f () x)) := by
  simp only [buildLayer, buildLayer_with_hash]
  simp only [runWithOracle_bind, runWithOracle_pure, Option.bind_eq_bind]
  rw [runWithOracle_mmap_query]
  simp only [Option.some_bind, Option.bind_some, Prod.mk.eta]

/-- Running buildMerkleTree with an oracle function gives buildMerkleTree_with_hash -/
lemma runWithOracle_buildMerkleTree (n : ℕ) (leaves : List.Vector α (2 ^ n))
    (f : (spec α).FunctionType) :
    runWithOracle f (buildMerkleTree α n leaves) =
    some (buildMerkleTree_with_hash α n leaves (fun x => f () x)) := by
  induction n with
  | zero =>
    unfold buildMerkleTree buildMerkleTree_with_hash
    simp only [runWithOracle_pure]
  | succ n ih =>
    unfold buildMerkleTree buildMerkleTree_with_hash
    simp only [runWithOracle_bind, runWithOracle_buildLayer, Option.bind_eq_bind,
      Option.bind_some, runWithOracle_pure]
    simp only [ih, Option.some_bind]

/-- Running getPutativeRoot with an oracle function gives getPutativeRoot_with_hash -/
lemma runWithOracle_getPutativeRoot (f : (spec α).FunctionType) :
    ∀ {n : ℕ} (i : Fin (2 ^ n)) (leaf : α) (proof : List.Vector α n),
    runWithOracle f (getPutativeRoot α i leaf proof) =
    some (getPutativeRoot_with_hash (α := α) i leaf proof (fun x => f () x)) := by
  intro n
  induction n with
  | zero =>
    intro i leaf proof
    unfold getPutativeRoot getPutativeRoot_with_hash
    simp only [runWithOracle_pure]
  | succ n ih =>
    intro i leaf proof
    unfold getPutativeRoot getPutativeRoot_with_hash
    simp only [runWithOracle_bind, Option.bind_eq_bind]
    -- Split on whether signBit is 0 or not
    by_cases h : i.val % 2 = 0
    · -- signBit = 0 case
      simp only [h, ↓reduceIte]
      -- The query gets evaluated by runWithOracle
      simp only [runWithOracle_bind]
      -- runWithOracle of query gives some (f () ...)
      have hq : runWithOracle f (query (spec := spec α) () ⟨leaf, proof.head⟩) =
                some (f () ⟨leaf, proof.head⟩) := by
        unfold runWithOracle OracleComp.construct'
        simp
      simp only [hq, Option.some_bind]
      exact ih ⟨i.val / 2, by omega⟩ (f () (leaf, proof.head)) proof.tail
    · -- signBit ≠ 0 case
      simp only [h, ↓reduceIte]
      simp only [runWithOracle_bind]
      have hq : runWithOracle f (query (spec := spec α) () ⟨proof.head, leaf⟩) =
                some (f () ⟨proof.head, leaf⟩) := by
        unfold runWithOracle OracleComp.construct'
        simp
      simp only [hq, Option.some_bind]
      exact ih ⟨i.val / 2, by omega⟩ (f () (proof.head, leaf)) proof.tail

/-- Functional completeness: getPutativeRoot_with_hash with correct proof gives the root -/
theorem functional_completeness {n : ℕ} (leaves : List.Vector α (2 ^ n))
    (i : Fin (2 ^ n)) (hashFn : α × α → α) :
    getPutativeRoot_with_hash (α := α) i leaves[i]
      (generateProof α i (buildMerkleTree_with_hash α n leaves hashFn)) hashFn =
    getRoot α (buildMerkleTree_with_hash α n leaves hashFn) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    simp [buildMerkleTree_with_hash, generateProof, getPutativeRoot_with_hash, getRoot]
    change leaves.get 0 = leaves.head
    simp
  | succ n ih =>
    -- Abbreviate the upper layer and the upper tree.
    let lastLayer := buildLayer_with_hash α n leaves hashFn
    let upperCache := buildMerkleTree_with_hash (α := α) n lastLayer hashFn
    -- Split on whether `i` is a left or right child at the bottom layer.
    by_cases hsign : i.val % 2 = 0
    · -- Left child: sibling is `i + 1`.
      have hdiv : 2 * (i.val / 2) = i.val := by
        have h := Nat.mod_add_div i.val 2
        -- `i % 2 = 0` implies `2 * (i / 2) = i`.
        simpa [hsign] using h
      have hright : 2 * (i.val / 2) + 1 = i.val + 1 := by omega
      have hnew :
          hashFn (leaves.get i, leaves.get (siblingIndex i)) =
            lastLayer.get ⟨i.val / 2, by omega⟩ := by
        simp [lastLayer, buildLayer_with_hash, siblingIndex, hsign, hdiv, hright]
      -- Unfold and apply the induction hypothesis on the upper tree.
      -- `generateProof` and `getRoot` reduce via `Cache.upper_cons` and `Cache.leaves_cons`.
      simp [buildMerkleTree_with_hash, lastLayer, upperCache, generateProof, getPutativeRoot_with_hash,
        getRoot, hsign, hnew]
      simpa [getRoot, Cache.cons, lastLayer, upperCache] using
        (ih (leaves := lastLayer) (i := ⟨i.val / 2, by omega⟩))
    · -- Right child: sibling is `i - 1`.
      have hmod1 : i.val % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one i.val with h0 | h1
        · exact (hsign h0).elim
        · exact h1
      have hdiv : 2 * (i.val / 2) = i.val - 1 := by
        have h := Nat.mod_add_div i.val 2
        -- `i % 2 = 1` implies `1 + 2 * (i / 2) = i`.
        have : 1 + 2 * (i.val / 2) = i.val := by simpa [hmod1] using h
        omega
      have hright : 2 * (i.val / 2) + 1 = i.val := by omega
      have hnew :
          hashFn (leaves.get (siblingIndex i), leaves.get i) =
            lastLayer.get ⟨i.val / 2, by omega⟩ := by
        have hiPos : 1 ≤ i.val := by
          have hne : i.val ≠ 0 := by
            intro h0
            simpa [h0] using hmod1
          exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
        have hi' :
            (⟨i.val - 1 + 1, by simpa [Nat.sub_add_cancel hiPos] using i.isLt⟩ :
                Fin (2 ^ (n + 1))) =
              i := by
          ext
          simpa [Nat.sub_add_cancel hiPos]
        simp [lastLayer, buildLayer_with_hash, siblingIndex, hsign, hmod1, hdiv, hright, hi']
      simp [buildMerkleTree_with_hash, lastLayer, upperCache, generateProof, getPutativeRoot_with_hash,
        getRoot, hsign, hnew]
      simpa [getRoot, Cache.cons, lastLayer, upperCache] using
        (ih (leaves := lastLayer) (i := ⟨i.val / 2, by omega⟩))

theorem buildLayer_neverFails (α : Type) [DecidableEq α] [Inhabited α] [Fintype α] [SelectableType α]
    (preexisting_cache : (spec α).QueryCache) (n : ℕ)
    (leaves : List.Vector α (2 ^ (n + 1))) :
    ((simulateQ randomOracle (buildLayer α n leaves)).run preexisting_cache).neverFails := by
  -- Use the fact that runWithOracle always returns some for buildLayer
  revert preexisting_cache
  rw [randomOracle_neverFails_iff_runWithOracle_neverFails]
  intro f
  rw [runWithOracle_buildLayer]
  simp only [Option.isSome_some]

/--
Building a Merkle tree never results in failure
(no matter what queries have already been made to the oracle before it runs).
-/
theorem buildMerkleTree_neverFails (α : Type) [DecidableEq α] [Inhabited α] [Fintype α] [SelectableType α] {n : ℕ}
    (leaves : List.Vector α (2 ^ n)) (preexisting_cache : (spec α).QueryCache) :
    ((simulateQ randomOracle (buildMerkleTree α n leaves)).run preexisting_cache).neverFails := by
  -- It feels like there should be some kind of tactic that inspects the structure of the
  -- `buildMerkleTree` definition to see that it never even mentions failure,
  -- and therefore can't fail.
  induction n generalizing preexisting_cache with
  | zero =>
    simp [buildMerkleTree]
  | succ n ih =>
    simp [buildMerkleTree, neverFails_bind_iff]
    constructor
    · exact buildLayer_neverFails α preexisting_cache n leaves
    · intro next_leaves next_cache h_mem_support
      apply ih

/-- Completeness theorem for Merkle trees: for any full binary tree with `2 ^ n` leaves, and for any
  index `i`, the verifier accepts the opening proof at index `i` generated by the prover.
-/
theorem completeness [SelectableType α] {n : ℕ}
    (leaves : List.Vector α (2 ^ n)) (i : Fin (2 ^ n)) (hash : α × α -> α)
    (preexisting_cache : (spec α).QueryCache) :
    (((do
      let cache ← buildMerkleTree α n leaves
      let proof := generateProof α i cache
      let verif ← verifyProof α i leaves[i] (getRoot α cache) proof).simulateQ
      (randomOracle)).run preexisting_cache).neverFails := by
  -- Reduce to showing success under any deterministic oracle function.
  revert preexisting_cache
  rw [randomOracle_neverFails_iff_runWithOracle_neverFails]
  intro f
  -- Simplify the computation under `runWithOracle`.
  simp_rw [verifyProof, guard_eq, bind_pure_comp, id_map', runWithOracle_bind,
    runWithOracle_buildMerkleTree, runWithOracle_getPutativeRoot]
  simp only [apply_ite, runWithOracle_pure, runWithOracle_failure, Option.bind_eq_bind,
    Option.bind_some, Option.isSome_some, Option.isSome_none, Bool.if_false_right, Bool.and_true,
    decide_eq_true_eq]
  -- Apply the purely functional completeness lemma.
  simpa using functional_completeness (α := α) (leaves := leaves) (i := i) (hashFn := fun x => f () x)

end

section Test

-- 6 = 110_big
-- Third neighbor (`j = 0`): 0 = 0 big
-- Second neighbor (`j = 1`): 2 = 10 big
-- First neighbor (`j = 2`): 7 = 111 big
#eval findNeighbors (6 : Fin (2 ^ 3)) 0
#eval findNeighbors (6 : Fin (2 ^ 3)) 1
#eval findNeighbors (6 : Fin (2 ^ 3)) 2

/-! ### Tests for siblingIndex -/

-- Even indices should map to index + 1
#eval siblingIndex (0 : Fin (2 ^ 3))  -- Expected: 1
#eval siblingIndex (2 : Fin (2 ^ 3))  -- Expected: 3
#eval siblingIndex (4 : Fin (2 ^ 3))  -- Expected: 5
#eval siblingIndex (6 : Fin (2 ^ 3))  -- Expected: 7

-- Odd indices should map to index - 1
#eval siblingIndex (1 : Fin (2 ^ 3))  -- Expected: 0
#eval siblingIndex (3 : Fin (2 ^ 3))  -- Expected: 2
#eval siblingIndex (5 : Fin (2 ^ 3))  -- Expected: 4
#eval siblingIndex (7 : Fin (2 ^ 3))  -- Expected: 6

-- siblingIndex is an involution (applying twice gives back the original)
#eval siblingIndex (siblingIndex (0 : Fin (2 ^ 3)))  -- Expected: 0
#eval siblingIndex (siblingIndex (3 : Fin (2 ^ 3)))  -- Expected: 3
#eval siblingIndex (siblingIndex (6 : Fin (2 ^ 3)))  -- Expected: 6

/-! ### Tests for buildLayer_with_hash -/

-- Simple hash function for testing: sum of pair
def testHashSum : ℕ × ℕ → ℕ := fun (a, b) => a + b

-- Build a layer from 4 leaves [1, 2, 3, 4] -> [3, 7] (1+2=3, 3+4=7)
#eval (buildLayer_with_hash ℕ 1 ⟨[1, 2, 3, 4], rfl⟩ testHashSum).toList
-- Expected: [3, 7]

-- Build a layer from 8 leaves
#eval (buildLayer_with_hash ℕ 2 ⟨[1, 2, 3, 4, 5, 6, 7, 8], rfl⟩ testHashSum).toList
-- Expected: [3, 7, 11, 15]

/-! ### Tests for buildMerkleTree_with_hash -/

-- Build tree with 2 leaves [1, 2] -> root = 3
#eval getRoot ℕ (buildMerkleTree_with_hash ℕ 1 ⟨[1, 2], rfl⟩ testHashSum)
-- Expected: 3

-- Build tree with 4 leaves [1, 2, 3, 4]
-- Layer 1: [3, 7] (1+2, 3+4)
-- Layer 0: [10] (3+7)
#eval getRoot ℕ (buildMerkleTree_with_hash ℕ 2 ⟨[1, 2, 3, 4], rfl⟩ testHashSum)
-- Expected: 10

-- Build tree with 8 leaves [1, 2, 3, 4, 5, 6, 7, 8]
-- Layer 2: [3, 7, 11, 15]
-- Layer 1: [10, 26]
-- Layer 0: [36]
#eval getRoot ℕ (buildMerkleTree_with_hash ℕ 3 ⟨[1, 2, 3, 4, 5, 6, 7, 8], rfl⟩ testHashSum)
-- Expected: 36

/-! ### Tests for generateProof -/

-- For a tree with 4 leaves, generate proof for each index
-- Tree structure:
--        root (10)
--       /    \
--     (3)    (7)
--    /  \   /  \
--   1    2 3    4

-- Proof for index 0 (leaf=1): need sibling 2, then sibling 7 -> [2, 7]
#eval (generateProof ℕ 0 (buildMerkleTree_with_hash ℕ 2 ⟨[1, 2, 3, 4], rfl⟩ testHashSum)).toList
-- Expected: [2, 7]

-- Proof for index 1 (leaf=2): need sibling 1, then sibling 7 -> [1, 7]
#eval (generateProof ℕ 1 (buildMerkleTree_with_hash ℕ 2 ⟨[1, 2, 3, 4], rfl⟩ testHashSum)).toList
-- Expected: [1, 7]

-- Proof for index 2 (leaf=3): need sibling 4, then sibling 3 -> [4, 3]
#eval (generateProof ℕ 2 (buildMerkleTree_with_hash ℕ 2 ⟨[1, 2, 3, 4], rfl⟩ testHashSum)).toList
-- Expected: [4, 3]

-- Proof for index 3 (leaf=4): need sibling 3, then sibling 3 -> [3, 3]
#eval (generateProof ℕ 3 (buildMerkleTree_with_hash ℕ 2 ⟨[1, 2, 3, 4], rfl⟩ testHashSum)).toList
-- Expected: [3, 3]

/-! ### Tests for getPutativeRoot_with_hash -/

-- Verify that getPutativeRoot_with_hash with correct proof gives the root
-- For index 0 with leaf 1 and proof [2, 7]:
-- Step 1: hash(1, 2) = 3 (left child, so leaf first)
-- Step 2: hash(3, 7) = 10 (left child again)
#eval getPutativeRoot_with_hash (α := ℕ) 0 1 ⟨[2, 7], rfl⟩ testHashSum
-- Expected: 10

-- For index 1 with leaf 2 and proof [1, 7]:
-- Step 1: hash(1, 2) = 3 (right child, so proof.head first)
-- Step 2: hash(3, 7) = 10 (left child)
#eval getPutativeRoot_with_hash (α := ℕ) 1 2 ⟨[1, 7], rfl⟩ testHashSum
-- Expected: 10

-- For index 3 with leaf 4 and proof [3, 3]:
-- Step 1: hash(3, 4) = 7 (right child)
-- Step 2: hash(3, 7) = 10 (right child)
#eval getPutativeRoot_with_hash (α := ℕ) 3 4 ⟨[3, 3], rfl⟩ testHashSum
-- Expected: 10

/-! ### End-to-end test: functional_completeness verification -/

-- Test that for all indices, generating a proof and computing putative root gives the actual root
def testFunctionalCompleteness (n : ℕ) (leaves : List.Vector ℕ (2 ^ n)) : Bool :=
  let cache := buildMerkleTree_with_hash ℕ n leaves testHashSum
  let root := getRoot ℕ cache
  -- Check all indices
  (List.finRange (2 ^ n)).all fun i =>
    let proof := generateProof ℕ i cache
    let putativeRoot := getPutativeRoot_with_hash (α := ℕ) i leaves[i] proof testHashSum
    putativeRoot == root

#eval testFunctionalCompleteness 1 ⟨[1, 2], rfl⟩              -- Expected: true
#eval testFunctionalCompleteness 2 ⟨[1, 2, 3, 4], rfl⟩        -- Expected: true
#eval testFunctionalCompleteness 3 ⟨[1, 2, 3, 4, 5, 6, 7, 8], rfl⟩  -- Expected: true

-- Test with different values
#eval testFunctionalCompleteness 2 ⟨[10, 20, 30, 40], rfl⟩    -- Expected: true
#eval testFunctionalCompleteness 2 ⟨[100, 200, 300, 400], rfl⟩ -- Expected: true

end Test

end MerkleTree
