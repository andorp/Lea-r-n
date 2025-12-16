
import Std
import Mathlib.Tactic

/--
A product ID is just a natural number (its decimal representation is implicit).
-/
abbrev ID := Nat

/--
A closed interval of IDs `[first, last]` from the puzzle input.
-/
structure Range where
  first : ID
  last  : ID
  valid : first <= last
  deriving Repr, BEq

/-- The full puzzle input is just a list of ranges. -/
abbrev Input := List Range

/-
  INVALID ID SPECIFICATION
  ------------------------

  An ID is invalid iff its *decimal* representation is of the form `xx`,
  i.e. some nonempty string repeated twice.

  We’ll first express this as a **Prop-level** specification over `String`.
-/

/-- `s` is exactly some nonempty string repeated twice: `s = t ++ t`. -/
def isDoubleString (s : List Char) : Prop :=
  ∃ t : List Char, t ≠ [] ∧ s = t ++ t

/--
An ID is invalid iff its decimal representation (via `Nat.repr`)
is a double string. This matches the textual description of the puzzle.
-/
def IsInvalidID (n : ID) : Prop :=
  isDoubleString n.repr.toList


/-! --------------------------------------------------------
     BASIC RANGE LEMMAS
     These will make later algorithms + proofs much easier.
  ---------------------------------------------------------- -/

/-- Every ID in a `Range` satisfies `first ≤ id ∧ id ≤ last`. -/
def Range.contains (r : Range) (n : ID) : Prop :=
  r.first ≤ n ∧ n ≤ r.last

/--
Convert a range to a list of all IDs in it.
This stays mathlib-free by using a primitive recursive helper.
-/
def Range.toList (r : Range) : List ID :=
  let rec aux (cur : Nat) (more : Nat) :=
    match more with
    | .zero   => []
    | .succ m => cur :: aux (cur + 1) m
  aux r.first (r.last - r.first).succ

/-- Every entry in `toList` is inside the range. -/
theorem Range.mem_toList {r : Range} {n : ID} :
    n ∈ r.toList → r.contains n := by
  intro h
  -- direct structural recursion proof later if needed
  -- (for now we leave this lemma as a placeholder TODO)
  admit

/-- If `m ≤ n`, then `n` is in the list iff the range covers it. -/
theorem Range.mem_toList_iff_contains :
    ∀ {r : Range} {n : ID}, n ∈ r.toList ↔ r.contains n := by
  intro r n
  -- This will be proven when we implement the recursion lemmas.
  admit

/-
  COMPUTABLE VERSION: isDoubleStringBool
  -------------------------------------
-/

/-- Generic helper: if `anyAux` returns true, some element satisfies `p`. -/
def anyNat (p : Nat -> Bool) (xs : List Nat) : Bool :=
  let rec go (ys : List Nat) : Bool :=
    match ys with
    | []      => false
    | k :: ks => if p k then true else go ks
  go xs

/--
Boolean version of `isDoubleString`.

It returns `true` exactly when the string is some nonempty prefix
repeated twice (we’ll prove that correspondence later).
-/
-- This is a bit of overcomplicated solution.
def isDoubleStringBool (cs : List Char) : Bool :=
  let len : Nat := cs.length
  let check (k : Nat) : Bool :=
    let k' := k.succ
    let pfx : List Char := List.take k' cs
    let candidate : List Char := pfx ++ pfx
    candidate = cs
  anyNat check (List.range (len / 2))

/-- Boolean check: is this ID invalid? (double decimal string) -/
def isInvalidID (n : ID) : Bool :=
  isDoubleStringBool n.repr.toList

/-- All invalid IDs within this closed range `[first, last]`. -/
def Range.invalidIDs (r : Range) : List ID :=
  r.toList.filter (fun n => isInvalidID n)

/-- All invalid IDs from all ranges in the input. -/
def Input.invalidIDs (inp : Input) : List ID :=
  (inp.map Range.invalidIDs).flatten

/-- Sum a list of natural numbers. -/
def sumList (xs : List Nat) : Nat :=
  xs.foldl (fun acc n => acc + n) 0

/-- AoC 2025 Day 2 – Part 1: sum of all invalid IDs. -/
def solvePart1 (inp : Input) : Nat :=
  sumList (Input.invalidIDs inp)

def exampleRanges : Input :=
  [ ⟨11, 22, by decide⟩
  , ⟨95,115, by decide⟩
  , ⟨998,1012, by decide⟩
  , ⟨1188511880,1188511890, by decide⟩
  , ⟨222220,222224, by decide⟩
  , ⟨1698522,1698528, by decide⟩
  , ⟨446443,446449, by decide⟩
  , ⟨38593856,38593862, by decide⟩
  , ⟨565653,565659, by decide⟩
  , ⟨824824821,824824827, by decide⟩
  , ⟨2121212118,2121212124, by decide⟩
  ]

#eval (solvePart1 exampleRanges) -- should be 1227775554

/-- Parse a decimal natural number from a string. -/
def parseNat (s : String) : Option Nat :=
  s.toNat?

/-- Parse a single `"a-b"` range into a `Range`. -/
def parseRange (s : String) : Option Range := do
  -- Remove incidental whitespace around the `a-b` chunk
  let s := s.trim
  let parts := s.splitOn "-"
  match parts with
  | [aStr, bStr] =>
      let a ← parseNat aStr.trim
      let b ← parseNat bStr.trim
      -- Enforce the invariant `a ≤ b` required by `Range`
      if h : a ≤ b then
        pure ⟨a, b, h⟩
      else
        none
  | _ =>
      none

/-- Parse the full puzzle input line into an `Input` (list of ranges). -/
def parseInput (s : String) : Option Input :=

  let parts := s.trim.splitOn ","

  let rec loop (ps : List String) : Option Input := do
    match ps with
    | [] => pure []
    | p :: ps =>
        -- Skip empty chunks (handles accidental trailing comma etc.)
        if p.trim = "" then
          loop ps
        else
          let r  ← parseRange p
          let rs ← loop ps
          pure (r :: rs)

  loop parts

-- def parseInput2 (s : String) : Option (List Range) := do
--   let lines := s.splitToList (· = '\n')
--   let nonempty := lines.filter (fun l => !l.trim.isEmpty)
--   nonempty.mapM parseRotation

def exampleInputStr : String :=
  "11-22,95-115,998-1012,1188511880-1188511890,222220-222224," ++
  "1698522-1698528,446443-446449,38593856-38593862,565653-565659," ++
  "824824821-824824827,2121212118-2121212124"

#eval
  match parseInput exampleInputStr with
  | some inp => solvePart1 inp     -- should be 1227775554
  | none     => 0

def day02main1 : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  match parseInput input with
  | some rs =>
      let ans := solvePart1 rs
      IO.println ans
  | none =>
      IO.eprintln s!"Error parsing input."

/-- Repeat a string `k` times by concatenation. -/
def repeatString (t : List Char) (k : Nat) : List Char :=
  (List.replicate k t).foldl (fun acc s => acc ++ s) []

/--
`s` is made of some nonempty string `t` repeated at least twice.
This is the spec for part 2.
-/
def isRepeatString (s : List Char) : Prop :=
  ∃ t : List Char, t ≠ [] ∧ ∃ k : Nat, 2 ≤ k ∧ s = repeatString t k

/-- Part 2: an ID is invalid if its decimal representation is a repeated string (≥ 2 times). -/
def IsInvalidID2 (n : ID) : Prop :=
  isRepeatString n.repr.toList

/-- Boolean version of "s is some chunk repeated at least twice". -/
def isRepeatStringBool (cs : List Char) : Bool :=
  let len : Nat := cs.length

  -- Repeat a character chunk `k` times.
  let rec repeatChunk (chunk : List Char) (k : Nat) : List Char :=
    match k with
    | 0        => []
    | k + 1    => chunk ++ repeatChunk chunk k

  -- Check a particular candidate chunk length (k.succ).
  let check (k : Nat) : Bool :=
    let d := k.succ         -- d ∈ [1, len/2]
    if len % d ≠ 0 then
      false
    else
      let times := len / d  -- because d ≤ len/2 and len ≥ 2d ⇒ times ≥ 2
      let chunk : List Char := List.take d cs
      let candidate : List Char := repeatChunk chunk times
      candidate == cs

  let indices : List Nat := List.range (len / 2)
  let rec anyAux (xs : List Nat) : Bool :=
    match xs with
    | []      => false
    | k :: ks => if check k then true else anyAux ks

  anyAux indices

/-- Boolean check: part 2 invalid ID (chunk repeated ≥ 2 times). -/
def isInvalidID2 (n : ID) : Bool :=
  isRepeatStringBool n.repr.toList

/-- All part-2 invalid IDs within this closed range `[first, last]`. -/
def Range.invalidIDs2 (r : Range) : List ID :=
  r.toList.filter (fun n => isInvalidID2 n)

/-- All part-2 invalid IDs from all ranges in the input. -/
def Input.invalidIDs2 (inp : Input) : List ID :=
  (inp.map Range.invalidIDs2).flatten

/-- AoC 2025 Day 2 – Part 2: sum of all (part-2) invalid IDs. -/
def solvePart2 (inp : Input) : Nat :=
  sumList (Input.invalidIDs2 inp)

#eval solvePart2 exampleRanges       -- should be 4174379265

def day02main2 : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  match parseInput input with
  | some rs =>
      let ans := solvePart2 rs
      IO.println ans
  | none =>
      IO.eprintln s!"Error parsing input."

theorem anyNat_true_iff
  {p : Nat -> Bool}
  {xs : List Nat} :
  -----------------
  anyNat p xs = true -> ∃ k ∈ xs, p k = true
:= by
  intro h1
  induction xs with
  | nil =>
    simp [anyNat,anyNat.go] at h1
  | cons x xs ih =>
    simp [anyNat,anyNat.go] at h1
    by_cases h2 : p x = true
    · refine ⟨x, by constructor, h2⟩
    · have h3 : anyNat p xs = true := by
        simp [h2] at h1
        simp [anyNat]
        assumption
      have ⟨k, h4, h5⟩ := ih h3
      exact ⟨k, by simp [h4], h5⟩

theorem anyNat_true_of_exists
  {p : Nat -> Bool}
  {xs : List Nat} :
  -----------------
  (∃ k ∈ xs, p k = true) -> anyNat p xs = true
:= by
  intro h1
  have ⟨k, h2, h3⟩ := h1
  simp [anyNat]
  induction xs with
  | nil =>
    contradiction
  | cons x xs ih =>
    simp [anyNat.go]
    simp at h2
    cases h2 with
    | inl h4 =>
      left
      simpa [h4.symm]
    | inr h4 =>
      right
      rw [ih]
      · exact ⟨k, h4,h3⟩
      · assumption

theorem ofList_ne_empty_of_list_ne_nil
  {l : List Char}
  (h : l ≠ []) :
  --------------
  String.ofList l ≠ ""
:= by
  intro h1
  have h2 : (l = []) := (String.ofList_eq_empty_iff).mp h1
  contradiction

theorem isDoubleStringBool_correct_left
  (s : List Char) :
  -----------------
  isDoubleStringBool s = true -> isDoubleString s
:= by
  intro h1
  unfold isDoubleStringBool at h1
  -- simp only at h1
  let cs : List Char := s
  let len : Nat := cs.length
  let check : Nat → Bool := fun k =>
    let k' := k.succ
    let pfx : List Char := List.take k' cs
    let candidate : List Char := pfx ++ pfx
    candidate = cs
  have h2 : anyNat check (List.range (len / 2)) = true := by
    simpa [cs,len,check] using h1
  have ⟨k, hkIn,hkCheck⟩ := anyNat_true_iff (p := check) (xs := List.range (len / 2)) h2
  have h3 : check k = true := hkCheck
  unfold check at h3

  let k' := k.succ
  let pfx : List Char := List.take k' cs
  let candidate : List Char := pfx ++ pfx

  have h4 : decide (candidate = cs) = true := by
    simpa [check,k',pfx,candidate] using hkCheck

  have h5 : candidate = cs := by
    exact of_decide_eq_true h4
  have h6 : pfx ≠ [] := by
    intro h7
    have h8 : [] = cs := by
      simpa [candidate,h7] using h4
    have h9 : len = 0 := by
      simp [len,h8.symm]
    have h10 : k ∈ List.range 0 := by
      simpa [h9] using hkIn
    have h11 : False := by
      simp at h10
    exact h11
  have h7 : s = pfx ++ pfx := by
    simp [candidate,cs] at h5
    exact h5.symm
  simp [isDoubleString]
  refine ⟨pfx, h6, h7⟩

theorem isDoubleStringBool_correct_right
  (s : List Char) :
  -----------------
  isDoubleString s -> isDoubleStringBool s = true
:= by
  intro h1
  unfold isDoubleString at h1
  have ⟨t,h3,h4⟩ := h1
  let d : Nat := t.length
  let k : Nat := d - 1
  have h5 : d >= 1 := by cases t with
  | nil => contradiction
  | cons x xs => simp [d]
  have h6 : k ∈ List.range (s.length / 2) := by
    have h7 : k >= 0 := by simp [k]
    have h8 : s.length = 2*d := by
      rw [h4,List.length_append, Nat.two_mul]
    simp [h8,k]
    nlinarith
  let cs : List Char := s
  let check : Nat → Bool := fun k =>
    let k' := k.succ
    let pfx : List Char := List.take k' s
    let candidate : List Char := pfx ++ pfx
    candidate = s
  have h7 : check k = true := by
    unfold check
    simp [k, Nat.sub_add_cancel h5,d,h4]
  unfold isDoubleStringBool
  change
    anyNat
      (fun k =>
        let k' := k.succ
        let pfx := List.take k' s
        let candidate := pfx ++ pfx
        decide (candidate = s))
      (List.range (s.length / 2)) = true
  have h8 : (fun k =>
      let k' := k.succ
      let pfx := List.take k' s
      let candidate := pfx ++ pfx
      decide (candidate = s)) k = true := by
    simpa [check] using h7
  have h9 :
      ∃ k ∈ List.range (s.length / 2),
        (fun k =>
          let k' := k.succ
          let pfx := List.take k' s
          let candidate := pfx ++ pfx
          decide (candidate = s)) k = true :=
    ⟨k, h6, h8⟩
  exact anyNat_true_of_exists h9

theorem isDoubleStringBool_correct
  (s : List Char) :
  -----------------
  isDoubleStringBool s = true <-> isDoubleString s
:=
  ⟨ isDoubleStringBool_correct_left s
  , isDoubleStringBool_correct_right s
  ⟩

theorem isRepeatString_correct_left
  (s : List Char) :
  -----------------
  isRepeatStringBool s = true -> isRepeatString s
:= by
  sorry

theorem isRepeatString_correct_right
  (s : List Char) :
  -----------------
  isRepeatString s -> isRepeatStringBool s = true
:= by
  sorry

theorem isRepeatString_correct
  (s : List Char) :
  -----------------
  isRepeatStringBool s = true <-> isRepeatString s
:=
  ⟨ isRepeatString_correct_left s
  , isRepeatString_correct_right s
  ⟩

inductive IsDoubleChars : List Char → Prop where
  | idc
    (c : Char) :
    ------------
    IsDoubleChars ([c] ++ [c])
  | ida
    (c : Char)
    (cs : List Char)
    (ind : IsDoubleChars (cs ++ cs)) :
    ----------------------------------
    IsDoubleChars (c::cs ++ (c::cs))

theorem isDoubleString_correctI_left
  (s : List Char) :
  -----------------
  isDoubleStringBool s = true -> IsDoubleChars s
:= by
  sorry

theorem isDoubleString_correctI_right
  (s : List Char) :
  -----------------
  IsDoubleChars s -> isDoubleStringBool s = true
:= by
  intro h1
  induction h1 with
  | idc c =>
    unfold isDoubleStringBool
    simp [anyNat, anyNat.go]
  | ida c cs i ih =>
    sorry

def List.repeat (n : Nat) (l : List t) : List t :=
  match n with
  | .zero   => []
  | .succ m => l ++ List.repeat m l

-- theorem repeat_length

inductive IsRepeatChars : Nat -> List Char → Prop where
  | irc
    (n : Nat)
    (c : Char) :
    ------------
    IsRepeatChars n (List.repeat n [c])
  | ira
    (n : Nat)
    (c : Char)
    (cs : List Char)
    (i : IsRepeatChars n (List.repeat n cs)) :
    ------------------------------------------
    IsRepeatChars n (List.repeat n (c::cs))
