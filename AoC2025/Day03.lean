import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-- A decimal digit. We will only ever use 1–9, but `Fin 10` is convenient. -/
abbrev Digit := Fin 10

/-- A bank of batteries: a line of digits, with at least two batteries. -/
structure Bank where
  digits : List Digit
  hlen   : 2 ≤ digits.length

/-- The whole input: many banks stacked. -/
abbrev Input := List Bank

/-- A choice of two batteries in a given bank (by index), with i < j. -/
structure Choice (b : Bank) where
  i   : Fin b.digits.length
  j   : Fin b.digits.length
  hij : i < j

abbrev Joltage := Nat

/-- Combine two digits into a two-digit number. -/
def pairValue (a b : Digit) : Joltage :=
  10 * (a : Nat) + (b : Nat)

/-- Value of a particular choice of two batteries in a bank. -/
def choiceValue {b : Bank} (c : Choice b) : Joltage :=
  pairValue (b.digits.get c.i) (b.digits.get c.j)

structure Options (b : Bank) t where
  options  : List t
  nonEmpty : options ≠ []

-- /-- All possible (i, j) with i < j in a given bank, as a list. -/
-- def allChoices (b : Bank) : Options b (Choice b) := sorry  -- to be defined later

-- /-- Spec: The set of all possible output joltages from this bank. -/
-- def bankValues (b : Bank) : Options b Joltage := sorry
--   -- (allChoices b).map (choiceValue b)

-- /-- Spec: maximum joltage for a bank (there is at least one choice). -/
-- def bankMax (b : Bank) : Joltage :=
--   match bankValues b with
--   | Options.mk options nonEmpty =>
--     match options with
--     | []        => by simp at (nonEmpty : [] ≠ [])
--     | (v :: vs) => vs.foldl Nat.max v

-- /-- Final answer: total output joltage over all banks. -/
-- def totalOutput (input : Input) : Joltage :=
--   (input.map bankMax).sum

-- /-- Lexicographic characterization of two-digit numbers built with `pairValue`. -/
-- theorem pairValue_lt_iff
--     {a b c d : Digit} :
--     pairValue a b < pairValue c d
--       ↔ (a < c) ∨ (a = c ∧ b < d) := by
--   -- proof later
--   sorry

-- theorem pairValue_le_iff
--     {a b c d : Digit} :
--     pairValue a b ≤ pairValue c d
--       ↔ (a < c) ∨ (a = c ∧ b ≤ d) := by
--   sorry

-- theorem pairValue_mono_left {a b c : Digit} (h : a ≤ b) :
--     pairValue a c ≤ pairValue b c := by
--   sorry

-- theorem pairValue_mono_right {a b c : Digit} (h : b ≤ c) :
--     pairValue a b ≤ pairValue a c := by
--   sorry

-- /-- Any valid bank has at least one valid choice (there's at least one i < j). -/
-- theorem exists_choice (b : Bank) : ∃ c : Choice b, True := by
--   sorry

-- /-- Every valid choice appears in `allChoices`. -/
-- theorem mem_allChoices_of_choice
--     (b : Bank) (c : Choice b) :
--     c ∈ (allChoices b).options := by
--   sorry

-- /-- Every element in `allChoices` is a valid choice. -/
-- theorem allChoices_mem_isChoice
--     (b : Bank) (c : Choice b) :
--     c ∈ (allChoices b).options → True := by
--   sorry

-- /-- `bankValues` is exactly the image of `choiceValue` over `allChoices`. -/
-- theorem mem_bankValues_iff
--     (b : Bank) (v : Nat) :
--     v ∈ (bankValues b).options
--       ↔ ∃ c : Choice b, choiceValue b c = v := by
--   unfold bankValues
--   -- standard `List.mem_map` reasoning
--   sorry

-- /-- `bankMax` is an upper bound on every choice's value. -/
-- theorem choiceValue_le_bankMax
--     (b : Bank) (c : Choice b) :
--     choiceValue b c ≤ bankMax b := by
--   sorry

-- /-- `bankMax` is actually attained by some choice. -/
-- theorem exists_choice_with_value_bankMax (b : Bank) :
--     ∃ c : Choice b, choiceValue b c = bankMax b := by
--   sorry

/-- Argmax on a nonempty list of digits, returning a `Fin` index. -/
def argmax (xs : List Digit) (nonEmpty : 1 ≤ xs.length) : Fin xs.length :=
  -- From `1 ≤ xs.length` get `0 < xs.length`
  have hlen : 0 < xs.length := by
    simpa [Nat.succ_le_iff] using nonEmpty
  -- Initial best index is 0 (safe because `xs` is nonempty)
  let init : Fin xs.length := ⟨0, hlen⟩
  -- Step function: given current best and a candidate index, update the best
  let step (best i : Fin xs.length) : Fin xs.length :=
    if xs.get best < xs.get i then i else best
  -- Fold over all indices `0 .. xs.length-1`
  (List.finRange xs.length).foldl step init

/-- Index of the maximum digit among positions 0 .. len-2. -/
def idxMaxInit (b : Bank) : Fin (b.digits.length - 1) := by
  match b with
  | Bank.mk digits hlen => match h : digits with
    | []      => simp at (hlen : 2 ≤ 0)
    | [_]     => simp at (hlen : 2 ≤ 1)
    | x :: xs =>
      -- take the prefix without the last element and argmax there
      have idx := argmax
                  digits.dropLast
                  (by rw [h,List.length_dropLast_cons]
                      simp at hlen
                      assumption)
      rw [h,List.length_dropLast] at idx
      exact idx

/-- Index of the maximum digit in the suffix starting strictly after `i`. -/
def idxMaxAfter (b : Bank) (i : Fin (b.digits.length - 1)) : Fin b.digits.length := by
  let xs := b.digits
  let start : Nat := i.1 + 1
  have hstart : start < xs.length := by
    -- xs.length ≥ 2 from the Bank invariant, and i.1 < xs.length - 1 by Fin
    -- omega solves: i < len-1  ⇒ i+1 < len
    simp [xs]
    omega
  let suffix := xs.drop start
  have hsuf : 1 ≤ suffix.length := by
    simp [suffix, List.length_drop]
    omega
  let k : Fin suffix.length := argmax suffix hsuf
  let jnat : Nat := start + k.1
  have hj : jnat < xs.length := by
    -- k.1 < suffix.length = xs.length - start
    have hk : k.1 < xs.length - start := by
      simpa [suffix, List.length_drop] using k.isLt
    -- now: start + k.1 < xs.length
    omega
  exact ⟨jnat, by simpa [xs]⟩

theorem bank_index_sub_add_cancel
  (b : Bank) :
  (b.digits.length - 1 + 1 = b.digits.length)
:= by
  have hlen := b.hlen
  have h1 : 1 ≤ b.digits.length := by omega
  rw [Nat.sub_add_cancel h1]

theorem idxMaxAfter_correct
  (b : Bank)
  (i : Fin (b.digits.length - 1)) :
  ---------------------------------
  Fin.castLE
    (by rw [bank_index_sub_add_cancel b])
    (Fin.castSucc i) < idxMaxAfter b i:=
by
  sorry

/-- Algorithmic version: max two-digit value from a bank. -/
def bankMaxAlg (b : Bank) : Nat :=
  let xs  := b.digits
  let i   := idxMaxInit b
  let j   := idxMaxAfter b i
  let k   := Fin.castSucc i
  -- dbg_trace s!"Bank i:{i} j:{j} k:{k}"
  have ct  := b.hlen
  have i' : Fin b.digits.length := by
    have k := Fin.castSucc i
    have h1 : 1 ≤ b.digits.length := by omega
    rw [Nat.sub_add_cancel h1] at k
    exact k
  -- dbg_trace s!"Bank i:{i} i':{i'} j:{j} xs[{i'}]{(xs.get i')} xs[{j}]{(xs.get j)}"
  let c : Choice b := Choice.mk i' j sorry
  choiceValue c

-- /-- The algorithm agrees with the spec. -/
-- theorem bankMaxAlg_correct (b : Bank) :
--     bankMaxAlg b = bankMax b := by
--   sorry

def totalOutputAlg (input : Input) : Nat :=
  (input.map bankMaxAlg).sum

-- theorem totalOutputAlg_correct (input : Input) :
--     totalOutputAlg input = totalOutput input
-- := by
--   sorry

def parseDigit (c : Char) : IO Digit := do
  let n := c.toNat - '0'.toNat
  if 1 ≤ n
    then
      if h2 : n < 10
        then .ok ⟨n, h2⟩
        else .error s!"Not a digit {c}"
    else .error s!"Not a digit {c}"

def parseBank (s : String) : IO Bank := do
  -- IO.println s!"parseBank {s}"
  let cs := s.toList
  let ds <- cs.mapM parseDigit
  -- IO.println s!"Digits {ds}"
  if h : 2 <= ds.length
    then .ok (Bank.mk ds h)
    else .error s!"Minimum 2 batteries required.{ds}"

def parseInput (s : String) : IO (List Bank) := do
  let lines := s.splitToList (· = '\n')
  let nonempty := lines.filter (fun l => !l.trim.isEmpty)
  nonempty.mapM parseBank

def solvePart0 (bs : List Bank) : List Nat :=
  (bs.map bankMaxAlg)

def solvePart1 (bs : List Bank) : Joltage :=
  (bs.map bankMaxAlg).sum

def day03main1 : IO Unit := do
  let stdin <- IO.getStdin
  let input <- stdin.readToEnd
  -- IO.println input
  let banks <- parseInput input
  let ans := solvePart1 banks
  IO.println ans
