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
  hij : i.val < j.val

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

/-- All possible (i, j) with i < j in a given bank, as a list. -/
def allChoices (b : Bank) : Options b (Choice b) := sorry  -- to be defined later

/-- Spec: The set of all possible output joltages from this bank. -/
def bankValues (b : Bank) : Options b Joltage :=
  match allChoices b with
  | Options.mk os ne =>
    Options.mk
      (os.map choiceValue)
      (by simpa [List.map_eq_nil_iff])

/-- Spec: maximum joltage for a bank (there is at least one choice). -/
def bankMax (b : Bank) : Joltage :=
  match bankValues b with
  | Options.mk options nonEmpty =>
    match options with
    | []        => by simp at (nonEmpty : [] ≠ [])
    | (v :: vs) => vs.foldl Nat.max v

/-- Final answer: total output joltage over all banks. -/
def totalOutput (input : Input) : Joltage :=
  (input.map bankMax).sum

/-- Lexicographic characterization of two-digit numbers built with `pairValue`. -/
theorem pairValue_lt_iff
  {a b c d : Digit} :
  -------------------
  pairValue a b < pairValue c d
  ↔ (a < c) ∨ (a = c ∧ b < d)
:= by
  constructor <;> intros h1
  · have h2 := Nat.lt_trichotomy a c
    cases h2 with
    | inl h3 => left; assumption
    | inr h3 => cases h3 with
      | inl h4 =>
        right
        simp [pairValue,h4] at h1
        refine And.intro (Fin.ext h4) h1
      | inr h4 =>
        exfalso
        simp [pairValue] at h1
        -- 10*c + d < 10*(c+1)  (because d < 10)
        have hcd_lt : 10 * (c : Nat) + (d : Nat) < 10 * ((c : Nat) + 1) := by
          -- uses d.isLt : (d:Nat) < 10
          omega
        -- c+1 ≤ a
        have hca : (c : Nat) + 1 ≤ (a : Nat) := Nat.succ_le_of_lt h4
        -- so 10*(c+1) ≤ 10*a
        have hmul : 10 * ((c : Nat) + 1) ≤ 10 * (a : Nat) :=
          Nat.mul_le_mul_left 10 hca
        -- hence 10*c + d < 10*a
        have hcd_lt_10a : 10 * (c : Nat) + (d : Nat) < 10 * (a : Nat) :=
          lt_of_lt_of_le hcd_lt hmul
        -- and 10*a ≤ 10*a + b
        have h10a_le : 10 * (a : Nat) ≤ 10 * (a : Nat) + (b : Nat) :=
          Nat.le_add_right _ _
        have h2 : 10 * (c : Nat) + (d : Nat) < 10 * (a : Nat) + (b : Nat) :=
          lt_of_lt_of_le hcd_lt_10a h10a_le
        exact lt_asymm h1 h2
  · cases h1 with
    | inl h2 =>
      simp [pairValue]
      have hb : (b : Nat) < 10 := b.isLt
      have : 10 * (a : Nat) + (b : Nat) < 10 * (c : Nat) := by
        -- since a < c, we have a+1 ≤ c, hence 10*(a+1) ≤ 10*c
        have hac : (a : Nat) + 1 ≤ (c : Nat) := Nat.succ_le_of_lt (show (a : Nat) < (c : Nat) from h2)
        have hmul : 10 * ((a : Nat) + 1) ≤ 10 * (c : Nat) := Nat.mul_le_mul_left 10 hac
        -- and b < 10 implies 10*a + b < 10*a + 10 = 10*(a+1)
        have hstep : 10 * (a : Nat) + (b : Nat) < 10 * ((a : Nat) + 1) := by
          omega
        exact lt_of_lt_of_le hstep hmul
      -- now add d (nonnegative) to the right: 10*c < 10*c + d
      have hright : 10 * (c : Nat) ≤ 10 * (c : Nat) + (d : Nat) := Nat.le_add_right _ _
      exact lt_of_lt_of_le this hright
    | inr h2 =>
      simp [pairValue]
      have ⟨h3,h4⟩ := h2
      simp [h3] <;> assumption

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

theorem idxMaxAfter_is_after_index
  (b : Bank)
  (i : Fin (b.digits.length - 1)) :
  ---------------------------------
  i.val < (idxMaxAfter b i).val
:= by
  simpa [idxMaxAfter, bank_index_sub_add_cancel,Fin.lt_def]
  using (by omega)

/-- Algorithmic version: max two-digit value from a bank. -/
def bankMaxAlg (b : Bank) : Nat :=
  let xs  := b.digits
  let i   := idxMaxInit b
  let j   := idxMaxAfter b i
  -- define i' exactly as the “i+1 in length len” cast
  let i' : Fin b.digits.length :=
    Fin.castLE (by rw [bank_index_sub_add_cancel b]) (Fin.castSucc i)
  have hij : i'.val < j.val := by
    -- `idxMaxAfter_is_after_index` already proves `i' < j` (as Fin),
    -- and `Fin.lt` is definitionaly `.val < .val`, so `simpa` will turn it into `.val < .val`.
    have ha := idxMaxAfter_is_after_index b i
    -- rewrite `j` and `i'` and convert `<` on Fin to `.val < .val`
    simpa [i', j, Fin.lt_def] using ha
  let c : Choice b := Choice.mk i' j hij
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

structure BankK (k : Nat) where
  digits : List Digit
  hlen   : k ≤ digits.length

abbrev InputK (k : Nat) := List (BankK k)

/- -
Pick a lexicographically maximum subsequence of length `k` from `xs`
(order preserved). Requires `k ≤ xs.length`.
- -/
def pickMaxSubseq (xs : List Digit) (k : Nat) (hk : k ≤ xs.length) : List Digit :=
  match k with
  | 0 => []
  | k+1 =>
    -- windowLen = n - (k+1) + 1 = n - k
    let n := xs.length
    let windowLen : Nat := n - k
    have hwin_pos : 1 ≤ (xs.take windowLen).length := by
      have h1 : 1 ≤ windowLen :=
        hk |> Nat.lt_of_succ_le
           |> Nat.sub_pos_of_lt
           |> Nat.succ_le_of_lt
           |> Nat.succ_le_iff.mp
      have hx : 1 ≤ xs.length :=
        Nat.le_trans (Nat.succ_le_succ (Nat.zero_le k)) hk
      simpa [List.length_take] using And.intro h1 hx
    let window := xs.take windowLen
    let i : Fin window.length := argmax window hwin_pos
    let d : Digit := window.get i

    let dropCount : Nat := i.1 + 1
    let rest := xs.drop dropCount
    have hk : k ≤ rest.length := by
      have hk2 : k ≤ n - dropCount := by
        -- Step 1: bound dropCount by windowLen = n - k
        have hdrop_le : dropCount ≤ windowLen := by
          -- i.isLt : i.1 < window.length
          have hi_lt : (i.1 : Nat) < windowLen := by
            -- window.length = min windowLen n, so window.length ≤ windowLen
            have hlen_le : window.length ≤ windowLen := by
              -- window = take windowLen xs
              -- length_take: length (take m xs) = min m (length xs)
              -- so min windowLen n ≤ windowLen
              simpa [window, List.length_take] using Nat.min_le_left windowLen n
            -- i.1 < window.length ≤ windowLen
            exact lt_of_lt_of_le i.isLt hlen_le
          -- convert i.1 < windowLen to i.1+1 ≤ windowLen
          exact Nat.succ_le_iff.mp hi_lt
        -- Step 2: turn dropCount ≤ n-k into k ≤ n-dropCount
        -- (this is just arithmetic)
        -- windowLen is definitional equal to n - k
        -- so rewrite and let omega finish
        -- (omega knows: dropCount ≤ n-k  ->  k ≤ n-dropCount)
        have : dropCount ≤ n - k := by
          simpa [windowLen] using hdrop_le
        omega
      -- rest = xs.drop dropCount
      -- length_drop : rest.length = n - dropCount
      simpa [rest, List.length_drop, n] using hk2
    d :: pickMaxSubseq rest k hk

/-- Convert a digit list to its base-10 numeric value. -/
def digitsValue (ds : List Digit) : Nat :=
  ds.foldl (fun acc d => acc * 10 + (d : Nat)) 0

def bankMaxAlg12 (b : BankK 12) : Nat :=
  digitsValue (pickMaxSubseq b.digits 12 b.hlen)

/-- Total output for Part 2. -/
def solvePart2 (input : InputK 12) : Nat :=
  (input.map bankMaxAlg12).sum

def parseBankK (k : Nat) (s : String) : IO (BankK k) := do
  -- IO.println s!"parseBank {s}"
  let cs := s.toList
  let ds <- cs.mapM parseDigit
  -- IO.println s!"Digits {ds}"
  if h : k <= ds.length
    then .ok (BankK.mk ds h)
    else .error s!"Minimum 2 batteries required.{ds}"

def parseInputK (k : Nat) (s : String) : IO (List (BankK k)) := do
  let lines := s.splitToList (· = '\n')
  let nonempty := lines.filter (fun l => !l.trim.isEmpty)
  nonempty.mapM (parseBankK k)

def day03main2 : IO Unit := do
  let stdin <- IO.getStdin
  let input <- stdin.readToEnd
  -- IO.println input
  let banks <- parseInputK 12 input
  let ans := solvePart2 banks
  IO.println ans

def nextYear : Int := 2026
