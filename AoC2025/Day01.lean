-- import Std.Data.List.Lemmas
-- open Std

-- import Mathlib
import Batteries.Data.List.Lemmas
import Mathlib.Tactic.Lemma
import Mathlib

inductive Dir
  | L
  | R

structure Rotation where
  dir   : Dir
  steps : Nat

/- Dial positions are number 0..99 (this invariant will be enforced) -/
abbrev Pos := Nat

def stepSpec (p : Pos) (r : Rotation) : Pos :=
  let n := r.steps
  match r.dir with
  | .R => (p + n) % 100
  | .L => (p + 100 - (n % 100)) % 100

theorem stepSpec_range
  (p : Pos)
  (r : Rotation) :
  ----------------
  stepSpec p r < 100
:= by
  unfold stepSpec
  cases r.dir with
  | R =>
    simp
    have h : 0 < 100 := by decide
    exact Nat.mod_lt _ h
  | L =>
    simp
    have h : 0 < 100 := by decide
    exact Nat.mod_lt _ h

theorem stepSpec_right
  (p : Pos)
  (n : Nat) :
  -----------
  stepSpec p ⟨Dir.R, n⟩ = (p + n) % 100
:= by
  unfold stepSpec
  simp

theorem stepSpec_left
  (p : Pos)
  (n : Nat) :
  -----------
  stepSpec p ⟨Dir.L, n⟩  = (p + 100 - (n % 100)) % 100
:= by
  unfold stepSpec
  simp

def runSpec : List Rotation -> Pos -> List Pos
  | []     , _ => []
  | r :: rs, p =>
      let p' := stepSpec p r
      p' :: runSpec rs p'

/-- Every position in the run stays in 0..99. -/
theorem runSpec_range
  (rs : List Rotation)
  (p  : Pos) :
  ------------
  ∀ q ∈ runSpec rs p, q < 100
:= by
  induction rs generalizing p with
  | nil =>
    intros q h
    simp [runSpec] at h
  | cons r rs ih =>
    intros q h
    simp [runSpec] at h
    cases h with
    | inl hq =>
      subst hq
      exact stepSpec_range p r
    | inr hmem =>
      exact ih (stepSpec p r) q hmem

def passwordSpec (pos : Pos) (rs : List Rotation) : Nat :=
  (runSpec rs pos).count 0

/-- The sample list from the problem statement. -/
def exampleRotations : List Rotation :=
  [ ⟨Dir.L, 68⟩,
    ⟨Dir.L, 30⟩,
    ⟨Dir.R, 48⟩,
    ⟨Dir.L, 5⟩,
    ⟨Dir.R, 60⟩,
    ⟨Dir.L, 55⟩,
    ⟨Dir.L, 1⟩,
    ⟨Dir.L, 99⟩,
    ⟨Dir.R, 14⟩,
    ⟨Dir.L, 82⟩ ]

/-- The example in the text: password should be 3. -/
theorem example_password :
  passwordSpec 50 exampleRotations = 3 := by
  -- This can be proved by expanding the run or using a small computation lemma.
  decide

def solve (pos : Pos) (cnt : Nat) (rs : List Rotation) : Nat :=
  Id.run do
    let mut pos : Pos := pos
    let mut cnt : Nat := cnt
    for r in rs do
      pos := stepSpec pos r
      if pos = 0
        then cnt := cnt + 1
    pure cnt

lemma loop_correct
  (rs : List Rotation)
  (pos cnt : Nat) :
  -----------------
  (solve pos cnt rs)
  =
  cnt + (runSpec rs pos).count 0
:= by
  induction rs generalizing pos cnt with
  | nil =>
      unfold solve
      simp [runSpec]
  | cons r rs ih =>
      unfold solve
      simp [runSpec] at ih ⊢
      by_cases h0 : stepSpec pos r = 0
      · simp [h0] at ⊢
        have h := ih 0 (cnt + 1)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simp [h0] at ⊢
        have h := ih (stepSpec pos r) cnt
        simpa using h

/--
Main correctness statement:

For every input list of rotations, our implemented solver `solve`
returns exactly the mathematically specified password.
-/
theorem solve_correct
  (pos : Pos)
  (rs : List Rotation) :
  solve pos 0 rs = passwordSpec pos rs :=
by
  unfold passwordSpec
  simp [loop_correct]
