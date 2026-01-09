import Std
import Mathlib.Data.List.Monad

open Std

/-- A cell is either empty `.` or a paper roll `@`. -/
inductive Cell where
  | empty : Cell
  | roll  : Cell
  deriving DecidableEq, Repr

/-- A rectangular grid whose height/width live in the type. -/
structure Grid (h w : Nat) where
  rows : Vector (Vector Cell w) h
  deriving Repr

/-- A position in a `Grid h w` is just (row, col) as `Fin`. -/
abbrev Pos (h w : Nat) := Fin h × Fin w

namespace Grid

def get (g : Grid h w) (p : Pos h w) : Cell :=
  (g.rows.get p.1).get p.2

end Grid

namespace Neigh

/-- Turn a Nat into a Fin n if it is < n. -/
def mkFin? (n : Nat) (i : Nat) : Option (Fin n) :=
  if h : i < n then some ⟨i, h⟩ else none

/-- Try to shift a (Fin h, Fin w) by (dr, dc). -/
def shift? {h w : Nat} (p : Pos h w) (dr dc : Int) : Option (Pos h w) :=
  let r : Int := p.1.1
  let c : Int := p.2.1
  let r' := r + dr
  let c' := c + dc
  if _hr0 : 0 ≤ r' then
    if _hc0 : 0 ≤ c' then
      let rn : Nat := Int.toNat r'
      let cn : Nat := Int.toNat c'
      match mkFin? h rn, mkFin? w cn with
      | some rf, some cf => some (rf, cf)
      | _, _ => none
    else none
  else none

/-- The 8 (dr, dc) offsets around a cell, excluding (0,0). -/
def offsets : List (Int × Int) :=
  [(-1,-1), (-1,0), (-1,1),
   ( 0,-1),         ( 0,1),
   ( 1,-1), ( 1,0), ( 1,1)]

/-- List of in-bounds neighbor positions. -/
def neighbors {h w : Nat} (p : Pos h w) : List (Pos h w) :=
  offsets.filterMap (fun (d : Int × Int) => shift? p d.1 d.2)

/-- Count adjacent rolls (@) around a position. -/
def adjacentRolls (g : Grid h w) (p : Pos h w) : Nat :=
  (neighbors p).foldl
    (fun acc q =>
      match Grid.get g q with
      | Cell.roll => acc + 1
      | Cell.empty => acc)
    0

/-- A roll is accessible if it has fewer than 4 roll-neighbors. -/
def accessible0 (g : Grid h w) (p : Pos h w) : Prop :=
  Grid.get g p = Cell.roll ∧ adjacentRolls g p < 4

end Neigh

namespace Parse

def parseCell (c : Char) : IO Cell :=
  match c with
  | '.' => .ok Cell.empty
  | '@' => .ok Cell.roll
  | _   => .error s!"Unexpected char: {c}"

def Vector.fromList (xs : List t) : Vector t xs.length :=
  ⟨xs.toArray, rfl⟩

def parseLine (s : String) : IO (Σ n, Vector Cell n) := do
  let chars := s.toList
  let vect  := Vector.fromList chars
  let cells <- vect.mapM parseCell
  pure ⟨chars.length, cells⟩

def checkVectSize {t m} (n : Nat) (xs : Vector t m) : IO (Vector t n) :=
  if h : n = m
    then pure (by rw [h]; exact xs)
    else .error "Ragging vector"

def parseGrid (input : String) : IO (Σ h, Σ w, Grid h w) := do
  let lines := input.trim.splitOn "\n"
  let parsed ← lines.mapM parseLine
  let w := match parsed with
    | []     => 0   -- No lines are parsed, widht of the vectors must be zero
    | p :: _ => p.1
  let rows ← parsed.mapM (fun x => checkVectSize w x.2)
  let h    := rows.length
  return ⟨h,w,Grid.mk (Vector.fromList rows)⟩

end Parse

namespace Part1

open Neigh

/-- A roll is accessible if it is `@` and has fewer than 4 roll-neighbors. -/
def accessible (g : Grid h w) (p : Pos h w) : Bool :=
  match Grid.get g p with
  | Cell.roll  => adjacentRolls g p < 4
  | Cell.empty => false

/-- A roll is accessible if it is `@` and has fewer than 4 roll-neighbors. -/
def accessibleD (g : Grid h w) (p : Pos h w) : Prop :=
  Grid.get g p = Cell.roll ∧ adjacentRolls g p < 4

/-- All positions in a `h×w` grid. -/
def allPos (h w : Nat) : List (Pos h w) := do
  let r <- (List.finRange h)
  let c <- (List.finRange w)
  pure (r, c)

/-- Final answer: number of accessible rolls. -/
def countAccessible (g : Grid h w) : Nat :=
  (allPos h w).foldl (fun acc p =>
      if accessible g p then acc + 1 else acc) 0

end Part1

def day04main1 : IO Unit := do
  let stdin <- IO.getStdin
  let input <- stdin.readToEnd
  let ⟨h, w, grid⟩ <- Parse.parseGrid input
  let ans := Part1.countAccessible grid
  IO.println ans

namespace Properties

open Neigh

inductive Position : Pos w h -> Prop where
  | corner {x : Fin w} {y : Fin h}
      (hw : x.val = 0 \/ x.val.succ = w)
      (hh : y.val = 0 \/ y.val.succ = h)
      : Position ⟨x,y⟩
  | edgeW {x : Fin w} {y : Fin h}
      (hw : x.val = 0 \/ x.val.succ = w)
      (hh : y.val ≠ 0 /\ y.val.succ ≠ h)
      : Position ⟨x,y⟩
  | edgeH {x : Fin w} {y : Fin h}
      (hw : x.val ≠ 0 /\ x.val.succ ≠ w)
      (hh : y.val = 0 \/ y.val.succ = h)
      : Position ⟨x,y⟩
  | interior {x : Fin w} {y : Fin h}
      (hw : x.val ≠ 0 /\ x.val.succ ≠ w)
      (hh : y.val ≠ 0 /\ y.val.succ ≠ h)
      : Position ⟨x,y⟩

def onEdge (x : Fin e) : Prop :=
  x.val = 0 ∨ x.val.succ = e

theorem notOnEdge
  {e : Nat}
  {x : Fin e}
  (h : ¬onEdge x) :
  -------------------
  (x.val ≠ 0 /\ x.val.succ ≠ e)
:= by
  exact (not_or.mp h)

def position (p : Pos w h) : Position p := by
  rcases p with ⟨x,y⟩
  by_cases hw : onEdge x <;> by_cases hh : onEdge y
  · exact Position.corner hw hh
  · exact Position.edgeW  hw (notOnEdge hh)
  · exact Position.edgeH  (notOnEdge hw) hh
  · exact Position.interior (notOnEdge hw) (notOnEdge hh)

theorem neighbors_length_le_8 {h w : Nat} (p : Pos h w) :
  (neighbors p).length ≤ 8 :=
by
  simpa [offsets] using (List.length_filterMap_le _ _)

private theorem foldl_add0or1_le_length
  (xs : List α)
  (step : Nat → α → Nat)
  (hstep : ∀ acc x, step acc x = acc ∨ step acc x = acc + 1) :
  ----------------
  ∀ a, xs.foldl step a ≤ a + xs.length
:= by
  induction xs with
  | nil =>
    simp
  | cons x xs ih =>
    simp [List.foldl]
    intros a
    have h1 := hstep a x
    cases h1 with
    | inl h1 =>
      have h2 := ih a
      rw [h1]
      simp [<- Nat.add_assoc]
      simp [Nat.le_trans h2 _]
    | inr h1 =>
      have h2 := ih (a + 1)
      rw [h1]
      simp [<- Nat.add_assoc, Nat.add_comm xs.length]
      exact h2

theorem adjacentRolls_le_neighbors {h w : Nat} (g : Grid h w) (p : Pos h w) :
  adjacentRolls g p ≤ (neighbors p).length
:= by
  unfold adjacentRolls
  let step : Nat → Pos h w → Nat := fun acc q =>
        match g.get q with
        | Cell.roll => acc + 1
        | Cell.empty => acc
  have hstep : ∀ acc q, step acc q = acc ∨ step acc q = acc + 1 := by
    intros acc q
    simp [step]
    cases g.get q <;> simp
  rw [<- Nat.add_zero ((neighbors p).length), Nat.add_comm]
  apply (foldl_add0or1_le_length (neighbors p) step hstep)

theorem adjacentRolls_le_8 {h w : Nat} (g : Grid h w) (p : Pos h w) :
  adjacentRolls g p ≤ 8
:= by
  simp [Nat.le_trans (adjacentRolls_le_neighbors _ _) (neighbors_length_le_8 _)]

theorem accessible_implies_adjacent_lt_4
  {h w : Nat} (g : Grid h w) (p : Pos h w) :
  Part1.accessible g p = true ->
  adjacentRolls g p < 4
:= by
  simp [Part1.accessible]
  cases (g.get p) <;> simp

/- The number of rolls in the grid-/
def countRolls {h w : Nat} (g : Grid h w) : Nat :=
  -- let positions := Part1.allPos h w
  List.foldl
    (fun acc p => match g.get p with
      | Cell.roll => acc + 1
      | Cell.empty => acc)
    0
    (Part1.allPos h w)

theorem foldl_acc_base
  (xs : List α)
  (f  : Nat → α → Nat)
  (z1 z2 : Nat)
  (h1 : z1 ≤ z2)
  (h2 : ∀ (a1 a2 : Nat) x, a1 ≤ a2 -> f a1 x ≤ f a2 x) :
  ---------------
  xs.foldl f z1 ≤ xs.foldl f z2
:= by
  revert f z1 z2 h1 h2
  induction xs with
  | nil =>
    intros f z1 z2 h1 h2
    simp
    assumption
  | cons x xs ih =>
    intros f z1 z2 h1 h2
    simp
    have h3 := h2 z1 z2 x h1
    exact ih f (f z1 x) (f z2 x) h3 h2

theorem foldl_acc_mono
  (xs  : List α)
  (f g : Nat → α → Nat)
  (hf : ∀ (a1 a2 : Nat) x, a1 ≤ a2 -> f a1 x ≤ f a2 x)
  (hfg : ∀ acc x, f acc x ≤ g acc x) :
  ------------------------------------
  ∀ acc, xs.foldl f acc ≤ xs.foldl g acc
:= by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl]
    intros acc
    have h2 := ih (f acc x)
    have h3 := ih (g acc x)
    have h4 := foldl_acc_base xs f (f acc x) (g acc x) (hfg _ _) hf
    apply Nat.le_trans h4 h3

theorem not_accessible_for_empty
  (g : Grid h w)
  (p : Pos  h w)
  (h : g.get p = Cell.empty) :
  ----------------------------
  (Part1.accessible g p = false)
:= by
  unfold Part1.accessible
  simp [h]

theorem countAccessible_le_countRolls {h w : Nat} (g : Grid h w) :
  Part1.countAccessible g ≤ countRolls g
:= by
  simp [Part1.countAccessible]
  simp [countRolls]
  let cntAccess : Nat -> Pos h w -> Nat := fun acc p =>
        if Part1.accessible g p = true then acc + 1 else acc
  let cntRoll : Nat -> Pos h w -> Nat := fun acc p =>
        match g.get p with
        | Cell.roll  => acc + 1
        | Cell.empty => acc
  have hAccessRollLE : ∀ acc p, cntAccess acc p ≤ cntRoll acc p := by
    unfold cntAccess
    unfold cntRoll
    intros acc p
    induction h1 : g.get p with
    | roll  => cases Part1.accessible g p <;> simp
    | empty => simp [not_accessible_for_empty g p h1]
  have hCndAccMonoton : ∀ (a1 a2 : Nat) (p : Pos h w), a1 ≤ a2 → cntAccess a1 p ≤ cntAccess a2 p
    := by
      intros a1 a2 p h1
      unfold cntAccess
      cases Part1.accessible g p <;> simp <;> assumption
  exact foldl_acc_mono (Part1.allPos h w) cntAccess cntRoll hCndAccMonoton hAccessRollLE 0

end Properties
