import Batteries.Data.List.Lemmas
import Mathlib
import Init.Data.Fin.Basic

-- part 1

inductive Dir
  | L
  | R

structure Rotation where
  dir   : Dir
  steps : Nat

/- Dial positions are number 0..99 (this invariant will be enforced) -/
abbrev Pos := Fin 100

def stepSpec (p : Pos) (r : Rotation) : Pos :=
  let n : Nat := r.steps
  let m : Pos := Fin.ofNat 100 n
  match r.dir with
  | .R => p + m
  | .L => p - m

def runSpec : List Rotation -> Pos -> List Pos
  | []     , _ => []
  | r :: rs, p =>
      let p' := stepSpec p r
      p' :: runSpec rs p'

def passwordSpec (pos : Pos) (rs : List Rotation) : Nat :=
  (runSpec rs pos).count 0

/-- The sample list from the problem statement. -/
def exampleRotations : List Rotation :=
  [ ⟨Dir.L, 68⟩,
    ⟨Dir.L, 30⟩,
    ⟨Dir.R, 48⟩,
    ⟨Dir.L, 5 ⟩,
    ⟨Dir.R, 60⟩,
    ⟨Dir.L, 55⟩,
    ⟨Dir.L, 1 ⟩,
    ⟨Dir.L, 99⟩,
    ⟨Dir.R, 14⟩,
    ⟨Dir.L, 82⟩
  ]

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

theorem loop_correct
  (rs  : List Rotation)
  (pos : Pos)
  (cnt : Nat) :
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
  (rs  : List Rotation) :
  -----------------------
  solve pos 0 rs = passwordSpec pos rs
:= by
  unfold passwordSpec
  simp [loop_correct]

/-- Parse a direction character into `Dir`. -/
def parseDir (c : Char) : Except String Dir :=
  match c with
  | 'L' => .ok Dir.L
  | 'R' => .ok Dir.R
  | _   => .error s!"Invalid direction character: {c}"

/-- Parse one line like `"L68"` or `"R5"` into a `Rotation`. -/
def parseRotation (line : String) : Except String Rotation := do
  match line.trim.toList with
  | [] =>
      .error "Empty line"
  | c :: cs =>
      let dir ← parseDir c
      let numStr := String.ofList cs
      match numStr.toNat? with
      | some n => .ok ⟨dir, n⟩
      | none      => .error s!"Invalid number in rotation line: {numStr}"

def parseInput (s : String) : Except String (List Rotation) := do
  let lines := s.splitToList (· = '\n')
  let nonempty := lines.filter (fun l => !l.trim.isEmpty)
  nonempty.mapM parseRotation

def day01main1 : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  match parseInput input with
  | .ok rs =>
      let ans := solve 50 0 rs
      IO.println ans
  | .error msg =>
      IO.eprintln s!"Error parsing input: {msg}"

-- part 2

def step1 (p : Pos) (d : Dir) : Pos :=
  match d with
  | .R => p + 1
  | .L => p + 99

def clicksSpec : Pos → Rotation → List Pos
  | _pos, ⟨_d, 0⟩ => []
  | pos , ⟨d , n+1⟩ =>
      let pos₁ := step1 pos d
      pos₁ :: clicksSpec pos₁ ⟨d, n⟩

theorem clicksSpec_length
  (pos : Pos)
  (r   : Rotation) :
  ------------------
  (clicksSpec pos r).length = r.steps := by
  cases r with
  | mk d n =>
    induction n generalizing pos with
    | zero      => simp [clicksSpec]
    | succ n ih => simp [clicksSpec, ih]

def runSpec2 : List Rotation → Pos → List Pos
  | [],      _   => []
  | r :: rs, pos =>
      let clicks := clicksSpec pos r
      let pos'   := stepSpec pos r
      clicks ++ runSpec2 rs pos'

def passwordSpec2 (pos : Pos) (rs : List Rotation) : Nat :=
  (runSpec2 rs pos).count 0

#eval passwordSpec2 50 exampleRotations

#eval (clicksSpec 50 ⟨Dir.R, 1000⟩).count 0

def zerosInRotRec : Pos -> Rotation -> Nat
  | pos, ⟨d, 0⟩   => 0
  | pos, ⟨d, n+1⟩ =>
      let pos₁ := step1 pos d
      (if pos₁ = 0 then 1 else 0) + zerosInRotRec pos₁ ⟨d, n⟩

/-- distance (in steps) going right until the *next* time we hit 0 -/
def distRight (p : Pos) : Nat :=
  if p.val = 0
    then 100
    else 100 - p.val

/-- distance (in steps) going left until the *next* time we hit 0 -/
def distLeft (p : Pos) : Nat :=
  if p.val = 0
    then 100
    else p.val

/-- distance (in steps) until the next time we hit 0 following `d` -/
def firstZeroSteps (d : Dir) (p : Pos) : Nat :=
  match d with
  | Dir.R => distRight p
  | Dir.L => distLeft p

/-- how many times we land exactly on 0 in `r.steps` moves from `pos` -/
def zerosInRot (pos : Pos) (r : Rotation) : Nat :=
  let first := firstZeroSteps r.dir pos
  let n     := r.steps
  if n < first
    then 0
    else 1 + (n - first) / 100

theorem zeroesInRotRec_spec
  (pos : Pos)
  (r : Rotation) :
  ----------------
  zerosInRotRec pos r = (clicksSpec pos r).count 0
:= by
  cases r with
  | mk d n =>
    induction n generalizing pos with
    | zero =>
      simp [zerosInRotRec, clicksSpec]
    | succ n ih =>
      simp
        [ zerosInRotRec
        , clicksSpec
        , List.count_cons
        , ih
        , Nat.add_comm
        ]

/-
theorem zerosInRot_eq_rec
  (pos : Pos)
  (r : Rotation) :
  ----------------
  zerosInRot pos r = zerosInRotRec pos r
:= by
  cases r with | mk d n =>
  sorry
-/

theorem zerosInRot_spec
  (pos : Pos)
  (r : Rotation) :
  ----------------
  zerosInRot pos r = (clicksSpec pos r).count 0
:= by
  cases r with | mk d n =>
  induction n generalizing pos d with
  | zero =>
      simp [zerosInRot,clicksSpec,firstZeroSteps]
      by_cases h1 : pos.val = 0
      · have hpos : pos = (0 : Pos) := by
          apply Fin.eq_of_val_eq
          simpa using h1
        cases d with
        | L => simp [distLeft, hpos]
        | R => simp [distRight, hpos]
      · cases d with
        | L =>
          simp [distLeft]
          intros h2
          by_cases h3 : pos = 0
          · simp [h3] at h1
          · have h4 : (↑pos : Nat) = 0 := by simp [h3] at h2
            exact h1 h4
        | R =>
          simp [distRight]
          intros h2
          by_cases h3 : pos = 0
          · simp [h3] at h1
          · have h4 : 100 - (↑pos : Nat) = 0 := by simpa [h3] using h2
            have h5 : 100 <= (↑pos : Nat) := by exact (Nat.sub_eq_zero_iff_le.mp h4)
            have h6 : (↑pos : Nat) < 100 := pos.isLt
            exact (Nat.not_le_of_gt h6) h5
  | succ n ih =>
    let rn   : Rotation := { dir := d, steps := n}
    let rn1  : Rotation := { dir := d, steps := n + 1 }
    let pos1 : Pos      := step1 pos d
    simp [zerosInRot, clicksSpec, List.count_cons] at ih ⊢
    have ih' := (ih pos1 d).symm
    have h1 := congrArg (fun x => x + if pos1 = 0 then 1 else 0) ih'
    simp [pos1,h1] at ⊢
    by_cases h2 : pos1 = 0
    · cases d <;> cases pos using Fin.cases
      · have pos1_ne_zero : pos1 ≠ (0 : Pos) := by
          simp [pos1,step1]
        exact (pos1_ne_zero h2).elim
      · rename_i i
        have h3 : step1 i.succ Dir.L = 0 := by
          simpa [pos1] using h2
        have h4 : (i.succ : Pos) ≠ 0 :=
          Fin.succ_ne_zero _
        have h5 : ((i.succ : Pos).val ≠ 0) := by
          intro h
          apply h4
          apply Fin.eq_of_val_eq
          simpa using h
        have h6 :
          (if n + 1 < firstZeroSteps Dir.L i.succ then 0 else 1 + (n + 1 - firstZeroSteps Dir.L i.succ) / 100)
          =
          (if n < firstZeroSteps Dir.L (step1 i.succ Dir.L) then 0 else 1 + (n - firstZeroSteps Dir.L (step1 i.succ Dir.L)) / 100) +
          (if step1 i.succ Dir.L = 0 then 1 else 0) := by
            simp [firstZeroSteps, distLeft, h2, h4, h3] at ⊢
            sorry
        simp [h6]
      · sorry
      · rename_i i
        sorry
    · sorry

#eval zerosInRot 50 ⟨Dir.R, 1000⟩

def solve2 (pos : Pos) (cnt : Nat) (rs : List Rotation) : Nat :=
  Id.run do
    let mut s : Nat × Pos := (cnt,pos)
    for r in rs do
      let c    := zerosInRot s.snd r
      let pos' := stepSpec s.snd r
      s := (s.fst + c,pos')
    pure s.fst

theorem zerosInRotRec_spec
  (pos : Pos)
  (r : Rotation) :
  ----------------
  zerosInRotRec pos r = (clicksSpec pos r).count 0
:= by
  cases r with | mk d n =>
  induction n generalizing pos with
  | zero => simp [zerosInRotRec, clicksSpec]
  | succ n ih => simp
    [ zerosInRotRec
    , clicksSpec
    , List.count_cons
    , Nat.add_comm
    , ih (step1 pos d)
    ]

theorem loop2_correct
  (rs : List Rotation)
  (pos : Pos)
  (cnt : Nat) :
  -----------------
  solve2 pos cnt rs
  =
  cnt + (runSpec2 rs pos).count 0
:= by
  induction rs generalizing pos cnt with
  | nil =>
    simp [solve2, runSpec2]
  | cons r rs ih =>
    simp [solve2,runSpec2,List.count_append] at ih ⊢
    have hzeros : zerosInRot pos r = (clicksSpec pos r).count 0
          := zerosInRot_spec pos r
    simp [hzeros]
    have h := ih (stepSpec pos r) (cnt + (clicksSpec pos r).count 0)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem solve2_correct
  (pos : Pos)
  (rs  : List Rotation) :
  -----------------------
  solve2 pos 0 rs = passwordSpec2 pos rs
:= by
  unfold passwordSpec2
  simp [loop2_correct]

def day01main2 : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  match parseInput input with
  | .ok rs =>
      let ans := solve2 50 0 rs
      IO.println ans
  | .error msg =>
      IO.eprintln s!"Error parsing input: {msg}"
