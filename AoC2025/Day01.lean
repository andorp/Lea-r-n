import Batteries.Data.List.Lemmas
import Mathlib

-- part 1

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

theorem loop_correct
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
      | none   => .error s!"Invalid number in rotation line: {numStr} {line.length}"

def parseInput (s : String) : Except String (List Rotation) := do
  let lines := s.splitToList (· = '\n')
  let nonempty := lines.filter (fun l => !l.trim.isEmpty)
  nonempty.mapM parseRotation

def day01main : IO Unit := do
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
  | .R => (p + 1) % 100
  | .L => (p + 100 - 1) % 100   -- i.e. (p - 1) mod 100

theorem step1_range
  (p : Pos)
  (d : Dir) :
  -----------
  step1 p d < 100 :=
by
  unfold step1
  cases d with
  | R =>
      simp
      have h : 0 < 100 := by decide
      exact Nat.mod_lt _ h
  | L =>
      simp
      have h : 0 < 100 := by decide
      exact Nat.mod_lt _ h

def clicksSpec : Pos → Rotation → List Pos
  | _pos, ⟨_d, 0⟩   => []
  | pos , ⟨d , n+1⟩ =>
      let pos₁ := step1 pos d
      pos₁ :: clicksSpec pos₁ ⟨d, n⟩

theorem clicksSpec_range
  (pos : Pos)
  (r   : Rotation) :
  ------------------
  ∀ q ∈ clicksSpec pos r, q < 100
:= by
  cases r with
  | mk d n =>
      induction n generalizing pos with
      | zero =>
          intro q h
          simp [clicksSpec] at h
          -- sorry
      | succ n ih =>
          intro q h
          simp [clicksSpec] at h
          cases h with
          | inl hq =>
              subst hq
              exact step1_range pos d
          | inr hmem =>
              -- tail case: recurse from pos₁
              exact ih _ _ hmem

theorem clicksSpec_length
  (pos : Pos)
  (r   : Rotation) :
  ------------------
  (clicksSpec pos r).length = r.steps := by
  cases r with
  | mk d n =>
      induction n generalizing pos with
      | zero =>
          simp [clicksSpec]
      | succ n ih =>
          simp [clicksSpec, ih, Nat.succ_eq_add_one]

/--
If a rotation has at least one step, the final position in the per-click trace
coincides with the `stepSpec` final position.
-/
theorem clicksSpec_last_eq_stepSpec
  (pos    : Pos)
  (r      : Rotation)
  (hsteps : r.steps ≠ 0) :
  ------------------------
  (clicksSpec pos r).getLast? = some (stepSpec pos r) :=
by
  -- Sketch: do induction on r.steps, tracking pos;
  -- you can fill this in later if you want this fact explicitly.
  -- For now, we can leave this lemma as a `sorry` if not needed immediately.
  sorry

def runSpec2 : List Rotation → Pos → List Pos
  | [],      _   => []
  | r :: rs, pos =>
      let clicks := clicksSpec pos r
      let pos'   := stepSpec pos r
      clicks ++ runSpec2 rs pos'

theorem runSpec2_range
  (rs : List Rotation)
  (pos : Pos) :
  -------------
  ∀ q ∈ runSpec2 rs pos, q < 100 := by
  induction rs generalizing pos with
  | nil =>
      intro q h
      simp [runSpec2] at h
  | cons r rs ih =>
      intro q h
      simp [runSpec2] at h
      cases h with
      | inl hInClicks =>
          -- from this rotation's clicks
          exact clicksSpec_range pos r q hInClicks
      | inr hInTail =>
          -- from later rotations; recurse from pos'
          exact ih (stepSpec pos r) q hInTail

def passwordSpec2 (pos : Pos) (rs : List Rotation) : Nat :=
  (runSpec2 rs pos).count 0

#eval passwordSpec2 50 exampleRotations

theorem example_password2 :
  passwordSpec2 50 exampleRotations = 6
:= by
  -- mathlib can brute-force this finite computation:
  -- decide
  sorry

#eval (clicksSpec 50 ⟨Dir.R, 1000⟩).count 0

example :
  (clicksSpec 50 ⟨Dir.R, 1000⟩).count 0 = 10
:= by
  sorry

/-
TODO
Or more generally, you can prove a formula for:
(clicksSpec p ⟨Dir.R, n⟩).count 0

as something like:
0 if we never wrap around,
otherwise 1 + (n - firstHit) / 100, where firstHit is how many steps to reach 0 the first time.
That’s a fun next theorem if you want to get into arithmetical reasoning and modular arithmetic proofs.
-/

def firstRight (pos : Pos) : Nat :=
  if pos = 0 then 100 else 100 - pos

def firstLeft (pos : Pos) : Nat :=
  if pos = 0 then 100 else pos

def zerosInRot (pos : Pos) (r : Rotation) : Nat :=
  let n := r.steps
  match r.dir with
  | Dir.R =>
      let first := firstRight pos
      if n < first
        then 0
        else 1 + (n - first) / 100
  | Dir.L =>
      let first := firstLeft pos
      if n < first
        then 0
        else 1 + (n - first) / 100

#eval zerosInRot 50 ⟨Dir.R, 1000⟩

def solve2 (pos : Pos) (cnt : Nat) (rs : List Rotation) : Nat :=
  Id.run do
    let mut s : Nat × Pos := (cnt,pos)
    for r in rs do
      let c    := zerosInRot s.snd r
      let pos' := stepSpec s.snd r
      s := (s.fst + c,pos')
    pure s.fst

theorem zerosInRot_spec
  (pos : Pos)
  (r : Rotation) :
  ----------------
  zerosInRot pos r = (clicksSpec pos r).count 0
:= by
  sorry

theorem loop2_correct
  (rs : List Rotation)
  (pos cnt : Nat) :
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
    -- have hzeros : zerosInRot pos r = (clicksSpec pos r).count 0 := zerosInRot_spec pos r
    -- simp [zerosInRot,hzeros] at ih ⊢
    have h := ih (stepSpec pos r) (cnt + (clicksSpec pos r).count 0)
    simpa [Nat.add_assoc,Nat.add_comm,NAt.add_left_comm] using h
    sorry
