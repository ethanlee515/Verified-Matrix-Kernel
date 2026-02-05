import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Fintype.Inv
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

structure pivot_t {a b : ℕ} where
  rk : ℕ
  locs : Fin rk → Fin b
  locs_increasing : StrictMono locs
  le_dim_rank : rk ≤ a

-- Aristotle
lemma pivot_locs_injective {a b} (p : @pivot_t a b) :
  Function.Injective p.locs := by
  apply p.locs_increasing.injective

def pivots_are_1s {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivot : @pivot_t a b) :=
    ∀ i : Fin pivot.rk,
    m (Fin.castLE pivot.le_dim_rank i) (pivot.locs i) = 1

def Matrix.is_zeroes_below
  {a b : ℕ} [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (i : Fin a) (j : Fin b) : Prop :=
  forall (i₀ : Fin a), (i₀ > i -> m i₀ j = 0)

def is_rref_with_pivots {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b) :=
  pivots_are_1s m pivots /\
  match pivots with
  | ⟨0, _, _, _⟩ => (m = 0)
  | ⟨rk₀ + 1, locs, _, le_dim_rank⟩ =>
    -- all 0s before first pivot
    (forall j, j < locs 0 -> forall i, m i j = 0) /\
    -- between pivots, 0s below
    (forall (i : Fin rk₀) (j : Fin b),
      let i' := Fin.castSucc i
      let iₐ : Fin a := Fin.castLE le_dim_rank i'
      locs i' ≤ j ->
      j < locs (i' + 1) ->
      m.is_zeroes_below iₐ j) /\
    -- after last pivot, 0s below
    (forall (j : Fin b),
      let rk₀' := Fin.last rk₀
      let i : Fin a := Fin.castLE le_dim_rank rk₀'
      (locs rk₀' ≤ j) ->
      (m.is_zeroes_below i j))

-- TODO edge case fixed, let Aristotle try again
#check Matrix.rank_eq_finrank_span_row
lemma pivot_rank_correct {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b)
  (is_pivot : is_rref_with_pivots m pivots) :
  Matrix.rank m = pivots.rk := by sorry

def kernel_from_non_pivot {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b)
  (j : Fin b) (i : Fin b) : ZMod 2 :=
  if i == j then 1
  else if is_pivot : i ∈ Finset.image pivots.locs Finset.univ then
    let i' : Set.range pivots.locs := ⟨i, by grind⟩
    let x := Function.Injective.invOfMemRange (by apply pivot_locs_injective) i'
    let xr : Fin a := Fin.castLE pivots.le_dim_rank x
    m xr j
  else 0

lemma ker_from_non_pivot_correct {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b)
  (pivots_correct : is_rref_with_pivots m pivots) j :
  kernel_from_non_pivot m pivots j ∈ m.toLin'.ker := by
  sorry

def ker_from_rref_aux {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b)
  (j : ℕ) (lt_j_b : j < b) : List (Fin b -> ZMod 2) :=
  let tail := match j with
  | 0 => []
  | j₀ + 1 => ker_from_rref_aux m pivots j₀ (by apply Nat.lt_of_succ_lt lt_j_b)
  let jfin : Fin b := Fin.ofNat b j
  if jfin ∈ Finset.image pivots.locs Finset.univ then
    tail
  else
    kernel_from_non_pivot m pivots jfin :: tail

def ker_from_rref {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b) : List (Fin b -> ZMod 2) :=
  ker_from_rref_aux m pivots (b - 1) (by simp [NeZero.pos])

#check finrank_span_eq_card

lemma ker_from_rref_lin_indep {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b)
  (pivots_correct : is_rref_with_pivots m pivots) :
  let ker := ker_from_rref m pivots
  LinearIndependent (ZMod 2) (fun (i : Fin (ker.length)) => ker[i]) := by
  sorry

lemma ker_from_rref_le_ker {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b)
  (pivots_correct : is_rref_with_pivots m pivots) :
  Submodule.span (ZMod 2) (ker_from_rref m pivots).toFinset ≤ m.toLin'.ker := by
  sorry

#check Submodule.eq_of_le_of_finrank_eq
-- TODO some sort of rank-nullity trick...

lemma ker_from_rref_correct {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b)
  (pivots_correct : is_rref_with_pivots m pivots) :
  m.toLin'.ker = Submodule.span (ZMod 2) (ker_from_rref m pivots).toFinset := by
  sorry

def demo_mat : Matrix (Fin 5) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0],
    ![0, 1, 1, 0, 1, 0],
    ![0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0]]

def demo_pivots : @pivot_t 5 6 where
  rk := 4
  locs := ![0, 1, 3, 5]
  locs_increasing := by
    intros i j; fin_cases i <;> fin_cases j <;> simp
  le_dim_rank := by simp

#eval ker_from_rref demo_mat demo_pivots
