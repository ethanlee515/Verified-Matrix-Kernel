import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Fintype.Inv

structure pivot_t {a b : ℕ} where
  rk : ℕ
  locs : Fin rk → Fin b
  locs_increasing :
    forall (i j : Fin rk), (i < j -> locs i < locs j)
  le_dim_rank : rk ≤ a

lemma pivot_locs_injective {a b} (p : @pivot_t a b) :
  Function.Injective p.locs := by
  sorry

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
  | ⟨0, _, _, _⟩ => True
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

def kernel_from_rref_aux {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b)
  (j : ℕ)
  (lt_j_b : j < b) : List (Fin b -> ZMod 2) :=
  let tail := match j with
  | 0 => []
  | j₀ + 1 => kernel_from_rref_aux m pivots j₀ (by sorry)
  let jfin : Fin b := Fin.ofNat b j
  if is_pivot : (jfin ∈ Finset.image pivots.locs Finset.univ) then
    tail
  else
    (fun i =>
      if is_pivot' : i ∈ Finset.image pivots.locs Finset.univ then
        let i' : Set.range pivots.locs := ⟨i, by sorry⟩
        let x := Function.Injective.invOfMemRange (by sorry) i'
        let xr : Fin a := Fin.castLE (by sorry) x
        m xr jfin
      else if (i = j) then 1 else 0
    ) :: tail

def kernel_from_rref {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b) : List (Fin b -> ZMod 2) :=
  kernel_from_rref_aux m pivots (b - 1) (by simp [NeZero.pos])

def demo_mat : Matrix (Fin 5) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0],
    ![0, 1, 1, 0, 1 ,0],
    ![0, 0, 0, 1, 0 ,0],
    ![0, 0, 0, 0, 0 ,1],
    ![0, 0, 0, 0, 0 ,0]]

def demo_pivots : @pivot_t 5 6 where
  rk := 4
  locs := ![0, 1, 3, 5]
  locs_increasing := by
    intros i j
    fin_cases i <;> fin_cases j <;> simp
  le_dim_rank := by simp

#eval! kernel_from_rref demo_mat demo_pivots
