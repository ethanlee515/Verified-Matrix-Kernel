import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Matrix.ToLin

structure pivot_t {a b : ℕ} where
  rk : ℕ
  locs : Fin rk → Fin b
  locs_increasing :
    forall (i j : Fin rk), (i < j -> locs i < locs j)
  le_dim_rank : rk ≤ a

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
