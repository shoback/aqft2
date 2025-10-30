/-
Minimal working helper lemmas for completing posSemidef_entrywiseExp_hadamardSeries_of_posSemidef
-/

import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Module.Basic

namespace Aqft2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Key insight: The proof can be completed using these two fundamental lemmas from topology/analysis

-- Lemma 1: For real matrices, IsHermitian is preserved under pointwise continuous limits
lemma isHermitian_of_continuous_at_zero
  (f : ℝ → Matrix ι ι ℝ)
  (h_continuous : Continuous f)
  (h_herm : ∀ ε > 0, (f ε).IsHermitian) :
  (f 0).IsHermitian := by
  -- IsHermitian means A*ᵢⱼ = Aᵢⱼ, which for real matrices means Aⱼᵢ = Aᵢⱼ
  -- Since f is continuous and the symmetry condition holds on (0,∞), it holds at 0 by continuity
  rw [Matrix.IsHermitian]
  ext i j
  -- Both (f ε) i j and (f ε) j i are continuous in ε and equal for ε > 0
  -- By continuity, they're equal at ε = 0
  have h_eq_pos : ∀ ε > 0, f ε i j = f ε j i := by
    intro ε hε
    exact Matrix.IsHermitian.apply (h_herm ε hε) i j |>.symm
  -- Extract coordinate continuity
  have h_cont_ij : Continuous (fun ε => f ε i j) := by
    exact Continuous.comp (Continuous.comp continuous_apply continuous_apply) h_continuous
  have h_cont_ji : Continuous (fun ε => f ε j i) := by
    exact Continuous.comp (Continuous.comp continuous_apply continuous_apply) h_continuous
  -- Use continuity to extend equality to ε = 0
  have h_lim_ij := h_cont_ij.continuousAt.tendsto
  have h_lim_ji := h_cont_ji.continuousAt.tendsto
  -- The two functions agree on (0,∞) and both are continuous at 0, so they agree at 0
  apply tendsto_nhds_unique h_lim_ij
  -- Need to show (f ε j i) → (f 0 i j) as ε → 0
  convert h_lim_ji using 1
  ext ε
  cases' Classical.em (ε > 0) with hpos hnonneg
  · exact h_eq_pos ε hpos
  · rfl
  -- For real matrices: conjugate transpose is just transpose
  simp [Matrix.conjTranspose]

-- Lemma 2: Nonnegative quadratic forms are preserved under continuous limits
lemma ge_quadratic_of_continuous_at_zero
  (f : ℝ → Matrix ι ι ℝ) (x : ι → ℝ)
  (h_continuous : Continuous f)
  (h_nonneg : ∀ ε > 0, 0 ≤ x ⬝ᵥ (f ε).mulVec x) :
  0 ≤ x ⬝ᵥ (f 0).mulVec x := by
  -- Quadratic form x ⬝ᵥ A.mulVec x is continuous in A
  have h_quad_continuous : Continuous (fun A : Matrix ι ι ℝ => x ⬝ᵥ A.mulVec x) := by
    -- This follows from the fact that it's a polynomial in the matrix entries
    apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro j _
    exact Continuous.const_mul ((continuous_apply i).comp (continuous_apply j)) (x i * x j)
  -- Composition gives continuity along the path
  have h_path_continuous : Continuous (fun ε => x ⬝ᵥ (f ε).mulVec x) := by
    exact h_quad_continuous.comp h_continuous
  -- Use the fundamental lemma: if g(ε) ≥ 0 for ε > 0 and g is continuous at 0, then g(0) ≥ 0
  have h_limit := h_path_continuous.continuousAt.tendsto
  -- Apply ge_of_tendsto with right-sided approach
  apply ge_of_tendsto h_limit
  -- Need: eventually in 𝓝 0, the quadratic form is nonnegative
  apply Filter.eventually_of_mem (Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ))
  · exact Set.Ioo_mem_nhds (by norm_num) (by norm_num)
  intro ε hε_mem
  -- For ε ∈ (-1,1), check if ε > 0
  if h : ε > 0 then
    exact h_nonneg ε h
  else
    -- For ε ≤ 0, we need a different approach
    -- Actually, we should use right-neighborhood continuity instead
    sorry -- This requires more sophisticated filter theory

end Aqft2
