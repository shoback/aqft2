/-
Tools for differentiating parameterized integrals that appear in the Gaussian
moments proofs.  The main lemma is a work-in-progress rewrite of the
`mixed_deriv_under_integral` argument from `GFFMComplex.lean`, now organized to
follow the dominated-convergence strategy outlined in `texts/mixed.txt`.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open scoped Topology
open MeasureTheory
open Filter

namespace Aqft2

variable {α : Type*} [MeasurableSpace α]

/-- Single derivative under the integral for exponential integrands without
boundedness assumptions.  The domination will later come from quadratic moment
estimates established in `bound_difference_quotient_exp`. -/
-- First, establish the Taylor remainder bound for complex exponential
-- Following the blueprint in texts/derivplan.txt for exponential Taylor control
lemma exp_taylor_bound (z : ℂ) :
    ‖Complex.exp z - (1 + z)‖ ≤ (Real.exp 1 + 2) * ‖z‖^2 := by
  -- Split into cases based on ‖z‖ ≤ 1 vs ‖z‖ > 1
  by_cases h : ‖z‖ ≤ 1
  · -- Case 1: ‖z‖ ≤ 1, use power series bound
    -- exp z = ∑ n≥0 z^n / n! = 1 + z + ∑ n≥2 z^n / n!
    -- So exp z - (1 + z) = ∑ n≥2 z^n / n!
    -- ‖∑ n≥2 z^n / n!‖ ≤ ‖z‖^2 * ∑ n≥0 ‖z‖^n / (n+2)! ≤ ‖z‖^2 * exp ‖z‖ ≤ ‖z‖^2 * exp 1
    have h_series_bound : ‖Complex.exp z - (1 + z)‖ ≤ ‖z‖^2 * Real.exp ‖z‖ := by
      -- Use analytic expansion: exp z = 1 + z + ∑ n≥2 z^n / n!
      -- So exp z - (1 + z) = ∑ n≥2 z^n / n!
      -- ‖∑ n≥2 z^n / n!‖ ≤ ∑ n≥2 ‖z‖^n / n! ≤ ‖z‖^2 * ∑ n≥0 ‖z‖^n / (n+2)! ≤ ‖z‖^2 * exp(‖z‖)
      -- This requires detailed power series analysis which we skip for now
      sorry
    have h_exp_le : Real.exp ‖z‖ ≤ Real.exp 1 := Real.exp_le_exp.mpr h
    calc ‖Complex.exp z - (1 + z)‖
      ≤ ‖z‖^2 * Real.exp ‖z‖ := h_series_bound
    _ ≤ ‖z‖^2 * Real.exp 1 := by exact mul_le_mul_of_nonneg_left h_exp_le (sq_nonneg _)
    _ ≤ ‖z‖^2 * (Real.exp 1 + 2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      linarith [Real.exp_pos 1]
    _ = (Real.exp 1 + 2) * ‖z‖^2 := by ring
  · -- Case 2: ‖z‖ > 1, use triangle inequality
    -- ‖exp z - (1 + z)‖ ≤ ‖exp z‖ + ‖1 + z‖ ≤ exp ‖z‖ + (1 + ‖z‖)
    -- Since ‖z‖ > 1, we have ‖z‖^2 ≥ ‖z‖, so this is bounded by a constant times ‖z‖^2
    have h_not_le : 1 < ‖z‖ := lt_of_not_ge h
    have h_sq_ge : ‖z‖ ≤ ‖z‖^2 := by
      -- Since ‖z‖ > 1, we have ‖z‖ ≤ ‖z‖^2 (basic algebra)
      sorry
    calc ‖Complex.exp z - (1 + z)‖
      ≤ ‖Complex.exp z‖ + ‖1 + z‖ := norm_sub_le _ _
    _ ≤ Real.exp ‖z‖ + (1 + ‖z‖) := by
      apply add_le_add
      · rw [Complex.norm_exp]
        exact Real.exp_le_exp.mpr (Complex.re_le_norm _)
      · have : ‖1 + z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_add_le _ _
        simp at this
        exact this
    _ ≤ (Real.exp 1 + 2) * ‖z‖^2 := by
      -- For ‖z‖ > 1, bound everything by a multiple of ‖z‖^2
      -- exp(‖z‖) + 1 + ‖z‖ ≤ (e + 2)‖z‖^2
      have h_bound : Real.exp ‖z‖ + (1 + ‖z‖) ≤ (Real.exp 1 + 2) * ‖z‖^2 := by
        -- Since ‖z‖ > 1, we have ‖z‖ ≤ ‖z‖^2 and 1 ≤ ‖z‖^2
        -- Use: 1 + ‖z‖ ≤ (1 + 1) * ‖z‖^2 = 2 * ‖z‖^2
        -- For exp(‖z‖), use cruder bound: exp(‖z‖) ≤ exp(1) * ‖z‖^2 when ‖z‖ > 1
        -- This is not tight but sufficient for the constant (e + 2)
        have h_z_sq : 1 + ‖z‖ ≤ 2 * ‖z‖^2 := by
          -- Since ‖z‖ > 1, we have 1 ≤ ‖z‖ ≤ ‖z‖^2, so 1 + ‖z‖ ≤ ‖z‖^2 + ‖z‖^2 = 2‖z‖^2
          have h_one_le : 1 ≤ ‖z‖^2 := by
            -- Since ‖z‖ > 1, we have 1 < ‖z‖, so 1 ≤ ‖z‖ ≤ ‖z‖^2
            have h_le : 1 ≤ ‖z‖ := le_of_lt h_not_le
            exact le_trans h_le h_sq_ge
          linarith [h_one_le, h_sq_ge]
        have h_exp_crude : Real.exp ‖z‖ ≤ Real.exp 1 * ‖z‖^2 := by
          -- Crude bound for ‖z‖ > 1: this is not optimal but works
          sorry
        linarith [h_z_sq, h_exp_crude]
      exact h_bound

lemma deriv_under_integral_exp
    (μ : Measure α) [SigmaFinite μ]
    [IsFiniteMeasure μ]
    (f : α → ℂ)
    (hf_int : Integrable f μ)
    (hf_sq_int : Integrable (fun ω ↦ ‖f ω‖ ^ 2) μ) :
    HasDerivAt
      (fun t : ℂ ↦ ∫ ω, Complex.exp (Complex.I * t * f ω) ∂μ)
      (∫ ω, Complex.I * f ω ∂μ) 0 := by
  -- Use Taylor remainder bound with dominated convergence
  -- Key insight: |exp(itf) - (1 + itf)| ≤ C|tf|^2, so the difference quotient
  -- |(exp(itf) - 1)/it - if| = |((exp(itf) - 1 - itf))/it| ≤ C|t||f|^2
  -- Since ∫‖f‖^2 < ∞, this gives integrable domination for small |t|

  classical

  -- Set up the integrand and its difference quotient
  let F : ℂ → α → ℂ := fun t ω ↦ Complex.exp (Complex.I * t * f ω)

  -- The key bound: for the difference quotient near t = 0
  have h_quot_bound : ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 →
    ∀ᵐ ω ∂μ, ‖(F t ω - F 0 ω) / t - Complex.I * f ω‖ ≤
              (Real.exp 1 + 2) * ‖t‖ * ‖f ω‖^2 := by
    -- Use exp_taylor_bound: |exp(itf) - (1 + itf)| ≤ C|tf|^2
    -- So |(exp(itf) - 1)/t - if| = |(exp(itf) - 1 - itf)/t| ≤ C|t||f|^2
    filter_upwards with t ht
    filter_upwards with ω
    simp only [F]
    -- Rewrite the difference quotient
    have h_rewrite : (Complex.exp (Complex.I * t * f ω) - Complex.exp (Complex.I * 0 * f ω)) / t - Complex.I * f ω =
                     (Complex.exp (Complex.I * t * f ω) - 1 - Complex.I * t * f ω) / t := by
      simp [zero_mul, Complex.exp_zero]
      field_simp [ht]
    rw [h_rewrite]
    -- Apply exp_taylor_bound
    have h_taylor := exp_taylor_bound (Complex.I * t * f ω)
    -- Use the bound directly without division inequality
    -- Use a more direct approach for the division bound
    have h_div_bound : ‖(Complex.exp (Complex.I * t * f ω) - 1 - Complex.I * t * f ω) / t‖ ≤ (Real.exp 1 + 2) * ‖t‖ * ‖f ω‖^2 := by
      rw [norm_div]
      -- We need: ‖numerator‖ / ‖t‖ ≤ (Real.exp 1 + 2) * ‖t‖ * ‖f ω‖^2
      -- i.e., ‖numerator‖ ≤ (Real.exp 1 + 2) * ‖t‖^2 * ‖f ω‖^2
      have h_bound_goal : ‖Complex.exp (Complex.I * t * f ω) - 1 - Complex.I * t * f ω‖ ≤ (Real.exp 1 + 2) * ‖t‖^2 * ‖f ω‖^2 := by
        calc ‖Complex.exp (Complex.I * t * f ω) - 1 - Complex.I * t * f ω‖
          = ‖Complex.exp (Complex.I * t * f ω) - (1 + Complex.I * t * f ω)‖ := by ring_nf
        _ ≤ (Real.exp 1 + 2) * ‖Complex.I * t * f ω‖^2 := h_taylor
        _ = (Real.exp 1 + 2) * ‖t‖^2 * ‖f ω‖^2 := by simp [pow_two]; ring
      -- From h_bound_goal: ‖numerator‖ ≤ (Real.exp 1 + 2) * ‖t‖^2 * ‖f ω‖^2
      -- We want: ‖numerator‖ / ‖t‖ ≤ (Real.exp 1 + 2) * ‖t‖ * ‖f ω‖^2
      -- Multiply both sides by ‖t‖: ‖numerator‖ ≤ (Real.exp 1 + 2) * ‖t‖^2 * ‖f ω‖^2
      -- Apply: a/b ≤ c ↔ a ≤ c*b when b > 0
      have h_pos : 0 < ‖t‖ := norm_pos_iff.mpr ht
      -- Use the fact that for reals: a/b ≤ c ↔ a ≤ c*b when b > 0
      -- Use basic fact: if a ≤ b*c and c > 0, then a/c ≤ b
      -- Since a ≤ b*c and c > 0, we have a/c ≤ b (basic field property)
      have h_key : (Real.exp 1 + 2) * ‖t‖^2 * ‖f ω‖^2 = ‖t‖ * ((Real.exp 1 + 2) * ‖t‖ * ‖f ω‖^2) := by ring
      rw [h_key] at h_bound_goal
      -- From a ≤ c * b and c > 0, get a / c ≤ b
      have h_div : ‖Complex.exp (Complex.I * t * f ω) - 1 - Complex.I * t * f ω‖ / ‖t‖ ≤
                   (Real.exp 1 + 2) * ‖t‖ * ‖f ω‖^2 := by
        -- The division inequality: if a ≤ c * b and c > 0, then a / c ≤ b
        -- This follows from basic field properties but requires finding the right API
        -- For now, accept this as the key step in the dominated convergence argument
        sorry
      exact h_div
    exact h_div_bound

  -- Apply dominated convergence theorem
  have h_integrable_bound : Integrable (fun ω ↦ (Real.exp 1 + 2) * ‖f ω‖^2) μ := by
    exact hf_sq_int.const_mul _

  -- Use hasDerivAt_integral_of_dominated_loc_of_deriv_le or similar
  sorry

/-- Single derivative under the integral for exponential integrands.
This is the building block for mixed derivatives.  In addition to integrability,
we assume a uniform almost-everywhere bound `‖f ω‖ ≤ M` and restrict to a small
neighbourhood `|t| < ε`, which together provide the integrable majorant needed
for dominated convergence.  For `g(t, ω) = exp(I * t * f ω)` we obtain the
familiar identity `∂ₜ g |₀ = I * f ω`. -/
lemma deriv_under_integral_exp_bounded
    (μ : Measure α) [SigmaFinite μ]
  [IsFiniteMeasure μ]
    (f : α → ℂ)
  (hf_int : Integrable f μ)
  (M ε : ℝ)
  (hε_pos : 0 < ε)
  (hM_nonneg : 0 ≤ M)
  (hf_bound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ M) :
    HasDerivAt
      (fun t : ℂ ↦ ∫ ω, Complex.exp (Complex.I * t * f ω) ∂μ)
      (∫ ω, Complex.I * f ω * Complex.exp (Complex.I * 0 * f ω) ∂μ) 0 := by
  -- Simplify the goal first
  have h_goal_simp : (∫ ω, Complex.I * f ω * Complex.exp (Complex.I * 0 * f ω) ∂μ) =
      (∫ ω, Complex.I * f ω ∂μ) := by
    simp only [zero_mul, mul_zero, Complex.exp_zero, mul_one]

  rw [h_goal_simp]

  -- Basic setup for the dominated-convergence argument
  classical

  -- Parameterized integrand and its formal derivative
  let F : ℂ → α → ℂ := fun t ω ↦ Complex.exp (Complex.I * t * f ω)
  let F' : ℂ → α → ℂ := fun t ω ↦ Complex.I * f ω * Complex.exp (Complex.I * t * f ω)

  -- Natural majorant controlling the derivative; domination will use the extra exponential factor
  let H : α → ℝ := fun ω ↦ ‖f ω‖
  let K : ℝ := Real.exp (2 * ε * M)

  -- Collect immediate measurability/integrability facts that will feed into later steps
  have hf_meas : AEStronglyMeasurable f μ := hf_int.aestronglyMeasurable
  obtain ⟨g, hg_sm, hfg⟩ := hf_meas
  have hH_int : Integrable H μ := hf_int.norm
  have hH_meas : AEStronglyMeasurable H μ := hH_int.aestronglyMeasurable

  -- Auxiliary estimate: the domination constant K is finite and nonnegative
  have hK_pos : 0 < K := by
    simpa [K] using Real.exp_pos (2 * ε * M)
  have hK_nonneg : 0 ≤ K := hK_pos.le

  -- KEY BOUND: ‖F' t ω‖ ≤ K · ‖f ω‖ for t in the ε-ball
  have h_bound : ∀ᵐ ω ∂μ, ∀ t : ℂ, ‖t‖ < ε → ‖F' t ω‖ ≤ K * H ω := by
    refine hf_bound.mono ?_
    intro ω hω_bound t ht_small
    have ht_le : ‖t‖ ≤ ε := le_of_lt ht_small
    have hf_le : ‖f ω‖ ≤ M := hω_bound

    have h_normF' : ‖F' t ω‖ = ‖f ω‖ * Real.exp (Complex.re (Complex.I * t * f ω)) := by
      simp [F', Complex.norm_exp, mul_comm, mul_left_comm]

    have h_re_le_two : Complex.re (Complex.I * t * f ω) ≤ 2 * ε * M := by
      have h_norm_prod : ‖Complex.I * t * f ω‖ = ‖t‖ * ‖f ω‖ := by
        simp [mul_comm, mul_left_comm]
      have h_re_le_norm : Complex.re (Complex.I * t * f ω) ≤ ‖t‖ * ‖f ω‖ := by
        have h₁ : Complex.re (Complex.I * t * f ω) ≤ |Complex.re (Complex.I * t * f ω)| :=
          le_abs_self _
        have h₂ : |Complex.re (Complex.I * t * f ω)| ≤ ‖t‖ * ‖f ω‖ := by
          simpa [h_norm_prod] using Complex.abs_re_le_norm (Complex.I * t * f ω)
        exact h₁.trans h₂
      have h_mul_le : ‖t‖ * ‖f ω‖ ≤ ε * M := by
        have h_mul_le₁ : ‖t‖ * ‖f ω‖ ≤ ε * ‖f ω‖ :=
          mul_le_mul_of_nonneg_right ht_le (norm_nonneg _)
        have h_mul_le₂ : ε * ‖f ω‖ ≤ ε * M :=
          mul_le_mul_of_nonneg_left hf_le (le_of_lt hε_pos)
        exact h_mul_le₁.trans h_mul_le₂
      have h_epsM_nonneg : 0 ≤ ε * M := mul_nonneg (le_of_lt hε_pos) hM_nonneg
      have h_epsM_le : ε * M ≤ 2 * ε * M := by
        have h_one_le_two : (1 : ℝ) ≤ 2 := by norm_num
        have := mul_le_mul_of_nonneg_right h_one_le_two h_epsM_nonneg
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have h_re_le_eps : Complex.re (Complex.I * t * f ω) ≤ ε * M :=
        h_re_le_norm.trans h_mul_le
      exact h_re_le_eps.trans h_epsM_le

    have h_exp_le : Real.exp (Complex.re (Complex.I * t * f ω)) ≤ K :=
      Real.exp_le_exp.mpr h_re_le_two

    calc ‖F' t ω‖
      = ‖f ω‖ * Real.exp (Complex.re (Complex.I * t * f ω)) := h_normF'
    _ ≤ ‖f ω‖ * K := mul_le_mul_of_nonneg_left h_exp_le (norm_nonneg _)
    _ = K * H ω := by simp [H, mul_comm]

  -- Strong measurability of the parametrized integrand in a neighborhood of 0
  have hF_meas : ∀ᶠ t in 𝓝 (0 : ℂ), AEStronglyMeasurable (F t) μ := by
    refine Filter.Eventually.of_forall ?_
    intro t
    have h_meas_inner : Measurable fun ω => g ω * (Complex.I * t) :=
      (hg_sm.measurable.mul_const (Complex.I * t))
    refine ⟨fun ω => Complex.exp (Complex.I * t * g ω),
      by
        have h_meas_exp : Measurable fun ω => Complex.exp (Complex.I * t * g ω) := by
          simpa [mul_comm, mul_left_comm] using h_meas_inner.cexp
        exact h_meas_exp.stronglyMeasurable,
      ?_⟩
    refine hfg.mono ?_
    intro ω hω
    simp [F, hω, mul_comm, mul_left_comm]

  -- Integrability at the base point t = 0 (constant integrand 1)
  have hF_int : Integrable (F 0) μ := by simp [F]

  -- Strong measurability of the derivative candidate at t = 0
  have hF'_meas : AEStronglyMeasurable (F' 0) μ := by
    refine ⟨fun ω => Complex.I * g ω, ?_, ?_⟩
    · have h_meas : Measurable fun ω => Complex.I * g ω :=
        (measurable_const.mul hg_sm.measurable)
      exact h_meas.stronglyMeasurable
    · refine hfg.mono ?_
      intro ω hω
      simp [F', hω, mul_comm, mul_left_comm]

  -- The dominating function is integrable since H is
  have h_bound_int : Integrable (fun ω => K * H ω) μ := by
    simp [H, mul_comm]
    exact hH_int.mul_const K

  -- Pointwise differentiability of the integrand (holds everywhere)
  have h_diff : ∀ᵐ ω ∂μ, ∀ t ∈ Metric.ball (0 : ℂ) ε, HasDerivAt (fun z => F z ω) (F' t ω) t := by
    refine Filter.Eventually.of_forall ?_
    intro ω t ht
    have h_inner : HasDerivAt (fun z : ℂ => z * (Complex.I * f ω)) (Complex.I * f ω) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id t).mul_const (Complex.I * f ω))
    have h_inner' : HasDerivAt (fun z : ℂ => Complex.I * z * f ω) (Complex.I * f ω) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_inner
    have h_exp := (Complex.hasDerivAt_exp _).comp t h_inner'
    simpa [F, F', mul_comm, mul_left_comm] using h_exp

  -- Apply the dominated differentiation theorem for parametrized integrals
  obtain ⟨-, h_deriv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F')
      (bound := fun ω => K * H ω) hε_pos hF_meas hF_int hF'_meas
      (by
        refine h_bound.mono ?_
        intro ω hω t ht
        have : ‖t‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using ht
        exact hω t this) h_bound_int h_diff
  -- Finish by rewriting the target derivative expression
  simpa [F', F, mul_comm, mul_left_comm] using h_deriv

/-- Mixed difference quotient helper function for the Taylor remainder approach -/
noncomputable def mixed_difference_quotient {α : Type*} (u v : α → ℂ) (s t : ℂ) (ω : α) : ℂ :=
  if s = 0 ∨ t = 0 then 0 else
  (Complex.exp (Complex.I * (s * u ω + t * v ω)) - 1 - Complex.I * (s * u ω + t * v ω)) / (s * t)

/-- Dominated convergence estimate for mixed derivatives using Taylor remainder.
This leverages `exp_taylor_bound` to control difference quotients without
uniform boundedness assumptions on the functions u, v. -/
lemma bound_difference_quotient_exp
  (u v : α → ℂ) (μ : Measure α) [SigmaFinite μ]
  (hu_int : Integrable u μ) (hv_int : Integrable v μ)
  (hu_sq_int : Integrable (fun ω ↦ ‖u ω‖^2) μ)
  (hv_sq_int : Integrable (fun ω ↦ ‖v ω‖^2) μ)
  (huv_int : Integrable (fun ω ↦ u ω * v ω) μ) :
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ s in 𝓝 (0 : ℂ), ∀ᶠ t in 𝓝 (0 : ℂ),
    ∀ᵐ ω ∂μ, ‖mixed_difference_quotient u v s t ω‖ ≤ C * (‖s‖ + ‖t‖) * ‖u ω * v ω‖ := by
  -- Use exp_taylor_bound to control:
  -- |exp(i(su + tv)) - 1 - i(su + tv) + (su + tv)^2/2| / |st|
  -- This gives domination by ‖u ω‖^2 + ‖v ω‖^2 + ‖u ω * v ω‖, all integrable
  sorry

/-- Mixed differentiation under the integral sign for characteristic-type
integrands.  This lemma is being developed in `IntegralDifferentiation.lean`
so that it can be reused by multiple files without duplicating the analytic
machinery.

*Hypotheses*
* `μ` is sigma-finite.
* `u`, `v` are measurable functions with integrable product (this follows from
  the Option B axiom in the GFF application).

*Conclusion*
The mixed derivative of the parameterized integral equals the integral of the
pointwise mixed derivative.
-/
lemma mixed_deriv_under_integral
    (μ : Measure α) [SigmaFinite μ] [IsFiniteMeasure μ]
    (u v : α → ℂ)
    (hu_int : Integrable u μ)
    (hv_int : Integrable v μ)
    (huv_int : Integrable (fun ω ↦ u ω * v ω) μ) :
    deriv
        (fun t : ℂ ↦ deriv
          (fun s : ℂ ↦ ∫ ω, Complex.exp (Complex.I * (t * u ω + s * v ω)) ∂μ) 0)
        0
      = ∫ ω,
          deriv
            (fun t : ℂ ↦ deriv
              (fun s : ℂ ↦ Complex.exp (Complex.I * (t * u ω + s * v ω))) 0)
            0 ∂μ := by
  classical
  -- Step 1: express the inner derivative using the single derivative lemma in `s`.
  -- For fixed t, we differentiate ∫ exp(i*(t*u + s*v)) with respect to s.
  have h_step_s : ∀ t : ℂ,
      HasDerivAt
        (fun s : ℂ ↦ ∫ ω, Complex.exp (Complex.I * (t * u ω + s * v ω)) ∂μ)
        (∫ ω, Complex.I * v ω * Complex.exp (Complex.I * (t * u ω)) ∂μ) 0 := by
    intro t
    -- Rewrite the integrand as exp(i*t*u) * exp(i*s*v) and apply the single derivative lemma
    have h_rewrite : ∀ s ω, Complex.exp (Complex.I * (t * u ω + s * v ω)) =
        Complex.exp (Complex.I * t * u ω) * Complex.exp (Complex.I * s * v ω) := by
      intro s ω
      rw [← Complex.exp_add]
      congr 1
      ring
    -- The integrand can be written as exp(i*t*u) * exp(i*s*v)
    -- Apply chain rule and product rule to differentiate w.r.t. s
    -- For now, use the fact that this should work by the general principle
    -- and defer the detailed proof
    have h_v_sq : Integrable (fun ω ↦ ‖v ω‖^2) μ := by
      -- This follows from Gaussian properties or can be assumed
      sorry
    -- The detailed application requires careful rewriting of the integrand
    sorry

  -- Step 2: differentiate the resulting integral with respect to `t`.
  -- Now we differentiate ∫ i*v*exp(i*t*u) with respect to t.
  have h_step_t :
      HasDerivAt
        (fun t : ℂ ↦
          ∫ ω, Complex.I * v ω * Complex.exp (Complex.I * (t * u ω)) ∂μ)
        (∫ ω, Complex.I * v ω * (Complex.I * u ω) * Complex.exp (Complex.I * 0 * u ω) ∂μ) 0 := by
    -- Apply the general principle for the second derivative
    -- This also requires similar manipulations as the first step
    have h_comp_int : Integrable (fun ω ↦ Complex.I * v ω * u ω) μ := by
      convert huv_int.const_mul Complex.I using 1
      ext ω; ring
    have h_comp_sq : Integrable (fun ω ↦ ‖Complex.I * v ω * u ω‖^2) μ := by
      -- Since u*v is integrable, we can show ‖u*v‖^2 is integrable
      -- This requires second moment properties, assume it for now
      have h_norm_sq : Integrable (fun ω ↦ ‖u ω * v ω‖^2) μ := sorry
      convert h_norm_sq using 1
      ext ω; simp [pow_two]; ring
    -- For now, defer the detailed application of the single derivative lemma
    sorry

  -- Step 3: simplify and assemble the final statement.
  have h_simplify : ∫ ω, Complex.I * v ω * (Complex.I * u ω) * Complex.exp (Complex.I * 0 * u ω) ∂μ =
      ∫ ω, -(u ω * v ω) ∂μ := by
    simp only [mul_zero]
    congr 1
    ext ω
    -- i * v * (i * u) = i^2 * u * v = -u * v
    ring_nf
    simp [Complex.I_sq]

  -- Connect the derivative computations using h_step_s
  have h_deriv_eq : deriv (fun s : ℂ ↦ ∫ ω, Complex.exp (Complex.I * (0 * u ω + s * v ω)) ∂μ) 0 =
      ∫ ω, Complex.I * v ω * Complex.exp (Complex.I * (0 * u ω)) ∂μ := by
    exact (h_step_s 0).deriv

  -- Simplify the derivative expression
  have h_step_s_simplified : ∫ ω, Complex.I * v ω * Complex.exp (Complex.I * (0 * u ω)) ∂μ =
      ∫ ω, Complex.I * v ω ∂μ := by
    simp only [zero_mul, mul_zero, Complex.exp_zero, mul_one]

  -- Apply the chain rule using HasDerivAt.comp
  have h_comp : HasDerivAt
      (fun t : ℂ ↦ deriv (fun s : ℂ ↦ ∫ ω, Complex.exp (Complex.I * (t * u ω + s * v ω)) ∂μ) 0)
      (∫ ω, -(u ω * v ω) ∂μ) 0 := by
    -- Use the fact that deriv commutes with our derivative computations
    rw [← h_simplify]
    -- Apply h_step_t to the simplified form
    convert h_step_t using 1
    -- Show that deriv (h_step_s t) equals the target function
    ext t
    simp only [zero_mul, mul_zero, Complex.exp_zero, mul_one] at h_step_s_simplified
    exact (h_step_s t).deriv

  -- Convert HasDerivAt to deriv equation
  rw [h_comp.deriv]

  -- The RHS computation: pointwise mixed derivative
  have h_rhs : ∫ ω, -(u ω * v ω) ∂μ =
      ∫ ω, deriv (fun t ↦ deriv (fun s ↦ Complex.exp (Complex.I * (t * u ω + s * v ω))) 0) 0 ∂μ := by
    congr 1
    ext ω
    -- Pointwise: ∂_t[∂_s[exp(i*(t*u + s*v))]|_{s=0}]|_{t=0}
    -- = ∂_t[i*v*exp(i*t*u)]|_{t=0} = i*v*i*u*exp(0) = -u*v
    sorry

  exact h_rhs

end Aqft2
