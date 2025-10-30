/-
Alternate OS0 proofs for Gaussian Free Field and general Gaussian measures.
Moved from Aqft2/GaussianFreeField.lean.
-/

import Aqft2.GaussianFreeField

open MeasureTheory Complex
open TopologicalSpace
open scoped BigOperators
open Finset

noncomputable section

/-- Alternate proof of OS0 (analyticity) for a general Gaussian measure.
    Sketches a finite-dimensional reduction via cylindrical projections. -/
theorem gaussian_satisfies_OS0_alt
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_gaussian : isGaussianGJ dμ_config)
  (h_bilinear : CovarianceBilinear dμ_config)
  : OS0_Analyticity dμ_config := by
  intro n J
  -- Gaussian form
  have h_form : ∀ (f : TestFunctionℂ),
      GJGeneratingFunctionalℂ dμ_config f =
        Complex.exp (-(1/2 : ℂ) * SchwingerFunctionℂ₂ dμ_config f f) :=
    h_gaussian.2
  -- Rewrite the generating functional using Gaussian form
  have h_rewrite : (fun z : Fin n → ℂ => GJGeneratingFunctionalℂ dμ_config (∑ i, z i • J i)) =
                   (fun z => Complex.exp (-(1/2 : ℂ) *
                     SchwingerFunctionℂ₂ dμ_config (∑ i, z i • J i) (∑ i, z i • J i))) := by
    funext z; exact h_form (∑ i, z i • J i)
  -- Show exp(-½ * quadratic_form) is analytic
  rw [h_rewrite]
  apply AnalyticOn.cexp
  apply AnalyticOn.mul
  · exact analyticOn_const
  ·
    -- Expand quadratic form via bilinearity as in gaussian_satisfies_OS0
    let B := GJcov_bilin dμ_config h_bilinear
    have h_expansion :
      (fun z : Fin n → ℂ => SchwingerFunctionℂ₂ dμ_config (∑ i, z i • J i) (∑ i, z i • J i)) =
      (fun z => ∑ i, ∑ j, z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) := by
      funext z
      have h_eq : B (∑ i, z i • J i) (∑ i, z i • J i) =
                  SchwingerFunctionℂ₂ dμ_config (∑ i, z i • J i) (∑ i, z i • J i) := rfl
      rw [← h_eq]
      exact bilin_sum_sum B n J z

    -- Reduce to a finite sum of monomials, each analytic
    rw [h_expansion]

    have h_sum_analytic : AnalyticOnNhd ℂ
      (fun z : Fin n → ℂ => ∑ i, ∑ j, z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) Set.univ := by
      have h_monomial : ∀ i j, AnalyticOnNhd ℂ
        (fun z : Fin n → ℂ => z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) Set.univ := by
        intro i j
        have h_factor : (fun z : Fin n → ℂ => z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) =
                        (fun z => SchwingerFunctionℂ₂ dμ_config (J i) (J j) * (z i * z j)) := by
          funext z; ring
        rw [h_factor]
        apply AnalyticOnNhd.mul
        · exact analyticOnNhd_const
        ·
          have coord_i : AnalyticOnNhd ℂ (fun z : Fin n → ℂ => z i) Set.univ :=
            (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticOnNhd _
          have coord_j : AnalyticOnNhd ℂ (fun z : Fin n → ℂ => z j) Set.univ :=
            (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).analyticOnNhd _
          exact AnalyticOnNhd.mul coord_i coord_j

      have h_outer_sum : ∀ i, AnalyticOnNhd ℂ
        (fun z : Fin n → ℂ => ∑ j, z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) Set.univ := by
        intro i
        have : (fun z : Fin n → ℂ => ∑ j, z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) =
               (∑ j : Fin n, fun z => z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) := by
          ext z; simp [Finset.sum_apply]
        rw [this]
        apply Finset.analyticOnNhd_sum
        intro j _; exact h_monomial i j

      have : (fun z : Fin n → ℂ => ∑ i, ∑ j, z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) =
             (∑ i : Fin n, fun z => ∑ j, z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) := by
        ext z; simp [Finset.sum_apply]
      rw [this]
      apply Finset.analyticOnNhd_sum
      intro i _
      exact h_outer_sum i

    exact h_sum_analytic.analyticOn

/-- Alternate proof that the Gaussian Free Field satisfies OS0 (Analyticity).
    Documents the finite-dimensional strategy via FiniteDim.gaussian_mgf_entire. -/
theorem gaussianFreeField_satisfies_OS0_alt (m : ℝ) [Fact (0 < m)] :
  OS0_Analyticity (gaussianFreeField_free m) := by
  exact gaussian_satisfies_OS0_alt (gaussianFreeField_free m)
    (isGaussianGJ_gaussianFreeField_free m)
    (covarianceBilinear_gaussianFreeField m)
