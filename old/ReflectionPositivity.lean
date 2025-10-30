import Aqft2.Covariance

open MeasureTheory Complex

noncomputable section

namespace Aqft2

open scoped ComplexConjugate

/-- Archived equivalence between the position and momentum formulations of reflection
positivity. This relies on analytic axioms that are not currently developed in the active
code path, so we keep the statement here for historical reference. -/
theorem reflection_positivity_position_momentum_equiv {m : ℝ} [Fact (0 < m)] :
	freeCovarianceReflectionPositive m ↔ freeCovarianceReflectionPositiveMomentum m := by
	constructor
	· -- Position → Momentum: Use Parseval's theorem
		intro h_pos f hf_support
		-- We need to show: 0 ≤ (momentum space integral).re
		-- We have from position space positivity: 0 ≤ (position space integral).re
		-- The key is that these are equal by Parseval's theorem and time reflection identity

		-- Apply Parseval's theorem to relate position and momentum space expressions
		have h_parseval : (∫ x, ∫ y, (QFT.compTimeReflection f) x * (freeCovariance m x y : ℂ) * f y ∂volume ∂volume).re
				= ∫ k, ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 * freePropagatorMomentum m k ∂volume :=
			parseval_time_reflection_covariance_explicit m f hf_support

		-- Apply the time reflection identity to connect momentum expressions
		have h_identity : (∫ k, (starRingEnd ℂ ((fourierTransform (QFT.compTimeReflection f)) k)) *
					 ↑(freePropagatorMomentum m k) *
					 ((fourierTransform f) k) ∂volume).re =
				 ∫ k, ‖(fourierTransform f) k‖^2 * freePropagatorMomentum m k ∂volume :=
			time_reflection_fourier_identity m f hf_support

		-- Since fourierTransform = SchwartzMap.fourierTransformCLM ℂ, the right sides are equal
		have h_eq : ∫ k, ‖(fourierTransform f) k‖^2 * freePropagatorMomentum m k ∂volume =
								∫ k, ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 * freePropagatorMomentum m k ∂volume := by
			-- Use simp to simplify the definitional equality
			simp only [fourierTransform]

		-- Combine all identities to show the momentum integral equals the position integral
		calc (∫ k, (starRingEnd ℂ ((fourierTransform (QFT.compTimeReflection f)) k)) *
							 ↑(freePropagatorMomentum m k) *
							 ((fourierTransform f) k) ∂volume).re
		_ = ∫ k, ‖(fourierTransform f) k‖^2 * freePropagatorMomentum m k ∂volume := h_identity
		_ = ∫ k, ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 * freePropagatorMomentum m k ∂volume := h_eq
		_ = (∫ x, ∫ y, (QFT.compTimeReflection f) x * (freeCovariance m x y : ℂ) * f y ∂volume ∂volume).re := h_parseval.symm
		_ ≥ 0 := h_pos f hf_support

	· -- Momentum → Position: Reverse application
		intro h_mom f hf_support
		-- We need to show: 0 ≤ (position space integral).re
		-- We have from momentum space positivity: 0 ≤ (momentum space integral).re
		-- Use the same equalities in reverse

		-- Apply Parseval's theorem
		have h_parseval : (∫ x, ∫ y, (QFT.compTimeReflection f) x * (freeCovariance m x y : ℂ) * f y ∂volume ∂volume).re
				= ∫ k, ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 * freePropagatorMomentum m k ∂volume :=
			parseval_time_reflection_covariance_explicit m f hf_support

		-- Apply the time reflection identity
		have h_identity : (∫ k, (starRingEnd ℂ ((fourierTransform (QFT.compTimeReflection f)) k)) *
					 ↑(freePropagatorMomentum m k) *
					 ((fourierTransform f) k) ∂volume).re =
				 ∫ k, ‖(fourierTransform f) k‖^2 * freePropagatorMomentum m k ∂volume :=
			time_reflection_fourier_identity m f hf_support

		-- Since fourierTransform = SchwartzMap.fourierTransformCLM ℂ, the right sides are equal
		have h_eq : ∫ k, ‖(fourierTransform f) k‖^2 * freePropagatorMomentum m k ∂volume =
								∫ k, ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 * freePropagatorMomentum m k ∂volume := by
			-- Use simp to simplify the definitional equality
			simp only [fourierTransform]

		-- Combine to show position integral equals momentum integral, which is non-negative
		calc (∫ x, ∫ y, (QFT.compTimeReflection f) x * (freeCovariance m x y : ℂ) * f y ∂volume ∂volume).re
		_ = ∫ k, ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 * freePropagatorMomentum m k ∂volume := h_parseval
		_ = ∫ k, ‖(fourierTransform f) k‖^2 * freePropagatorMomentum m k ∂volume := h_eq.symm
		_ = (∫ k, (starRingEnd ℂ ((fourierTransform (QFT.compTimeReflection f)) k)) *
						 ↑(freePropagatorMomentum m k) *
						 ((fourierTransform f) k) ∂volume).re := h_identity.symm
		_ ≥ 0 := h_mom f hf_support

end Aqft2
