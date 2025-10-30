/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

## GFF OS3: Reflection Positivity for Gaussian Free Field

This file proves that the Gaussian Free Field satisfies the OS3 (Reflection Positivity)
axiom by combining the abstract framework from OS3.lean with the specific properties
of the free field covariance.

### Strategy:

The proof follows the factorization approach using `gaussian_quadratic_real_rewrite`:

1. **Matrix Factorization**: For the OS3 quadratic form `∑ᵢⱼ c̄ᵢ cⱼ Z[fᵢ - Θfⱼ]`,
   we factor it as `∑ᵢⱼ (Z[fᵢ]c̄ᵢ)(Z[fⱼ]cⱼ) exp(Rᵢⱼ)` where `Rᵢⱼ = Re S₂(Θfᵢ, fⱼ)`.

2. **Matrix Structure**: This has the form `M = (d d†) ∘ exp(R)` where:
   - `dᵢ = Z[fᵢ]` are the Gaussian values
   - `R` is the reflection positivity matrix
   - `∘` is the Hadamard (entrywise) product

3. **Positivity Chain**:
   - `R` is PSD by covariance reflection positivity (free field property)
   - `exp(R)` is PSD by entrywise exponential preservation (HadamardExp.lean)
   - `(d d†)` is rank-one PSD
   - Their Hadamard product is PSD by the Schur product theorem

4. **Conclusion**: The real part of the OS3 quadratic form is ≥ 0.

### Key Dependencies:
- `gaussian_quadratic_real_rewrite` from OS3.lean (factorization)
- Free field covariance reflection positivity from Covariance.lean
- Entrywise exponential preservation from HadamardExp.lean
- Schur product theorem from SchurProduct.lean
-/

import Aqft2.OS3
import Aqft2.Covariance
import Aqft2.HadamardExp
import Aqft2.SchurProduct
import Aqft2.GFFMconstruct
import Aqft2.GaussianFreeField
import Aqft2.ComplexTestFunction

--it is ok to use results in old.GFF_OS3 but these should be
--textually copied into this file to use them.
--import old.GFF_OS3

open MeasureTheory Complex Matrix
open TopologicalSpace SchwartzMap

noncomputable section

open scoped BigOperators
open Finset

/-! ## Gaussian Free Field Properties via Covariance Function

Instead of axiomatizing properties of the complex measure gaussianFreeField_free directly,
we prove them using the explicit covariance function freeCovarianceℂ and the connection
gff_two_point_equals_covarianceℂ_free. This avoids the complex Minlos construction.
-/

/-- The 2-point Schwinger function is bilinear via freeCovarianceℂ properties. -/
lemma covarianceBilinear_gaussianFreeField_free (m : ℝ) [Fact (0 < m)] :
  CovarianceBilinear (gaussianFreeField_free m) := by
  -- Reuse the bilinearity proved in `GaussianFreeField.lean`
  simpa using covarianceBilinear_gaussianFreeField m

/-- Time reflection invariance follows from freeCovarianceℂ properties. -/
lemma reflectionInvariance_gaussianFreeField_free (m : ℝ) [Fact (0 < m)] :
  OS3_ReflectionInvariance (gaussianFreeField_free m) := by
  -- Use gff_two_point_equals_covarianceℂ_free and reflection invariance of free covariance
  -- TODO: prove that freeCovarianceℂ is invariant under time reflection
  sorry

/-- Covariance reflection positivity follows from explicit free field properties. -/
lemma covarianceReflectionPositive_gaussianFreeField_free (m : ℝ) [Fact (0 < m)] :
  CovarianceReflectionPositive (gaussianFreeField_free m) := by
  -- Use gff_two_point_equals_covarianceℂ_free and reflection positivity of free covariance
  -- The free field covariance is reflection positive by construction
  -- TODO: prove using reflection_matrix_positivity in Covariance.lean
  sorry

/-- Entrywise exponential preserves PSD on real symmetric PSD matrices (finite index).
    Bridge lemma to be discharged using HadamardExp (Hadamard series) machinery. -/
private lemma entrywiseExp_posSemidef_of_posSemidef
  {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
  (hR : R.PosSemidef) : Matrix.PosSemidef (fun i j => Real.exp (R i j)) := by
  classical
  -- PSD for the Hadamard-series exponential
  have hS : (Aqft2.entrywiseExp_hadamardSeries (ι:=Fin n) R).PosSemidef :=
    Aqft2.posSemidef_entrywiseExp_hadamardSeries_of_posSemidef (ι:=Fin n) R hR
  -- Convert to PSD for the entrywise exponential
  have hExp : (Aqft2.entrywiseExp (ι:=Fin n) R).PosSemidef := by
    simpa [Aqft2.entrywiseExp_eq_hadamardSeries (ι:=Fin n) R] using hS
  -- Unfold the definition of entrywiseExp
  simpa [Aqft2.entrywiseExp] using hExp

/-- If E is a real symmetric PSD matrix, then for any complex vector y,
    the Hermitian quadratic form with kernel E is real and nonnegative. -/
private lemma complex_quadratic_nonneg_of_real_psd
  {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ)
  (hE : E.PosSemidef) (y : Fin n → ℂ) :
  0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (y i) * y j * (E i j : ℂ)).re := by
  classical
  -- Real and imaginary parts of y
  let a : Fin n → ℝ := fun i => (y i).re
  let b : Fin n → ℝ := fun i => (y i).im
  -- Compute the real part of each term using mul_re and conjugation identities
  have hre_term : ∀ i j,
      ((starRingEnd ℂ) (y i) * y j * (E i j : ℂ)).re
      = ((a i) * (a j) + (b i) * (b j)) * (E i j) := by
    intro i j
    have h1 : ((starRingEnd ℂ) (y i) * y j).re = (a i) * (a j) + (b i) * (b j) := by
      -- (conj yi * yj).re = ai*aj + bi*bj
      simp [a, b, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    -- For real r, (z * (r:ℂ)).re = z.re * r
    have h2 : (((starRingEnd ℂ) (y i) * y j) * (E i j : ℂ)).re
            = ((starRingEnd ℂ) (y i) * y j).re * (E i j) := by
      simp
    calc
      ((starRingEnd ℂ) (y i) * y j * (E i j : ℂ)).re
          = ((starRingEnd ℂ) (y i) * y j).re * (E i j) := h2
      _ = ((a i) * (a j) + (b i) * (b j)) * (E i j) := by simp [h1]
  -- Push real part through the finite sums and split into a- and b-contributions
  have h_rewrite :
      (∑ i, ∑ j, (starRingEnd ℂ) (y i) * y j * (E i j : ℂ)).re
      = (∑ i, ∑ j, (a i) * (a j) * (E i j)) + (∑ i, ∑ j, (b i) * (b j) * (E i j)) := by
    -- First, split the inner sum for each fixed i
    have h_each : ∀ i,
        (∑ j, ((starRingEnd ℂ) (y i) * y j * (E i j : ℂ))).re
        = (∑ j, (a i) * (a j) * (E i j)) + (∑ j, (b i) * (b j) * (E i j)) := by
      intro i
      calc
        (∑ j, ((starRingEnd ℂ) (y i) * y j * (E i j : ℂ))).re
            = ∑ j, ((starRingEnd ℂ) (y i) * y j * (E i j : ℂ)).re := by simp
        _ = ∑ j, (((a i) * (a j) + (b i) * (b j)) * (E i j)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj; simp [hre_term]
        _ = ∑ j, ((a i) * (a j) * (E i j) + (b i) * (b j) * (E i j)) := by
              have : (fun j => (((a i) * (a j) + (b i) * (b j)) * (E i j)))
                     = (fun j => (a i) * (a j) * (E i j) + (b i) * (b j) * (E i j)) := by
                funext j; ring
              simp [this]
        _ = (∑ j, (a i) * (a j) * (E i j)) + (∑ j, (b i) * (b j) * (E i j)) := by
              simp [Finset.sum_add_distrib]
    -- Now sum over i and distribute the outer sum
    calc
      (∑ i, ∑ j, (starRingEnd ℂ) (y i) * y j * (E i j : ℂ)).re
          = ∑ i, (∑ j, ((starRingEnd ℂ) (y i) * y j * (E i j : ℂ))).re := by simp
      _ = ∑ i, ((∑ j, (a i) * (a j) * (E i j)) + (∑ j, (b i) * (b j) * (E i j))) := by
            refine Finset.sum_congr rfl ?_; intro i hi; simpa using h_each i
      _ = (∑ i, ∑ j, (a i) * (a j) * (E i j)) + (∑ i, ∑ j, (b i) * (b j) * (E i j)) := by
            simp [Finset.sum_add_distrib]
  -- Identify each sum as a real quadratic form aᵀ E a and bᵀ E b
  have h_a' : ∑ i, ∑ j, (a i) * (a j) * (E i j) = ∑ i, ∑ j, a i * ((E i j) * a j) := by
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  have h_b' : ∑ i, ∑ j, (b i) * (b j) * (E i j) = ∑ i, ∑ j, b i * ((E i j) * b j) := by
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  have h_a'' : ∑ i, ∑ j, a i * ((E i j) * a j) = a ⬝ᵥ (E.mulVec a) := by
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
  have h_b'' : ∑ i, ∑ j, b i * ((E i j) * b j) = b ⬝ᵥ (E.mulVec b) := by
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
  have h_a := h_a'.trans h_a''
  have h_b := h_b'.trans h_b''
  -- PSD gives nonnegativity of each quadratic form
  have hQa : 0 ≤ a ⬝ᵥ (E.mulVec a) := hE.2 a
  have hQb : 0 ≤ b ⬝ᵥ (E.mulVec b) := hE.2 b
  -- Conclude
  have : 0 ≤ (a ⬝ᵥ (E.mulVec a)) + (b ⬝ᵥ (E.mulVec b)) := add_nonneg hQa hQb
  -- Rewrite back to the complex expression
  simpa [h_rewrite, h_a, h_b]

/-- Real-part identity: expand Re(∑ conj c_i c_j z_{ij}) into the split form
    with explicit Re/Im weights from c. -/
private lemma re_weighted_sum_eq_split
  {n : ℕ} (c : Fin n → ℂ) (z : Fin n → Fin n → ℂ) :
  (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * z i j).re
  = (∑ i, ∑ j,
        ((c i).re * (c j).re + (c i).im * (c j).im) * (z i j).re)
    - (∑ i, ∑ j,
        ((c i).re * (c j).im - (c i).im * (c j).re) * (z i j).im) := by
  classical
  -- termwise identity
  have hterm : ∀ i j,
      ((starRingEnd ℂ) (c i) * c j * z i j).re
      = ((c i).re * (c j).re + (c i).im * (c j).im) * (z i j).re
        - ((c i).re * (c j).im - (c i).im * (c j).re) * (z i j).im := by
    intro i j
    -- set w = conj(c_i) * c_j, z0 = z_ij
    set w : ℂ := (starRingEnd ℂ) (c i) * c j with hw
    set z0 : ℂ := z i j with hz
    have hw_re : w.re = (c i).re * (c j).re + (c i).im * (c j).im := by
      simp [hw, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have hw_im : w.im = (c i).re * (c j).im - (c i).im * (c j).re := by
      have h0 : w.im = (c i).re * (c j).im + (-(c i).im) * (c j).re := by
        simp [hw, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      simpa [sub_eq_add_neg] using h0
    have hprod : (w * z0).re = w.re * z0.re - w.im * z0.im := by
      simp [Complex.mul_re]
    calc
      ((starRingEnd ℂ) (c i) * c j * z i j).re
          = (w * z0).re := by simp [hw, hz]
      _ = w.re * z0.re - w.im * z0.im := hprod
      _ = ((c i).re * (c j).re + (c i).im * (c j).im) * z0.re
            - ((c i).re * (c j).im - (c i).im * (c j).re) * z0.im := by
            simp [hw_re, hw_im]
      _ = ((c i).re * (c j).re + (c i).im * (c j).im) * (z i j).re
            - ((c i).re * (c j).im - (c i).im * (c j).re) * (z i j).im := by
            simp [hz]
  -- sum both sides
  calc
    (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * z i j).re
        = ∑ i, (∑ j, ((starRingEnd ℂ) (c i) * c j * z i j)).re := by simp
    _ = ∑ i, ∑ j, ((starRingEnd ℂ) (c i) * c j * z i j).re := by simp
    _ = ∑ i, ∑ j,
          (((c i).re * (c j).re + (c i).im * (c j).im) * (z i j).re
            - ((c i).re * (c j).im - (c i).im * (c j).re) * (z i j).im) := by
          refine Finset.sum_congr rfl ?_
          intro i hi; refine Finset.sum_congr rfl ?_
          intro j hj; simp [hterm]
    _ = (∑ i, ∑ j, ((c i).re * (c j).re + (c i).im * (c j).im) * (z i j).re)
        - (∑ i, ∑ j, ((c i).re * (c j).im - (c i).im * (c j).re) * (z i j).im) := by
          simp [Finset.sum_sub_distrib]

/-- Matrix formulation of OS3 for the free field. -/
theorem gaussianFreeField_OS3_matrix (m : ℝ) [Fact (0 < m)]
  {n : ℕ} (f : Fin n → PositiveTimeTestFunction) (c : Fin n → ℂ) :
  let f_complex : Fin n → TestFunctionℂ := fun i => toComplex (f i).val
  0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
    GJGeneratingFunctionalℂ (gaussianFreeField_free m)
      (f_complex i - QFT.compTimeReflection (f_complex j))).re := by
  -- Abbreviations
  let dμ := gaussianFreeField_free m
  -- Gaussian/bilinear/reflection invariance assumptions (from old.GFF_OS3 axioms)
  have h_gaussian : isGaussianGJ dμ := by simpa [dμ] using isGaussianGJ_gaussianFreeField_free m
  have h_bilinear : CovarianceBilinear dμ := by simpa [dμ] using covarianceBilinear_gaussianFreeField_free m
  have h_reflectInv : OS3_ReflectionInvariance dμ := by simpa [dμ] using reflectionInvariance_gaussianFreeField_free m
  -- Rewrite via factorization lemma
  have h_factor := gaussian_quadratic_real_rewrite dμ h_gaussian h_bilinear h_reflectInv f c
  -- It suffices to show the RHS is ≥ 0
  have : 0 ≤ (∑ i, ∑ j,
        (starRingEnd ℂ) ((GJGeneratingFunctionalℂ dμ (f i).val) * c i)
        * ((GJGeneratingFunctionalℂ dμ (f j).val) * c j)
        * Real.exp ((SchwingerFunctionℂ₂ dμ (QFT.compTimeReflection (f i).val) (f j).val).re)
      ).re := by
    -- Define y_i := Z[f_i] * c_i and E_ij := exp(R_ij)
    let Z : Fin n → ℂ := fun i => GJGeneratingFunctionalℂ dμ (f i).val
    let y : Fin n → ℂ := fun i => Z i * c i
    let R : Matrix (Fin n) (Fin n) ℝ := fun i j =>
      (SchwingerFunctionℂ₂ dμ (QFT.compTimeReflection (f i).val) (f j).val).re
    let E : Matrix (Fin n) (Fin n) ℝ := fun i j => Real.exp (R i j)
    -- Covariance reflection positivity ⇒ R is PSD
    have h_reflectPos : CovarianceReflectionPositive dμ := by
      simpa [dμ] using covarianceReflectionPositive_gaussianFreeField_free m
    have hRpsd : R.PosSemidef := reflection_matrix_posSemidef dμ h_reflectPos f
    -- Entrywise exponential preserves PSD ⇒ E is PSD
    have hEpsd : E.PosSemidef := by
      simpa [E] using entrywiseExp_posSemidef_of_posSemidef R hRpsd
    -- Conclude nonnegativity of complex quadratic form with kernel E and vector y
    -- Note the sum matches exactly after unfolding
    simpa [y, Z, E, R, mul_comm, mul_left_comm, mul_assoc] using
      complex_quadratic_nonneg_of_real_psd E hEpsd y
  -- Transfer back to the LHS using h_factor: RHS.re = LHS.re
  rw [h_factor]
  exact this

/-! ## Main OS3 Theorem for Gaussian Free Field

We now prove that the Gaussian Free Field satisfies OS3 by combining
the abstract factorization framework with the specific properties of the free field.
-/

/-- **Main Theorem**: The Gaussian Free Field satisfies OS3 (Reflection Positivity).

    This theorem establishes that for any finite family of positive-time test functions
    and any complex coefficients, the OS3 inequality holds:

    Re ∑ᵢⱼ c̄ᵢ cⱼ Z[fᵢ - Θfⱼ] ≥ 0

    The proof uses the factorization approach: we rewrite the quadratic form as
    a Hadamard product of positive semidefinite matrices, then apply the Schur
    product theorem.
-/
theorem gaussianFreeField_satisfies_OS3 (m : ℝ) [Fact (0 < m)] :
  OS3_ReflectionPositivity (gaussianFreeField_free m) := by
  -- Directly use the matrix formulation proved below
  intro n f c
  simpa using gaussianFreeField_OS3_matrix m f c

end
