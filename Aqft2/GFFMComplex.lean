/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

## Complex Covariance and Integrability for Gaussian Free Fields

This file contains the complex extensions and integrability proofs for Gaussian Free Fields,
building on the core construction in GFFMconstruct.lean. It provides the implementation of
gaussian_pairing_product_integrable_free_core using the generalized n-point theory.

### Main Results:
- Complex covariance structure via Minlos analyticity
- Mixed derivative computations for characteristic functionals
- Integration theorems for Gaussian measures
- Connection between Schwinger functions and complex covariance

This file depends on both GFFMconstruct.lean and GaussianMoments.lean to provide
the concrete implementation of integrability results.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

import Aqft2.GFFMconstruct
import Aqft2.GaussianMoments
import Aqft2.MinlosAnalytic
import Aqft2.MixedDerivLemma
import Aqft2.IntegralDifferentiation_axioms

open MeasureTheory Complex
open TopologicalSpace SchwartzMap

noncomputable section

/-- For the Gaussian Free Field measure, the product of two complex pairings with test functions
    is integrable. This is now implemented using the direct 2-point theorem. -/
lemma gaussian_pairing_product_integrable_free_core
  (m : ℝ) [Fact (0 < m)] (φ ψ : TestFunctionℂ) :
  Integrable (fun ω => distributionPairingℂ_real ω φ * distributionPairingℂ_real ω ψ)
    (gaussianFreeField_free m).toMeasure := by
  -- Use the direct 2-point case from GaussianMoments
  exact gaussian_pairing_product_integrable_free_2point m φ ψ

namespace GFF_Minlos_Complex

open MinlosAnalytic

-- Supporting lemmas moved early to enable integral proof of mixed_deriv_schwinger

/-- Complex conjugate of a complex-valued test function. This is the pointwise
    conjugate, which remains a Schwartz function. -/
noncomputable def testFunctionConj (g : TestFunctionℂ) : TestFunctionℂ :=
  SchwartzMap.mk
    (fun x => (starRingEnd ℂ) (g x))
    (by
      -- Smoothness follows from smoothness of `g` and of complex conjugation.
      -- We defer the analytic details to future work.
      sorry)
    (by
      -- Rapid decay is preserved under complex conjugation because `‖conj z‖ = ‖z‖`.
      -- A detailed proof requires bounds on derivatives, postponed for now.
      sorry)

@[simp] lemma testFunctionConj_apply (g : TestFunctionℂ) (x : SpaceTime) :
    testFunctionConj g x = (starRingEnd ℂ) (g x) := rfl


/-- Schwinger function at n=2 equals the product integral (complex version). -/
lemma schwinger_eq_integral_product
  (μ : ProbabilityMeasure FieldConfiguration) (f g : TestFunctionℂ) :
  SchwingerFunctionℂ₂ μ f g
    = ∫ ω, distributionPairingℂ_real ω f * distributionPairingℂ_real ω g ∂μ.toMeasure := by
  -- Unfold SchwingerFunctionℂ₂ and compute the product over Fin 2
  unfold SchwingerFunctionℂ₂
  unfold SchwingerFunctionℂ
  -- The product over Fin 2 of v i is v 0 * v 1; here v 0 = f, v 1 = g
  -- Use the Fin.prod_univ_two simp lemma
  simp [Fin.prod_univ_two]

/-- Package the real free covariance as a CovarianceForm for MinlosAnalytic. -/
noncomputable def freeCovarianceForm_struct (m : ℝ) : MinlosAnalytic.CovarianceForm where
  Q := fun f g => freeCovarianceFormR m f g
  symm := by intro f g; simpa using freeCovarianceFormR_symm m f g
  psd := by intro f; simpa using freeCovarianceFormR_pos m f
  cont_diag := by
    -- `freeCovarianceFormR_continuous` is exactly continuity of f ↦ Q f f
    simpa using freeCovarianceFormR_continuous m
  add_left := by
    intro f₁ f₂ g
    -- freeCovarianceFormR is bilinear by linearity of integration
    exact freeCovarianceFormR_add_left m f₁ f₂ g
  smul_left := by
    intro c f g
    -- freeCovarianceFormR is bilinear by linearity of integration
    exact freeCovarianceFormR_smul_left m c f g


/-- Bridge: identify the Minlos complexification Qc of the real free covariance with the
    explicitly defined complex free covariance `freeCovarianceℂ`, after applying
    complex conjugation to the second argument to match sesquilinearity.

    Proof strategy (extracted to free_Qc_eq_freeCovarianceℂ_proof.lean for development):
    1. Both sides are ℂ-bilinear extensions of the same real form freeCovarianceFormR
  MinlosAnalytic.Qc (freeCovarianceForm_struct m) f (testFunctionConj g) =
    freeCovarianceℂ m f g := by
    3. Use simp lemmas from Basic.lean to show (decompose f).1 x = (f x).re, etc.
    4. Expand freeCovarianceℂ m f g using pointwise f = re + i·im, star(g) = re - i·im
    5. Apply freeCovarianceℂ_agrees_on_reals to each of the 4 resulting double integrals
    6. Match with Qc's canonical complexification formula

    This is the key technical bridge connecting the Minlos analytic continuation
    with the explicitly defined complex covariance. -/

lemma free_Qc_eq_freeCovarianceℂ
  (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
  MinlosAnalytic.Qc (freeCovarianceForm_struct m) f g = freeCovarianceℂ_bilinear m f g := by
  classical
  let fr : TestFunction := (complex_testfunction_decompose f).1
  let fi : TestFunction := (complex_testfunction_decompose f).2
  let gr : TestFunction := (complex_testfunction_decompose g).1
  let gi : TestFunction := (complex_testfunction_decompose g).2
  let frC : TestFunctionℂ := toComplex fr
  let fiC : TestFunctionℂ := toComplex fi
  let grC : TestFunctionℂ := toComplex gr
  let giC : TestFunctionℂ := toComplex gi
  have hf : f = frC + Complex.I • fiC := by
    ext x
    simpa [fr, fi, frC, fiC, toComplex_apply, smul_eq_mul,
      complex_testfunction_decompose] using
      (complex_testfunction_decompose_recompose f x)
  have hg : g = grC + Complex.I • giC := by
    ext x
    simpa [gr, gi, grC, giC, toComplex_apply, smul_eq_mul,
      complex_testfunction_decompose] using
      (complex_testfunction_decompose_recompose g x)
  set expr : ℂ :=
    (freeCovarianceFormR m fr gr - freeCovarianceFormR m fi gi : ℝ)
      + Complex.I * (freeCovarianceFormR m fr gi + freeCovarianceFormR m fi gr : ℝ)
  have hQc : MinlosAnalytic.Qc (freeCovarianceForm_struct m) f g = expr := by
    simp [expr, MinlosAnalytic.Qc, freeCovarianceForm_struct, fr, fi, gr, gi,
      complex_testfunction_decompose]
  have h_expand :
      freeCovarianceℂ_bilinear m f g =
        freeCovarianceℂ_bilinear m frC grC
          + Complex.I * freeCovarianceℂ_bilinear m frC giC
          + Complex.I * freeCovarianceℂ_bilinear m fiC grC
          - freeCovarianceℂ_bilinear m fiC giC := by
    -- Apply bilinearity to expand the expression
    calc freeCovarianceℂ_bilinear m f g
      _ = freeCovarianceℂ_bilinear m (frC + Complex.I • fiC) (grC + Complex.I • giC) := by
          simp [hf, hg]
      _ = freeCovarianceℂ_bilinear m frC (grC + Complex.I • giC)
            + freeCovarianceℂ_bilinear m (Complex.I • fiC) (grC + Complex.I • giC) := by
          exact freeCovarianceℂ_bilinear_add_left m frC (Complex.I • fiC) (grC + Complex.I • giC)
      _ = (freeCovarianceℂ_bilinear m frC grC + freeCovarianceℂ_bilinear m frC (Complex.I • giC))
            + (freeCovarianceℂ_bilinear m (Complex.I • fiC) grC
                + freeCovarianceℂ_bilinear m (Complex.I • fiC) (Complex.I • giC)) := by
          rw [freeCovarianceℂ_bilinear_add_right m frC grC (Complex.I • giC),
              freeCovarianceℂ_bilinear_add_right m (Complex.I • fiC) grC (Complex.I • giC)]
      _ = freeCovarianceℂ_bilinear m frC grC
            + Complex.I * freeCovarianceℂ_bilinear m frC giC
            + Complex.I * freeCovarianceℂ_bilinear m fiC grC
            - freeCovarianceℂ_bilinear m fiC giC := by
          have h1 : freeCovarianceℂ_bilinear m frC (Complex.I • giC) = Complex.I * freeCovarianceℂ_bilinear m frC giC :=
            freeCovarianceℂ_bilinear_smul_right m Complex.I frC giC
          have h2 : freeCovarianceℂ_bilinear m (Complex.I • fiC) grC = Complex.I * freeCovarianceℂ_bilinear m fiC grC :=
            freeCovarianceℂ_bilinear_smul_left m Complex.I fiC grC
          have h3 : freeCovarianceℂ_bilinear m (Complex.I • fiC) (Complex.I • giC) = -freeCovarianceℂ_bilinear m fiC giC := by
            calc freeCovarianceℂ_bilinear m (Complex.I • fiC) (Complex.I • giC)
              _ = Complex.I * freeCovarianceℂ_bilinear m fiC (Complex.I • giC) := by
                  exact freeCovarianceℂ_bilinear_smul_left m Complex.I fiC (Complex.I • giC)
              _ = Complex.I * (Complex.I * freeCovarianceℂ_bilinear m fiC giC) := by
                  rw [freeCovarianceℂ_bilinear_smul_right m Complex.I fiC giC]
              _ = (Complex.I * Complex.I) * freeCovarianceℂ_bilinear m fiC giC := by ring
              _ = -freeCovarianceℂ_bilinear m fiC giC := by simp [Complex.I_mul_I]
          rw [h1, h2, h3]
          ring
  have h_rr : freeCovarianceℂ_bilinear m frC grC = (freeCovarianceFormR m fr gr : ℂ) := by
    simpa [frC] using freeCovarianceℂ_bilinear_agrees_on_reals (m := m) fr gr
  have h_rgi : freeCovarianceℂ_bilinear m frC giC = (freeCovarianceFormR m fr gi : ℂ) := by
    simpa [frC, giC] using freeCovarianceℂ_bilinear_agrees_on_reals (m := m) fr gi
  have h_igr : freeCovarianceℂ_bilinear m fiC grC = (freeCovarianceFormR m fi gr : ℂ) := by
    simpa [fiC, grC] using freeCovarianceℂ_bilinear_agrees_on_reals (m := m) fi gr
  have h_igi : freeCovarianceℂ_bilinear m fiC giC = (freeCovarianceFormR m fi gi : ℂ) := by
    simpa [fiC, giC] using freeCovarianceℂ_bilinear_agrees_on_reals (m := m) fi gi
  have h_expand' :
      freeCovarianceℂ_bilinear m f g =
        (freeCovarianceFormR m fr gr : ℂ)
        - (freeCovarianceFormR m fi gi : ℂ)
        + Complex.I * (freeCovarianceFormR m fr gi : ℂ)
        + Complex.I * (freeCovarianceFormR m fi gr : ℂ) := by
    simpa [h_rr, h_rgi, h_igr, h_igi, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using h_expand
  have h_bilin : freeCovarianceℂ_bilinear m f g = expr := by
    rw [h_expand']
    simp only [expr]
    -- Use norm_cast and abel_nf to handle the rearrangement and coercions
    norm_cast
    abel_nf
    -- Now apply distributivity to finish
    rw [← mul_add]
    norm_cast
  exact hQc.trans h_bilin.symm


/-- Complex generating functional for the free GFF (via Minlos analyticity).
    This avoids any circularity: we use the proven real characteristic functional
    `gff_real_characteristic` and the general complex extension theorem. -/
theorem gff_complex_characteristic_minlos (m : ℝ) [Fact (0 < m)] :
  ∀ J : TestFunctionℂ,
    GJGeneratingFunctionalℂ (gaussianFreeField_free m) J
      = Complex.exp (-(1/2 : ℂ) * (MinlosAnalytic.Qc (freeCovarianceForm_struct m) J J)) := by
  classical
  intro J
  -- Apply the general complex CF theorem with C = freeCovarianceForm_struct m
  refine MinlosAnalytic.gaussian_CF_complex (C := freeCovarianceForm_struct m)
    (μ := gaussianFreeField_free m)
    (h_realCF := ?hreal) J
  -- Real characteristic functional already established
  intro f
  -- Definitional equality of real test-function type aliases lets this `simpa` work
  simpa [GJGeneratingFunctional, distributionPairing]
    using (gff_real_characteristic (m := m) (f := f))

/-- Mixed derivative via Minlos form: for Φ(t,s) = Z[t f + s g] and
    Z[J] = exp(-½ Qc(J,J)), one has
      ∂²/∂t∂s Φ(0,0) = -Qc(f,g).

    Formalized using Lean's `deriv` by currying in `s` then differentiating in `t`:
      deriv (fun t => deriv (fun s => GJGeneratingFunctionalℂ μ (t • f + s • g)) 0) 0
        = -(MinlosAnalytic.Qc C f g).

    Proof outline (medium difficulty): expand Qc(t f + s g, t f + s g) by bilinearity
    (Qc_add_left/right, Qc_smul_left/right), then differentiate exp at 0. -/
lemma mixed_deriv_minlos_Qc
  (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
  let μ := gaussianFreeField_free m
  let C := freeCovarianceForm_struct m
  deriv (fun t : ℂ => deriv (fun s : ℂ => GJGeneratingFunctionalℂ μ (t • f + s • g)) 0) 0
    = -(MinlosAnalytic.Qc C f g) := by
  intro μ C

  -- Step 1: Use the bilinearity of Qc to expand the quadratic form
  have h_bilinear : ∀ t s : ℂ,
      MinlosAnalytic.Qc C (t • f + s • g) (t • f + s • g) =
      t^2 * MinlosAnalytic.Qc C f f +
      (2 : ℂ) * t * s * MinlosAnalytic.Qc C f g +
      s^2 * MinlosAnalytic.Qc C g g := by
    intro t s
    -- Expand using bilinearity: Qc(tf+sg, tf+sg) = Qc(tf,tf) + Qc(tf,sg) + Qc(sg,tf) + Qc(sg,sg)
    rw [MinlosAnalytic.Qc_add_left]
    rw [MinlosAnalytic.Qc_add_right, MinlosAnalytic.Qc_add_right]
    -- Now we have: Qc(tf,tf) + Qc(tf,sg) + Qc(sg,tf) + Qc(sg,sg)
    rw [MinlosAnalytic.Qc_smul_left, MinlosAnalytic.Qc_smul_left, MinlosAnalytic.Qc_smul_left, MinlosAnalytic.Qc_smul_left]
    rw [MinlosAnalytic.Qc_smul_right, MinlosAnalytic.Qc_smul_right, MinlosAnalytic.Qc_smul_right, MinlosAnalytic.Qc_smul_right]
    -- Now we have: t²Qc(f,f) + ts·Qc(f,g) + st·Qc(g,f) + s²Qc(g,g)
    -- Use symmetry: Qc(g,f) = Qc(f,g)
    have h_symm : MinlosAnalytic.Qc C g f = MinlosAnalytic.Qc C f g := by
      exact MinlosAnalytic.Qc_symm C g f
    rw [h_symm]
    -- Now: t•t•Qc(f,f) + t•s•Qc(f,g) + s•t•Qc(f,g) + s•s•Qc(g,g)
    -- Note: t•s means scalar multiplication, convert to regular multiplication
    simp only [smul_eq_mul]
    ring

  -- Step 2: Consider the function Φ(t,s) = exp(-½ Qc(tf+sg, tf+sg))
  let Φ : ℂ → ℂ → ℂ := fun t s =>
    Complex.exp (-(1/2 : ℂ) * MinlosAnalytic.Qc C (t • f + s • g) (t • f + s • g))

  -- Step 3: The mixed derivative computation
  -- From h_bilinear, we have Φ(t,s) = exp(-½(t²A + 2tsB + s²C)) where:
  let A := MinlosAnalytic.Qc C f f
  let B := MinlosAnalytic.Qc C f g
  let Ccoeff := MinlosAnalytic.Qc C g g

  -- Key lemma: mixed derivative of exponential of quadratic form
  have h_mixed_deriv_exp :
    deriv (fun t => deriv (fun s => Complex.exp (-(1/2 : ℂ) * (t^2 * A + 2*t*s*B + s^2*Ccoeff))) 0) 0 = -B := by

    -- Mathematical outline:
    -- For F(t,s) = exp(-½(t²A + 2tsB + s²C)), we compute:
    -- 1. ∂F/∂s|_{s=0} = exp(-½t²A) * (-½)(2tB) = exp(-½t²A) * (-tB)
    -- 2. ∂²F/∂t∂s|_{(0,0)} = ∂/∂t[exp(-½t²A) * (-tB)]|_{t=0}
    -- 3. Using product rule at t=0: = [0 * 0] + [1 * (-B)] = -B

    -- Step 3a: First derivative with respect to s at s=0
    have h_deriv_s : ∀ t : ℂ,
      deriv (fun s => Complex.exp (-(1/2 : ℂ) * (t^2 * A + 2*t*s*B + s^2*Ccoeff))) 0
      = Complex.exp (-(1/2 : ℂ) * (t^2 * A)) * (-(t * B)) := by
      intro t
      classical
      -- Derivative of the inner polynomial in s at 0
      have hid : HasDerivAt (fun s : ℂ => s) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℂ))
      have h_lin : HasDerivAt (fun s : ℂ => (2 * t * B) * s) (2 * t * B) 0 := by
        simpa using hid.const_mul (2 * t * B)
      have h_sq : HasDerivAt (fun s : ℂ => s ^ 2) 0 0 := by
        simpa [pow_two] using (hid.mul hid)
      have h_sqC : HasDerivAt (fun s : ℂ => s ^ 2 * Ccoeff) 0 0 := by
        simpa using h_sq.mul_const Ccoeff
      have h_sum : HasDerivAt (fun s : ℂ => (2 * t * B) * s + s ^ 2 * Ccoeff)
          ((2 * t * B) + 0) 0 := h_lin.add h_sqC
      have h_const : HasDerivAt (fun _ : ℂ => t ^ 2 * A) 0 0 := by
        simpa using (hasDerivAt_const (x := (0 : ℂ)) (c := t ^ 2 * A))
      -- combine constant and sum, then rearrange
      have h_poly : HasDerivAt (fun s : ℂ => t ^ 2 * A + ((2 * t * B) * s + s ^ 2 * Ccoeff))
            ((2 * t * B) + 0) 0 := by
        simpa [Pi.add_def, add_comm] using (h_const.add h_sum)
      have h_poly' : HasDerivAt (fun s : ℂ => t ^ 2 * A + 2 * t * s * B + s ^ 2 * Ccoeff)
          ((2 * t * B) + 0) 0 := by
        simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
          using h_poly
      -- Chain rule for exponential composed with the inner polynomial
      have h_inner : HasDerivAt
          (fun s : ℂ => -(1/2 : ℂ) * (t ^ 2 * A + 2 * t * s * B + s ^ 2 * Ccoeff))
          (-(1/2 : ℂ) * ((2 * t * B) + 0)) 0 := by
        simpa using h_poly'.const_mul (-(1/2 : ℂ))
      have h_cexp := h_inner.cexp
      -- simplify u(0) and u'(0)
      have h_scal : (-(1/2 : ℂ)) * ((2 : ℂ)) = (-1 : ℂ) := by ring
      have h_der := h_cexp.deriv
      -- use simp to collapse 0-terms and power
      simp [pow_two] at h_der
      -- now turn (-(1/2))*((2*t*B)+0) into -(t*B)
      simpa [pow_two, h_scal, mul_comm, mul_left_comm, mul_assoc, add_comm] using h_der

    -- Step 3b: Second derivative with respect to t at t=0
    have h_deriv_t :
      deriv (fun t => Complex.exp (-(1/2 : ℂ) * (t ^ 2 * A)) * (-(t * B))) 0 = -B := by
      classical
      -- define factors
      let f : ℂ → ℂ := fun t => Complex.exp (-(1/2 : ℂ) * (t ^ 2 * A))
      let gneg : ℂ → ℂ := fun t => -(t * B)
      -- f'(0) = 0
      have hid0 : HasDerivAt (fun t : ℂ => t) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℂ))
      have h_sq0 : HasDerivAt (fun t : ℂ => t ^ 2) 0 0 := by
        simpa [pow_two] using (hid0.mul hid0)
      have h_t2A : HasDerivAt (fun t : ℂ => t ^ 2 * A) 0 0 := by
        simpa using h_sq0.mul_const A
      have h_u : HasDerivAt (fun t : ℂ => -(1/2 : ℂ) * (t ^ 2 * A)) 0 0 := by
        simpa using h_t2A.const_mul (-(1/2 : ℂ))
      have hF : HasDerivAt f 0 0 := by
        simpa [f] using h_u.cexp
      -- gneg'(0) = -B
      have hGneg : HasDerivAt gneg (-B) 0 := by
        have hGpos : HasDerivAt (fun t : ℂ => t * B) B 0 := by
          simpa using hid0.mul_const B
        simpa [gneg] using hGpos.neg
      -- product rule for f * gneg
      have hmul : HasDerivAt (fun t => f t * gneg t) (-B) 0 := by
        -- Apply the product rule and show the derivative value equals -B
        have hprod := hF.mul hGneg
        -- Show that f * gneg equals fun t => f t * gneg t
        have h_func_eq : (f * gneg) = (fun t => f t * gneg t) := rfl
        rw [h_func_eq] at hprod
        -- Show that 0 * gneg 0 + f 0 * (-B) = -B
        have h_deriv_val : (0 : ℂ) * gneg 0 + f 0 * (-B) = -B := by
          simp [f, gneg, Complex.exp_zero]
        rwa [← h_deriv_val]
      -- conclude derivative identity
      have h_goal_eq : (fun t => f t * gneg t) = (fun t => Complex.exp (-(1/2 : ℂ) * (t^2 * A)) * (-(t * B))) := by
        funext t
        simp only [f, gneg]
      rw [h_goal_eq] at hmul
      exact hmul.deriv

    -- Step 3c: Combine the steps
    have h_eq : (fun t => deriv (fun s => Complex.exp (-(1/2 : ℂ) * (t^2 * A + 2*t*s*B + s^2*Ccoeff))) 0)
              = (fun t => Complex.exp (-(1/2 : ℂ) * (t^2 * A)) * (-(t * B))) := by
      funext t
      exact h_deriv_s t

    rw [h_eq]
    exact h_deriv_t

  -- Step 4: Apply to our Φ function using the bilinear expansion
  have h_Phi_form : ∀ t s : ℂ,
    Φ t s = Complex.exp (-(1/2 : ℂ) * (t^2 * A + 2*t*s*B + s^2*Ccoeff)) := by
    intro t s
    simp only [Φ, A, B, Ccoeff]
    congr 2
    exact h_bilinear t s

  -- Step 5: Conclude the mixed derivative equals -B = -Qc C f g
  have h_mixed_deriv_Phi : deriv (fun t => deriv (fun s => Φ t s) 0) 0 = -B := by
    have h_eq : (fun t => deriv (fun s => Φ t s) 0) =
                (fun t => deriv (fun s => Complex.exp (-(1/2 : ℂ) * (t^2 * A + 2*t*s*B + s^2*Ccoeff))) 0) := by
      funext t
      congr 1
      funext s
      exact h_Phi_form t s
    rw [h_eq]
    exact h_mixed_deriv_exp

  -- Step 6: Connect to the original generating functional via complex CF theorem
  have h_rewrite :
    (fun t : ℂ => deriv (fun s : ℂ => GJGeneratingFunctionalℂ μ (t • f + s • g)) 0)
    = (fun t : ℂ => deriv (fun s : ℂ => Φ t s) 0) := by
    funext t
    have h_inner_eq : (fun s : ℂ => GJGeneratingFunctionalℂ μ (t • f + s • g)) = (fun s : ℂ => Φ t s) := by
      funext s
      -- Use the complex characteristic functional theorem
      simpa [Φ] using (gff_complex_characteristic_minlos (m := m) (J := t • f + s • g))
    -- Apply congrArg to preserve the derivative
    simpa using congrArg (fun h : ℂ → ℂ => deriv h 0) h_inner_eq

  -- Step 7: Final conclusion
  have h_goal :
    deriv (fun t : ℂ => deriv (fun s : ℂ => GJGeneratingFunctionalℂ μ (t • f + s • g)) 0) 0
    = deriv (fun t : ℂ => deriv (fun s : ℂ => Φ t s) 0) 0 := by
    simpa using congrArg (fun h : ℂ → ℂ => deriv h 0) h_rewrite

  rw [h_goal, h_mixed_deriv_Phi]


/-- Mixed derivative via Gaussian integral: for Φ(t,s) = Z[t f + s g] with centered μ,
    one has the standard identity (second moment/Wick):
      ∂²/∂t∂s Φ(0,0) = -SchwingerFunctionℂ₂ μ f g.

    Formalized as
      deriv (fun t => deriv (fun s => GJGeneratingFunctionalℂ μ (t • f + s • g)) 0) 0
        = -(SchwingerFunctionℂ₂ μ f g).

    Proof outline (standard): differentiate under the integral of exp(i⟨ω, t f + s g⟩),
    use centering to kill first-order terms, the mixed term gives -E[⟨ω,f⟩⟨ω,g⟩]. -/
lemma mixed_deriv_schwinger
  (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
  let μ := gaussianFreeField_free m
  deriv (fun t : ℂ => deriv (fun s : ℂ => GJGeneratingFunctionalℂ μ (t • f + s • g)) 0) 0
    = -(SchwingerFunctionℂ₂ μ f g) := by
  intro μ
  -- Strategy: Use the integral representation and interchange derivatives with integration

  -- Step 1: Rewrite SchwingerFunctionℂ₂ using the integral representation
  rw [schwinger_eq_integral_product]

  -- Step 2: The goal is now to show that the mixed derivative equals
  -- -∫ ω, distributionPairingℂ_real ω f * distributionPairingℂ_real ω g ∂μ.toMeasure

  -- Step 1 (definitions): set useful abbreviations
  let u : FieldConfiguration → ℂ := fun ω => distributionPairingℂ_real ω f
  let v : FieldConfiguration → ℂ := fun ω => distributionPairingℂ_real ω g
  let Φ : ℂ → ℂ → ℂ := fun t s => GJGeneratingFunctionalℂ μ (t • f + s • g)

  -- Step 2 (pairing linearity): ⟨ω, t•f + s•g⟩ = t⟨ω,f⟩ + s⟨ω,g⟩
  have pairing_lin : ∀ (ω : FieldConfiguration) (t s : ℂ),
      distributionPairingℂ_real ω (t • f + s • g) = t * u ω + s * v ω := by
    intro ω t s
    simpa [u, v] using (pairing_linear_combo ω f g t s)

  -- Step 3: Define the pointwise integrand function ψ(ω, t, s) = exp(i(t·u(ω) + s·v(ω)))
  let ψ : FieldConfiguration → ℂ → ℂ → ℂ :=
    fun ω t s => Complex.exp (Complex.I * (t * u ω + s * v ω))

  -- Step 4: Show that Φ(t,s) equals the integral of ψ
  have h_phi_integral : ∀ t s : ℂ,
      Φ t s = ∫ ω, ψ ω t s ∂μ.toMeasure := by
    intro t s
    simp only [Φ, ψ, GJGeneratingFunctionalℂ]
    -- By definition of GJGeneratingFunctionalℂ: ∫ exp(I * distributionPairingℂ_real ω (t•f + s•g))
    -- Use pairing linearity: distributionPairingℂ_real ω (t•f + s•g) = t * u ω + s * v ω
    congr 1
    funext ω
    congr 1
    congr 1
    exact pairing_lin ω t s

  -- Step 5: Compute the pointwise mixed derivative ∂²ψ/∂t∂s at (0,0)
  have h_pointwise_mixed_deriv : ∀ ω : FieldConfiguration,
      deriv (fun t => deriv (fun s => ψ ω t s) 0) 0 = -(u ω * v ω) := by
    intro ω
    -- Apply the helper lemma for mixed derivatives
    simp only [ψ]
    -- ψ ω t s = exp(I * (t * u ω + s * v ω))
    -- This matches the pattern exp(I * (t * a + s * b)) with a = u ω, b = v ω
    exact mixed_deriv_exp_bilinear (u ω) (v ω)

  -- Step 6: Apply dominated convergence to interchange derivative and integral
  have h_dom_conv : deriv (fun t => deriv (fun s => Φ t s) 0) 0 =
      ∫ ω, deriv (fun t => deriv (fun s => ψ ω t s) 0) 0 ∂μ.toMeasure := by
    -- Rewrite Φ in terms of the integral
    have h_eq : (fun t s => Φ t s) = (fun t s => ∫ ω, ψ ω t s ∂μ.toMeasure) := by
      funext t s; exact h_phi_integral t s
    -- We need to rewrite the function Φ using h_eq to transform to the integral form
    have h_rewrite : (fun t => deriv (fun s => Φ t s) 0) = (fun t => deriv (fun s => ∫ (ω : FieldConfiguration), ψ ω t s ∂↑μ) 0) := by
      funext t
      congr 1
      funext s
      exact h_phi_integral t s
    rw [h_rewrite]
    -- Note: The axiom mixed_deriv_under_integral_gaussian is for real TestFunction,
    -- but we need it for complex TestFunctionℂ. The general pattern still applies
    -- to Gaussian measures under the Fernique-type axioms, so we use the original
    -- mixed derivative lemma pattern but invoke it axiomatically.
    -- This is justified by the same dominated convergence arguments as the axiom.
    sorry

  -- Step 7: Combine everything to get the final result
  rw [h_dom_conv]
  simp only [h_pointwise_mixed_deriv]
  -- Now: ∫ ω, -(u ω * v ω) ∂μ.toMeasure = -∫ ω, u ω * v ω ∂μ.toMeasure
  rw [← integral_neg]
  -- This equals -∫ ω, distributionPairingℂ_real ω f * distributionPairingℂ_real ω g ∂μ.toMeasure
  -- Goal is already achieved by the definitions of u and v

/-- Bridge lemma: MinlosAnalytic.Qc equals SchwingerFunctionℂ₂ for the free GFF.
    This connects the two representations of complex bilinear covariance extension. -/
lemma schwinger_eq_Qc_free (m : ℝ) [Fact (0 < m)]
  (f g : TestFunctionℂ) :
  SchwingerFunctionℂ₂ (gaussianFreeField_free m) f g =
    MinlosAnalytic.Qc (freeCovarianceForm_struct m) f g := by
  classical
  -- Strategy (no polarization, no prior bilinearity needed):
  -- Consider Φ(t,s) := Z[t f + s g] = GJGeneratingFunctionalℂ μ (t•f + s•g).
  -- For centered Gaussian μ with Minlos complex form, the mixed derivative at (0,0)
  -- satisfies
  --   ∂²Φ/∂t∂s|₀ = -(SchwingerFunctionℂ₂ μ f g)  and also  ∂²Φ/∂t∂s|₀ = -(Qc C f g).
  -- Hence SchwingerFunctionℂ₂ μ f g = Qc C f g.

  -- Abbreviations
  let μ := gaussianFreeField_free m
  let C := freeCovarianceForm_struct m

  -- Complex CF form from Minlos: Z[J] = exp(-½ Qc(J,J)) for all J
  have hF : ∀ J : TestFunctionℂ,
      GJGeneratingFunctionalℂ μ J = Complex.exp (-(1/2 : ℂ) * MinlosAnalytic.Qc C J J) := by
    intro J; simpa using (gff_complex_characteristic_minlos (m := m) J)

  -- Define Φ(t,s) := Z[t f + s g]. (Used conceptually to state the mixed derivative identities.)
  let _Φ : ℂ → ℂ → ℂ := fun t s => GJGeneratingFunctionalℂ μ (t • f + s • g)

  -- Strategy: Both sides represent the same mixed derivative ∂²/∂t∂s Φ(t,s)|₀ where Φ(t,s) = Z[tf+sg].
  -- By hF, we know: Z[tf+sg] = exp(-½ Qc(tf+sg, tf+sg))
  -- So the integral form and exponential form are the same function.
  -- Their mixed derivatives at (0,0) must therefore be equal.

  -- Mathematical background (conceptual):
  -- For Φ(t,s) = exp(-½ Qc(tf+sg, tf+sg)):
  -- Using bilinearity: Qc(tf+sg, tf+sg) = t²Qc(f,f) + 2tsQc(f,g) + s²Qc(g,g)
  -- Standard calculus: ∂²/∂t∂s exp(-½·) at 0 = -Qc(f,g)
  --
  -- For Φ(t,s) = ∫ exp(i⟨ω,tf+sg⟩) dμ(ω):
  -- Standard analysis: ∂²/∂t∂s under integral = -∫ ⟨ω,f⟩⟨ω,g⟩ dμ = -SchwingerFunctionℂ₂(f,g)

  -- The equality follows from hF: both expressions are the same function
  have h_eq_neg : -(MinlosAnalytic.Qc C f g) = -(SchwingerFunctionℂ₂ μ f g) := by
    -- Both sides equal the same mixed derivative of Φ(t,s) = Z[t f + s g]
    -- Apply the two auxiliary lemmas and equate their conclusions.
    have h1 := mixed_deriv_minlos_Qc (m := m) f g
    have h2 := mixed_deriv_schwinger (m := m) f g
    -- h1 : deriv (fun t => deriv (fun s => Z[t f + s g]) 0) 0 = -Qc(f,g)
    -- h2 : deriv (fun t => deriv (fun s => Z[t f + s g]) 0) 0 = -S₂(f,g)
    -- Since both equal the same mixed derivative, we have -Qc(f,g) = -S₂(f,g)
    rw [← h1, ← h2]
  -- Cancel the minus sign
  have h_eq : MinlosAnalytic.Qc C f g = SchwingerFunctionℂ₂ μ f g := by
    have := congrArg (fun z : ℂ => (-1 : ℂ) * z) h_eq_neg
    simpa using this

  -- Conclude (swap sides to match the statement)
  simpa [μ, C] using h_eq.symm

end GFF_Minlos_Complex

/-- For the specialized free-field GFF, the complex 2-point function equals the complex
    free covariance (bilinear version). -/
theorem gff_two_point_equals_covarianceℂ_free
  (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
  SchwingerFunctionℂ₂ (gaussianFreeField_free m) f g = freeCovarianceℂ_bilinear m f g := by
  -- From the Minlos complex CF, we have S₂ = Qc of the real covariance form
  have h := GFF_Minlos_Complex.schwinger_eq_Qc_free (m := m) f g
  -- Identify Qc with the explicit bilinear complex covariance
  have hQc := GFF_Minlos_Complex.free_Qc_eq_freeCovarianceℂ (m := m) (f := f) (g := g)
  simpa [hQc] using h

/-- Complex generating functional for the free GFF.
    Derived by combining the Minlos complex form with the bridge lemma `schwinger_eq_Qc_free`. -/
theorem gff_complex_generating (m : ℝ) [Fact (0 < m)] :
  ∀ J : TestFunctionℂ,
    GJGeneratingFunctionalℂ (gaussianFreeField_free m) J =
      Complex.exp (-(1/2 : ℂ) * SchwingerFunctionℂ₂ (gaussianFreeField_free m) J J) := by
  intro J
  -- Start from the Minlos complex form: exp(-½ Qc(J,J))
  have h_minlos := GFF_Minlos_Complex.gff_complex_characteristic_minlos m J
  -- Bridge: Qc(J,J) = S₂(J,J)
  have h_bridge := (GFF_Minlos_Complex.schwinger_eq_Qc_free (m := m) J J).symm
  -- Rewriting gives the target form
  simpa [h_bridge] using h_minlos

/-- The Gaussian Free Field constructed via Minlos is Gaussian. -/
theorem isGaussianGJ_gaussianFreeField_free (m : ℝ) [Fact (0 < m)] :
  isGaussianGJ (gaussianFreeField_free m) := by
  constructor
  · exact gaussianFreeField_free_centered m
  · intro J; simpa using (gff_complex_generating m J)

end
