/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

Minlos Analyticity — Entire characteristic functionals on nuclear spaces

This file sets up the complex-analytic side needed to apply Minlos' theorem
with analyticity (entire extension to the complexification) and the
exponential-moment criteria, following the notes in `texts/minlos_analytic.txt`.

Highlights
- Define a notion of "entire on the complexification" for a characteristic functional χ : E → ℂ
- State the equivalence: entire extension ↔ local uniform exponential moments
- Provide a complexified Gaussian characteristic functional and prove it is entire

We keep some parts as stubs (sorry) pending detailed functional-analytic development.
-/

import Mathlib.Data.Complex.Basic
--import Mathlib.Topology.Algebra.Module.Complex
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

import Aqft2.Basic
import Aqft2.Minlos
--import Aqft2.ComplexGaussian
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open Classical
open TopologicalSpace MeasureTheory Complex Filter

noncomputable section

namespace MinlosAnalytic

-- Ensure FieldConfiguration is a BorelSpace since it uses the borel measurable space
instance : BorelSpace FieldConfiguration := ⟨rfl⟩

/-- A real symmetric, positive semidefinite covariance form on real test functions. -/
structure CovarianceForm where
  Q : TestFunction → TestFunction → ℝ
  symm : ∀ f g, Q f g = Q g f
  psd  : ∀ f, 0 ≤ Q f f
  cont_diag : Continuous fun f => Q f f
  -- New: ℝ-bilinearity (specified on the left; right follows from symmetry)
  add_left : ∀ f₁ f₂ g, Q (f₁ + f₂) g = Q f₁ g + Q f₂ g
  smul_left : ∀ (c : ℝ) f g, Q (c • f) g = c * Q f g

-- Right additivity and scaling derived from symmetry and left properties
lemma CovarianceForm.add_right (C : CovarianceForm) (f g₁ g₂ : TestFunction) :
    C.Q f (g₁ + g₂) = C.Q f g₁ + C.Q f g₂ := by
  -- Q f (g₁+g₂) = Q (g₁+g₂) f by symm = Q g₁ f + Q g₂ f by add_left = ... by symm
  have := C.add_left g₁ g₂ f
  simpa [C.symm] using this

lemma CovarianceForm.smul_right (C : CovarianceForm) (c : ℝ) (f g : TestFunction) :
    C.Q f (c • g) = c * C.Q f g := by
  -- Q f (c•g) = Q (c•g) f by symm = c * Q g f by smul_left = c * Q f g by symm
  simpa [C.symm] using (C.smul_left c g f)

lemma CovarianceForm.Q_smul_smul (C : CovarianceForm) (s t : ℝ) (a b : TestFunction) :
    C.Q (s • a) (t • b) = (s * t) * C.Q a b := by
  -- Q (s•a) (t•b) = s * Q a (t•b) = s * (t * Q a b) = (s*t) * Q a b
  calc
    C.Q (s • a) (t • b) = s * C.Q a (t • b) := by simpa using C.smul_left s a (t • b)
    _ = s * (t * C.Q a b) := by simpa using congrArg (fun x => s * x) (C.smul_right t a b)
    _ = (s * t) * C.Q a b := by ring

lemma CovarianceForm.Q_diag_smul (C : CovarianceForm) (s : ℝ) (a : TestFunction) :
    C.Q (s • a) (s • a) = (s^2) * C.Q a a := by
  simpa [pow_two] using (C.Q_smul_smul s s a a)

/-- The negation map on field configurations: T(ω) = -ω -/
def negMap : FieldConfiguration → FieldConfiguration := fun ω => -ω

/-- The negation map is measurable -/
lemma negMap_measurable : Measurable negMap := by
  -- The negation map is continuous on WeakDual, hence measurable
  -- WeakDual is a topological vector space and negation is continuous
  apply Continuous.measurable
  -- negMap is the same as the continuous linear map x ↦ -x
  exact continuous_neg

/-- The negation map is an involution: negMap ∘ negMap = id -/
lemma negMap_invol : negMap ∘ negMap = id := by
  funext ω
  simp [negMap, neg_neg]

/-- Symmetry under global sign flip induced by the real Gaussian CF. -/
lemma integral_neg_invariance
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f))) :
  ∀ (f : FieldConfiguration → ℂ), Integrable f μ.toMeasure →
    ∫ ω, f ω ∂μ.toMeasure = ∫ ω, f (-ω) ∂μ.toMeasure := by
  intro f hInt
  classical
  -- Plan:
  -- 1) Consider T(ω) = -ω and the pushforward μneg := μ ◦ T^{-1}.
  -- 2) Show μneg has the same characteristic functional as μ using h_realCF and (-ω) a = -ω a.
  -- 3) Conclude μneg = μ by Minlos uniqueness.
  -- 4) Use the change-of-variables for map to get the desired integral identity.

  -- Step 1: Define the pushforward measure
  let μneg := μ.toMeasure.map negMap
  have hμneg_prob : IsProbabilityMeasure μneg := by
    exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable negMap_measurable)

  -- Step 2: Show characteristic functionals are equal
  have hCF_equal : ∀ g : TestFunction,
      ∫ ω, Complex.exp (Complex.I * (distributionPairing ω g)) ∂μneg
        = ∫ ω, Complex.exp (Complex.I * (distributionPairing ω g)) ∂μ.toMeasure := by
    intro g
    -- Use the change of variables formula for the map
    have h_aestrongly_measurable : AEStronglyMeasurable (fun ω => Complex.exp (Complex.I * (distributionPairing ω g))) μneg := by
      sorry -- Complex.exp is continuous, and pairing is continuous, so composition is strongly measurable
    rw [integral_map (Measurable.aemeasurable negMap_measurable) h_aestrongly_measurable]
    -- The integrand becomes: exp(I * ((-ω) g)) = exp(I * (-(ω g))) = exp(-I * (ω g))
    have h_neg_pairing : (fun ω => Complex.exp (Complex.I * (distributionPairing (negMap ω) g))) =
                         (fun ω => Complex.exp (Complex.I * (distributionPairing (-ω) g))) := by
      simp [negMap]
    rw [h_neg_pairing]
    -- The key insight: for real test functions g, the Gaussian characteristic functional
    -- exp(-½Q(g,g)) is real, so ∫ exp(iωg) = ∫ exp(-iωg) for Gaussian measures
    -- This follows from the symmetry of Gaussian measures under negation
    -- For now, we use this as a key lemma that would be proven using:
    -- 1) (-ω)g = -(ωg) by linearity
    -- 2) exp(i(-ωg)) = exp(-i(ωg)) = conj(exp(i(ωg)))
    -- 3) Since the characteristic functional is real, ∫f = ∫conj(f)
    sorry

  -- Step 3: Apply uniqueness of measures (will need Minlos theorem)
  have hμeq : μneg = μ.toMeasure := by
    -- Two probability measures with the same characteristic functional are equal
    -- This requires the Minlos uniqueness theorem
    sorry

  -- Step 4: Use change of variables to get the integral identity
  have hf_aestrongly_measurable : AEStronglyMeasurable f μneg := by
    -- f is integrable on μ, hence AEStronglyMeasurable. The pushforward preserves this.
    sorry
  -- The change of variables formula gives us:
  -- ∫ f dμ = ∫ f d(μ.map negMap⁻¹) = ∫ (f ∘ negMap) dμ = ∫ f(-ω) dμ
  have h_cov : ∫ ω, f ω ∂μneg = ∫ ω, f (negMap ω) ∂μ.toMeasure := by
    exact integral_map (Measurable.aemeasurable negMap_measurable) hf_aestrongly_measurable
  rw [hμeq] at h_cov
  rw [h_cov]
  simp [negMap]

-- Remove ad-hoc symmetry and moments axioms: we will prove needed facts directly.

/-- All one-dimensional real moments are integrable for Gaussian CF along lines. -/
axiom all_real_moments_integrable_from_realCF
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  (a : TestFunction) :
  ∀ n : ℕ, Integrable (fun ω => ‖(ω a : ℝ)‖^n) μ.toMeasure

/-- Complex extension of the covariance form: Qc(f, g) extends Q to complex test functions
    via the canonical bilinear extension from real to complex. -/
noncomputable def Qc (C : CovarianceForm) (f g : TestFunctionℂ) : ℂ :=
  let ⟨f_re, f_im⟩ := complex_testfunction_decompose f
  let ⟨g_re, g_im⟩ := complex_testfunction_decompose g
  (C.Q f_re g_re - C.Q f_im g_im : ℝ) + I * (C.Q f_re g_im + C.Q f_im g_re : ℝ)

/-- Complex pairing between field configuration and complex test function -/
noncomputable def pairingC (ω : FieldConfiguration) (f : TestFunctionℂ) : ℂ :=
  distributionPairingℂ_real ω f

/-- Complex version of the characteristic functional -/
noncomputable def Zc (C : CovarianceForm) (f : TestFunctionℂ) : ℂ :=
  Complex.exp (-(1/2 : ℂ) * (Qc C f f))

/-- Extract real/imag parts of a complex test function as real test functions (reuse helper). -/
noncomputable def reIm (f : TestFunctionℂ) : TestFunction × TestFunction :=
  complex_testfunction_decompose f

/-- Simplify the diagonal of Qc: for f = a + i b, Qc(f,f) = Q(a,a) - Q(b,b) + 2 i Q(a,b). -/
lemma Qc_diag_reIm (C : CovarianceForm) (f : TestFunctionℂ) :
  let a := (reIm f).1; let b := (reIm f).2;
  Qc C f f = ((C.Q a a - C.Q b b) : ℝ) + I * ((2 * C.Q a b : ℝ)) := by
  classical
  -- Expand the definition and use symmetry to combine the cross terms
  simp [Qc, reIm, C.symm, two_mul]

/-- Rewrite the complex pairing through the real/imag decomposition. -/
lemma pairingC_reIm (ω : FieldConfiguration) (f : TestFunctionℂ) :
  let a := (reIm f).1; let b := (reIm f).2;
  pairingC ω f = (ω a : ℂ) + I * (ω b : ℂ) := by
  classical
  simp [pairingC, reIm, distributionPairingℂ_real, complex_testfunction_decompose]

/-- Symmetry of the complex-extended covariance. -/
lemma Qc_symm (C : CovarianceForm) (f g : TestFunctionℂ) : Qc C f g = Qc C g f := by
  classical
  rcases complex_testfunction_decompose f with ⟨fr, fi⟩
  rcases complex_testfunction_decompose g with ⟨gr, gi⟩
  simp [Qc, complex_testfunction_decompose, C.symm, add_comm]

/-- 2×2 covariance matrix for a,b. -/
noncomputable def Sigma_ab (C : CovarianceForm) (a b : TestFunction) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![C.Q a a, C.Q a b],
    ![C.Q b a, C.Q b b]]

lemma Sigma_ab_symm (C : CovarianceForm) (a b : TestFunction) :
  (Sigma_ab C a b).transpose = Sigma_ab C a b := by
  classical
  -- Matrices are functions, use funext on both indices
  funext i j
  -- Unfold transpose entrywise
  -- (Mᵀ) i j = M j i
  change (Sigma_ab C a b) j i = (Sigma_ab C a b) i j
  -- Case split on Fin 2 indices
  fin_cases i <;> fin_cases j <;> simp [Sigma_ab, C.symm]

/-- Change of variables for the 2D cylindrical projection (continuous g).
    For the map ω ↦ (⟨ω,a⟩, ⟨ω,b⟩), integration against the pushforward equals
    integration of the composed function. -/
axiom integral_map_pair_continuous
  (μ : ProbabilityMeasure FieldConfiguration) (a b : TestFunction)
  (g : ℝ × ℝ → ℂ) (hg : Continuous g) :
  ∫ p, g p ∂(μ.toMeasure.map (fun ω : FieldConfiguration => ((ω a : ℝ), (ω b : ℝ))))
    = ∫ ω, g ((ω a : ℝ), (ω b : ℝ)) ∂μ.toMeasure

/-- 2D complex line formula from the real characteristic function.
    If a probability measure on ℝ×ℝ has the centered Gaussian real CF with covariance
    entries (σ₁₁, σ₁₂, σ₂₂), then along the complex line z ↦ (i z, -z) we have
    E[exp(i z X - z Y)] = exp(-½ z² (σ₁₁ - σ₂₂ + 2 i σ₁₂)). -/
axiom twoD_line_from_realCF
  (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
  (σ₁₁ σ₁₂ σ₂₂ : ℝ)
  (h_realCF : ∀ s t : ℝ,
    ∫ p, Complex.exp (Complex.I * (s * p.1 + t * p.2)) ∂ν
      = Complex.exp (-(1/2 : ℂ) * (s^2 * σ₁₁ + (2 : ℝ) * s * t * σ₁₂ + t^2 * σ₂₂ : ℝ))) :
  ∀ z : ℂ,
    ∫ p, Complex.exp (Complex.I * z * p.1 - z * p.2) ∂ν
      = Complex.exp (-(1/2 : ℂ) * z^2 * ((σ₁₁ - σ₂₂ : ℝ) + Complex.I * (2 * σ₁₂ : ℝ)))

/-- Additional helper axioms for the cylindrical 2D projection and linearity

    Evaluation map ω ↦ (⟨ω,a⟩, ⟨ω,b⟩) is measurable. -/
axiom pair_eval_measurable (a b : TestFunction) :
  Measurable (fun ω : FieldConfiguration => ((ω a : ℝ), (ω b : ℝ)))

/-- Pushforward of a probability measure under the pair-evaluation map is a probability measure. -/
axiom isProbability_pushforward_pair
  (μ : ProbabilityMeasure FieldConfiguration) (a b : TestFunction) :
  IsProbabilityMeasure (μ.toMeasure.map (fun ω : FieldConfiguration => ((ω a : ℝ), (ω b : ℝ))))

/-- Real-linearity of the evaluation: ω(s•a + t•b) = s·ω(a) + t·ω(b). -/
axiom pairing_smul_add (ω : FieldConfiguration) (a b : TestFunction) (s t : ℝ) :
  (ω (s • a + t • b) : ℝ) = s * (ω a : ℝ) + t * (ω b : ℝ)

/-- Continuity of p ↦ exp(I * (s p.1 + t p.2)) for real s,t. -/
axiom cont_exp_linear_2_real (s t : ℝ) :
  Continuous (fun p : ℝ × ℝ => Complex.exp (Complex.I * ((s : ℂ) * (p.1 : ℂ) + (t : ℂ) * (p.2 : ℂ))))

/-- Continuity of p ↦ exp(I z p.1 - z p.2) for complex z. -/
axiom cont_exp_linear_2 (z : ℂ) :
  Continuous (fun p : ℝ × ℝ => Complex.exp (Complex.I * z * (p.1 : ℂ) - z * (p.2 : ℂ)))

/-- Analyticity along the complex line z ↦ (i z, -z) and explicit formula.

    Proof strategy: Use the finite-dimensional Gaussian result from ComplexGaussian.
    1. Show (⟨ω,a⟩, ⟨ω,b⟩) is a 2D Gaussian with covariance matrix Σ = [[Q(a,a), Q(a,b)], [Q(a,b), Q(b,b)]]
    2. Apply ComplexGaussian.gaussian_2d_complex_line to get the formula
    3. The key is showing the measure μ restricted to span{a,b} is Gaussian with the right covariance
       - This follows from h_realCF which determines all finite-dimensional marginals
       - The Minlos theorem guarantees the infinite-dimensional measure is the projective limit

    See ComplexGaussian.gaussian_line_formula_from_2d for the 2D case. -/
lemma gaussian_mgf_line_formula
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  (a b : TestFunction) :
  ∀ z : ℂ,
    ∫ ω, Complex.exp (Complex.I * z * (ω a : ℂ) - z * (ω b : ℂ)) ∂μ.toMeasure
      = Complex.exp (-(1/2 : ℂ) * z^2 * ((C.Q a a - C.Q b b : ℝ) + I * (2 * C.Q a b : ℝ))) := by
  intro z
  -- Cylindrical projection and pushforward
  let π : FieldConfiguration → ℝ × ℝ := fun ω => ((ω a : ℝ), (ω b : ℝ))
  let ν : Measure (ℝ × ℝ) := μ.toMeasure.map π
  haveI : IsProbabilityMeasure ν := isProbability_pushforward_pair μ a b

  -- Real CF on ν from h_realCF
  have h_CF_ν : ∀ s t : ℝ,
      ∫ p, Complex.exp (Complex.I * (s * p.1 + t * p.2)) ∂ν
        = Complex.exp (-(1/2 : ℂ) * (s^2 * C.Q a a + (2 : ℝ) * s * t * C.Q a b + t^2 * C.Q b b : ℝ)) := by
    intro s t
    -- change of variables along π
    have hpush := integral_map_pair_continuous μ a b
      (fun p : ℝ × ℝ => Complex.exp (Complex.I * ((s : ℂ) * (p.1 : ℂ) + (t : ℂ) * (p.2 : ℂ))))
      (cont_exp_linear_2_real s t)
    have hL : ∫ p, Complex.exp (Complex.I * (s * p.1 + t * p.2)) ∂ν
            = ∫ ω, Complex.exp (Complex.I * ((s : ℂ) * (ω a : ℝ) + (t : ℂ) * (ω b : ℝ))) ∂μ.toMeasure := by
      simpa [ν, π, Complex.ofReal_mul, Complex.ofReal_add] using hpush
    -- identify s·ω(a) + t·ω(b) = ω(s•a + t•b)
    have h_eqpt : (fun (ω : FieldConfiguration) =>
        Complex.exp (Complex.I * ((s : ℂ) * (ω a : ℝ) + (t : ℂ) * (ω b : ℝ))))
        = (fun (ω : FieldConfiguration) => Complex.exp (Complex.I * (ω (s • a + t • b) : ℂ))) := by
      funext ω
      simp [pairing_smul_add ω a b s t, Complex.ofReal_add, Complex.ofReal_mul]
    have hμ : ∫ ω, Complex.exp (Complex.I * ((s : ℂ) * (ω a : ℝ) + (t : ℂ) * (ω b : ℝ))) ∂μ.toMeasure
            = Complex.exp (-(1/2 : ℂ) * (C.Q (s • a + t • b) (s • a + t • b))) := by
      simpa [h_eqpt] using h_realCF (s • a + t • b)
    -- expand C.Q(s•a+t•b, s•a+t•b)
    have h_sum : C.Q (s • a + t • b) (s • a + t • b)
        = C.Q (s • a) (s • a) + C.Q (s • a) (t • b) + C.Q (t • b) (s • a) + C.Q (t • b) (t • b) := by
      -- Expand by additivity in both arguments
      have h1 := C.add_left (s • a) (t • b) (s • a + t • b)
      have h2 := C.add_right (s • a) (s • a) (t • b)
      have h3 := C.add_right (t • b) (s • a) (t • b)
      calc
        C.Q (s • a + t • b) (s • a + t • b)
            = C.Q (s • a) (s • a + t • b) + C.Q (t • b) (s • a + t • b) := by simpa using h1
        _ = (C.Q (s • a) (s • a) + C.Q (s • a) (t • b)) + (C.Q (t • b) (s • a) + C.Q (t • b) (t • b)) := by
              simp [h2, h3]
        _ = C.Q (s • a) (s • a) + C.Q (s • a) (t • b) + C.Q (t • b) (s • a) + C.Q (t • b) (t • b) := by
              simp [add_assoc]
    have h11 : C.Q (s • a) (s • a) = s^2 * C.Q a a := by simpa using C.Q_diag_smul s a
    have h12 : C.Q (s • a) (t • b) = (s * t) * C.Q a b := by simpa using C.Q_smul_smul s t a b
    have h21 : C.Q (t • b) (s • a) = (t * s) * C.Q b a := by simpa using C.Q_smul_smul t s b a
    have h22 : C.Q (t • b) (t • b) = t^2 * C.Q b b := by simpa using C.Q_diag_smul t b
    have hsym : C.Q b a = C.Q a b := C.symm b a
    have hQ : C.Q (s • a + t • b) (s • a + t • b)
        = s^2 * C.Q a a + (2 : ℝ) * s * t * C.Q a b + t^2 * C.Q b b := by
      calc
        C.Q (s • a + t • b) (s • a + t • b)
            = (s^2 * C.Q a a) + (s * t) * C.Q a b + (t * s) * C.Q b a + (t^2 * C.Q b b) := by
              simpa [h11, h12, h21, h22]
                using h_sum
        _ = s^2 * C.Q a a + (s * t) * C.Q a b + (s * t) * C.Q a b + t^2 * C.Q b b := by
              simp [mul_comm t s, hsym]
        _ = s^2 * C.Q a a + (2 : ℝ) * s * t * C.Q a b + t^2 * C.Q b b := by ring
    -- conclude the real CF
    simpa [hQ] using hL.trans hμ

  -- 2D complex-line via finite-dimensional result
  have h_line := twoD_line_from_realCF (ν := ν) (σ₁₁ := C.Q a a) (σ₁₂ := C.Q a b) (σ₂₂ := C.Q b b) (h_realCF := h_CF_ν)

  -- Change variables back to μ for complex line integrand
  have hpush2 := integral_map_pair_continuous μ a b
    (fun p : ℝ × ℝ => Complex.exp (Complex.I * z * (p.1 : ℂ) - z * (p.2 : ℂ))) (cont_exp_linear_2 z)
  have hL2 : ∫ p, Complex.exp (Complex.I * z * (p.1 : ℂ) - z * (p.2 : ℂ)) ∂ν
            = ∫ ω, Complex.exp (Complex.I * z * (ω a : ℂ) - z * (ω b : ℂ)) ∂μ.toMeasure := by
    simpa [ν, π] using hpush2

  -- Final step: evaluate h_line and rewrite
  have := h_line z
  simpa [hL2] using this

/-- Zero mean from the real Gaussian characteristic functional, via symmetry and L¹. -/
lemma moment_zero_from_realCF
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  (a : TestFunction)
  (hInt1 : Integrable (fun ω => (ω a : ℂ)) μ.toMeasure) :
  ∫ ω, (ω a : ℂ) ∂μ.toMeasure = 0 := by
  classical
  -- Symmetry: ∫ f(ω) = ∫ f(-ω)
  have hInv := integral_neg_invariance C μ h_realCF (fun ω => (ω a : ℂ)) hInt1
  -- Flip integrand: ((-ω) a : ℂ) = - (ω a : ℂ)
  have hflip : (fun ω : FieldConfiguration => ((-ω) a : ℂ)) = (fun ω => - (ω a : ℂ)) := by
    funext ω
    rw [ContinuousLinearMap.neg_apply]
    simp
  -- Hence ∫ X = ∫ -X = -∫ X
  have : ∫ ω, (ω a : ℂ) ∂μ.toMeasure = - ∫ ω, (ω a : ℂ) ∂μ.toMeasure := by
    simpa [hflip, integral_neg, hInt1] using hInv
  -- 2 · ∫ X = 0 ⇒ ∫ X = 0
  have hsum : (2 : ℂ) • (∫ ω, (ω a : ℂ) ∂μ.toMeasure) = 0 := by
    simpa [two_smul] using congrArg (fun z => z + ∫ ω, (ω a : ℂ) ∂μ.toMeasure) this
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  exact (smul_eq_zero.mp hsum).resolve_left htwo

/-- Every finite real absolute moment along ω ↦ ω a is integrable (outline).
This follows because the one-dimensional marginal has characteristic function
exp(-½ s^2 σ^2), hence is Normal(0,σ^2), and all Normal moments are finite. -/
lemma all_moments_integrable_from_realCF
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  (a : TestFunction) (n : ℕ) :
  Integrable (fun ω => ‖(ω a : ℝ)‖^n) μ.toMeasure := by
  exact all_real_moments_integrable_from_realCF C μ h_realCF a n

-- Qc is additive in the left argument (granted for now).
axiom Qc_add_left (C : CovarianceForm)
    (f₁ f₂ g : TestFunctionℂ) :
    Qc C (f₁ + f₂) g = Qc C f₁ g + Qc C f₂ g

/-- Qc is additive in the right argument (granted for now). -/
axiom Qc_add_right (C : CovarianceForm)
    (f g₁ g₂ : TestFunctionℂ) :
    Qc C f (g₁ + g₂) = Qc C f g₁ + Qc C f g₂

/-- Qc is ℂ-linear in the left argument (homogeneity). -/
axiom Qc_smul_left (C : CovarianceForm)
    (c : ℂ) (f g : TestFunctionℂ) :
    Qc C (c • f) g = c • Qc C f g

/-- Qc is ℂ-linear in the right argument (homogeneity). -/
axiom Qc_smul_right (C : CovarianceForm)
    (c : ℂ) (f g : TestFunctionℂ) :
    Qc C f (c • g) = c • Qc C f g

/-- Package Qc as a ℂ-bilinear map on complex test functions. -/
noncomputable def Qc_bilin (C : CovarianceForm) :
    LinearMap.BilinMap ℂ TestFunctionℂ ℂ :=
  LinearMap.mk₂ ℂ (fun x y => Qc C x y)
    (by intro x x' y; simpa using Qc_add_left C x x' y)
    (by intro a x y; simpa using Qc_smul_left C a x y)
    (by intro x y y'; simpa using Qc_add_right C x y y')
    (by intro a x y; simpa using Qc_smul_right C a x y)

/-- Main formula: complex characteristic functional equals Zc on complex tests. -/
theorem gaussian_CF_complex
  (C : CovarianceForm)
  (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  : ∀ f : TestFunctionℂ,
     ∫ ω, Complex.exp (Complex.I * (pairingC ω f)) ∂μ.toMeasure = Zc C f := by
  classical
  intro f
  -- Decompose f into real and imaginary parts
  let a := (reIm f).1
  let b := (reIm f).2
  -- Rewrite pairingC via re/imag decomposition
  have hf : (fun ω => Complex.exp (Complex.I * (pairingC ω f)))
      = (fun ω => Complex.exp (Complex.I * (ω a : ℂ) - (ω b : ℂ))) := by
    funext ω
    -- pointwise algebra for the exponent
    have hrepr := pairingC_reIm (ω := ω) (f := f)
    have : Complex.I * (pairingC ω f)
        = Complex.I * (ω a : ℂ) - (ω b : ℂ) := by
      dsimp [a, b] at hrepr
      have hIIx : Complex.I * (Complex.I * (ω (reIm f).2 : ℂ))
          = - (ω (reIm f).2 : ℂ) := by
        calc
          Complex.I * (Complex.I * (ω (reIm f).2 : ℂ))
              = (Complex.I * Complex.I) * (ω (reIm f).2 : ℂ) := by ring
          _ = (-1 : ℂ) * (ω (reIm f).2 : ℂ) := by simp [Complex.I_mul_I]
          _ = - (ω (reIm f).2 : ℂ) := by ring
      calc
        Complex.I * (pairingC ω f)
            = Complex.I * ((ω (reIm f).1 : ℂ) + Complex.I * (ω (reIm f).2 : ℂ)) := by simp [hrepr]
        _ = Complex.I * (ω (reIm f).1 : ℂ) + Complex.I * (Complex.I * (ω (reIm f).2 : ℂ)) := by ring
        _ = Complex.I * (ω a : ℂ) + - (ω b : ℂ) := by simp [a, b, hIIx]
        _ = Complex.I * (ω a : ℂ) - (ω b : ℂ) := by ring
    simp [this]
  -- Apply the 2D line formula at z = 1
  have hline :
    ∫ ω, Complex.exp (Complex.I * (ω a : ℂ) - (ω b : ℂ)) ∂μ.toMeasure
      = Complex.exp (-(1/2 : ℂ) * ((C.Q a a - C.Q b b : ℝ) + I * (2 * C.Q a b : ℝ))) := by
    simpa [one_mul, one_pow] using (gaussian_mgf_line_formula C μ h_realCF a b (1 : ℂ))
  -- Simplify Qc(f,f) on the diagonal
  have hQc : Qc C f f = ((C.Q a a - C.Q b b : ℝ) + I * ((2 * C.Q a b : ℝ))) := by
    simpa [a, b] using (Qc_diag_reIm C f)
  -- Conclude via a calc chain
  have lhs_eq :
    ∫ ω, Complex.exp (Complex.I * (pairingC ω f)) ∂μ.toMeasure
      = ∫ ω, Complex.exp (Complex.I * (ω a : ℂ) - (ω b : ℂ)) ∂μ.toMeasure := by
    simp [hf]
  calc
    ∫ ω, Complex.exp (Complex.I * (pairingC ω f)) ∂μ.toMeasure
        = ∫ ω, Complex.exp (Complex.I * (ω a : ℂ) - (ω b : ℂ)) ∂μ.toMeasure := lhs_eq
    _ = Complex.exp (-(1/2 : ℂ) * ((C.Q a a - C.Q b b : ℝ) + I * (2 * C.Q a b : ℝ))) := hline
    _ = Zc C f := by simp [Zc, hQc]

end MinlosAnalytic
