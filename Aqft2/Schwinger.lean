/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

## Schwinger Functions for AQFT

This file implements Schwinger functions - the fundamental n-point correlation functions
of quantum field theory. These encode all physical information and satisfy the
Osterwalder-Schrader axioms, serving as the bridge between constructive QFT and
traditional Wightman axioms.

### Core Definitions:

**Schwinger Functions (Moment-based):**
- `SchwingerFunction`: S_n(f₁,...,fₙ) = ∫ ⟨ω,f₁⟩⟨ω,f₂⟩...⟨ω,fₙ⟩ dμ(ω)
- `SchwingerFunction₁` through `SchwingerFunction₄`: Specialized n-point functions
- `SchwingerFunctionℂ`: Complex version for complex test functions

**Distribution-based Framework:**
- `SpaceTimeProduct`: n-fold product space (SpaceTime)ⁿ
- `TestFunctionProduct`: Schwartz functions on (SpaceTime)ⁿ
- `SchwingerDistribution`: S_n as distribution on (SpaceTime)ⁿ
- `tensorProductTestFunction`: f₁ ⊗ f₂ ⊗ ... ⊗ fₙ tensor products

**Generating Functional Connection:**
- `generating_functional_as_series`: Z[J] = ∑ (i)ⁿ/n! S_n(J,...,J)
- `extractCoefficient`: Extract S_n from exponential series
- `schwinger_function_from_series_coefficient`: Inversion formula

### Key Properties:

**Basic Relations:**
- `schwinger_eq_mean`: S₁ equals GJ mean functional
- `schwinger_eq_covariance`: S₂ equals field covariance
- `schwinger_vanishes_centered`: S₁ = 0 for centered measures

**Special Cases:**
- `generating_functional_centered`: Centered measures start with quadratic term
- `generating_functional_gaussian`: Gaussian case with Wick's theorem
- `IsGaussianMeasure`: Characterizes Gaussian field measures

**Symmetry Properties:**
- `schwinger_function_clm_invariant`: 2-point CLM invariance from generating functional symmetry
- `schwinger_function_clm_invariant_general`: n-point CLM invariance theorem
- Connection to rotation, translation, and discrete symmetries

**Spacetime Properties:**
- `schwinger_distribution_translation_invariance`: Translation symmetry
- `schwinger_distribution_euclidean_locality`: Euclidean locality/clustering
- `TwoPointSchwingerDistribution`: Covariance structure

### Mathematical Framework:

**Two Perspectives:**
1. **Constructive**: Direct integration ∫ ⟨ω,f₁⟩...⟨ω,fₙ⟩ dμ(ω)
2. **Distributional**: S_n ∈ 𝒟'((SpaceTime)ⁿ) with locality properties

**Exponential Series Connection:**
Z[J] = ∫ exp(i⟨ω,J⟩) dμ(ω) = ∑ₙ (i)ⁿ/n! Sₙ(J,...,J)
More constructive than functional derivatives, natural for Gaussian measures.

**Physical Interpretation:**
- S₁: Mean field (vacuum expectation)
- S₂: Two-point correlation (propagator)
- S₃: Three-point vertex (interaction)
- S₄: Four-point scattering amplitude
- Higher Sₙ: Multi-particle correlations

**Connection to OS Axioms:**
- OS-1 (temperedness): S_n are tempered distributions
- OS-2 (Euclidean invariance): Group action on correlation functions (via CLM invariance)
- OS-3 (reflection positivity): Positivity of restricted correlations
- OS-4 (ergodicity): Clustering at large separations

**Relation to Other Modules:**
- Foundation: `Basic` (field configurations, distributions)
- Symmetries: `Euclidean` (spacetime symmetries), `DiscreteSymmetry` (time reflection)
- Measures: `Minlos`, `GFFMconstruct` (Gaussian realizations)
- Analysis: `FunctionalAnalysis` (Fourier theory), `SCV` (complex analyticity)

This provides the computational core for proving the Osterwalder-Schrader axioms
and constructing explicit quantum field theory models.
-/

import Mathlib.Tactic  -- gives `ext` and `simp` power
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Algebra.Order.Group.Unbundled.Abs

-- Import our basic definitions
import Aqft2.HilbertSpace
import Aqft2.Basic
import Aqft2.FunctionalAnalysis
import Aqft2.ComplexTestFunction

open MeasureTheory Complex
open TopologicalSpace

noncomputable section

variable {𝕜 : Type} [RCLike 𝕜]

/-! ## Schwinger Functions

The Schwinger functions S_n are the n-th moments of field operators φ(f₁)...φ(fₙ)
where φ(f) = ⟨ω, f⟩ is the field operator defined by pairing the field configuration
with a test function.

Following Glimm and Jaffe, these are the fundamental correlation functions:
S_n(f₁,...,fₙ) = ∫ ⟨ω,f₁⟩ ⟨ω,f₂⟩ ... ⟨ω,fₙ⟩ dμ(ω)

The Schwinger functions contain all the physics and satisfy the OS axioms.
They can be obtained from the generating functional via exponential series:
S_n(f₁,...,fₙ) = (-i)ⁿ (coefficient of (iJ)ⁿ/n! in Z[J])
-/

/-- The n-th Schwinger function: n-point correlation function of field operators.
    S_n(f₁,...,fₙ) = ∫ ⟨ω,f₁⟩ ⟨ω,f₂⟩ ... ⟨ω,fₙ⟩ dμ(ω)

    This is the fundamental object in constructive QFT - all physics is contained
    in the infinite sequence of Schwinger functions {S_n}_{n=1}^∞. -/
def SchwingerFunction (dμ_config : ProbabilityMeasure FieldConfiguration) (n : ℕ)
  (f : Fin n → TestFunction) : ℝ :=
  ∫ ω, (∏ i, distributionPairing ω (f i)) ∂dμ_config.toMeasure

/-- The 1-point Schwinger function: the mean field -/
def SchwingerFunction₁ (dμ_config : ProbabilityMeasure FieldConfiguration)
  (f : TestFunction) : ℝ :=
  SchwingerFunction dμ_config 1 ![f]

/-- The 2-point Schwinger function: the covariance -/
def SchwingerFunction₂ (dμ_config : ProbabilityMeasure FieldConfiguration)
  (f g : TestFunction) : ℝ :=
  SchwingerFunction dμ_config 2 ![f, g]

/-- The 3-point Schwinger function -/
def SchwingerFunction₃ (dμ_config : ProbabilityMeasure FieldConfiguration)
  (f g h : TestFunction) : ℝ :=
  SchwingerFunction dμ_config 3 ![f, g, h]

/-- The 4-point Schwinger function -/
def SchwingerFunction₄ (dμ_config : ProbabilityMeasure FieldConfiguration)
  (f g h k : TestFunction) : ℝ :=
  SchwingerFunction dμ_config 4 ![f, g, h, k]

/-- The Schwinger function equals the GJ mean for n=1 -/
lemma schwinger_eq_mean (dμ_config : ProbabilityMeasure FieldConfiguration) (f : TestFunction) :
  SchwingerFunction₁ dμ_config f = GJMean dμ_config f := by
  unfold SchwingerFunction₁ SchwingerFunction GJMean
  -- The product over a singleton {0} is just the single element f 0 = f
  classical
  -- simplify the finite product over Fin 1 and evaluate the single entry of ![f]
  simp

/-- The Schwinger function equals the direct covariance integral for n=2 -/
lemma schwinger_eq_covariance (dμ_config : ProbabilityMeasure FieldConfiguration) (f g : TestFunction) :
  SchwingerFunction₂ dμ_config f g = ∫ ω, (distributionPairing ω f) * (distributionPairing ω g) ∂dμ_config.toMeasure := by
  unfold SchwingerFunction₂ SchwingerFunction
  -- The product over {0, 1} expands to (f 0) * (f 1) = f * g
  classical
  simp [Fin.prod_univ_two]

/-- For centered measures (zero mean), the 1-point function vanishes -/
lemma schwinger_vanishes_centered (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_centered : ∀ f : TestFunction, GJMean dμ_config f = 0) (f : TestFunction) :
  SchwingerFunction₁ dμ_config f = 0 := by
  rw [schwinger_eq_mean]
  exact h_centered f

/-- Complex version of Schwinger functions for complex test functions -/
def SchwingerFunctionℂ (dμ_config : ProbabilityMeasure FieldConfiguration) (n : ℕ)
  (f : Fin n → TestFunctionℂ) : ℂ :=
  ∫ ω, (∏ i, distributionPairingℂ_real ω (f i)) ∂dμ_config.toMeasure

/-- The complex 2-point Schwinger function for complex test functions.
    This is the natural extension of SchwingerFunction₂ to complex test functions. -/
def SchwingerFunctionℂ₂ (dμ_config : ProbabilityMeasure FieldConfiguration)
  (φ ψ : TestFunctionℂ) : ℂ :=
  SchwingerFunctionℂ dμ_config 2 ![φ, ψ]

/-- Property that SchwingerFunctionℂ₂ is ℂ-bilinear in both arguments.
    This is a key property for Gaussian measures and essential for OS0 analyticity. -/
def CovarianceBilinear (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (c : ℂ) (φ₁ φ₂ ψ : TestFunctionℂ),
    SchwingerFunctionℂ₂ dμ_config (c • φ₁) ψ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ ∧
    SchwingerFunctionℂ₂ dμ_config (φ₁ + φ₂) ψ = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₂ ψ ∧
    SchwingerFunctionℂ₂ dμ_config φ₁ (c • ψ) = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ ∧
    SchwingerFunctionℂ₂ dμ_config φ₁ (ψ + φ₂) = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₁ φ₂

/-- If the product pairing is integrable for all test functions, then the complex
    2-point Schwinger function is ℂ-bilinear in both arguments. -/
lemma CovarianceBilinear_of_integrable
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_int : ∀ (φ ψ : TestFunctionℂ),
    Integrable (fun ω => distributionPairingℂ_real ω φ * distributionPairingℂ_real ω ψ)
      dμ_config.toMeasure) :
  CovarianceBilinear dμ_config := by
  classical
  intro c φ₁ φ₂ ψ
  -- Abbreviations for the integrands
  let u₁ : FieldConfiguration → ℂ := fun ω => distributionPairingℂ_real ω φ₁
  let u₂ : FieldConfiguration → ℂ := fun ω => distributionPairingℂ_real ω φ₂
  let v  : FieldConfiguration → ℂ := fun ω => distributionPairingℂ_real ω ψ
  have hint₁ : Integrable (fun ω => u₁ ω * v ω) dμ_config.toMeasure := by simpa using h_int φ₁ ψ
  have hint₂ : Integrable (fun ω => u₂ ω * v ω) dμ_config.toMeasure := by simpa using h_int φ₂ ψ
  have hint₃ : Integrable (fun ω => u₁ ω * u₂ ω) dμ_config.toMeasure := by simpa using h_int φ₁ φ₂

  -- 1) Scalar multiplication in the first argument
  have h_smul_left_integrand :
      (fun ω => distributionPairingℂ_real ω (c • φ₁) * distributionPairingℂ_real ω ψ)
      = (fun ω => c • (u₁ ω * v ω)) := by
    funext ω
    have h := pairing_linear_combo ω φ₁ (0 : TestFunctionℂ) c 0
    -- dp ω (c•φ₁) = c * dp ω φ₁
    have h' : distributionPairingℂ_real ω (c • φ₁) = c * distributionPairingℂ_real ω φ₁ := by
      simpa using h
    -- Multiply by the second factor and reassociate
    rw [h']
    simp [u₁, v, smul_eq_mul]
    ring
  have h1 :
      SchwingerFunctionℂ₂ dμ_config (c • φ₁) ψ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
    -- Use scalar pull-out from the integral
    have hlin : ∫ ω, c • (u₁ ω * v ω) ∂dμ_config.toMeasure
                = c • ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure := by
      simpa using (integral_smul (μ := dμ_config.toMeasure)
        (f := fun ω => u₁ ω * v ω) c)
    calc
      SchwingerFunctionℂ₂ dμ_config (c • φ₁) ψ
          = ∫ ω, distributionPairingℂ_real ω (c • φ₁) * distributionPairingℂ_real ω ψ ∂dμ_config.toMeasure := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, Fin.prod_univ_two]
      _ = ∫ ω, c • (u₁ ω * v ω) ∂dμ_config.toMeasure := by
            simp [h_smul_left_integrand]
      _ = c • ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure := hlin
      _ = c • SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, u₁, v, Fin.prod_univ_two]
      _ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
            rw [smul_eq_mul]

  -- 2) Additivity in the first argument
  have h_add_left_integrand :
      (fun ω => distributionPairingℂ_real ω (φ₁ + φ₂) * distributionPairingℂ_real ω ψ)
      = (fun ω => u₁ ω * v ω + u₂ ω * v ω) := by
    funext ω
    have h := pairing_linear_combo ω φ₁ φ₂ (1 : ℂ) (1 : ℂ)
    have h' : distributionPairingℂ_real ω (φ₁ + φ₂)
              = distributionPairingℂ_real ω φ₁ + distributionPairingℂ_real ω φ₂ := by
      simpa using h
    rw [h']
    ring

  have hsum_left : ∫ ω, (u₁ ω * v ω + u₂ ω * v ω) ∂dμ_config.toMeasure
      = ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure + ∫ ω, u₂ ω * v ω ∂dμ_config.toMeasure := by
    simpa using (integral_add (hf := hint₁) (hg := hint₂))
  have h2 :
      SchwingerFunctionℂ₂ dμ_config (φ₁ + φ₂) ψ
        = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₂ ψ := by
    calc
      SchwingerFunctionℂ₂ dμ_config (φ₁ + φ₂) ψ
          = ∫ ω, (u₁ ω * v ω + u₂ ω * v ω) ∂dμ_config.toMeasure := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, Fin.prod_univ_two, h_add_left_integrand]
      _ = ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure + ∫ ω, u₂ ω * v ω ∂dμ_config.toMeasure := hsum_left
      _ = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₂ ψ := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, u₁, u₂, v, Fin.prod_univ_two, Matrix.cons_val_zero]

  -- 3) Scalar multiplication in the second argument
  have h_smul_right_integrand :
      (fun ω => distributionPairingℂ_real ω φ₁ * distributionPairingℂ_real ω (c • ψ))
      = (fun ω => c • (u₁ ω * v ω)) := by
    funext ω
    have h := pairing_linear_combo ω ψ (0 : TestFunctionℂ) c 0
    have h' : distributionPairingℂ_real ω (c • ψ) = c * distributionPairingℂ_real ω ψ := by
      simpa using h
    rw [h']
    simp [u₁, v, smul_eq_mul]
    ring
  have h3 :
      SchwingerFunctionℂ₂ dμ_config φ₁ (c • ψ) = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
    have hlin : ∫ ω, c • (u₁ ω * v ω) ∂dμ_config.toMeasure
                = c • ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure := by
      simpa using (integral_smul (μ := dμ_config.toMeasure)
        (f := fun ω => u₁ ω * v ω) c)
    calc
      SchwingerFunctionℂ₂ dμ_config φ₁ (c • ψ)
          = ∫ ω, distributionPairingℂ_real ω φ₁ * distributionPairingℂ_real ω (c • ψ) ∂dμ_config.toMeasure := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, Fin.prod_univ_two]
      _ = ∫ ω, c • (u₁ ω * v ω) ∂dμ_config.toMeasure := by
            simp [h_smul_right_integrand]
      _ = c • ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure := hlin
      _ = c • SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, u₁, v, Fin.prod_univ_two]
      _ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
            rw [smul_eq_mul]

  -- 4) Additivity in the second argument
  have h_add_right_integrand :
      (fun ω => distributionPairingℂ_real ω φ₁ * distributionPairingℂ_real ω (ψ + φ₂))
      = (fun ω => u₁ ω * v ω + u₁ ω * u₂ ω) := by
    funext ω
    have h := pairing_linear_combo ω ψ φ₂ (1 : ℂ) (1 : ℂ)
    have h' : distributionPairingℂ_real ω (ψ + φ₂)
              = distributionPairingℂ_real ω ψ + distributionPairingℂ_real ω φ₂ := by
      simpa using h
    rw [h']
    ring

  have hsum_right : ∫ ω, (u₁ ω * v ω + u₁ ω * u₂ ω) ∂dμ_config.toMeasure
      = ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure + ∫ ω, u₁ ω * u₂ ω ∂dμ_config.toMeasure := by
    have hint₁₂ : Integrable (fun ω => u₁ ω * u₂ ω) dμ_config.toMeasure := hint₃
    simpa using (integral_add (hf := hint₁) (hg := hint₁₂))
  have h4 :
      SchwingerFunctionℂ₂ dμ_config φ₁ (ψ + φ₂)
        = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₁ φ₂ := by
    calc
      SchwingerFunctionℂ₂ dμ_config φ₁ (ψ + φ₂)
          = ∫ ω, (u₁ ω * v ω + u₁ ω * u₂ ω) ∂dμ_config.toMeasure := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, Fin.prod_univ_two, h_add_right_integrand]
      _ = ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure + ∫ ω, u₁ ω * u₂ ω ∂dμ_config.toMeasure := hsum_right
      _ = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₁ φ₂ := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, u₁, u₂, v, Fin.prod_univ_two, Matrix.cons_val_zero]

  -- Bundle the four identities
  exact And.intro h1 (And.intro h2 (And.intro h3 h4))
/-! ## Exponential Series Connection to Generating Functional

The key insight: Instead of functional derivatives, we use the constructive exponential series:
Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω) = ∑_{n=0}^∞ (i)^n/n! * S_n(J,...,J)

This approach is more elementary and constructive than functional derivatives.
-/
/-- A (centered) Gaussian field measure: the generating functional is an exponential of a quadratic form. -/
def IsGaussianMeasure (dμ : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∃ (Cov : TestFunction → TestFunction → ℝ),
    ∀ J : TestFunction,
      GJGeneratingFunctional dμ J = Complex.exp ((-(1 : ℂ) / 2) * (Cov J J : ℂ))

/-- Extract a coefficient from the one-parameter slice t ↦ f(t • J) by a simple scaling rule.
    This is a minimal placeholder consistent with series-like behavior: it scales out n!.
    Note: A more precise version would use the n-th derivative at 0 of t ↦ f(t • J) divided by n!. -/
def extractCoefficient (n : ℕ) (f : TestFunction → ℂ) (J : TestFunction) : ℂ :=
  (1 / (n.factorial : ℂ)) * f (n • J)

/-
  === Exponential series for Z[J] via Dominated Convergence (along a ray) ===

  We prove:
    Z[J] = ∑ (i)^n / n! * S_n(J,…,J),

  by expanding exp(i⟨ω,J⟩) pointwise, bounding partial sums by exp(|⟨ω,J⟩|),
  and swapping ∫ and limit. This requires only an along‑ray exponential‑moment
  hypothesis. We package that as a simple Prop and then derive your theorem.
-/

open BigOperators MeasureTheory Complex

noncomputable section
namespace AQFT_exponential_series

variable {FieldConfiguration TestFunction : Type} -- (only to appease editors)
-- (We actually use the ones from your file; no new structures introduced.)

/-- Along‑ray exponential moment: E[exp(|⟨ω,J⟩|)] < ∞.  This is precisely the
    domination we need to justify exchanging the integral with the n→∞ limit. -/
def ExpMomentAlong
    (dμ : ProbabilityMeasure _root_.FieldConfiguration) (J : _root_.TestFunction) : Prop :=
  Integrable (fun ω => Real.exp (|_root_.distributionPairing ω J|)) dμ.toMeasure

/-- Finite Taylor partial sum of the exponential `exp(i x)` (complex valued). -/
private def expIPartial (N : ℕ) (x : ℝ) : ℂ :=
  (Finset.range (N+1)).sum (fun n =>
    (Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ))

/-- Pointwise limit of the partial sums `expIPartial N x` is `exp(i x)`. -/
private lemma expIPartial_tendsto (x : ℝ) :
  Filter.Tendsto (fun N => expIPartial N x) Filter.atTop (nhds (Complex.exp (Complex.I * (x : ℂ)))) := by
  classical
  -- Power series for the complex exponential at z = i * x
  -- Use the Banach algebra version of the exponential series has-sum.
  have hsum :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (𝔸 := ℂ)
      (x := (Complex.I * (x : ℂ))))
  -- Re-express terms to match our expIPartial integrand
  have hsum' : HasSum (fun n : ℕ =>
      (Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ))
      (Complex.exp (Complex.I * (x : ℂ))) := by
    -- Rewrite ((I * x)^n)/(n!) and (·)•(·) into our summand shape
    --   (n! : ℂ)⁻¹ • (I * x)^n = I^n * x^n / (n!)
    simpa [mul_pow, div_eq_mul_inv, smul_eq_mul,
           mul_comm, mul_left_comm, mul_assoc, Complex.exp_eq_exp_ℂ]
      using hsum
  -- Partial sums over range N tend to the sum
  have htend := hsum'.tendsto_sum_nat
  -- Compose with the shift N ↦ N+1 so we get range (N+1)
  have hshift : Filter.Tendsto (fun N : ℕ => N + 1) Filter.atTop Filter.atTop := by
    simpa using (Filter.tendsto_add_atTop_nat 1)
  -- Our definition uses range (N+1), align it and conclude
  have hsum_def :
      (fun N => expIPartial N x)
        = (fun N => (Finset.range (N+1)).sum
              (fun n => (Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ))) := by
    funext N; simp [expIPartial]
  -- Final: tendsto of our partial sums
  simpa [hsum_def] using htend.comp hshift

private lemma expIPartial_norm_le (x : ℝ) (N : ℕ) :
  ‖expIPartial N x‖ ≤ Real.exp (|x|) := by
  classical
  -- 1) Triangle inequality on the finite sum
  have h₁ :
      ‖expIPartial N x‖
        ≤ (Finset.range (N+1)).sum
            (fun n => ‖(Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ)‖) := by
    simpa [expIPartial] using
      (norm_sum_le (s := Finset.range (N+1))
        (f := fun n => (Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ)))

  -- 2) Bound each term by (|x|^n)/n! and sum
  have h_term_le :
      ∀ n, ‖(Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ)‖
            ≤ (|x| : ℝ) ^ n / (n.factorial : ℝ) := by
    intro n
    have hfac_nonneg : 0 ≤ (n.factorial : ℝ) := by
      exact_mod_cast Nat.zero_le (n.factorial)
    -- Use multiplicativity of the norm and basic computations via simp
    -- ‖I^n‖ = 1, ‖(x:ℂ)^n‖ = |x|^n, ‖(n! : ℂ)‖ = n!
    simpa [norm_mul, norm_pow, div_eq_mul_inv, norm_inv] using
      (le_of_eq (by
        have := by
          simp [norm_mul, norm_pow, div_eq_mul_inv, norm_inv, hfac_nonneg]
        simpa using this))

  have h₂ :
      (Finset.range (N+1)).sum
          (fun n => ‖(Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ)‖)
        ≤ (Finset.range (N+1)).sum (fun n : ℕ => (|x| : ℝ) ^ n / (n.factorial : ℝ)) := by
    exact Finset.sum_le_sum (fun n _hn => h_term_le n)

  -- 3) Partial sums of ∑ |x|^n / n! are bounded by exp |x|
  have hsumR :
      HasSum (fun n : ℕ => (|x| : ℝ) ^ n / (n.factorial : ℝ))
             (Real.exp (|x|)) := by
    -- Banach algebra exponential series over ℝ at x = |x|
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Real.exp_eq_exp_ℝ]
      using (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) (x := (|x|)))

  have h_nonneg :
      ∀ n, 0 ≤ (|x| : ℝ) ^ n / (n.factorial : ℝ) := by
    intro n
    exact div_nonneg (pow_nonneg (abs_nonneg x) n) (by exact_mod_cast Nat.zero_le (n.factorial))

  have h₃ :
      (Finset.range (N+1)).sum (fun n => (|x| : ℝ) ^ n / (n.factorial : ℝ))
        ≤ Real.exp (|x|) := by
    -- Use the modern Summable.sum_le_tsum
    have := (hsumR.summable.sum_le_tsum (s := Finset.range (N+1))
      (by
        intro n hn
        exact h_nonneg n))
    simpa [hsumR.tsum_eq] using this

  -- 4) Chain the bounds
  exact h₁.trans (le_trans h₂ h₃)



/-- Product over `Fin n` of a constant equals the n-th power (for our integrand). -/
private lemma prod_const_pow (x : ℝ) (n : ℕ) :
  (∏ _i : Fin n, x) = x ^ n := by
  classical
  -- Standard finitary identity; available as `Finset.card_univ` + `Finset.prod_const`.
  --   ∏_{i∈univ} x = x^(Fintype.card (Fin n)) = x^n
  have h : (∏ _i : Fin n, x) = x ^ (Fintype.card (Fin n)) := by
    simpa using (Finset.prod_const (s := (Finset.univ : Finset (Fin n))) (a := x))
  simpa [Fintype.card_fin] using h

/-- Identify `S_n(J,…,J)` as the integral of the n-th power of `⟨ω,J⟩`. -/
private lemma schwinger_eq_integral_pow
  (dμ : ProbabilityMeasure _root_.FieldConfiguration) (J : _root_.TestFunction) (n : ℕ) :
  (SchwingerFunction dμ n (fun _ => J) : ℝ)
  = ∫ ω, (distributionPairing ω J) ^ n ∂ dμ.toMeasure := by
  -- Unfold `SchwingerFunction` and simplify the Finite product on `Fin n`
  -- to a power using `prod_const_pow`.
  classical
  unfold SchwingerFunction
  -- integrand: ∏ i, ⟨ω,J⟩ = (⟨ω,J⟩)^n
  -- Pointwise product-to-power identity
  have hω : ∀ ω : _root_.FieldConfiguration, (∏ _i : Fin n, distributionPairing ω J) = (distributionPairing ω J) ^ n := by
    intro ω
    simpa using (prod_const_pow (distributionPairing ω J) n)
  -- Rewrite under the integral using the pointwise identity
  simp [hω]

/-- **Main dominated convergence step along a ray**:
    If `E[exp(|⟨ω,J⟩|)] < ∞`, then
      `∫ exp(i⟨ω,J⟩) dμ = ∑ i^n/n! ∫ ⟨ω,J⟩^n dμ`,
    which is exactly your generating-functional series with `S_n(J,…,J)`.
-/
theorem generating_functional_as_series_of_expMoment
  (dμ : ProbabilityMeasure _root_.FieldConfiguration) (J : _root_.TestFunction)
  (hExp : ExpMomentAlong dμ J) :
  GJGeneratingFunctional dμ J
    = ∑' n : ℕ,
        (Complex.I ^ n / (n.factorial : ℂ))
        * (SchwingerFunction dμ n (fun _ => J) : ℂ) := by
  classical
  -- Dominating function g(ω) = exp(|⟨ω,J⟩|) (real-valued, integrable by assumption)
  have h_dom : Integrable (fun ω => (Real.exp (|distributionPairing ω J|) : ℝ)) dμ.toMeasure := hExp

  -- 1) measurability and pointwise domination for the partial sums
  have h_measF :
      ∀ N, AEStronglyMeasurable (fun ω => expIPartial N (distributionPairing ω J)) dμ.toMeasure := by
    intro N
    -- composition of a measurable real function with a polynomial (continuous) → measurable
    -- and ℂ-valued function is strongly measurable
    -- (measurability of `distributionPairing · J` is assumed in your development; `by measurability` works here)
    refine (aestronglyMeasurable_of_measurable ?m).mono_ac ?
    · -- measurability
      -- `expIPartial N` is a finite linear combination of continuous monomials, hence continuous
      -- so the composition is measurable
      -- We simply use automation:
      -- (If your project needs it, add an explicit lemma: `measurable_distributionPairing : Measurable (fun ω => distributionPairing ω J)`.)
      by measurability
    · -- absolutely continuous measure side-condition is automatic here
      exact absolutelyContinuous_of_le (by simp)

  have h_boundF :
      ∀ N, ∀ᵐ ω ∂ dμ.toMeasure,
        ‖expIPartial N (distributionPairing ω J)‖
          ≤ Real.exp (|distributionPairing ω J|) := by
    intro N
    refine eventually_of_forall (fun ω => ?_)
    simpa using expIPartial_norm_le (distributionPairing ω J) N

  -- 2) limit integrand measurability and bound
  have h_meas_lim :
      AEStronglyMeasurable
        (fun ω => Complex.exp (Complex.I * (distributionPairing ω J : ℂ)))
        dμ.toMeasure := by
    -- continuous → measurable → strongly measurable
    by measurability

  have h_bound_lim :
      ∀ᵐ ω ∂ dμ.toMeasure,
        ‖Complex.exp (Complex.I * (distributionPairing ω J : ℂ))‖
          ≤ Real.exp (|distributionPairing ω J|) := by
    -- ‖exp(i x)‖ = exp(Re(i x)) = exp(0) = 1 ≤ exp(|x|)
    refine eventually_of_forall (fun ω => ?_)
    have : ‖Complex.exp (Complex.I * (distributionPairing ω J : ℂ))‖
           = Real.exp ((Complex.I * (distributionPairing ω J : ℂ)).re) := by
      simpa using Complex.norm_exp (Complex.I * (distributionPairing ω J : ℂ))
    have hRe : (Complex.I * (distributionPairing ω J : ℂ)).re = 0 := by
      -- Re(i * x) = 0 for real x
      simp
    simp [this, hRe, one_le_exp_iff.mpr (abs_nonneg _)]

  -- 3) pointwise convergence: partial sums → complex exponential
  have h_pt :
      ∀ᵐ ω ∂ dμ.toMeasure,
        Tendsto (fun N => expIPartial N (distributionPairing ω J))
                atTop
                (nhds (Complex.exp (Complex.I * (distributionPairing ω J : ℂ)))) :=
    eventually_of_forall (fun ω => expIPartial_tendsto (distributionPairing ω J))

  -- 4) dominated convergence for the integral (complex-valued)
  have h_tend :
      Tendsto (fun N => ∫ ω, expIPartial N (distributionPairing ω J) ∂ dμ.toMeasure)
              atTop
              (nhds (∫ ω, Complex.exp (Complex.I * (distributionPairing ω J : ℂ))
                        ∂ dμ.toMeasure)) :=
    integral_tendsto_of_dominated_convergence
      (bound := fun ω => Real.exp (|distributionPairing ω J|))
      (fun N => h_measF N) h_boundF h_dom h_pt h_meas_lim h_bound_lim

  -- Turn the `tendsto` into an equality with `lim` (the limit exists and equals the integral)
  have h_int_swap :
      ∫ ω, Complex.exp (Complex.I * (distributionPairing ω J : ℂ)) ∂ dμ.toMeasure
        = lim atTop (fun N => ∫ ω, expIPartial N (distributionPairing ω J) ∂ dμ.toMeasure) := by
    -- `Filter.Tendsto.lim_eq` (a.k.a. `h_tend.lim_eq`) gives exactly this equality
    simpa using h_tend.lim_eq

  -- 5) Evaluate the integral of the finite sum, then pass to the limit
  have h_eval :
      (fun N => ∫ ω, expIPartial N (distributionPairing ω J) ∂ dμ.toMeasure)
      = (fun N =>
          (Finset.range (N+1)).sum
            (fun n =>
              (Complex.I ^ n / (n.factorial : ℂ))
              * (∫ ω, ((distributionPairing ω J : ℝ) ^ n : ℝ) ∂ dμ.toMeasure : ℂ))) := by
    funext N
    -- linearity + move constants out of the integral
    simp [expIPartial, div_eq_mul_inv, Finset.sum_mul, integral_sum,
          integral_mul_left, integral_const, integral_mul_left, mul_comm, mul_left_comm, mul_assoc]

  -- 6) Replace ∫ ⟨ω,J⟩^n with S_n(J,…,J)
  have h_S :
      ∀ n, (∫ ω, ((distributionPairing ω J : ℝ) ^ n : ℝ) ∂ dμ.toMeasure : ℂ)
             = (SchwingerFunction dμ n (fun _ => J) : ℂ) := by
    intro n
    have := schwinger_eq_integral_pow dμ J n
    simpa using congrArg (fun r => (r : ℂ)) this

  -- 7) Limit of partial sums = `tsum`
  have h_sum :
      lim atTop (fun N =>
        (Finset.range (N+1)).sum
          (fun n =>
            (Complex.I ^ n / (n.factorial : ℂ))
            * (SchwingerFunction dμ n (fun _ => J) : ℂ)))
      = ∑' n : ℕ,
          (Complex.I ^ n / (n.factorial : ℂ))
          * (SchwingerFunction dμ n (fun _ => J) : ℂ) := by
    -- standard: partial sums of a series converge to its `tsum`
    simpa using (tendsto_finset_range_sum_atTop_iff_tsum_nat
      (f := fun n => (Complex.I ^ n / (n.factorial : ℂ))
                     * (SchwingerFunction dμ n (fun _ => J) : ℂ))).symm

  -- 8) Identify `GJGeneratingFunctional` as the integral of the exponential and assemble
  have hZ :
      GJGeneratingFunctional dμ J
        = ∫ ω, Complex.exp (Complex.I * (distributionPairing ω J : ℂ)) ∂ dμ.toMeasure := by
    -- This is exactly your definition of the (complex) generating functional Z[J].
    -- If it's not by `rfl`, add a project-local simp lemma unfolding your definition.
    simp [GJGeneratingFunctional]

  calc
    GJGeneratingFunctional dμ J
        = ∫ ω, Complex.exp (Complex.I * (distributionPairing ω J : ℂ)) ∂ dμ.toMeasure := by
            simpa [hZ]
    _ = lim atTop (fun N => ∫ ω, expIPartial N (distributionPairing ω J) ∂ dμ.toMeasure) := h_int_swap
    _ = lim atTop (fun N =>
          (Finset.range (N+1)).sum
            (fun n =>
              (Complex.I ^ n / (n.factorial : ℂ))
              * (∫ ω, ((distributionPairing ω J : ℝ) ^ n : ℝ) ∂ dμ.toMeasure : ℂ))) := by
          simpa [h_eval]
    _ = lim atTop (fun N =>
          (Finset.range (N+1)).sum
            (fun n =>
              (Complex.I ^ n / (n.factorial : ℂ))
              * (SchwingerFunction dμ n (fun _ => J) : ℂ))) := by
          -- replace each integrand term using `h_S`
          refine congrArg (fun f => lim atTop f) ?_
          funext N
          refine Finset.sum_congr rfl (fun n _hn => ?_)
          simpa [mul_comm, mul_left_comm, mul_assoc] using congrArg (fun z => (Complex.I ^ n / (n.factorial : ℂ)) * z) (h_S n)
    _ = ∑' n : ℕ,
          (Complex.I ^ n / (n.factorial : ℂ))
          * (SchwingerFunction dμ n (fun _ => J) : ℂ) := h_sum

theorem generating_functional_as_series
  (dμ_config : ProbabilityMeasure FieldConfiguration) (J : TestFunction) :
  GJGeneratingFunctional dμ_config J =
  ∑' n : ℕ, (Complex.I ^ n / (n.factorial : ℂ))
          * (SchwingerFunction dμ_config n (fun _ => J) : ℂ) := by
  -- Provide (or import) the along‑ray exponential moment:
  have hExp : ExpMomentAlong dμ_config J := by
    -- For Gaussians: follows from mgf finiteness (E[e^{|X|}] < ∞]).
    -- For general measures: add your hypothesis here.
    sorry
  exact generating_functional_as_series_of_expMoment dμ_config J hExp


theorem generating_functional_as_series (dμ_config : ProbabilityMeasure FieldConfiguration) (J : TestFunction) :
  GJGeneratingFunctional dμ_config J =
  ∑' n : ℕ, (Complex.I ^ n / (n.factorial : ℂ)) * (SchwingerFunction dμ_config n (fun _ => J) : ℂ) := by
  sorry

/-- For centered measures (zero mean), the generating functional starts with the quadratic term.
    Z[J] = 1 + (i)²/2! * S₂(J,J) + (i)³/3! * S₃(J,J,J) + ...,
         = 1 - ½S₂(J,J) - (i/6)S₃(J,J,J) + ... -/
theorem generating_functional_centered (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_centered : ∀ f : TestFunction, GJMean dμ_config f = 0) (J : TestFunction) :
  GJGeneratingFunctional dμ_config J =
  1 + ∑' n : ℕ, if n = 0 then 0 else (Complex.I ^ n / (n.factorial : ℂ)) * (SchwingerFunction dμ_config n (fun _ => J) : ℂ) := by
  sorry

/-- Gaussian case: only even Schwinger functions are non-zero.
    For Gaussian measures, S_{2n+1} = 0 and S_{2n} follows Wick's theorem. -/
theorem generating_functional_gaussian (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_gaussian : IsGaussianMeasure dμ_config) (J : TestFunction) :
  GJGeneratingFunctional dμ_config J =
  ∑' n : ℕ, ((-1)^n / ((2*n).factorial : ℂ)) * (SchwingerFunction dμ_config (2*n) (fun _ => J) : ℂ) := by
  sorry

/-- The fundamental inversion formula: extracting Schwinger functions from the generating functional.
    This shows how to compute correlation functions from the generating functional. -/
theorem schwinger_function_from_series_coefficient (dμ_config : ProbabilityMeasure FieldConfiguration)
  (n : ℕ) (J : TestFunction) :
  SchwingerFunction dμ_config n (fun _ => J) =
  (-Complex.I)^n * (n.factorial : ℂ) * (extractCoefficient n (GJGeneratingFunctional dμ_config) J) := by
  sorry

/-! ## Schwinger Functions as Distributions

The Schwinger functions can also be viewed as distributions (measures/densities)
on the product space (SpaceTime)^n. This is the traditional QFT perspective where
S_n is a distribution S_n ∈ 𝒟'((SpaceTime)^n) such that:

∫ ⟨ω,f₁⟩ ⟨ω,f₂⟩ ... ⟨ω,fₙ⟩ dμ(ω) = ⟪S_n, f₁ ⊗ f₂ ⊗ ... ⊗ fₙ⟫

where f₁ ⊗ f₂ ⊗ ... ⊗ fₙ is the tensor product test function on (SpaceTime)^n.

This perspective is essential for:
- Locality and support properties
- Lorentz invariance
- Cluster decomposition
- Connection to Wightman axioms
-/

/-- The product space of n copies of spacetime -/
abbrev SpaceTimeProduct (n : ℕ) := (Fin n) → SpaceTime

/-- Test functions on the n-fold product space -/
abbrev TestFunctionProduct (n : ℕ) := SchwartzMap (SpaceTimeProduct n) ℝ

/-- Complex test functions on the n-fold product space -/
abbrev TestFunctionProductℂ (n : ℕ) := SchwartzMap (SpaceTimeProduct n) ℂ

/-- The tensor product of n test functions gives a test function on the product space.
    This represents f₁(x₁) ⊗ f₂(x₂) ⊗ ... ⊗ fₙ(xₙ) = f₁(x₁) * f₂(x₂) * ... * fₙ(xₙ) -/
def tensorProductTestFunction (n : ℕ) (f : Fin n → TestFunction) : TestFunctionProduct n := sorry

/-- Complex version of tensor product -/
def tensorProductTestFunctionℂ (n : ℕ) (f : Fin n → TestFunctionℂ) : TestFunctionProductℂ n := sorry

/-- Placeholder for Dirac delta as a test function (needed for distribution theory) -/
def DiracDelta (x : SpaceTime) : TestFunction := sorry

/-- Complex version of Dirac delta -/
def DiracDelta_complex (x : SpaceTime) : TestFunctionℂ := sorry

/-- The Schwinger distribution S_n as a distribution on (SpaceTime)^n.
    This is the fundamental object in the Wightman framework.

    The pairing ⟪S_n, F⟫ for test function F on (SpaceTime)^n gives the
    correlation function value. -/
def SchwingerDistribution (dμ_config : ProbabilityMeasure FieldConfiguration) (n : ℕ) :
  TestFunctionProduct n → ℝ :=
  fun F => ∫ x, F x * (∫ ω, (∏ i, distributionPairing ω (DiracDelta (x i))) ∂dμ_config.toMeasure) ∂(volume : Measure (SpaceTimeProduct n))

/-- A more practical definition: the Schwinger distribution evaluated on tensor products.
    This gives the standard n-point correlation function. -/
def SchwingerDistributionOnTensor (dμ_config : ProbabilityMeasure FieldConfiguration) (n : ℕ)
  (f : Fin n → TestFunction) : ℝ :=
  SchwingerFunction dμ_config n f

/-- The fundamental relationship: evaluating the Schwinger distribution on a tensor product
    of test functions gives the same result as the direct Schwinger function definition. -/
lemma schwinger_distribution_tensor_eq (dμ_config : ProbabilityMeasure FieldConfiguration)
  (n : ℕ) (f : Fin n → TestFunction) :
  SchwingerDistributionOnTensor dμ_config n f = SchwingerFunction dμ_config n f := by
  unfold SchwingerDistributionOnTensor
  rfl

/-- For practical computations, we need a more direct definition of the Schwinger distribution.
    This version takes a general test function on (SpaceTime)^n and integrates it against
    the n-point correlation measure. -/
def SchwingerDistributionDirect (dμ_config : ProbabilityMeasure FieldConfiguration) (n : ℕ)
  (F : TestFunctionProduct n) : ℝ :=
  ∫ ω, ∫ x, F x * (∏ i, distributionPairing ω (DiracDelta (x i))) ∂(volume : Measure (SpaceTimeProduct n)) ∂dμ_config.toMeasure

/-- The Schwinger distribution satisfies the tensor product property.
    When the test function F is a tensor product f₁ ⊗ ... ⊗ fₙ,
    the distribution evaluation reduces to the standard Schwinger function. -/
theorem schwinger_distribution_tensor_property (dμ_config : ProbabilityMeasure FieldConfiguration)
  (n : ℕ) (f : Fin n → TestFunction) :
  SchwingerDistributionDirect dμ_config n (tensorProductTestFunction n f) =
  SchwingerFunction dμ_config n f := by
  sorry

/-- Complex version of the Schwinger distribution -/
def SchwingerDistributionℂ (dμ_config : ProbabilityMeasure FieldConfiguration) (n : ℕ)
  (F : TestFunctionProductℂ n) : ℂ :=
  ∫ ω, ∫ x, F x * (∏ i, distributionPairingℂ_real ω (DiracDelta_complex (x i))) ∂(volume : Measure (SpaceTimeProduct n)) ∂dμ_config.toMeasure

/-- The 2-point Schwinger distribution encodes the field covariance structure -/
def TwoPointSchwingerDistribution (dμ_config : ProbabilityMeasure FieldConfiguration) :
  TestFunctionProduct 2 → ℝ :=
  SchwingerDistributionDirect dμ_config 2

/-- The 2-point distribution evaluated on the tensor product f₁ ⊗ f₂ gives the covariance -/
lemma two_point_distribution_eq_covariance (dμ_config : ProbabilityMeasure FieldConfiguration)
  (f g : TestFunction) :
  TwoPointSchwingerDistribution dμ_config (tensorProductTestFunction 2 ![f, g]) =
  SchwingerFunction₂ dμ_config f g := by
  sorry

/-! ## Locality and Spacetime Properties

Properties related to causality, locality, and spacetime symmetries.
-/

/-- Placeholder definitions for geometric and measure-theoretic concepts -/
def translation_invariant_measure (dμ : ProbabilityMeasure FieldConfiguration) (a : SpaceTime) : Prop := sorry
def translate_product_test_function {n : ℕ} (F : TestFunctionProduct n) (a : SpaceTime) : TestFunctionProduct n := sorry

/-- Euclidean locality property: correlation functions depend on relative distances.
    In Euclidean QFT, locality is expressed through clustering and decay properties
    rather than causal separation. -/
theorem schwinger_distribution_euclidean_locality (dμ_config : ProbabilityMeasure FieldConfiguration)
  (n : ℕ) (F : TestFunctionProduct n) :
  -- In Euclidean QFT, locality manifests as clustering: correlations decay with distance
  -- This is a placeholder for proper Euclidean locality properties
  SchwingerDistributionDirect dμ_config n F = sorry := by
  sorry

/-- Translation invariance: if the measure is translation invariant,
    then S_n(x₁,...,xₙ) = S_n(x₁+a,...,xₙ+a) for any spacetime vector a. -/
theorem schwinger_distribution_translation_invariance
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_trans_inv : ∀ a : SpaceTime, translation_invariant_measure dμ_config a)
  (n : ℕ) (F : TestFunctionProduct n) (a : SpaceTime) :
  SchwingerDistributionDirect dμ_config n F =
  SchwingerDistributionDirect dμ_config n (translate_product_test_function F a) := by
  sorry

/-! ## CLM Invariance Properties

Continuous linear map (CLM) invariance is a fundamental symmetry property in QFT.
If the generating functional is invariant under a CLM L, then the underlying
correlation structure (Schwinger functions) should also be invariant.
-/

/-- **CLM Invariance of 2-Point Schwinger Functions**

    If the generating functional is invariant under a continuous linear map L
    on complex test functions, then the 2-point Schwinger function is also invariant.

    This is the general Schwinger function version of the result proven in OS3.lean
    for Gaussian measures. The key insight is that symmetries of the generating
    functional (which encodes the full measure) must be reflected in all n-point
    correlation functions.

    Mathematical statement: If Z[L h] = Z[h] for all h, then S₂(L f, L g) = S₂(f, g).

    This lemma provides the foundation for proving rotation invariance, translation
    invariance, and other continuous symmetries of correlation functions from
    corresponding invariances of the generating functional.
-/
lemma schwinger_function_clm_invariant
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (L : TestFunctionℂ →L[ℝ] TestFunctionℂ)
  (h_invariant : ∀ h : TestFunctionℂ,
    GJGeneratingFunctionalℂ dμ_config (L h) = GJGeneratingFunctionalℂ dμ_config h)
  (f g : TestFunctionℂ) :
  SchwingerFunctionℂ₂ dμ_config (L f) (L g) = SchwingerFunctionℂ₂ dμ_config f g := by
  -- Proof strategy:
  -- 1. Express S₂(f,g) in terms of functional derivatives of Z[h] at h=0
  -- 2. Use the chain rule: ∂²Z[h]/∂f∂g = ∂²Z[L⁻¹h]/∂(Lf)∂(Lg) when Z[Lh] = Z[h]
  -- 3. The invariance h_invariant allows us to relate derivatives at different points
  -- 4. For Gaussian measures, this reduces to the covariance invariance proven in OS3.lean
  --
  -- The full proof requires:
  -- - Functional derivative machinery for relating S₂ to Z
  -- - Properties of continuous linear maps on test function spaces
  -- - Analysis of how CLM invariance propagates through functional derivatives
  --
  -- This is a fundamental result connecting global symmetries (generating functional
  -- invariance) to local correlation properties (Schwinger function invariance).
  sorry

/-- **CLM Invariance for General n-Point Schwinger Functions**

    Generalization to arbitrary n-point functions: if the generating functional
    is invariant under L, then all Schwinger functions are invariant.

    This provides a systematic way to prove symmetry properties of all correlation
    functions from symmetries of the generating functional.
-/
lemma schwinger_function_clm_invariant_general
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (L : TestFunctionℂ →L[ℝ] TestFunctionℂ)
  (h_invariant : ∀ h : TestFunctionℂ,
    GJGeneratingFunctionalℂ dμ_config (L h) = GJGeneratingFunctionalℂ dμ_config h)
  (n : ℕ) (f : Fin n → TestFunctionℂ) :
  SchwingerFunctionℂ dμ_config n (fun i => L (f i)) = SchwingerFunctionℂ dμ_config n f := by
  -- This follows from the same functional derivative argument as the 2-point case,
  -- extended to n-th order derivatives. The key insight is that CLM invariance
  -- of the generating functional implies invariance of all its functional derivatives.
  sorry

/-! ## Summary

The Schwinger function framework provides:

### 1. Moment-based Definition (SchwingerFunction)
- Direct integration of field operator products
- Natural for computational purposes
- Connection to generating functionals via exponential series

### 2. Distribution-based Definition (SchwingerDistribution)
- Traditional QFT perspective on (SpaceTime)^n
- Essential for locality, causality, Lorentz invariance
- Connection to Wightman axioms

### 3. Exponential Series Connection
- Constructive approach: Z[J] = ∑ (i)^n/n! * S_n(J,...,J)
- More elementary than functional derivatives
- Natural for Gaussian measures and Wick's theorem

### 4. Spacetime Properties
- Locality and causality via support properties
- Translation invariance and spacetime symmetries
- Foundation for proving OS axioms
-/
