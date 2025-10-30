/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

## Gaussian Free Field Construction via Minlos Theorem

This file constructs Gaussian probability measures on field configurations using
the Minlos theorem. The key insight: a Gaussian measure is uniquely determined
by its covariance function, and nuclear covariances give measures on tempered distributions.

### Integrability strategy

To prove that Gaussian pairings belong to \(L^2\) under the free field measure, we considered two
approaches:

1. **Option A (analytic infrastructure):** Equip `FieldConfiguration` with the strong dual topology
  so that evaluation maps become continuous linear functionals in Mathlib's sense, then appeal to
  Fernique's theorem (`ProbabilityTheory.IsGaussian.memLp_dual`).
2. **Option B (axiomatic shortcut):** Introduce an axiom asserting that every distribution pairing
  has finite moments of all orders with respect to `gaussianFreeField_free`. This avoids the
  topological work at the cost of a temporary assumption.

For now we adopt **Option B** via the axiom `gaussianFreeField_pairing_memLp`. Future work should
replace this axiom by implementing the analytic infrastructure described in Option A.

### Core Framework:

**Covariance Structure:**
- `CovarianceFunction`: Symmetric, bilinear, positive semidefinite covariance with boundedness
- `CovarianceNuclear`: Nuclear (trace class) condition required for Minlos theorem
- `SchwingerFunctionℂ₂`: Complex 2-point correlation function ⟨φ(f)φ(g)⟩

**Gaussian Characterization:**
- `isCenteredGJ`: Zero mean condition for Gaussian measures
- `isGaussianGJ`: Generating functional Z[J] = exp(-½⟨J, CJ⟩) for centered Gaussian

### Minlos Construction:

**Main Constructor:**
- `constructGaussianMeasureMinlos_free`: Specialized construction for free field via Minlos theorem

**Note:** General Minlos construction for arbitrary nuclear covariance functions
is available in `Aqft2.GeneralMinlos` (incomplete, contains sorry statements).

### Free Field Realization:

**Klein-Gordon Propagator:**
- `freeFieldPropagator`: C(k) = 1/(ik² + m²) in momentum space
- `freeFieldCovariance`: Covariance built from propagator via Fourier transform
- `freeFieldCovariance_nuclear`: Proof of nuclear condition for m > 0, d < 4

**Main Result:**
- `gaussianFreeField`: The Gaussian Free Field measure for mass m > 0

### Mathematical Foundation:

**Minlos Theorem:** For nuclear covariance C on Schwartz space S(ℝᵈ), there exists
unique probability measure μ on S'(ℝᵈ) with characteristic functional Z[f] = exp(-½⟨f,Cf⟩).

**Nuclear Condition:** Tr(C) = ∫ 1/(k² + m²) dk < ∞ for d < 4 (with m > 0).
Essential for extending cylindrical measures to σ-additive measures on S'(ℝᵈ).

**Advantages:** Direct infinite-dimensional construction without Kolmogorov extension,
standard approach in constructive QFT, handles dimension restrictions naturally.

### Integration:

**AQFT Connections:** Uses `Basic` (field configurations), `Minlos` (measure theory),
`Schwinger` (correlation functions), provides foundation for OS axiom verification.

**Implementation:** Core mathematical structure complete, ready for nuclear condition
proofs and explicit Fourier transform implementation.

Standard approach for constructing Gaussian Free Fields in quantum field theory.
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique

import Aqft2.Basic
import Aqft2.Schwinger
import Aqft2.Minlos
import Aqft2.Covariance
import Aqft2.MinlosAnalytic
import Aqft2.MixedDerivLemma
import Aqft2.ComplexTestFunction

open MeasureTheory Complex
open TopologicalSpace SchwartzMap

noncomputable section

/-! ## Gaussian Measures on Field Configurations
-/

/-- A covariance function on test functions that determines the Gaussian measure -/
structure CovarianceFunction where
  covar : TestFunctionℂ → TestFunctionℂ → ℂ
  symmetric : ∀ f g, covar f g = (starRingEnd ℂ) (covar g f)
  bilinear_left : ∀ c f₁ f₂ g, covar (c • f₁ + f₂) g = c * covar f₁ g + covar f₂ g
  bilinear_right : ∀ f c g₁ g₂, covar f (c • g₁ + g₂) = (starRingEnd ℂ) c * covar f g₁ + covar f g₂
  positive_semidefinite : ∀ f, 0 ≤ (covar f f).re
  bounded : ∃ M > 0, ∀ f, ‖covar f f‖ ≤ M * (∫ x, ‖f x‖ ∂volume) * (∫ x, ‖f x‖^2 ∂volume)^(1/2)

/-- A measure is centered (has zero mean) -/
def isCenteredGJ (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (f : TestFunction), GJMean dμ_config f = 0

/-- A measure is Gaussian if its generating functional has the Gaussian form.
    For a centered Gaussian measure, Z[J] = exp(-½⟨J, CJ⟩) where C is the covariance. -/
def isGaussianGJ (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  isCenteredGJ dμ_config ∧
  ∀ (J : TestFunctionℂ),
    GJGeneratingFunctionalℂ dμ_config J =
    Complex.exp (-(1/2 : ℂ) * SchwingerFunctionℂ₂ dμ_config J J)

/-! ## Construction via Minlos Theorem -/

/-- Nuclear space structure for real test functions (axiom placeholder). -/
axiom nuclear_TestFunctionR : NuclearSpace TestFunctionR

/-- Instance to enable typeclass resolution for NuclearSpace on TestFunctionR. -/
instance instNuclear_TestFunctionR : NuclearSpace TestFunctionR := nuclear_TestFunctionR

/-- Specialized Minlos construction for the free field using the square-root propagator embedding. -/
noncomputable def constructGaussianMeasureMinlos_free (m : ℝ) [Fact (0 < m)] :
  ProbabilityMeasure FieldConfiguration := by
  classical
  -- Build the embedding T with ‖T f‖² = freeCovarianceFormR m f f
  have ex1 := sqrtPropagatorEmbedding m
  let H : Type := Classical.choose ex1
  have ex2 := Classical.choose_spec ex1
  let hSem : SeminormedAddCommGroup H := Classical.choose ex2
  have ex3 := Classical.choose_spec ex2
  let hNorm : NormedSpace ℝ H := Classical.choose ex3
  have ex4 := Classical.choose_spec ex3
  let T : TestFunctionR →ₗ[ℝ] H := Classical.choose ex4
  have h_eq : ∀ f : TestFunctionR, freeCovarianceFormR m f f = ‖T f‖^2 := Classical.choose_spec ex4
  -- Continuity and normalization
  have h_cont := freeCovarianceFormR_continuous m
  have h_zero : freeCovarianceFormR m (0) (0) = 0 := by simp [freeCovarianceFormR]
  -- Use Minlos: directly obtain a ProbabilityMeasure with the Gaussian characteristic functional
  have h_minlos :=
    gaussian_measure_characteristic_functional
      (E := TestFunctionR) (H := H) T (freeCovarianceFormR m)
      (by intro f; simpa using h_eq f)
      True.intro h_zero h_cont
  exact Classical.choose h_minlos

/-- The Gaussian Free Field with mass m > 0, constructed via specialized Minlos -/
noncomputable def gaussianFreeField_free (m : ℝ) [Fact (0 < m)] : ProbabilityMeasure FieldConfiguration :=
  constructGaussianMeasureMinlos_free m

/-- Real characteristic functional of the free GFF: for real test functions f, the generating
    functional equals the Gaussian form with the real covariance. -/
theorem gff_real_characteristic (m : ℝ) [Fact (0 < m)] :
  ∀ f : TestFunctionR,
    GJGeneratingFunctional (gaussianFreeField_free m) f =
      Complex.exp (-(1/2 : ℂ) * (freeCovarianceFormR m f f : ℝ)) := by
  classical
  -- Rebuild the same Minlos construction to access its specification
  have ex1 := sqrtPropagatorEmbedding m
  let H : Type := Classical.choose ex1
  have ex2 := Classical.choose_spec ex1
  let hSem : SeminormedAddCommGroup H := Classical.choose ex2
  have ex3 := Classical.choose_spec ex2
  let hNorm : NormedSpace ℝ H := Classical.choose ex3
  have ex4 := Classical.choose_spec ex3
  let T : TestFunctionR →ₗ[ℝ] H := Classical.choose ex4
  have h_eq : ∀ f : TestFunctionR, freeCovarianceFormR m f f = ‖T f‖^2 := Classical.choose_spec ex4
  have h_cont := freeCovarianceFormR_continuous m
  have h_zero : freeCovarianceFormR m (0) (0) = 0 := by simp [freeCovarianceFormR]
  have h_minlos :=
    gaussian_measure_characteristic_functional
      (E := TestFunctionR) (H := H) T (freeCovarianceFormR m)
      (by intro f; simpa using h_eq f)
      True.intro h_zero h_cont
  -- Unfold the definition of our chosen ProbabilityMeasure to reuse the spec
  have hchar := (Classical.choose_spec h_minlos)
  intro f
  -- By definition, gaussianFreeField_free chooses the same ProbabilityMeasure
  -- returned by gaussian_measure_characteristic_functional
  simpa [gaussianFreeField_free, constructGaussianMeasureMinlos_free,
        GJGeneratingFunctional, gaussian_characteristic_functional,
        distributionPairing]
    using (hchar f)

/-- Standard fact (placeholder): a Gaussian measure with even real characteristic functional
    is centered. Will be replaced by a proof via pushforward invariance under ω ↦ -ω. -/
axiom gaussianFreeField_free_centered (m : ℝ) [Fact (0 < m)] :
  isCenteredGJ (gaussianFreeField_free m)

/-- The Gaussian Free Field measure constructed via Minlos is a Gaussian measure.
    This follows from the construction but requires connecting our explicit Minlos construction
    to mathlib's IsGaussian typeclass. Asserted as axiom for now. -/
axiom gaussianFreeField_free_isGaussian (m : ℝ) [Fact (0 < m)] :
  ProbabilityTheory.IsGaussian (gaussianFreeField_free m).toMeasure

/-- Fernique-type axiom: every distribution pairing has finite moments of all orders under the
free Gaussian Free Field measure. -/
axiom gaussianFreeField_pairing_memLp
  (m : ℝ) [Fact (0 < m)] (φ : TestFunction) (p : ENNReal) (hp : p ≠ ⊤) :
  MemLp (distributionPairingCLM φ) p (gaussianFreeField_free m).toMeasure

/-- Fernique-type exponential integrability for the smeared field.
For every real test function `φ`, there exists `α > 0` such that
`exp (α ⋅ (⟨X, φ⟩)^2)` is integrable under the free Gaussian GFF measure. -/
axiom gaussianFreeField_pairing_expSq_integrable
  (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
  ∃ α : ℝ, 0 < α ∧
    Integrable
      (fun ω =>
        Real.exp (α * (distributionPairingCLM φ ω)^2))
      (gaussianFreeField_free m).toMeasure

/-- For real test functions, the square of the Gaussian pairing is integrable under the
    free Gaussian Free Field measure. This is the diagonal (f = g) case needed for
    establishing two-point integrability. -/
lemma gaussian_pairing_square_integrable_real
    (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
  Integrable (fun ω => (distributionPairing ω φ) ^ 2)
    (gaussianFreeField_free m).toMeasure := by
  -- Option B: invoke the Fernique-type axiom giving Lᵖ moments for the pairing
  have h_memLp :=
    gaussianFreeField_pairing_memLp m φ ((2 : ℕ) : ENNReal) (by simp)
  -- L² membership directly implies integrability of the square
  have h_integrable_CLM := h_memLp.integrable_sq
  -- Translate the statement from the continuous linear map to the scalar pairing
  simpa [distributionPairingCLM_apply] using h_integrable_CLM

end
