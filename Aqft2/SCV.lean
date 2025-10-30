/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

## Several Complex Variables (SCV) for AQFT

This file provides the theory of several complex variables needed for the OS-0 (analyticity) axiom
in the Osterwalder-Schrader framework. It focuses on complex analyticity of generating functionals
and the crucial polynomial structure that emerges from bilinear forms on test functions.

### Key Definitions & Structures:

**Complex Variable Foundations:**
- `ℂn`: Type abbreviation for `Fin n → ℂ` (n-dimensional complex space)
- `Entire`: Predicate for entire functions (analytic on all of ℂⁿ)
- Complex analyticity using Mathlib's `AnalyticOn ℂ f Set.univ`

**Linear Combinations of Test Functions:**
- `weightedSumCLM`: Continuous linear map `ℂⁿ →L[ℂ] TestFunctionℂ`
- Maps coefficient vector `z : ℂⁿ` to test function `∑ᵢ zᵢ • Jᵢ`
- Automatic continuity from finite-dimensional domain
- Foundation for complex analytic generating functionals

**Gaussian Functions and Analyticity:**
- `gaussian1`: Single-variable Gaussian `exp(-z²)` on ℂ
- `gaussian`: Multi-variable Gaussian `exp(-∑ᵢ zᵢ²)` on ℂⁿ
- `h_exp_arg`: Proof that `-z²` is analytic
- `gaussian1_entire`: Proof that single Gaussian is entire
- `sumSquares_analytic`: Proof that `∑ᵢ zᵢ²` is analytic on ℂⁿ

**Analyticity Machinery:**
- Coordinate projections are analytic: `(x : ℂⁿ) ↦ xᵢ`
- Powers preserve analyticity: `f^n` analytic if `f` analytic
- Finite sums preserve analyticity: `∑ᵢ fᵢ` analytic if each `fᵢ` analytic
- Composition with exponential: `exp ∘ f` analytic if `f` analytic

**Connection to L² Bilinear Forms (Framework):**
- `L2BilinearForm_polynomial_in_coefficients`: Key theorem (commented/framework)
- Shows that L² bilinear forms give polynomial dependence in complex coefficients
- Essential for proving analyticity of generating functionals
- Links to exp(-½⟨∑ᵢ zᵢJᵢ, ∑ⱼ zⱼJⱼ⟩) structure

**Mathematical Foundation:**
Establishes analyticity for OS-0: symmetric bilinear forms ⟨∑ᵢ zᵢJᵢ, ∑ⱼ zⱼJⱼ⟩ = ∑ᵢⱼ zᵢzⱼ⟨Jᵢ,Jⱼ⟩
give polynomial dependence (no conjugation) → exp(polynomial) is entire → Z[∑ᵢ zᵢJᵢ] analytic.

**Integration:** Links to `Basic` (test functions), `OS_Axioms` (OS-0), and L² theory for
analytic continuation from Euclidean to Minkowski QFT.

General facts about functions of several complex variables.
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Aqft2.Basic  -- For test functions and distribution framework
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.RCLike.Extend

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density

import Aqft2.Basic

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure

namespace SCV

noncomputable section
open scoped MeasureTheory Complex BigOperators

abbrev ℂn (n : ℕ) := Fin n → ℂ

def Entire {n : ℕ} (f : ℂn n → ℂ) : Prop :=
  AnalyticOn ℂ f Set.univ          --  ⇔  ∀ z, HolomorphicAt ℂ f z

variable (x : ℂ) (f : TestFunctionℂ)

#check x • f        -- Lean should report:  `x • f : TestFunctionℂ`

variable (n : ℕ)
variable (J : Fin n → TestFunctionℂ)   -- test functions
variable (z : ℂn n)               -- coefficients

/-- **Linear combination operator**
    `weightedSumCLM J` takes a coefficient vector `z : ℂⁿ` and returns the test
    function `∑ i, z i • J i`.  Being linear and the domain finite-dimensional,
    it is automatically continuous, so we package it as a `ContinuousLinearMap`. -/

noncomputable
def weightedSumCLM : ℂn n →L[ℂ] TestFunctionℂ := by
  let L : ℂn n →ₗ[ℂ] TestFunctionℂ :=
    { toFun      := fun z ↦ (Finset.univ).sum (fun i ↦ z i • J i),
      map_add'   := by
        intro z₁ z₂
        simp [add_smul, Finset.sum_add_distrib],
      map_smul' := by
        intro c z
        simp [smul_smul, Finset.smul_sum]
    }
  have hcont : Continuous L := L.continuous_of_finiteDimensional
  exact { toLinearMap := L, cont := hcont }


/- tests of ability to prove functions are analytic -/

def gaussian1 (z : ℂ) : ℂ := Complex.exp (-(z ^ 2))

lemma h_exp_arg : AnalyticOn ℂ (fun z : ℂ ↦ -(z ^ 2)) Set.univ :=
  ((analyticOn_id (𝕜 := ℂ) (E := ℂ) (s := Set.univ)).pow 2).neg

/-- The Gaussian is analytic on all of ℂ – i.e. *entire*. -/
lemma gaussian1_entire : AnalyticOn ℂ gaussian1 Set.univ := by
 simpa [gaussian1] using
  ((analyticOn_id (𝕜 := ℂ) (E := ℂ) (s := Set.univ)).pow 2).neg.cexp

def gaussian (x : ℂn n) : ℂ := Complex.exp (-∑ i, (x i)^2)

lemma sumSquares_analytic {n : ℕ} :
    AnalyticOn ℂ (fun x : ℂn n ↦ ∑ i, (x i) ^ 2) Set.univ := by
  /- 1.  Each coordinate projection is analytic-on-a-neighbourhood. -/
  have h_coord (i : Fin n) :
      AnalyticOnNhd ℂ (fun x : ℂn n ↦ x i) Set.univ :=
      (ContinuousLinearMap.proj i : ℂn n →L[ℂ] ℂ).analyticOnNhd _

  /- 2.  Square it (`(hf).pow 2`) – still `AnalyticOnNhd`. -/
  have h_sq (i : Fin n) :
      AnalyticOnNhd ℂ (fun x : ℂn n ↦ (x i) ^ 2) Set.univ :=
      (h_coord i).pow 2

  have h_sum_aux :
      AnalyticOnNhd ℂ
        (fun x : ℂn n ↦ ∑ i ∈ (Finset.univ : Finset (Fin n)), (x i) ^ 2)
        Set.univ := by
          have : (fun x : ℂn n ↦ ∑ i ∈ (Finset.univ : Finset (Fin n)), (x i) ^ 2) =
                 ∑ i ∈ (Finset.univ : Finset (Fin n)), (fun x : ℂn n ↦ (x i) ^ 2) := by
            ext x
            simp only [Finset.sum_apply]
          rw [this]
          apply Finset.analyticOnNhd_sum
          intro i _hi
          exact h_sq i

  simpa [Finset.sum_apply] using h_sum_aux.analyticOn

/-
/-- Key theorem: The L2 bilinear form on test functions gives polynomial dependence in complex coefficients.
    This is exactly what we need for complex analyticity of the generating functional!

    NOTE: Commented out because L2BilinearForm has been moved to L2FieldSpace.lean
    This theorem depends on the old L² framework that's being refactored.
    -/
theorem L2BilinearForm_polynomial_in_coefficients (n : ℕ) (J : Fin n → TestFunctionℂ) :
  AnalyticOn ℂ (fun z : ℂn n =>
    Complex.exp (-(1/2 : ℂ) * L2BilinearForm
      ((∑ i, z i • J i).toLp (p := 2) (μ := μ))
      ((∑ i, z i • J i).toLp (p := 2) (μ := μ)))) Set.univ := by
  -- Strategy:
  -- 1. The L2BilinearForm expands to ∑ᵢ ∑ⱼ zᵢ * zⱼ * L2BilinearForm(Jᵢ, Jⱼ)
  -- 2. This is a polynomial in z (quadratic form with NO conjugation)
  -- 3. exp(polynomial) is entire
  -- 4. The key insight: TRUE bilinear form ⇒ no conjugation ⇒ analyticity preserved

  apply AnalyticOn.cexp
  apply AnalyticOn.mul
  · -- The constant -(1/2) is analytic
    exact analyticOn_const
  · -- The L2BilinearForm gives a polynomial (quadratic form)
    -- Use L2BilinearForm_linear_combination to expand the sum
    -- The result ∑ᵢ ∑ⱼ zᵢ * zⱼ * L2BilinearForm(Jᵢ, Jⱼ) is polynomial in z
    -- Polynomials are analytic
    sorry -- Apply polynomial analyticity using the bilinear expansion
-/
