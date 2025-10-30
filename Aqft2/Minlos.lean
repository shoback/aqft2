/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

Minlos Theorem and Bochner's Theorem

This file contains foundational results for constructing infinite-dimensional Gaussian measures,
including Bochner's theorem for finite dimensions and the Minlos theorem for nuclear spaces.

Key results:
- IsPositiveDefinite: Definition of positive-definite functions
- bochner_Rn: Bochner's theorem in finite dimensions (characteristic functions)
- Future: Minlos theorem for infinite-dimensional construction
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2

open Complex MeasureTheory Matrix
open BigOperators

noncomputable section

/-! ## Positive Definiteness -/

/-- A function φ : α → ℂ is positive definite if for any finite collection
    of points x₁, ..., xₘ and complex coefficients c₁, ..., cₘ, we have
    ∑ᵢⱼ c̄ᵢ cⱼ φ(xᵢ - xⱼ) ≥ 0

    This is the standard definition in harmonic analysis and probability theory. -/
def IsPositiveDefinite {α : Type*} [AddGroup α] (φ : α → ℂ) : Prop :=
  ∀ (m : ℕ) (x : Fin m → α) (c : Fin m → ℂ),
    0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * φ (x i - x j)).re

/-! ## Bochner's Theorem -/

/-- Bochner's theorem in finite dimensions (ℝⁿ):
    A continuous positive-definite function φ with φ(0) = 1 is the Fourier transform
    (characteristic function) of a unique probability measure.

    This is a fundamental result connecting harmonic analysis and probability theory.
    The infinite-dimensional generalization (Minlos theorem) is used to construct
    the Gaussian Free Field. -/
axiom bochner_Rn
  {n : ℕ} (φ : (Fin n → ℝ) → ℂ)
  (hcont : Continuous φ)
  (hpd : IsPositiveDefinite φ)
  (hnorm : φ 0 = 1) :
  ∃ μ : Measure (Fin n → ℝ), IsProbabilityMeasure μ ∧
    (∀ t, φ t = ∫ ξ, Complex.exp (I * (∑ i, t i * ξ i)) ∂μ)
  -- Standard proof via Stone-Weierstrass and Riesz representation

/-- Lévy uniqueness of characteristic functions on ℝⁿ:
    If two probability measures have identical characteristic functions for all
    real frequencies, then the measures are equal. -/
axiom levy_cf_uniqueness_Rn
  {n : ℕ}
  (μ₁ μ₂ : ProbabilityMeasure (Fin n → ℝ)) :
  (∀ t : (Fin n → ℝ),
    ∫ ξ, Complex.exp (I * (∑ i, t i * ξ i)) ∂μ₁.toMeasure =
    ∫ ξ, Complex.exp (I * (∑ i, t i * ξ i)) ∂μ₂.toMeasure) →
  μ₁ = μ₂

/-! ## Minlos Theorem -/

/-- A nuclear locally convex space. This is a placeholder for the proper nuclear space structure.
    In practice, E would be the Schwartz space S(ℝᵈ) with its nuclear topology. -/
class NuclearSpace (E : Type*) [AddCommGroup E] [TopologicalSpace E] : Prop where
  nuclear : True  -- Placeholder for nuclear condition

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

-- We need a measurable space structure on the weak dual
instance : MeasurableSpace (WeakDual ℝ E) := borel _

/-- **Minlos Theorem**: Existence of infinite-dimensional probability measures.

    Let E be a nuclear locally convex space and let Φ : E → ℂ be a characteristic functional.
    If Φ is:
    1. Continuous (with respect to the nuclear topology on E)
    2. Positive definite (in the sense of Bochner)
    3. Normalized: Φ(0) = 1

    Then there exists a unique probability measure μ on the topological dual E'
    (equipped with the weak* topology) such that:

    Φ(f) = ∫_{E'} exp(i⟨f,ω⟩) dμ(ω)

    **Applications**:
    - For E = S(ℝᵈ) (Schwartz space), E' = S'(ℝᵈ) (tempered distributions)
    - Gaussian measures: Φ(f) = exp(-½⟨f, Cf⟩) with nuclear covariance C
    - Construction of the Gaussian Free Field

    **Historical Note**: This theorem, proved by R.A. Minlos in 1959, is fundamental
    to the construction of infinite-dimensional Gaussian measures in quantum field theory. -/
axiom minlos_theorem
  [NuclearSpace E]
  (Φ : E → ℂ)
  (h_continuous : Continuous Φ)
  (h_positive_definite : IsPositiveDefinite Φ)
  (h_normalized : Φ 0 = 1) :
  ∃ μ : Measure (WeakDual ℝ E), IsProbabilityMeasure μ ∧
    (∀ f : E, Φ f = ∫ ω, Complex.exp (I * (ω f)) ∂μ)

/-- **Minlos Uniqueness**: If two probability measures on the weak dual have the same
    characteristic functional, then they are equal. -/
axiom minlos_uniqueness
  [NuclearSpace E]
  (μ₁ μ₂ : ProbabilityMeasure (WeakDual ℝ E)) :
  (∀ f : E,
    ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ₁.toMeasure =
    ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ₂.toMeasure) →
  μ₁ = μ₂

/-! ## Applications to Gaussian Free Fields -/

/-- For Gaussian measures, the characteristic functional has the special form
    Φ(f) = exp(-½⟨f, Cf⟩) where C is a nuclear covariance operator. -/
def gaussian_characteristic_functional
  (covariance_form : E → E → ℝ) (f : E) : ℂ :=
  Complex.exp (-(1/2 : ℂ) * (covariance_form f f))

/-- Standard fact: Gaussian characteristic functionals built from symmetric
    positive semidefinite forms are positive definite.
    Composition preserves positive definiteness: if ψ is positive definite on H and
    T : E →ₗ[ℝ] H is linear, then ψ ∘ T is positive definite on E. -/
lemma isPositiveDefinite_precomp_linear
  {E H : Type*} [AddCommGroup E] [AddCommGroup H]
  [Module ℝ E] [Module ℝ H]
  (ψ : H → ℂ) (hPD : IsPositiveDefinite ψ) (T : E →ₗ[ℝ] H) :
  IsPositiveDefinite (fun f : E => ψ (T f)) := by
  intro m x c
  simpa using hPD m (fun i => T (x i)) c

/- Narrow axiom: Gaussian RBF kernel is positive definite on any real normed vector space. -/
axiom gaussian_rbf_pd_normed
  {H : Type*} [SeminormedAddCommGroup H] [NormedSpace ℝ H] :
  IsPositiveDefinite (fun h : H => Complex.exp (-(1/2 : ℂ) * (‖h‖^2 : ℝ)))

/- Narrow proved version: if covariance is realized as a squared norm via a linear
    embedding T into a real normed vector space H, then the Gaussian characteristic
    functional is positive definite. -/
lemma gaussian_positive_definite_via_embedding
  {E H : Type*} [AddCommGroup E] [Module ℝ E]
  [SeminormedAddCommGroup H] [NormedSpace ℝ H]
  (T : E →ₗ[ℝ] H)
  (covariance_form : E → E → ℝ)
  (h_eq : ∀ f, covariance_form f f = (‖T f‖^2 : ℝ)) :
  IsPositiveDefinite (fun f => Complex.exp (-(1/2 : ℂ) * (covariance_form f f))) := by
  -- Reduce to Gaussian RBF on H and precomposed with T
  have hPD_H := gaussian_rbf_pd_normed (H := H)
  -- Compose with T and rewrite using h_eq
  intro m x c
  have repl : ∀ i j,
      covariance_form (x i - x j) (x i - x j)
      = (‖T (x i - x j)‖^2 : ℝ) := by
    intro i j; simpa using h_eq (x i - x j)
  have hlin : ∀ i j, T (x i - x j) = T (x i) - T (x j) := by
    intro i j; simp [LinearMap.map_sub]
  have hnorm : ∀ i j, (‖T (x i - x j)‖^2 : ℝ) = (‖T (x i) - T (x j)‖^2 : ℝ) := by
    intro i j; simp [hlin i j]
  -- Apply PD of Gaussian on H precomposed with T
  have hPD_comp :
    0 ≤ (∑ i, ∑ j,
      (starRingEnd ℂ) (c i) * c j *
        Complex.exp (-(1/2 : ℂ) * ((‖T (x i) - T (x j)‖^2 : ℝ)))).re := by
    simpa using (isPositiveDefinite_precomp_linear
      (ψ := fun h : H => Complex.exp (-(1/2 : ℂ) * (‖h‖^2 : ℝ))) hPD_H T) m x c
  -- Rewrite differences inside T using linearity
  have hPD_comp1 :
    0 ≤ (∑ i, ∑ j,
      (starRingEnd ℂ) (c i) * c j *
        Complex.exp (-(1/2 : ℂ) * ((‖T (x i - x j)‖^2 : ℝ)))).re := by
    simpa [LinearMap.map_sub] using hPD_comp
  -- Finally rewrite norm-squared via covariance_form equality
  have : 0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
      Complex.exp (-(1/2 : ℂ) * (covariance_form (x i - x j) (x i - x j)))).re := by
    simpa [repl] using hPD_comp1
  exact this

/-- Application of Minlos theorem to Gaussian measures.
    If the covariance form can be realized as a squared norm via a linear embedding T into
    a real normed vector space H, then the Gaussian characteristic functional Φ(f) = exp(-½⟨f, Cf⟩)
    satisfies the conditions of Minlos theorem, yielding a Gaussian probability measure on E'. -/
 theorem minlos_gaussian_construction
  [NuclearSpace E]
  {H : Type*} [SeminormedAddCommGroup H] [NormedSpace ℝ H]
  (T : E →ₗ[ℝ] H)
  (covariance_form : E → E → ℝ)
  (h_eq : ∀ f, covariance_form f f = (‖T f‖^2 : ℝ))
  (_h_nuclear : True)
  (h_zero : covariance_form 0 0 = 0)
  (h_continuous : Continuous (fun f => covariance_form f f))
  : ∃ μ : Measure (WeakDual ℝ E), IsProbabilityMeasure μ ∧
    (∀ f : E, gaussian_characteristic_functional covariance_form f =
              ∫ ω, Complex.exp (I * (ω f)) ∂μ) := by
  -- Apply Minlos theorem to the Gaussian characteristic functional
  apply minlos_theorem (gaussian_characteristic_functional covariance_form)
  -- 1. Continuity: composition of continuous maps
  · have h_covar_continuous : Continuous (fun f => (covariance_form f f : ℂ)) := by
      exact Continuous.comp continuous_ofReal h_continuous
    have h_scaled_continuous : Continuous (fun f => -(1/2 : ℂ) * (covariance_form f f : ℂ)) := by
      apply Continuous.mul
      · exact continuous_const
      · exact h_covar_continuous
    exact Continuous.comp continuous_exp h_scaled_continuous
  -- 2. Positive definiteness via embedding
  · exact gaussian_positive_definite_via_embedding T covariance_form h_eq
  -- 3. Normalization at 0
  · simp [gaussian_characteristic_functional, h_zero]

/-- The measure constructed by Minlos theorem for a Gaussian characteristic functional
    indeed has that functional as its characteristic function.

    This theorem makes explicit that the Gaussian measure μ constructed via Minlos
    satisfies: for any test function f,
    ∫ ω, exp(i⟨f,ω⟩) dμ(ω) = exp(-½⟨f,Cf⟩)

    This is the fundamental property connecting the abstract Minlos construction
    to the concrete Gaussian generating functional used in quantum field theory. -/
theorem gaussian_measure_characteristic_functional
  [NuclearSpace E]
  {H : Type*} [SeminormedAddCommGroup H] [NormedSpace ℝ H]
  (T : E →ₗ[ℝ] H)
  (covariance_form : E → E → ℝ)
  (h_eq : ∀ f, covariance_form f f = (‖T f‖^2 : ℝ))
  (h_nuclear : True)
  (h_zero : covariance_form 0 0 = 0)
  (h_continuous : Continuous (fun f => covariance_form f f))
  : ∃ μ : ProbabilityMeasure (WeakDual ℝ E),
    (∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure =
              gaussian_characteristic_functional covariance_form f) := by
  -- Get the measure from minlos_gaussian_construction
  have h_minlos := minlos_gaussian_construction T covariance_form h_eq h_nuclear h_zero h_continuous
  obtain ⟨μ, hprob, hchar⟩ := h_minlos
  -- Convert to ProbabilityMeasure and apply the result
  use ⟨μ, hprob⟩
  intro f
  exact (hchar f).symm

end
