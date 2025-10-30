/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

## Real Reflection Positivity for the Gaussian Free Field

This file sets up the real-valued version of the OS3 reflection positivity proof
for the Gaussian free field.  We work with the real positive-time test-function
subspace and relate it to the existing complex formulation in `OS3` and `GFF_OS3`.

The eventual goal is to show
`OS3_ReflectionPositivity_real (gaussianFreeField_free m)` for every positive mass
`m`, by transporting the complex matrix inequality proved previously to the real
setting.

### TODO
* Prove the reflection identities for `freeCovarianceFormR` and the associated
  matrix reflection positivity statement.
* Evaluate the real generating functional explicitly and establish the entry
  factorisation in the purely real setting.
* Combine these ingredients to finish the proof of
  `gaussianFreeField_OS3_matrix_real`.
-/

import Aqft2.Basic
import Aqft2.PositiveTimeTestFunction_real
import Aqft2.DiscreteSymmetry
import Aqft2.OS_Axioms
import Aqft2.GFFMconstruct
import Aqft2.HadamardExp
import Aqft2.SchurProduct

open MeasureTheory Complex Matrix
open scoped Real InnerProductSpace BigOperators

noncomputable section

namespace QFT

/-- Entrywise exponential preserves PSD on real symmetric PSD matrices (finite index).
    Bridge lemma to be discharged using HadamardExp (Hadamard series) machinery. -/
private lemma entrywiseExp_posSemidef_of_posSemidef
  {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
  (hR : R.PosSemidef) : Matrix.PosSemidef (fun i j => Real.exp (R i j)) := by
  classical
  -- PSD for the Hadamard-series exponential
  have hS : (Aqft2.entrywiseExp_hadamardSeries (ι := Fin n) R).PosSemidef :=
    Aqft2.posSemidef_entrywiseExp_hadamardSeries_of_posSemidef (ι := Fin n) R hR
  -- Convert to PSD for the entrywise exponential
  have hExp : (Aqft2.entrywiseExp (ι := Fin n) R).PosSemidef := by
    simpa [Aqft2.entrywiseExp_eq_hadamardSeries (ι := Fin n) R] using hS
  -- Unfold the definition of entrywiseExp
  simpa [Aqft2.entrywiseExp] using hExp


/-- Helper identity: complexifying after real time reflection agrees with
  first complexifying and then applying the complex time reflection. -/
lemma toComplex_compTimeReflectionReal (h : TestFunction) :
  toComplex (QFT.compTimeReflectionReal h) =
    QFT.compTimeReflection (toComplex h) := by
  ext x
  simp [toComplex_apply, QFT.compTimeReflectionReal, QFT.compTimeReflection]

/-- Time reflection leaves the real free covariance invariant. -/
lemma freeCovarianceFormR_reflection_invariant
    (m : ℝ) (f g : TestFunction) :
    freeCovarianceFormR m (QFT.compTimeReflectionReal f)
      (QFT.compTimeReflectionReal g) = freeCovarianceFormR m f g := by
  sorry

/-- Mixed-time-reflection identity for the real free covariance. -/
lemma freeCovarianceFormR_reflection_cross
    (m : ℝ) (f g : TestFunction) :
    freeCovarianceFormR m (QFT.compTimeReflectionReal f) g
      = freeCovarianceFormR m (QFT.compTimeReflectionReal g) f := by
  classical
  have h_invol_f :
      QFT.compTimeReflectionReal (QFT.compTimeReflectionReal f) = f := by
    ext x
    change
        (QFT.compTimeReflectionReal
            (QFT.compTimeReflectionReal f) : TestFunction) x = f x
    have h_time_aux := QFT.timeReflectionLE.right_inv x
    have h_time :
        QFT.timeReflectionLinear (QFT.timeReflectionLinear x) = x := by
      convert h_time_aux using 1
    simp [QFT.compTimeReflectionReal, QFT.timeReflectionCLM,
      QFT.timeReflectionLinear, QFT.timeReflection]
  have h_invol_g :
      QFT.compTimeReflectionReal (QFT.compTimeReflectionReal g) = g := by
    ext x
    change
        (QFT.compTimeReflectionReal
            (QFT.compTimeReflectionReal g) : TestFunction) x = g x
    have h_time_aux := QFT.timeReflectionLE.right_inv x
    have h_time :
        QFT.timeReflectionLinear (QFT.timeReflectionLinear x) = x := by
      convert h_time_aux using 1
    simp [QFT.compTimeReflectionReal, QFT.timeReflectionCLM,
      QFT.timeReflectionLinear, QFT.timeReflection]
  have h_step :
      freeCovarianceFormR m (QFT.compTimeReflectionReal f) g
        = freeCovarianceFormR m f (QFT.compTimeReflectionReal g) := by
    simpa [h_invol_g]
      using freeCovarianceFormR_reflection_invariant (m := m)
        (f := f) (g := QFT.compTimeReflectionReal g)
  calc
    freeCovarianceFormR m (QFT.compTimeReflectionReal f) g
        = freeCovarianceFormR m f (QFT.compTimeReflectionReal g) := h_step
    _ = freeCovarianceFormR m (QFT.compTimeReflectionReal g) f := by
        simpa using (freeCovarianceFormR_symm m f (QFT.compTimeReflectionReal g))

/-- Reflection matrix built from the real covariance is positive semidefinite.
    This is the real analogue of covariance reflection positivity. -/
lemma freeCovarianceFormR_reflection_matrix_posSemidef
    (m : ℝ) [Fact (0 < m)]
    {n : ℕ} (f : Fin n → PositiveTimeTestFunction) :
    Matrix.PosSemidef (fun i j : Fin n =>
      freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f j).val) := by
  classical
  -- Step 1: identify the reflection covariance matrix with a Gram matrix in L².
  have h_step₁ : True := by
    -- TODO: expand `freeCovarianceFormR` via pairing random variables.
    sorry

  -- Step 2: construct the time-reflection isometry on the underlying Hilbert space.
  have h_step₂ : True := by
    -- TODO: build the operator τ and show τ² = id.
    sorry

  -- Step 3: show the reflected test functions land in the positive-time subspace.
  have h_step₃ : True := by
    -- TODO: use support properties of `PositiveTimeTestFunction`.
    sorry

  -- Step 4: deduce the quadratic form is a norm square, hence nonnegative.
  have h_step₄ : True := by
    -- TODO: identify the quadratic form with ‖Σ cᵢ Γ(fᵢ)‖².
    sorry

  -- Final assembly: the Gram description yields positive semidefiniteness.
  -- TODO: combine Steps 1–4 to provide the actual matrix PSD witness.
  sorry

/-- Quadratic expansion identity for reflected arguments. -/
lemma freeCovarianceFormR_reflection_expansion
    (m : ℝ) (f g : TestFunction) :
    freeCovarianceFormR m
        (f - QFT.compTimeReflectionReal g)
        (f - QFT.compTimeReflectionReal g)
      = freeCovarianceFormR m f f
        + freeCovarianceFormR m g g
        - 2 * freeCovarianceFormR m (QFT.compTimeReflectionReal f) g := by
  classical
  set θf := QFT.compTimeReflectionReal f
  set θg := QFT.compTimeReflectionReal g
  set Cf : ℝ := freeCovarianceFormR m f f
  set Cg : ℝ := freeCovarianceFormR m g g
  set Cfg : ℝ := freeCovarianceFormR m θf g
  have h_neg_left : ∀ u v : TestFunction,
      freeCovarianceFormR m (-u) v = -freeCovarianceFormR m u v := by
    intro u v
    simpa using
      (freeCovarianceFormR_smul_left (m := m) (c := (-1 : ℝ)) (f := u) (g := v))
  have h_neg_right : ∀ u v : TestFunction,
      freeCovarianceFormR m u (-v) = -freeCovarianceFormR m u v := by
    intro u v
    calc
      freeCovarianceFormR m u (-v)
          = freeCovarianceFormR m (-v) u := by
              simp [freeCovarianceFormR_symm]
      _ = -freeCovarianceFormR m v u := h_neg_left v u
      _ = -freeCovarianceFormR m u v := by
            simp [freeCovarianceFormR_symm]
  have h_cross : freeCovarianceFormR m θg f = Cfg := by
    simpa [θf, θg, Cfg]
      using
        (freeCovarianceFormR_reflection_cross (m := m) (f := f) (g := g)).symm
  have h_invariant : freeCovarianceFormR m θg θg = Cg := by
    simpa [θg, Cg]
      using freeCovarianceFormR_reflection_invariant (m := m) (f := g) (g := g)
  have h_term₁ :
      freeCovarianceFormR m f (f - θg) = Cf - Cfg := by
    have h_add :=
      freeCovarianceFormR_add_left (m := m)
        (f₁ := f) (f₂ := -θg) (g := f)
    have h_add' :
        freeCovarianceFormR m (f - θg) f
          = freeCovarianceFormR m f f
              + freeCovarianceFormR m (-θg) f := by
      simpa [sub_eq_add_neg, θg] using h_add
    calc
      freeCovarianceFormR m f (f - θg)
          = freeCovarianceFormR m (f - θg) f := by
              simp [sub_eq_add_neg, freeCovarianceFormR_symm]
      _ = freeCovarianceFormR m f f
            + freeCovarianceFormR m (-θg) f := h_add'
      _ = Cf + (-freeCovarianceFormR m θg f) := by
            simp [θg, Cf, h_neg_left]
      _ = Cf - Cfg := by
            simp [sub_eq_add_neg, h_cross]
  have h_term₂ :
      freeCovarianceFormR m (-θg) (f - θg) = -Cfg + Cg := by
    have h_add :=
      freeCovarianceFormR_add_left (m := m)
        (f₁ := f) (f₂ := -θg) (g := -θg)
    have h_add' :
        freeCovarianceFormR m (f - θg) (-θg)
          = freeCovarianceFormR m f (-θg)
              + freeCovarianceFormR m (-θg) (-θg) := by
      simpa [sub_eq_add_neg, θg] using h_add
    have h_negneg :
        freeCovarianceFormR m (-θg) (-θg)
          = freeCovarianceFormR m θg θg := by
      have h₁ := h_neg_left θg (-θg)
      have h₂ := h_neg_right θg θg
      have h₁' : freeCovarianceFormR m (-θg) (-θg) = -freeCovarianceFormR m θg (-θg) := by
        simpa [θg] using h₁
      have h₂' : freeCovarianceFormR m θg (-θg) = -freeCovarianceFormR m θg θg := by
        simpa [θg] using h₂
      calc
        freeCovarianceFormR m (-θg) (-θg)
            = -freeCovarianceFormR m θg (-θg) := h₁'
        _ = -(-freeCovarianceFormR m θg θg) := by
              simpa using congrArg (fun t => -t) h₂'
        _ = freeCovarianceFormR m θg θg := by simp
    calc
      freeCovarianceFormR m (-θg) (f - θg)
          = freeCovarianceFormR m (f - θg) (-θg) := by
              simp [sub_eq_add_neg, freeCovarianceFormR_symm]
      _ = freeCovarianceFormR m f (-θg)
            + freeCovarianceFormR m (-θg) (-θg) := h_add'
      _ = -freeCovarianceFormR m f θg
            + freeCovarianceFormR m (-θg) (-θg) := by
              simp [θg, h_neg_right]
      _ = -freeCovarianceFormR m f θg
            + freeCovarianceFormR m θg θg := by
              simp [h_negneg]
      _ = -Cfg + Cg := by
          have h_sym : freeCovarianceFormR m f θg = freeCovarianceFormR m θg f := by
            simpa using freeCovarianceFormR_symm m f θg
          simp [h_sym, h_cross, h_invariant]
  have h_total :=
      freeCovarianceFormR_add_left (m := m)
        (f₁ := f) (f₂ := -θg) (g := f - θg)
  have h_total' :
      freeCovarianceFormR m (f - θg) (f - θg)
        = freeCovarianceFormR m f (f - θg)
            + freeCovarianceFormR m (-θg) (f - θg) := by
    simpa [sub_eq_add_neg, θg] using h_total
  calc
    freeCovarianceFormR m (f - θg) (f - θg)
        = freeCovarianceFormR m f (f - θg)
            + freeCovarianceFormR m (-θg) (f - θg) := h_total'
    _ = (Cf - Cfg) + (-Cfg + Cg) := by
          simp [h_term₁, h_term₂]
    _ = Cf + Cg - 2 * Cfg := by ring

/-- Evaluate the real generating functional of the free field on a real test function. -/
lemma gaussianFreeField_real_generating_re
    (m : ℝ) [Fact (0 < m)] (h : TestFunction) :
    (GJGeneratingFunctional (gaussianFreeField_free m) h).re
      = Real.exp (-(1 / 2 : ℝ) * freeCovarianceFormR m h h) := by
  classical
  set r : ℝ := -(1 / 2 : ℝ) * freeCovarianceFormR m h h
  have h_char := congrArg Complex.re (gff_real_characteristic (m := m) h)
  have h_arg :
      (-(1 / 2 : ℂ) * (freeCovarianceFormR m h h : ℝ))
        = Complex.ofReal r := by
    simp [r, Complex.ofReal_mul]
  have h_exp_rewrite :
      (Complex.exp (-(1 / 2 : ℂ) * (freeCovarianceFormR m h h : ℝ))).re
        = Real.exp r := by
    simpa [h_arg, r] using (Complex.exp_ofReal_re r)
  have h_char' := h_char
  rw [h_exp_rewrite] at h_char'
  simpa [r] using h_char'

/-- Factorisation of OS3 matrix entries in the purely real setting. -/
lemma gaussianFreeField_real_entry_factor
    (m : ℝ) [Fact (0 < m)]
    {f g : PositiveTimeTestFunction} :
    (GJGeneratingFunctional (gaussianFreeField_free m)
        (f.val - QFT.compTimeReflectionReal g.val)).re
      = (GJGeneratingFunctional (gaussianFreeField_free m) (f.val)).re
        * (GJGeneratingFunctional (gaussianFreeField_free m) (g.val)).re
        * Real.exp
            (freeCovarianceFormR m
              (QFT.compTimeReflectionReal (f.val)) (g.val)) := by
  classical
  -- shorthand for the covariance terms appearing in the exponent
  set Cf : ℝ := freeCovarianceFormR m (f.val) (f.val)
  set Cg : ℝ := freeCovarianceFormR m (g.val) (g.val)
  set Cfg : ℝ :=
    freeCovarianceFormR m (QFT.compTimeReflectionReal (f.val)) (g.val)
  -- Evaluate the generating functionals via the real characteristic formula
  have hf := gaussianFreeField_real_generating_re (m := m) (h := f.val)
  have hg := gaussianFreeField_real_generating_re (m := m) (h := g.val)
  have hfg :=
    gaussianFreeField_real_generating_re (m := m)
      (h := f.val - QFT.compTimeReflectionReal g.val)
  -- Use the reflection expansion to rewrite the covariance of f - Θg
  have h_expansion := freeCovarianceFormR_reflection_expansion (m := m)
    (f := f.val) (g := g.val)
  -- Translate the equalities coming from the generating functionals into exponentials
  have hf' :
      (GJGeneratingFunctional (gaussianFreeField_free m) (f.val)).re
        = Real.exp (-(1 / 2 : ℝ) * Cf) := by simpa [Cf] using hf
  have hg' :
      (GJGeneratingFunctional (gaussianFreeField_free m) (g.val)).re
        = Real.exp (-(1 / 2 : ℝ) * Cg) := by simpa [Cg] using hg
  have hfg' :
      (GJGeneratingFunctional (gaussianFreeField_free m)
          (f.val - QFT.compTimeReflectionReal g.val)).re
        =
        Real.exp (-(1 / 2 : ℝ)
          * freeCovarianceFormR m
              (f.val - QFT.compTimeReflectionReal g.val)
              (f.val - QFT.compTimeReflectionReal g.val)) := by
    simpa using hfg
  -- Rewrite the exponent using the quadratic expansion lemma
  have h_covariance_rewrite :
      freeCovarianceFormR m
          (f.val - QFT.compTimeReflectionReal g.val)
          (f.val - QFT.compTimeReflectionReal g.val)
        = Cf + Cg - 2 * Cfg := by
    simpa [Cf, Cg, Cfg] using h_expansion
  -- Combine all exponentials and simplify
  set a : ℝ := -(1 / 2 : ℝ) * Cf
  set b : ℝ := -(1 / 2 : ℝ) * Cg
  set A : ℝ := a + b
  have hA : A = -(1 / 2 : ℝ) * Cf + -(1 / 2 : ℝ) * Cg := by
    simp [A, a, b]
  have h_factor :
      -(1 / 2 : ℝ) * (Cf + Cg - 2 * Cfg) = A + Cfg := by
    have h_ring : -(1 / 2 : ℝ) * (Cf + Cg - 2 * Cfg)
        = -(1 / 2 : ℝ) * Cf + -(1 / 2 : ℝ) * Cg + Cfg := by
          ring
    simpa [A, a, b, add_comm, add_left_comm, add_assoc, hA] using h_ring
  calc
    (GJGeneratingFunctional (gaussianFreeField_free m)
        (f.val - QFT.compTimeReflectionReal g.val)).re
        = Real.exp (-(1 / 2 : ℝ) * (Cf + Cg - 2 * Cfg)) := by
              simpa [h_covariance_rewrite] using hfg'
  _ =
    Real.exp (-(1 / 2 : ℝ) * Cf)
    * Real.exp (-(1 / 2 : ℝ) * Cg)
    * Real.exp (Cfg) := by
        -- Exponential of sums factorises; use `Real.exp_add` twice
        calc
        Real.exp (-(1 / 2 : ℝ) * (Cf + Cg - 2 * Cfg))
          = Real.exp (A + Cfg) := by
              simpa using (congrArg Real.exp h_factor)
        _ = Real.exp A * Real.exp Cfg := by
              simp [Real.exp_add]
        _ =
          (Real.exp a * Real.exp b)
            * Real.exp Cfg := by
              simp [A, a, b, Real.exp_add]
    _ =
        (GJGeneratingFunctional (gaussianFreeField_free m) (f.val)).re
        * (GJGeneratingFunctional (gaussianFreeField_free m) (g.val)).re
        * Real.exp Cfg := by
        simp [hf', hg', Cfg, a, b, one_div, mul_comm, mul_assoc]
section GaussianRealReflectionPositivity

variable (m : ℝ) [Fact (0 < m)]

/-- Real-vs-complex comparison lemma for single matrix entries.
    This will identify the real OS3 matrix element with the real part of the
    complex element obtained after complexifying both arguments. -/
lemma gaussian_real_entry_agrees
    (dμ := gaussianFreeField_free m)
    {f g : PositiveTimeTestFunction} :
    (GJGeneratingFunctional dμ (f.val - QFT.compTimeReflectionReal g.val)).re
      = (GJGeneratingFunctionalℂ dμ
          (toComplex f.val - QFT.compTimeReflection (toComplex g.val))).re := by
  classical
  have h_toComplex_sub :
      toComplex (f.val - QFT.compTimeReflectionReal g.val)
        = toComplex f.val - toComplex (QFT.compTimeReflectionReal g.val) := by
    ext x
    simp [toComplex_apply]
  have h_time := toComplex_compTimeReflectionReal (h := g.val)
  have h_gen := GJGeneratingFunctionalℂ_toComplex (dμ_config := dμ)
    (f := f.val - QFT.compTimeReflectionReal g.val)
  -- identify the complex generating functional on the left with the real one
  have h_eq := (congrArg Complex.re h_gen).symm
  -- rewrite the complex argument using the helper lemmas
  simpa [h_toComplex_sub, h_time] using h_eq

/-- Real quadratic form equals the real part of the complex quadratic form.
    This will allow us to transfer the positive semidefiniteness result from the
    complex setting to the real one. -/
lemma gaussian_real_quadratic_agrees
    (dμ := gaussianFreeField_free m)
    {n : ℕ} (f : Fin n → PositiveTimeTestFunction) (c : Fin n → ℝ) :
    (∑ i, ∑ j, c i * c j *
        (GJGeneratingFunctional dμ
          ((f i).val - QFT.compTimeReflectionReal (f j).val)).re)
      = (∑ i, ∑ j, (starRingEnd ℂ) (Complex.ofReal (c i)) * (Complex.ofReal (c j)) *
          GJGeneratingFunctionalℂ dμ
            (toComplex (f i).val - QFT.compTimeReflection (toComplex (f j).val))).re := by
  classical
  have h_entry : ∀ i j,
      (GJGeneratingFunctional dμ
            ((f i).val - QFT.compTimeReflectionReal (f j).val)).re
        = (GJGeneratingFunctionalℂ dμ
            (toComplex (f i).val - QFT.compTimeReflection (toComplex (f j).val))).re := by
    intro i j
    simpa using
      gaussian_real_entry_agrees (m := m) (f := f i) (g := f j) (dμ := dμ)
  simp [h_entry]

/-- Matrix formulation of the real OS3 inequality for the Gaussian free field. -/
lemma gaussianFreeField_OS3_matrix_real
    {n : ℕ} (f : Fin n → PositiveTimeTestFunction) (c : Fin n → ℝ) :
    0 ≤ (∑ i, ∑ j, c i * c j *
        (GJGeneratingFunctional (gaussianFreeField_free m)
          ((f i).val - QFT.compTimeReflectionReal (f j).val)).re) := by
  classical
  -- Build the auxiliary data appearing in the factorisation argument.
  let Z : Fin n → ℝ := fun i =>
    (GJGeneratingFunctional (gaussianFreeField_free m) (f i).val).re
  let R : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    freeCovarianceFormR m
      (QFT.compTimeReflectionReal (f i).val) (f j).val
  let E : Matrix (Fin n) (Fin n) ℝ := fun i j => Real.exp (R i j)
  let y : Fin n → ℝ := fun i => c i * Z i
  -- Use the real entry factorisation and reflection positivity for the covariance.
  -- Step 1: Apply the factorisation to each matrix entry
  have h_factor : ∀ i j,
      (GJGeneratingFunctional (gaussianFreeField_free m)
        ((f i).val - QFT.compTimeReflectionReal (f j).val)).re
      = Z i * Z j * E i j := by
    intro i j
    have h_entry := gaussianFreeField_real_entry_factor (m := m) (f := f i) (g := f j)
    simp [Z, E, R] at h_entry ⊢
    exact h_entry

  -- Step 2: Rewrite the sum using the factorisation
  have h_sum₁ :
      (∑ i, ∑ j, c i * c j *
        (GJGeneratingFunctional (gaussianFreeField_free m)
          ((f i).val - QFT.compTimeReflectionReal (f j).val)).re)
      = ∑ i, ∑ j, c i * c j * (Z i * Z j * E i j) := by
    simp_rw [h_factor]

  -- Step 3: express the quadratic form using the rescaled vector y
  have h_sum₂ :
      (∑ i, ∑ j, c i * c j * (Z i * Z j * E i j))
        = ∑ i, ∑ j, y i * y j * E i j := by
    simp [y, Z, E, R, mul_comm, mul_left_comm, mul_assoc]

  -- Step 4: Apply PSD property of E
  have h_R_psd : R.PosSemidef := by
    simpa [R] using freeCovarianceFormR_reflection_matrix_posSemidef (m := m) f

  have h_E_psd : E.PosSemidef := by
    simpa [E] using entrywiseExp_posSemidef_of_posSemidef R h_R_psd

  -- Step 5: Use PSD property - the quadratic form yᵀEy is nonnegative
  have h_quad_sum :
      (∑ i, ∑ j, y i * y j * E i j)
        = y ⬝ᵥ (E.mulVec y) := by
    classical
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_assoc]

  have hy_nonneg : 0 ≤ y ⬝ᵥ (E.mulVec y) := h_E_psd.2 y

  have h_goal :
      0 ≤ (∑ i, ∑ j, c i * c j *
        (GJGeneratingFunctional (gaussianFreeField_free m)
          ((f i).val - QFT.compTimeReflectionReal (f j).val)).re) := by
    have h₁ : 0 ≤ ∑ i, ∑ j, y i * y j * E i j := by
      simpa [h_quad_sum] using hy_nonneg
    have h₂ : 0 ≤ ∑ i, ∑ j, c i * c j * (Z i * Z j * E i j) := by
      simpa [h_sum₂] using h₁
    simpa [h_sum₁] using h₂

  exact h_goal

/-- Main theorem: the Gaussian free field satisfies the real reflection
  positivity axiom.  The proof will rely on the existing complex OS3 matrix
  inequality together with the comparison lemmas above. -/
theorem gaussianFreeField_OS3_real :
    OS3_ReflectionPositivity_real (gaussianFreeField_free m) := by
  intro n f c
  simpa using gaussianFreeField_OS3_matrix_real (m := m) f c

end GaussianRealReflectionPositivity

end QFT

end
