/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

## Complex Test Function Linearity

This file contains lemmas about linearity properties of complex test functions
and their pairings with field configurations.

### Main Results:

**Complex Arithmetic Helpers:**
- `re_of_complex_combination`: Real part of complex linear combination
- `im_of_complex_combination`: Imaginary part of complex linear combination

**Decomposition Linearity:**
- `ω_re_decompose_linear`: ω-linearity of real component under complex operations
- `ω_im_decompose_linear`: ω-linearity of imaginary component under complex operations

**Pairing Linearity:**
- `pairing_linear_combo`: Key result showing distributionPairingℂ_real is ℂ-linear
  in the test function argument

These results are essential for proving bilinearity of Schwinger functions
and other quantum field theory constructions.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace

import Aqft2.Basic

open Complex MeasureTheory

noncomputable section

-- Key lemma: how reCLM behaves with complex operations
private lemma re_of_complex_combination (a b : ℂ) (u v : ℂ) :
  Complex.re (a * u + b * v) = a.re * u.re - a.im * u.im + b.re * v.re - b.im * v.im := by
  -- Use basic complex arithmetic
  simp only [add_re, mul_re]
  ring

-- Key lemma: how imCLM behaves with complex operations
private lemma im_of_complex_combination (a b : ℂ) (u v : ℂ) :
  Complex.im (a * u + b * v) = a.re * u.im + a.im * u.re + b.re * v.im + b.im * v.re := by
  -- Use basic complex arithmetic
  simp only [add_im, mul_im]
  ring

/-- ω-linearity of the real component of the complex test-function decomposition under
    complex linear combinations. This follows from ℝ-linearity of ω and pointwise
    behavior of complex operations on Schwartz functions. -/
lemma ω_re_decompose_linear
  (ω : FieldConfiguration) (f g : TestFunctionℂ) (t s : ℂ) :
  ω ((complex_testfunction_decompose (t • f + s • g)).1)
    = t.re * ω ((complex_testfunction_decompose f).1)
      - t.im * ω ((complex_testfunction_decompose f).2)
      + s.re * ω ((complex_testfunction_decompose g).1)
      - s.im * ω ((complex_testfunction_decompose g).2) := by
  -- First, identify the real-part test function of t•f + s•g as a linear combination
  have h_sum_re_eq :
      (complex_testfunction_decompose (t • f + s • g)).1
        = t.re • (complex_testfunction_decompose f).1
          - t.im • (complex_testfunction_decompose f).2
          + s.re • (complex_testfunction_decompose g).1
          - s.im • (complex_testfunction_decompose g).2 := by
    ext x
    -- Rewrite to Complex.re/Complex.im and use algebra on ℂ
    change Complex.reCLM ((t • f + s • g) x)
        = t.re * Complex.reCLM (f x) - t.im * Complex.imCLM (f x)
          + s.re * Complex.reCLM (g x) - s.im * Complex.imCLM (g x)
    -- Evaluate pointwise scalar multiplication and addition
    simp
    -- Switch CLMs to the scalar functions and finish with the algebraic identity
    change Complex.re (t * f x + s * g x)
        = t.re * Complex.re (f x) - t.im * Complex.im (f x)
          + s.re * Complex.re (g x) - s.im * Complex.im (g x)
    simpa using re_of_complex_combination t s (f x) (g x)
  -- Apply ω (a real-linear functional) to both sides
  have := congrArg (fun (φ : TestFunction) => ω φ) h_sum_re_eq
  -- Simplify using linearity of ω over ℝ
  simpa [map_add, map_sub, map_smul]
    using this

/-- ω-linearity of the imaginary component of the complex test-function decomposition under
    complex linear combinations. -/
lemma ω_im_decompose_linear
  (ω : FieldConfiguration) (f g : TestFunctionℂ) (t s : ℂ) :
  ω ((complex_testfunction_decompose (t • f + s • g)).2)
    = t.re * ω ((complex_testfunction_decompose f).2)
      + t.im * ω ((complex_testfunction_decompose f).1)
      + s.re * ω ((complex_testfunction_decompose g).2)
      + s.im * ω ((complex_testfunction_decompose g).1) := by
  -- Identify the imaginary-part test function of t•f + s•g as a linear combination
  have h_sum_im_eq :
      (complex_testfunction_decompose (t • f + s • g)).2
        = t.re • (complex_testfunction_decompose f).2
          + t.im • (complex_testfunction_decompose f).1
          + s.re • (complex_testfunction_decompose g).2
          + s.im • (complex_testfunction_decompose g).1 := by
    ext x
    -- Rewrite to Complex.im/Complex.re and use algebra on ℂ
    change Complex.imCLM ((t • f + s • g) x)
        = t.re * Complex.imCLM (f x) + t.im * Complex.reCLM (f x)
          + s.re * Complex.imCLM (g x) + s.im * Complex.reCLM (g x)
    -- Evaluate pointwise scalar multiplication and addition
    simp
    -- Switch CLMs to scalar functions and finish with the algebraic identity
    change Complex.im (t * f x + s * g x)
        = t.re * Complex.im (f x) + t.im * Complex.re (f x)
          + s.re * Complex.im (g x) + s.im * Complex.re (g x)
    simpa using im_of_complex_combination t s (f x) (g x)
  -- Apply ω (a real-linear functional) to both sides
  have := congrArg (fun (φ : TestFunction) => ω φ) h_sum_im_eq
  -- Simplify using linearity of ω over ℝ
  simpa [map_add, map_smul]
    using this

/-- Linearity of the complex pairing in the test-function argument. -/
lemma pairing_linear_combo
  (ω : FieldConfiguration) (f g : TestFunctionℂ) (t s : ℂ) :
  distributionPairingℂ_real ω (t • f + s • g)
    = t * distributionPairingℂ_real ω f + s * distributionPairingℂ_real ω g := by
  classical
  apply Complex.ext
  · -- Real parts
    -- Expand both sides to re/imag pieces
    simp [distributionPairingℂ_real]
    -- Goal is now: ω ((complex_testfunction_decompose (t•f+s•g)).1)
    --              = (t * ((ω (..f..).1 + i ω (..f..).2)) + s * ((ω (..g..).1 + i ω (..g..).2))).re
    -- Use algebraic identity on the RHS
    have hre_rhs :
        (t * ((ω ((complex_testfunction_decompose f).1) : ℂ) + I * (ω ((complex_testfunction_decompose f).2) : ℂ))
            + s * ((ω ((complex_testfunction_decompose g).1) : ℂ) + I * (ω ((complex_testfunction_decompose g).2) : ℂ))).re
          = t.re * ω ((complex_testfunction_decompose f).1)
              - t.im * ω ((complex_testfunction_decompose f).2)
              + s.re * ω ((complex_testfunction_decompose g).1)
              - s.im * ω ((complex_testfunction_decompose g).2) := by
      simpa using re_of_complex_combination t s
        ((ω ((complex_testfunction_decompose f).1) : ℂ) + I * (ω ((complex_testfunction_decompose f).2) : ℂ))
        ((ω ((complex_testfunction_decompose g).1) : ℂ) + I * (ω ((complex_testfunction_decompose g).2) : ℂ))
    -- Use ω-linearity identity on the LHS
    have hre := ω_re_decompose_linear ω f g t s
    -- Finish by rewriting both sides to the same expression
    simpa [hre_rhs, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
      using hre
  · -- Imag parts
    simp [distributionPairingℂ_real]
    have him_rhs :
        (t * ((ω ((complex_testfunction_decompose f).1) : ℂ) + I * (ω ((complex_testfunction_decompose f).2) : ℂ))
            + s * ((ω ((complex_testfunction_decompose g).1) : ℂ) + I * (ω ((complex_testfunction_decompose g).2) : ℂ))).im
          = t.re * ω ((complex_testfunction_decompose f).2)
              + t.im * ω ((complex_testfunction_decompose f).1)
              + s.re * ω ((complex_testfunction_decompose g).2)
              + s.im * ω ((complex_testfunction_decompose g).1) := by
      simpa using im_of_complex_combination t s
        ((ω ((complex_testfunction_decompose f).1) : ℂ) + I * (ω ((complex_testfunction_decompose f).2) : ℂ))
        ((ω ((complex_testfunction_decompose g).1) : ℂ) + I * (ω ((complex_testfunction_decompose g).2) : ℂ))
    have him := ω_im_decompose_linear ω f g t s
    simpa [him_rhs, add_comm, add_left_comm, add_assoc]
      using him

/-- Pointwise identity: for any complex-valued test function f, we have
    f(x) = re(f(x)) + i · im(f(x)). -/
lemma eval_re_add_im (f : TestFunctionℂ) : ∀ x, f x = (Complex.re (f x) : ℂ) + Complex.I * (Complex.im (f x) : ℂ) := by
  intro x
  -- Start from z = re z + im z * I (symmetric of re_add_im)
  calc
    f x = (Complex.re (f x) : ℂ) + (Complex.im (f x) : ℂ) * Complex.I := by
      exact (Complex.re_add_im (f x)).symm
    _ = (Complex.re (f x) : ℂ) + Complex.I * (Complex.im (f x) : ℂ) := by
      ring

/-- Pointwise identity for conjugation in terms of re/im parts of a complex test function. -/
lemma eval_conj_re_sub_im (g : TestFunctionℂ) :
  ∀ x, (starRingEnd ℂ) (g x) = (Complex.re (g x) : ℂ) - Complex.I * (Complex.im (g x) : ℂ) := by
  intro x
  -- Notation
  set a : ℂ := (Complex.re (g x) : ℂ) with ha
  set b : ℂ := (Complex.im (g x) : ℂ) with hb
  have hx : g x = a + Complex.I * b := by
    -- expand a,b
    rw [ha, hb]
    exact eval_re_add_im g x
  -- Apply star to both sides and compute explicitly on RHS
  have hstar := congrArg (starRingEnd ℂ) hx
  -- Compute star of RHS using ring-hom axioms
  have hRHS : (starRingEnd ℂ) (a + Complex.I * b) = a + (-Complex.I) * b := by
    -- map addition and multiplication
    calc
      (starRingEnd ℂ) (a + Complex.I * b)
          = (starRingEnd ℂ) a + (starRingEnd ℂ) (Complex.I * b) := by
              simp [map_add]
      _ = a + (starRingEnd ℂ) Complex.I * (starRingEnd ℂ) b := by
              rw [map_mul]
              -- Now need to show (starRingEnd ℂ) a = a
              rw [ha, hb]
              simp
      _ = a + (-Complex.I) * b := by
              -- star of real-coerced a,b is themselves; star I = -I
              congr 2
              · exact Complex.conj_I
              · rw [hb]
                exact Complex.conj_ofReal _
  -- Put together
  calc
    (starRingEnd ℂ) (g x)
        = (starRingEnd ℂ) (a + Complex.I * b) := hstar
    _ = a + (-Complex.I) * b := hRHS
    _ = a - Complex.I * b := by ring

/-- Embed a real test function as a complex-valued test function by coercing values via ℝ → ℂ. -/
def toComplex (f : TestFunction) : TestFunctionℂ :=
  SchwartzMap.mk (fun x => (f x : ℂ)) (by
    -- ℝ → ℂ coercion is smooth
    exact ContDiff.comp Complex.ofRealCLM.contDiff f.smooth'
  ) (by
    -- Polynomial growth is preserved since ℝ → ℂ coercion preserves norms
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    use C
    intro x
    -- Use the fact that iteratedFDeriv commutes with continuous linear maps
    have h_norm_eq : ‖iteratedFDeriv ℝ n (fun x ↦ (f x : ℂ)) x‖ = ‖iteratedFDeriv ℝ n f.toFun x‖ := by
      -- This follows from derivatives of compositions with continuous linear maps
      sorry -- Technical lemma about iteratedFDeriv and ofRealCLM
    rw [h_norm_eq]
    exact hC x
  )

@[simp] lemma toComplex_apply (f : TestFunction) (x : SpaceTime) :
  toComplex f x = (f x : ℂ) := by
  -- Follows from definition of toComplex
  rfl

@[simp] lemma complex_testfunction_decompose_toComplex_fst (f : TestFunction) :
  (complex_testfunction_decompose (toComplex f)).1 = f := by
  ext x
  simp [complex_testfunction_decompose, toComplex_apply]

@[simp] lemma complex_testfunction_decompose_toComplex_snd (f : TestFunction) :
  (complex_testfunction_decompose (toComplex f)).2 = 0 := by
  ext x
  simp [complex_testfunction_decompose, toComplex_apply]

@[simp] lemma distributionPairingℂ_real_toComplex
  (ω : FieldConfiguration) (f : TestFunction) :
  distributionPairingℂ_real ω (toComplex f) = distributionPairing ω f := by
  simp [distributionPairingℂ_real, distributionPairing]

variable (dμ_config : ProbabilityMeasure FieldConfiguration)

@[simp] lemma GJGeneratingFunctionalℂ_toComplex
  (f : TestFunction) :
  GJGeneratingFunctionalℂ dμ_config (toComplex f) = GJGeneratingFunctional dμ_config f := by
  unfold GJGeneratingFunctionalℂ GJGeneratingFunctional
  simp [distributionPairingℂ_real_toComplex]
