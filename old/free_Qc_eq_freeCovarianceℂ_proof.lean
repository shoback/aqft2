/-
Working file for proving free_Qc_eq_freeCovarianceℂ

This is extracted from GFFMconstruct.lean to allow incremental development
without blocking the main build.

Goal: Prove that MinlosAnalytic.Qc (freeCovarianceForm_struct m) f g = freeCovarianceℂ m f g

Strategy:
1. Both sides are ℂ-bilinear extensions of the same real form freeCovarianceFormR
2. Qc uses the canonical complexification formula:
   Qc(f,g) = Q(Re f, Re g) - Q(Im f, Im g) + i(Q(Re f, Im g) + Q(Im f, Re g))
3. freeCovarianceℂ is defined as ∫∫ f(x) · K(x,y) · star(g(y))
4. Expand f = re(f) + i·im(f), star(g) = re(g) - i·im(g) pointwise
5. Use freeCovarianceℂ_agrees_on_reals to convert each of 4 double integrals
6. Match with Qc formula

Key lemmas now available in Basic.lean:
- complex_testfunction_decompose_fst_apply: (decompose f).1 x = (f x).re
- complex_testfunction_decompose_snd_apply: (decompose f).2 x = (f x).im
- complex_testfunction_decompose_fst_apply_coe: ((decompose f).1 x : ℂ) = (f x).re
- complex_testfunction_decompose_snd_apply_coe: ((decompose f).2 x : ℂ) = (f x).im

Key lemma from Covariance.lean:
- freeCovarianceℂ_agrees_on_reals:
    freeCovarianceℂ m (toComplex f) (toComplex g) = (freeCovarianceFormR m f g : ℂ)
-/

import Aqft2.Basic
import Aqft2.Covariance
import Aqft2.MinlosAnalytic

open scoped ComplexConjugate

open Complex

-- Bilinearity helpers (available in the main file; assumed here for the working proof).
axiom freeCovarianceℂ_bilinear_add_left
  (m : ℝ) (f₁ f₂ g : TestFunctionℂ) :
  freeCovarianceℂ_bilinear m (f₁ + f₂) g
    = freeCovarianceℂ_bilinear m f₁ g + freeCovarianceℂ_bilinear m f₂ g

axiom freeCovarianceℂ_bilinear_add_right
  (m : ℝ) (f g₁ g₂ : TestFunctionℂ) :
  freeCovarianceℂ_bilinear m f (g₁ + g₂)
    = freeCovarianceℂ_bilinear m f g₁ + freeCovarianceℂ_bilinear m f g₂

axiom freeCovarianceℂ_bilinear_smul_left
  (m : ℝ) (c : ℂ) (f g : TestFunctionℂ) :
  freeCovarianceℂ_bilinear m (c • f) g = c * freeCovarianceℂ_bilinear m f g

axiom freeCovarianceℂ_bilinear_smul_right
  (m : ℝ) (c : ℂ) (f g : TestFunctionℂ) :
  freeCovarianceℂ_bilinear m f (c • g) = c * freeCovarianceℂ_bilinear m f g

axiom freeCovarianceℂ_bilinear_agrees_on_reals
  (m : ℝ) (f g : TestFunction) :
  freeCovarianceℂ_bilinear m (toComplex f) (toComplex g)
    = (freeCovarianceFormR m f g : ℂ)

noncomputable def freeCovarianceForm_struct (m : ℝ) : MinlosAnalytic.CovarianceForm :=
{ Q := fun f g => freeCovarianceFormR m f g
, symm := by intro f g; simpa using freeCovarianceFormR_symm m f g
, psd := by intro f; simpa using freeCovarianceFormR_pos m f
, cont_diag := by
    -- `freeCovarianceFormR_continuous` already provides continuity of the diagonal.
    simpa using freeCovarianceFormR_continuous m
, add_left := by
    intro f₁ f₂ g
    simpa using freeCovarianceFormR_add_left m f₁ f₂ g
, smul_left := by
    intro c f g
    simpa using freeCovarianceFormR_smul_left m c f g }

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
