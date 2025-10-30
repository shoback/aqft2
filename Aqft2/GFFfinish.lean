/-
Final bundling of OS axioms for the free Gaussian Free Field (GFF).

This file provides a "master theorem" that assembles OS0–OS4 for the
measure `gaussianFreeField_free m`, reusing the individual results proved
elsewhere. In particular, OS3 is proved in `Aqft2/GFF_OS3.lean` via the
matrix/Schur–Hadamard argument, while OS0 (and potentially OS1/OS2/OS4)
are provided from `Aqft2/GaussianFreeField.lean`.

We expose a conditional master theorem: given OS1, OS2, OS4 for the free GFF,
we conclude all axioms OS0–OS4, plugging in OS0 from the existing proof
and OS3 from `GFF_OS3`.

Once separate files provide GFF-specific theorems for OS1, OS2, and OS4,
this file can be updated to a fully unconditional statement by importing
those lemmas and removing the hypotheses.
-/

import Aqft2.GaussianFreeField
import Aqft2.GFF_OS3_real

open scoped BigOperators

namespace Aqft2

noncomputable section

/-- Shorthand for the free GFF probability measure used throughout. -/
@[simp] def μ_GFF (m : ℝ) [Fact (0 < m)] := gaussianFreeField_free m

/-! ## Master OS theorem for the free GFF -/

/-- Single master theorem: assuming the standard covariance hypotheses for the free GFF
(boundedness for OS1, Euclidean invariance for OS2) and OS4 clustering, the free GFF
satisfies all five OS axioms. OS0 is supplied by `gaussianFreeField_satisfies_OS0_alt`, and
OS3 by `gaussianFreeField_satisfies_OS3`.

This bundles the full result under assumptions that are natural to verify for the free
covariance. -/
theorem gaussianFreeField_satisfies_all_OS_axioms (m : ℝ) [Fact (0 < m)]
  (h_bound : CovarianceBoundedComplex (μ_GFF m))
  (h_euc   : CovarianceEuclideanInvariantℂ (μ_GFF m))
  (h_OS4   : OS4_Clustering (μ_GFF m)) :
  OS0_Analyticity (μ_GFF m) ∧
  OS1_Regularity (μ_GFF m) ∧
  OS2_EuclideanInvariance (μ_GFF m) ∧
  OS3_ReflectionPositivity_real (μ_GFF m) ∧
  OS4_Clustering (μ_GFF m) := by
  -- Gaussianity of the free GFF generating functional
  have h_gauss : isGaussianGJ (μ_GFF m) := by
    simpa using isGaussianGJ_gaussianFreeField_free m
  -- OS0 from alternate finite-dimensional proof
  have h_OS0 : OS0_Analyticity (μ_GFF m) := by
    simpa using gaussianFreeField_satisfies_OS0 m
  -- OS1 from the generic Gaussian theorem with bounded covariance
  have h_OS1 : OS1_Regularity (μ_GFF m) :=
    gaussian_satisfies_OS1 (μ_GFF m) h_gauss h_bound
  -- OS2 from the generic Gaussian theorem with Euclidean-invariant covariance
  have h_OS2 : OS2_EuclideanInvariance (μ_GFF m) :=
    gaussian_satisfies_OS2 (μ_GFF m) h_gauss h_euc
  -- OS3 from the dedicated OS3 file
  have h_OS3 : OS3_ReflectionPositivity_real (μ_GFF m) :=
    QFT.gaussianFreeField_OS3_real m
  -- Bundle
  exact ⟨h_OS0, h_OS1, h_OS2, h_OS3, h_OS4⟩

end

end Aqft2
