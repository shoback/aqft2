/-
Simplified statements for differentiating Gaussian moment generating functions.

This module packages the Option B axioms introduced in
`Aqft2.GFFMconstruct` into streamlined derivative-under-the-integral
principles that can be used throughout the project without repeatedly
verifying integrability hypotheses.  They will eventually be promoted to
theorems once the analytic infrastructure in `IntegralDifferentiation.lean`
is completed, but for now we record them as assumptions aligned with the
axiomatic Fernique-type bounds already in use.
-/

import Aqft2.GFFMconstruct

open MeasureTheory Complex

namespace Aqft2

variable (m : ℝ) [Fact (0 < m)]

/-- Differentiation under the integral sign for the exponential of a single
smeared field.  Thanks to the Fernique-type axioms, no additional integrability
assumptions on the test function are required. -/
axiom deriv_under_integral_exp_gaussian
    (φ : TestFunction) :
    HasDerivAt
      (fun t : ℂ ↦
        ∫ ω,
          Complex.exp (Complex.I * t * distributionPairingCLM φ ω)
            ∂(gaussianFreeField_free m).toMeasure)
      (∫ ω, Complex.I * distributionPairingCLM φ ω
          ∂(gaussianFreeField_free m).toMeasure)
      0

/-- Mixed differentiation under the integral sign for the exponential of two
smeared fields.  This is the `Option B` axiomatisation of the OS₂ dominated
convergence argument. -/
axiom mixed_deriv_under_integral_gaussian
    (φ ψ : TestFunction) :
    deriv
        (fun t : ℂ ↦
          deriv
            (fun s : ℂ ↦
              ∫ ω,
                Complex.exp (Complex.I * (t * distributionPairingCLM φ ω
                    + s * distributionPairingCLM ψ ω))
                  ∂(gaussianFreeField_free m).toMeasure) 0)
        0
      =
        ∫ ω,
          deriv
            (fun t : ℂ ↦
              deriv
                (fun s : ℂ ↦
                  Complex.exp (Complex.I * (t * distributionPairingCLM φ ω
                      + s * distributionPairingCLM ψ ω))) 0)
            0
            ∂(gaussianFreeField_free m).toMeasure

end Aqft2
