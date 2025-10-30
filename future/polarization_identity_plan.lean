/--
  Goal: eventually supply the polarization identity for complex bilinear forms.
  We previously carried this as an axiom in `Aqft2/GFFMComplex.lean`.  The statement we
  plan to prove is recorded below for reference:

    polarization_identity {E : Type*} [AddCommGroup E] [Module ℂ E]
      (B : E → E → ℂ)
      (h_bilin : ∀ (c : ℂ) (x y z : E),
        B (c • x) y = c * B x y ∧
        B (x + z) y = B x y + B z y ∧
        B x (c • y) = c * B x y ∧
        B x (y + z) = B x y + B x z)
      (f g : E) :
      B f g = (1/4 : ℂ) * (
        B (f + g) (f + g) - B (f - g) (f - g) -
        Complex.I * B (f + Complex.I • g) (f + Complex.I • g) +
        Complex.I * B (f - Complex.I • g) (f - Complex.I • g)).

  Proof idea: adapt the standard polarization identity for sesquilinear forms, using the
  ℂ-bilinearity assumptions encoded in `h_bilin`.  Once the complex covariance extension is
  finalized, the lemma should follow from a short algebraic argument.
  Until then, the project references this file instead of assuming the axiom.
-/
