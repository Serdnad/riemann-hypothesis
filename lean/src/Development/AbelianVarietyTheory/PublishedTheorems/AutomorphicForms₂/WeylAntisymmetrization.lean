import Mathlib

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.GoodMetric

variable {ι : Type} {m : ι → ℕ}

abbrev Root (m : ι → ℕ) : Type := Σ τ, Fin (m τ)

variable (m)

def chernRoots : MvPolynomial (ι × ℕ) ℝ →ₐ[ℝ] MvPolynomial (Root m) ℝ :=
  aeval fun x => rename (Sigma.mk x.1) (esymm (Fin (m x.1)) ℝ x.2)

variable [Fintype ι]

def fibrePoint : MvPolynomial (Root m) ℝ := ∏ x : Root m, (-X x) ^ (m x.1 - 1 - x.2)

def rootDiscr : MvPolynomial (Root m) ℝ :=
  ∏ τ, ∏ j : Fin (m τ), ∏ i ∈ Finset.Iio j, (X ⟨τ, j⟩ - X ⟨τ, i⟩)

variable {m} in
open Classical in

def antisymm (Q : MvPolynomial (Root m) ℝ) : MvPolynomial (Root m) ℝ :=
  ∑ w : ∀ τ, Equiv.Perm (Fin (m τ)),
    ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q

end GlobalTheory.GoodMetric
