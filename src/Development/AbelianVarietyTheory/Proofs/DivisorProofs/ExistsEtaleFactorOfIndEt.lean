module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatMapMaximalIdealIsSeparable
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_etale_factor_of_indEt : ∀ (A O : Type) [CommRing A] [CommRing O] [Algebra A O], IndEt A O → ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B] (φ : B →ₐ[A] O), ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.Etale A C) (ψ : B →ₐ[A] C) (χ : C →ₐ[A] O), χ.comp ψ = φ := by
  intros
  apply _root_.GlobalTheory.IndEtaleLocal.exists_etale_factor <;> assumption

end GlobalTheory.EtC
