module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinTwistingCharacterDeltaGoodStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodSetupCountEqZeroOffBadPlaces
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NormUnit

theorem coprime_absNorm {K : Type} [Field K] [NumberField K] (l : ℕ) (hl : l.Prime)
    (P : HeightOneSpectrum (𝓞 K)) (hP : ((l : ℕ) : 𝓞 K) ∉ P.asIdeal) :
    Nat.Coprime l (Ideal.absNorm P.asIdeal) := by
  intros
  apply _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem <;> assumption

theorem isUnit_natCast_of_coprime {R : Type} [CommRing R] [IsLocalRing R] {l n : ℕ}
    (hl : ((l : ℕ) : R) ∈ IsLocalRing.maximalIdeal R) (h : Nat.Coprime l n) : IsUnit ((n : ℕ) : R) := by
  by_contra hn
  have hn' : ((n : ℕ) : R) ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hn
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 h : IsCoprime (l : ℤ) (n : ℤ))
  have e : (1 : R) = (a : R) * (l : R) + (b : R) * (n : R) := by
    have := congrArg (Int.cast : ℤ → R) hab
    push_cast at this
    exact this.symm
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [e]; exact add_mem (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hn')
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem normProd_inv_mem (D : D7) (ρ : Setup D.ntw) (i : D.ntw.Tw) (b : Bool) (Q : Finset (Pl D.host.E))
    (hQ : Disjoint Q (D.ntw.S0 i)) : ((normProd Q : ℕ) : ℂ)⁻¹ ∈ (ρ.eO i b).range := by
  have hcop : Nat.Coprime (D.ntw.l i) (normProd Q) := by
    unfold normProd
    refine Nat.Coprime.prod_right fun P hP => coprime_absNorm _ (D.ntw.lPrime i).out P fun hl => ?_
    exact Finset.disjoint_left.1 hQ hP (D.ntw.twistExcludedPlaces_contains_residueChar i hl)
  obtain ⟨u, hu⟩ := isUnit_natCast_of_coprime (D.ntw.O_l i) hcop
  refine ⟨(u⁻¹ : (D.ntw.O i)ˣ), ?_⟩
  have h1 : ρ.eO i b (u : D.ntw.O i) = ((normProd Q : ℕ) : ℂ) := by rw [hu, map_natCast]
  rw [← h1]
  exact map_units_inv (ρ.eO i b) u

end GlobalTheory.NormUnit
