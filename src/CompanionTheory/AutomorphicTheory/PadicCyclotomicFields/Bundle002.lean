module

public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohDefs
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmp
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.EulerCharGaloisOfCardEq
public import GroundTheory.ProfiniteCohomology.LocalTateDuality.TensorHomDualRepRootsOfUnityIsoCartierPairing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel Formalism.GaloisCohomology

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

theorem locfin_of (hF : SgcField) : Formalism.GaloisCohomology.LocalFinitenessK := by
  intro l _ K hK r M _ _ _ _ _ rho hr hc
  obtain ⟨hsep, v, t, hloc, -⟩ := hF l K hK
  let : ValuativeRel ↥K := v
  let : TopologicalSpace ↥K := t
  have : IsNonarchimedeanLocalField ↥K := hloc
  have : IsSepClosure ↥K (PadicAlgCl l) := hsep
  obtain ⟨A, hA, e, he⟩ := gcRep (Formalism.GaloisCohomology.GK l K) (ZMod (l ^ r)) M rho hc
  have : IsDiscreteRep A := hA
  have : Finite A := Finite.of_equiv M e.toEquiv
  have hcard : Nat.card A = Nat.card M := (Nat.card_congr e.toEquiv).symm
  have hM : (Nat.card A : ↥K) ≠ 0 := by
    rw [hcard]
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  obtain ⟨e0, -⟩ := gc0 (Formalism.GaloisCohomology.GK l K) (ZMod (l ^ r)) M rho A e he
  obtain ⟨e1, -⟩ := gc1 (Formalism.GaloisCohomology.GK l K) (ZMod (l ^ r)) M rho A e he
  obtain ⟨e2, -⟩ := gc2 (Formalism.GaloisCohomology.GK l K) (ZMod (l ^ r)) M rho A e he
  refine ⟨?_, ?_, ?_, fun n hn => ?_⟩
  · have := finite_cohomology_localField A hM 0
    exact Finite.of_equiv _ e0.symm.toEquiv
  · have := finite_cohomology_localField A hM 1
    exact Finite.of_equiv _ e1.symm.toEquiv
  · have := finite_cohomology_localField A hM 2
    exact Finite.of_equiv _ e2.symm.toEquiv
  · obtain ⟨en⟩ := gcn (Formalism.GaloisCohomology.GK l K) (ZMod (l ^ r)) M rho A e he n
    have := subsingleton_cohomology_localField A hM n hn
    exact en.toEquiv.subsingleton

end CompanionTheory.LocalTateOrthogonality.Gcoh
end

section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

theorem exists_card_eq_pow (l : ℕ) [hl : Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] : ∃ k, Nat.card M = l ^ k := by
  have h : IsPGroup l (Multiplicative M) := fun g => ⟨r, by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)), ZMod.natCast_self,
      zero_smul]⟩
  exact (IsPGroup.iff_card (p := l) (G := Multiplicative M)).1 h

theorem euler_of (hRep : SgcRep) (h0 : Sgc0) (h1 : Sgc1) (h2 : Sgc2) (hF : SgcField) :
    Formalism.GaloisCohomology.LocalEulerCharK := by
  intro l hl K hK r M _ _ _ _ _ rho _ hrho
  obtain ⟨hsep, v, t, hloc, hcard⟩ := hF l K hK
  obtain ⟨A, hA, e, he⟩ := hRep _ _ M rho hrho
  obtain ⟨e0, -⟩ := h0 _ _ M rho A e he
  obtain ⟨e1, -⟩ := h1 _ _ M rho A e he
  obtain ⟨e2, -⟩ := h2 _ _ M rho A e he
  obtain ⟨k, hk⟩ := exists_card_eq_pow l r M
  have : Finite A := Finite.of_equiv M e.toEquiv
  have hA' : Nat.card A = l ^ k := (Nat.card_congr e.toEquiv).symm.trans hk
  have hne : ((Nat.card A : ℕ) : K) ≠ 0 := by
    rw [hA']
    exact Nat.cast_ne_zero.2 (pow_ne_zero _ hl.out.ne_zero)
  have hE := @card_cohomology_mul_div_eq K (PadicAlgCl l) _ v t hloc _ _ hsep A hA this hne
  have hfin := @finite_cohomology_localField K (PadicAlgCl l) _ v t hloc _ _ hsep A hA this hne 1
  rw [hA', hcard k] at hE
  rw [Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv, hk]
  have hp1 : (Nat.card (cohomology A 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hp2 : (((l ^ k) ^ Module.finrank ℚ_[l] K : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (pow_ne_zero _ (pow_ne_zero _ hl.out.ne_zero))
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_mul, Nat.cast_mul, (div_eq_iff hp1).1 hE]
  field_simp

end CompanionTheory.LocalTateOrthogonality.Gcoh
end
