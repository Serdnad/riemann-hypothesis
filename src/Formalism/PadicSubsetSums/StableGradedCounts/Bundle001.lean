module

public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RepresentationTheory.Basic
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
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

section

open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem lpow_order_iff {G : Type*} [Monoid G] {l n : ℕ} (hl : l.Prime) (hn : n ≠ 0) (z : G)
    (hz : z ^ n = 1) : (∃ a : ℕ, z ^ (l ^ a) = 1) ↔ z ^ (l ^ padicValNat l n) = 1 := by
  constructor
  · rintro ⟨a, ha⟩
    have hg : z ^ (l ^ a).gcd n = 1 := pow_gcd_eq_one.2 ⟨ha, hz⟩
    obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow hl).1 (Nat.gcd_dvd_left (l ^ a) n)
    have hkn : l ^ k ∣ n := by
      rw [← hk']
      exact Nat.gcd_dvd_right _ _
    haveI := Fact.mk hl
    have hkv : k ≤ padicValNat l n := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hn).1 hkn
    obtain ⟨c, hc⟩ := pow_dvd_pow l hkv
    rw [hc, pow_mul, ← hk', hg, one_pow]
  · intro h
    exact ⟨_, h⟩

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem exists_algEquiv_extending {F E : Type} [Field F] [Field E] [Algebra F E] [IsAlgClosed E]
    (σ₀ : algebraicClosure F E ≃ₐ[F] algebraicClosure F E) :
    ∃ σ : E ≃ₐ[F] E, ∀ a : algebraicClosure F E, σ (a : E) = (σ₀ a : E) := by
  obtain ⟨ι, B, hB⟩ := exists_isTranscendenceBasis' (algebraicClosure F E) E
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis B hB
  let e₁ : MvPolynomial ι (algebraicClosure F E) ≃ₐ[algebraicClosure F E]
      Algebra.adjoin (algebraicClosure F E) (Set.range B) := hB.1.aevalEquiv
  let m : MvPolynomial ι (algebraicClosure F E) ≃+* MvPolynomial ι (algebraicClosure F E) :=
    MvPolynomial.mapEquiv ι σ₀.toRingEquiv
  let e : Algebra.adjoin (algebraicClosure F E) (Set.range B) ≃+*
      Algebra.adjoin (algebraicClosure F E) (Set.range B) :=
    e₁.symm.toRingEquiv.trans (m.trans e₁.toRingEquiv)
  let σ : E ≃+* E := IsAlgClosure.equivOfEquiv E E e
  have he : ∀ a : algebraicClosure F E,
      e (algebraMap _ _ a) = algebraMap _ _ (σ₀ a) := by
    intro a
    simp only [e, m, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C,
      ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl
  have hσ : ∀ a : algebraicClosure F E, σ (a : E) = (σ₀ a : E) := by
    intro a
    have h1 : (a : E) = algebraMap (Algebra.adjoin (algebraicClosure F E) (Set.range B)) E
        (algebraMap _ _ a) := rfl
    rw [h1, IsAlgClosure.equivOfEquiv_algebraMap, he]
    rfl
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) ?_, hσ⟩
  intro r
  have h1 : algebraMap F E r = ((algebraMap F (algebraicClosure F E) r : algebraicClosure F E) : E) :=
    rfl
  rw [h1, hσ, AlgEquiv.commutes]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section

namespace Formalism.IrreducibleCountingLemmas.TW

theorem asAlgebraHom_apply_eq_sum {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (x : MonoidAlgebra K G) (v : V) :
    ρ.asAlgebraHom x v = ∑ g ∈ x.coeff.support, x.coeff g • ρ g v := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum,
    LinearMap.sum_apply]
  rfl

end Formalism.IrreducibleCountingLemmas.TW
end
