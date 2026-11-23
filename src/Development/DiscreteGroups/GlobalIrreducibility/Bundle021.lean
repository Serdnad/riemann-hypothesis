module

public import Development.DiscreteGroups.GlobalIrreducibility.DzTypeCut
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.DiscreteGroups.GlobalIrreducibility.ExistsOfMemKOne
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Mathlib.Algebra.Group.End
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesOfIsSubquotient
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle018

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem lDepth : LDepth := by
  intro E _ _ w g _ i hi n τ σ hs
  obtain ⟨φ, hφ, hφe⟩ := hs
  obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
    by_contra h
    exact hφ (LinearMap.ext fun u => not_not.1 fun hne => h ⟨u, hne⟩)
  let e := equivRep σ
  have hfix : ∀ m ∈ KOne (w.adicCompletion E) (Fin n), σ.ρ m (φ u) = φ u := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := DiscreteGroups.sglob.DzIso.exists_of_mem_KOne i hi hm
    have := hφe k u
    rw [hk, map_one, Module.End.one_apply] at this
    exact this.symm
  intro hbot
  have hv : e.toIntertwiningMap (φ u) ∈ fixed (cls σ).rep (KOne (w.adicCompletion E) (Fin (cls σ).1)) := by
    intro m
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [← e.toIntertwiningMap.isIntertwining, hfix m m.2]
  rw [hbot, Submodule.mem_bot] at hv
  have h2 : e.toLinearEquiv (φ u) = 0 := hv
  exact hu (e.toLinearEquiv.injective (h2.trans (map_zero _).symm))

end DiscreteGroups.sglob.DzType
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Filter Topology

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [hg : Fact g.Prime]

theorem val_lt_one_of_norm_lt_one (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (u : ℚ_[g])
    (hu : ‖u‖ < 1) : Valued.v (i u) < 1 := by
  have := DiscreteGroups.sglob.DzIso.norm_lt_of_lt i hi hu
  rwa [Valued.toNormedField.norm_lt_one_iff] at this

theorem mem_of_val_lt_one (y : 𝓞 E) (h : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) < 1) :
    y ∈ w.asIdeal := by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
  have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w (y : E)
  rwa [e] at h

theorem val_le_one_int (y : 𝓞 E) : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) ≤ 1 := by
  have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w (y : E)
  rw [e]
  exact w.valuation_le_one y

theorem alg_sub_natCast (y : 𝓞 E) (a : ℕ) : algebraMap E (w.adicCompletion E) (((y - (a : 𝓞 E) : 𝓞 E)) : E) =
    algebraMap E (w.adicCompletion E) (y : E) - (a : w.adicCompletion E) := by
  simp

theorem alg_natCast (a : ℕ) : algebraMap E (w.adicCompletion E) (((a : 𝓞 E)) : E) = (a : w.adicCompletion E) := by
  simp

theorem normV_eq_of_padic (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) : normV w = g := by
  classical
  have hres : ∀ y : 𝓞 E, ∃ a : ℕ, y - (a : 𝓞 E) ∈ w.asIdeal := by
    intro y
    set x := i.symm (algebraMap E (w.adicCompletion E) (y : E)) with hx
    have hxy : i x = algebraMap E (w.adicCompletion E) (y : E) := by rw [hx, RingEquiv.apply_symm_apply]
    have hxn : ‖x‖ ≤ 1 := by
      by_contra hc
      push Not at hc
      have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact absurd hc (by norm_num)
      have h1 : ‖x⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hc
      have h2 := val_lt_one_of_norm_lt_one w g i hi _ h1
      rw [map_inv₀, hxy, map_inv₀] at h2
      have h3 := val_le_one_int w y
      have hy0 : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) ≠ 0 := by
        intro h0
        rw [h0, inv_zero] at h2
        have : i x ≠ 0 := (map_ne_zero i).mpr hx0
        rw [hxy] at this
        exact this ((Valuation.zero_iff _).mp h0)
      have h4 : 1 ≤ (Valued.v (algebraMap E (w.adicCompletion E) (y : E)))⁻¹ := one_le_inv₀ (zero_lt_iff.mpr hy0) |>.mpr h3
      exact absurd h2 (not_lt.mpr h4)
    let xz : ℤ_[g] := ⟨x, hxn⟩
    obtain ⟨a, -, ha⟩ := PadicInt.exists_mem_range xz
    refine ⟨a, mem_of_val_lt_one w _ ?_⟩
    have h5 : ‖x - a‖ < 1 := by
      have h := (PadicInt.mem_nonunits).mp ha
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h
      exact h
    have h6 := val_lt_one_of_norm_lt_one w g i hi _ h5
    rw [map_sub, hxy, map_natCast] at h6
    rw [alg_sub_natCast]
    exact h6
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    apply mem_of_val_lt_one w
    have := val_lt_one_of_norm_lt_one w g i hi (g : ℚ_[g]) Padic.norm_p_lt_one
    rw [map_natCast] at this
    rw [alg_natCast]
    exact this
  haveI : w.asIdeal.IsPrime := w.isPrime
  have hgQ : ((g : ℕ) : 𝓞 E ⧸ w.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hgw
  haveI : CharP (𝓞 E ⧸ w.asIdeal) g := (CharP.charP_iff_prime_eq_zero hg.out).mpr hgQ
  let f : ZMod g →+* 𝓞 E ⧸ w.asIdeal := ZMod.castHom (dvd_refl g) _
  have hinj : Function.Injective f := f.injective
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, ha⟩ := hres y
    refine ⟨(a : ZMod g), ?_⟩
    rw [ZMod.castHom_apply, ZMod.cast_natCast (dvd_refl g), ← map_natCast (Ideal.Quotient.mk w.asIdeal),
      Ideal.Quotient.eq]
    rw [← neg_mem_iff, neg_sub]
    exact ha
  unfold normV
  rw [← Nat.card_congr (RingEquiv.ofBijective f ⟨hinj, hsurj⟩).toEquiv, Nat.card_zmod]

end DiscreteGroups.sglob.DzType

end
end

section

noncomputable section

namespace DiscreteGroups.sglob.DzType.Rt

theorem le_of_sigmaEquiv {s n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) (a : Fin s) : d a ≤ n := by
  have h1 := Fintype.card_le_of_injective _ (sigma_mk_injective (β := fun a => Fin (d a)) (i := a))
  simpa [Fintype.card_congr e] using h1

section Loc

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitRead GlobalTheory.PendOf ValuativeRel GlobalTheory.StepData

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory GlobalTheory.RegType

variable {g : ℕ} [Fact g.Prime] {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {w : HeightOneSpectrum (𝓞 E)}
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

variable {Ω : Type} [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : IsRec h rc) (hDZ : DiscreteGroups.sglob.DzType.DepthZeroInertiaBig)
  (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : LabelDatum g) (h5 : 5 ≤ g) (hA : AllLab L)
  {t : G E Ω} (ht : t ∈ Ine (F := E) A) (hκ : Formalism.L2.NT.TameCoupled A κ t L.gen)
include hi hrc hDZ ht hκ

end Loc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField



end DiscreteGroups.sglob.DzType.Rt

end
end
