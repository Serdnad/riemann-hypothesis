module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle865
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle068
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

namespace GlobalTheory.ConjNormPow

theorem absNorm_comap_equiv {K : Type} [Field K] [NumberField K] (e : 𝓞 K ≃+* 𝓞 K)
    (I : Ideal (𝓞 K)) : Ideal.absNorm (I.comap e) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv (I.comap e) I e
    (Ideal.map_comap_of_surjective _ e.surjective I).symm).toEquiv

theorem absNorm_maxPowDividing_conjPl : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (N : ℕ), Ideal.absNorm ((Formalism.L2.DIV.conjPl P).maxPowDividing (Ideal.span {((N : ℕ) : 𝓞 D.host.E)})) = Ideal.absNorm (P.maxPowDividing (Ideal.span {((N : ℕ) : 𝓞 D.host.E)})) := by
  intro D P N
  classical
  let σ : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingEquiv.ofRingHom Formalism.L2.DIV.starOHom Formalism.L2.DIV.starOHom
    (RingHom.ext fun a => Formalism.L2.DIV.starO_starO a) (RingHom.ext fun a => Formalism.L2.DIV.starO_starO a)
  have hc : (Formalism.L2.DIV.conjPl P).asIdeal = P.asIdeal.comap σ := rfl
  set J : Ideal (𝓞 D.host.E) := Ideal.span {((N : ℕ) : 𝓞 D.host.E)} with hJdef
  have hJ : J.comap σ = J := by
    rw [← Ideal.map_symm, hJdef, Ideal.map_span, Set.image_singleton, map_natCast]
  have hpow : ∀ k : ℕ, (P.asIdeal.comap σ) ^ k = (P.asIdeal ^ k).comap σ := by
    intro k
    rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]
  have hiff : ∀ k : ℕ, J ≤ (P.asIdeal.comap σ) ^ k ↔ J ≤ P.asIdeal ^ k := by
    intro k
    rw [hpow, ← hJ, Ideal.comap_le_comap_iff_of_surjective _ σ.surjective, hJ]
  have hcount : (Associates.mk (Formalism.L2.DIV.conjPl P).asIdeal).count (Associates.mk J).factors =
      (Associates.mk P.asIdeal).count (Associates.mk J).factors := by
    by_cases hJ0 : J = ⊥
    · rw [hJ0, ← Ideal.zero_eq_bot, Associates.mk_zero, Associates.factors_zero]
      simp only [Associates.count]
      split_ifs <;> rfl
    have hm : Associates.mk J ≠ 0 := Associates.mk_ne_zero.mpr hJ0
    have key : ∀ (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (k : ℕ),
        k ≤ (Associates.mk Q.asIdeal).count (Associates.mk J).factors ↔ J ≤ Q.asIdeal ^ k := by
      intro Q k
      rw [← Associates.prime_pow_dvd_iff_le hm (Associates.irreducible_mk.mpr Q.irreducible),
        ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]
    apply le_antisymm
    · rw [key P, ← hiff, ← hc, ← key]
    · rw [key (Formalism.L2.DIV.conjPl P), hc, hiff, ← key]
  simp only [IsDedekindDomain.HeightOneSpectrum.maxPowDividing]
  rw [hcount, hc, hpow, absNorm_comap_equiv]

end GlobalTheory.ConjNormPow
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem mb_le_conjPl_of_not_le : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (Q : Formalism.L2.DIV.Pl D.host.E), ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ¬ l₂.Mb ≤ Q.asIdeal → l₂.Mb ≤ (Formalism.L2.DIV.conjPl Q).asIdeal := by
  intro D H l₂ Q hM hnot
  have hprod : l₂.Mb * l₂.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ Q.asIdeal := by
    rw [l₂.prod, Ideal.span_le, Set.singleton_subset_iff]; exact hM
  rcases Ideal.IsPrime.mul_le Q.isPrime |>.1 hprod with h | h
  · exact absurd h hnot
  · rw [Ideal.map_le_iff_le_comap] at h
    intro x hx
    have hx' := h hx
    show Formalism.L2.DIV.starOHom x ∈ Q.asIdeal
    have e : Formalism.L2.DIV.starOHom x = (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) x := by
      apply RingOfIntegers.ext
      have hb := H.bar_eq x
      simp only [RingEquiv.coe_toRingHom] at hb ⊢
      rw [hb]
      exact Formalism.L2.DIV.starO_coe x
    rw [e]; exact hx'

end GlobalTheory.LevelSeries
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

namespace GlobalTheory.WeilUnitNorm

open MeasureTheory

theorem weil_norm_one_of_unit_norm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (μ : MeasureTheory.Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (p : GA D S × GA D T) (f : WO S T → ℂ), IsThetaFunO ψ S T f → nrm2 μ 𝓕 f = 1 → nrm2 μ 𝓕 (om p f) = 1 := by
  intro D ψ S T χS χT om hW μ 𝓕 hC p f hf h1
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have key := hW.om_unit μ 𝓕 hC.1 hC.2.1 p f hf
  have hf' := hW.om_pres p f hf
  have m1 : AEStronglyMeasurable (fun w => ‖om p f w‖ ^ 2) (μ.restrict 𝓕) :=
    (hf'.cont.norm.pow 2).aestronglyMeasurable
  have m2 : AEStronglyMeasurable (fun w => ‖f w‖ ^ 2) (μ.restrict 𝓕) :=
    (hf.cont.norm.pow 2).aestronglyMeasurable
  have e : nrm2 μ 𝓕 (om p f) = nrm2 μ 𝓕 f := by
    unfold nrm2
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => by positivity) m1,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => by positivity) m2]
    congr 1
    simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    exact key
  rw [e, h1]

end GlobalTheory.WeilUnitNorm
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelFieldApprox

open Formalism.L2.Host

theorem val_eq_one_of_close {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)} {y : E}
    (h : v.valuation E (y - 1) < 1) : v.valuation E y = 1 := by
  have e : y = (y - 1) + 1 := by ring
  rw [e, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one])]
  exact map_one _

theorem locK_eq_one {E : Type} [Field E] [NumberField E] (χ : HChar E) (v : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (hn : χ.LevelLe v n) (y : Eˣ) (h : v.valuation E ((y : E) - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) :
    χ.locK v y = 1 ∧ v.valuation E (y : E) = 1 := by
  have hlt : v.valuation E ((y : E) - 1) < 1 :=
    lt_of_le_of_lt h (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hv := val_eq_one_of_close hlt
  have e1 : ((atFin v y : (v.adicCompletion E)ˣ) : v.adicCompletion E) = algebraMap E (v.adicCompletion E) (y : E) := rfl
  have hval : ∀ x : E, Valued.v (algebraMap E (v.adicCompletion E) x) = v.valuation E x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  refine ⟨?_, hv⟩
  show χ.loc v (atFin v y) = 1
  refine hn _ ?_ ?_
  · show Valued.v ((atFin v y : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1
    rw [e1, hval, hv]
  · rw [e1, ← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, hval]
    exact h.trans (WithZero.exp_le_exp.mpr (by omega))

theorem exists_approx : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (M₀ : ℕ) (u : Eˣ), (u : E) = ((M₀ : ℕ) : E) → ∀ (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ a : Eˣ, IsIntegral ℤ (a : E) ∧ (∀ v ∈ T, χ.locK v a = χ.locK v u ∧ v.valuation E (a : E) = v.valuation E ((M₀ : ℕ) : E)) ∧ ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → χ.locK v a = 1 ∧ v.valuation E (a : E) = 1 := by
  intro E _ _ χ M₀ u hu T
  classical
  have hM0 : M₀ ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [hu]; simp)
  have hM : ((M₀ : ℕ) : 𝓞 E) ≠ 0 := by exact_mod_cast hM0
  have hMe : ((M₀ : ℕ) : E) ≠ 0 := by exact_mod_cast hM0
  have hfin : {v : HeightOneSpectrum (𝓞 E) | ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((M₀ : ℕ) : 𝓞 E)}) ?_).subset fun v hv => ?_
    · rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    · exact Ideal.dvd_span_singleton.2 hv
  set S : Finset (HeightOneSpectrum (𝓞 E)) := T ∪ hfin.toFinset with hS
  choose n hn using GlobalTheory.Mem.UnrAe.exists_levelLe χ
  have hm : ∀ v : HeightOneSpectrum (𝓞 E), ∃ m : ℕ, v.intValuation ((M₀ : ℕ) : 𝓞 E) = WithZero.exp (-(m : ℤ)) :=
    fun v => ⟨_, v.intValuation_if_neg hM⟩
  choose m hm using hm
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal)
    (fun v => if v ∈ T then m v + n v + 1 else n v + 1)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h'))
    (fun v => if (v : HeightOneSpectrum (𝓞 E)) ∈ T then ((M₀ : ℕ) : 𝓞 E) else 1)
  have hvz : ∀ v : HeightOneSpectrum (𝓞 E), ∀ z : 𝓞 E, v.valuation E (z : E) = v.intValuation z :=
    fun v z => HeightOneSpectrum.valuation_of_algebraMap (K := E) v z
  have hT : ∀ v ∈ T, v.valuation E ((y : E) - ((M₀ : ℕ) : E)) ≤ WithZero.exp (-((m v : ℤ) + n v + 1)) := by
    intro v hv
    have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hy v (Finset.mem_union_left _ hv))
    simp only [hv, if_true] at h1
    have e : (y : E) - ((M₀ : ℕ) : E) = ((y - ((M₀ : ℕ) : 𝓞 E) : 𝓞 E) : E) := by push_cast; rfl
    rw [e, hvz]
    convert h1 using 2
    push_cast; ring
  have hO : ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T →
      v.valuation E ((y : E) - 1) ≤ WithZero.exp (-((n v : ℤ) + 1)) := by
    intro v hv hvT
    have h1 := (v.intValuation_le_pow_iff_mem _ _).2
      (hy v (Finset.mem_union_right _ (hfin.mem_toFinset.2 hv)))
    simp only [hvT, if_false] at h1
    have e : (y : E) - 1 = ((y - 1 : 𝓞 E) : E) := by push_cast; rfl
    rw [e, hvz]
    convert h1 using 2
    push_cast; ring
  have hMv : ∀ v, v.valuation E ((M₀ : ℕ) : E) = WithZero.exp (-(m v : ℤ)) := by
    intro v
    rw [← hm v, ← hvz]; simp
  have hTv : ∀ v ∈ T, v.valuation E (y : E) = v.valuation E ((M₀ : ℕ) : E) := by
    intro v hv
    have e : (y : E) = ((y : E) - ((M₀ : ℕ) : E)) + ((M₀ : ℕ) : E) := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    rw [hMv]
    exact lt_of_le_of_lt (hT v hv) (WithZero.exp_lt_exp.mpr (by omega))
  have hOv : ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → v.valuation E (y : E) = 1 :=
    fun v hv hvT => val_eq_one_of_close (lt_of_le_of_lt (hO v hv hvT)
      (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega))
  by_cases hy0 : (y : E) = 0
  · refine ⟨1, by simpa using isIntegral_one, fun v hv => ?_, fun v hv hvT => ?_⟩
    · exact absurd (hTv v hv) (by rw [hy0, map_zero, hMv]; exact (WithZero.exp_ne_zero).symm)
    · exact absurd (hOv v hv hvT) (by rw [hy0, map_zero]; exact zero_ne_one)
  set a : Eˣ := Units.mk0 (y : E) hy0 with ha
  refine ⟨a, y.isIntegral_coe, fun v hv => ?_, fun v hv hvT => ?_⟩
  · have hw := (locK_eq_one χ v (hn v) (a * u⁻¹) ?_).1
    · refine ⟨?_, hTv v hv⟩
      have : a = (a * u⁻¹) * u := by group
      rw [this, map_mul, hw, one_mul]
    · rw [Units.val_mul, Units.val_inv_eq_inv_val, hu, ha, Units.val_mk0]
      have e : (y : E) * ((M₀ : ℕ) : E)⁻¹ - 1 = ((y : E) - ((M₀ : ℕ) : E)) / ((M₀ : ℕ) : E) := by
        field_simp
      rw [e, map_div₀, hMv]
      calc _ ≤ WithZero.exp (-((m v : ℤ) + n v + 1)) / WithZero.exp (-(m v : ℤ)) :=
            div_le_div_of_nonneg_right (hT v hv) zero_le'
        _ = _ := by rw [div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]; congr 1; ring
  · exact locK_eq_one χ v (hn v) a (by rw [ha, Units.val_mk0]; exact hO v hv hvT)

end GlobalTheory.LevelFieldApprox
end
end

section

namespace GlobalTheory.ConjSpan

theorem exists_ringEquiv_fix_ne (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (z : ℂ)
    (hz : Transcendental ℚ z) : ∃ τ : ℂ ≃+* ℂ, (∀ x, τ (σ x) = σ x) ∧ τ z ≠ z := by
  letI : Algebra K ℂ := σ.toAlgebra
  haveI : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq (fun q => by simp)
  have hzK : Transcendental K z := fun h => hz (h.restrictScalars ℚ)
  have hind : AlgebraicIndepOn K id ({z} : Set ℂ) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using hzK
  obtain ⟨B, hzB, hB⟩ := exists_isTranscendenceBasis_superset hind
  have hzB' : z ∈ B := hzB rfl
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hB
  let n : MvPolynomial B K ≃ₐ[K] MvPolynomial B K :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval fun i => - MvPolynomial.X i)
      (MvPolynomial.aeval fun i => - MvPolynomial.X i) (by ext; simp) (by ext; simp)
  let e := hB.1.aevalEquiv.symm.trans (n.trans hB.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e.toRingEquiv, ?_, ?_⟩
  · intro x
    have hx : σ x = algebraMap K ℂ x := rfl
    rw [hx, IsScalarTower.algebraMap_apply K (Algebra.adjoin K (Set.range ((↑) : B → ℂ))) ℂ,
      IsAlgClosure.equivOfEquiv_algebraMap]
    simp
  have h1 : algebraMap _ ℂ (hB.1.aevalEquiv (MvPolynomial.X ⟨z, hzB'⟩)) = z := by
    rw [hB.1.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  have h2 : IsAlgClosure.equivOfEquiv ℂ ℂ e.toRingEquiv z = -z := by
    conv_lhs => rw [← h1]
    rw [IsAlgClosure.equivOfEquiv_algebraMap]
    have : e.toRingEquiv (hB.1.aevalEquiv (MvPolynomial.X ⟨z, hzB'⟩))
        = hB.1.aevalEquiv (- MvPolynomial.X ⟨z, hzB'⟩) := by
      simp [e, n]
    rw [this, map_neg, map_neg, h1]
  rw [h2]
  intro h
  have hz0 : z = 0 := by linear_combination (-1/2 : ℂ) * h
  exact hz (hz0 ▸ isAlgebraic_zero)

theorem exists_eq_of_forall_fixed (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (z : ℂ)
    (hz : ∀ τ : ℂ ≃+* ℂ, (∀ x, τ (σ x) = σ x) → τ z = z) : ∃ c : K, σ c = z := by
  by_cases ha : IsAlgebraic ℚ z
  · have := GlobalTheory.FixedAlgebraic.mem_of_forall_ringEquiv_fixed σ.fieldRange z ha (fun τ hτ => hz τ
      (fun x => hτ _ ⟨x, rfl⟩))
    simpa using this
  · obtain ⟨τ, hτ, hne⟩ := exists_ringEquiv_fix_ne K σ z ha
    exact absurd (hz τ hτ) hne

theorem span_conj_eq_top : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (ι : Type) [Fintype ι]
    (e : ι → ℂ), (∀ c : ι → K, ∑ i, σ (c i) * e i = 0 → c = 0) →
    Submodule.span ℂ {v : ι → ℂ | ∃ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) ∧ v = fun i => φ (e i)} = ⊤ := by
  intro K _ _ σ ι _ e he
  classical
  let R : Submodule ℂ (ι → ℂ) :=
    { carrier := {z | ∀ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) → ∑ i, z i * φ (e i) = 0}
      add_mem' := by
        intro a b ha hb φ hφ
        simp only [Set.mem_setOf_eq, Pi.add_apply, add_mul, Finset.sum_add_distrib, ha φ hφ,
          hb φ hφ, add_zero]
      zero_mem' := by intro φ hφ; simp
      smul_mem' := by
        intro c a ha φ hφ
        simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum,
          ha φ hφ, mul_zero] }
  have hRmem : ∀ z, z ∈ R ↔ ∀ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) → ∑ i, z i * φ (e i) = 0 :=
    fun z => Iff.rfl
  have key : ∀ n, ∀ z ∈ R, (Finset.univ.filter (fun i => z i ≠ 0)).card = n → z = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro z hz hcard
    by_contra hne
    obtain ⟨i0, hi0⟩ : ∃ i, z i ≠ 0 := by
      by_contra h; push_neg at h; exact hne (funext h)
    set z' := (z i0)⁻¹ • z with hz'
    have hz'R : z' ∈ R := R.smul_mem _ hz
    have hz'i0 : z' i0 = 1 := by simp [z', hi0]
    have hsupp : (Finset.univ.filter (fun i => z' i ≠ 0))
        = Finset.univ.filter (fun i => z i ≠ 0) := by
      ext i; simp [z', hi0]
    have hfix : ∀ ψ : ℂ ≃+* ℂ, (∀ x, ψ (σ x) = σ x) → ∀ i, ψ (z' i) = z' i := by
      intro ψ hψ
      have hw : (fun i => ψ (z' i)) - z' ∈ R := by
        refine R.sub_mem ?_ hz'R
        rw [hRmem]
        intro φ hφ
        have h1 := (hRmem z').1 hz'R (φ.trans ψ.symm) (by
          intro x
          rw [RingEquiv.trans_apply, hφ, RingEquiv.symm_apply_eq, hψ])
        have h2 := congrArg ψ h1

        simpa [map_sum, map_mul] using h2
      have hlt : (Finset.univ.filter (fun i => ((fun i => ψ (z' i)) - z') i ≠ 0)).card < n := by
        rw [← hcard, ← hsupp]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨i0, by simp [hz'i0], by simp [hz'i0]⟩
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, ne_eq] at hi ⊢
          intro h
          apply hi
          simp [h]
      have h3 := ih _ hlt _ hw rfl
      intro i
      have h4 := congrFun h3 i
      simpa [sub_eq_zero] using h4
    choose c hc using fun i => exists_eq_of_forall_fixed K σ (z' i) (fun τ hτ => hfix τ hτ i)
    have hc0 := he c (by
      have h5 := (hRmem z').1 hz'R (RingEquiv.refl ℂ) (fun x => rfl)
      simpa [hc] using h5)
    have h6 : z' i0 = 0 := by rw [← hc i0, hc0]; simp
    rw [hz'i0] at h6
    exact one_ne_zero h6
  by_contra hS
  obtain ⟨f, hf0, hf⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hS) inferInstance
  let z : ι → ℂ := fun i => f (fun j => if i = j then 1 else 0)
  have hzR : z ∈ R := by
    rw [hRmem]
    intro φ hφ
    have hmem : (fun i => φ (e i)) ∈ Submodule.span ℂ
        {v : ι → ℂ | ∃ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) ∧ v = fun i => φ (e i)} :=
      Submodule.subset_span ⟨φ, hφ, rfl⟩
    have h7 : f (fun i => φ (e i)) = 0 := by
      have h8 := Submodule.mem_map_of_mem (f := f) hmem
      rw [hf, Submodule.mem_bot] at h8
      exact h8
    rw [LinearMap.pi_apply_eq_sum_univ] at h7
    simpa [z, smul_eq_mul, mul_comm] using h7
  have hz0 := key _ z hzR rfl
  apply hf0
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.pi_apply_eq_sum_univ]
  have : ∀ i, f (fun j => if i = j then 1 else 0) = 0 := fun i => congrFun hz0 i
  simp [this]

end GlobalTheory.ConjSpan
end
