module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle792
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingEquivPlaceCorrespondencePlaceUnder
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle207
import GroundTheory.LocalFields.LocalFourierHaar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle130
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle074
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import GroundTheory.LocalFields.PadicLogSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle237
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle278
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPeriodProductEqOfInvertibleCharacter
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix GlobalTheory.IsoPull

namespace GlobalTheory.DegOneChar

section Char

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem detChar_map (i : k ≃+* k') (χ : kˣ →* ℂˣ) (g : GL (Fin 1) k') :
    detChar (Fin 1) χ (GeneralLinearGroup.map (n := Fin 1) i.symm.toRingHom g) =
      detChar (Fin 1) (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) g := by
  simp only [detChar_apply, MonoidHom.comp_apply]
  congr 1
  ext
  simp [RingHom.map_det]

theorem trGL_ofChar (i : k ≃+* k') (hi' : Continuous i.symm) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (h' : IsSmoothChar (χ.comp (Units.map i.symm.toRingHom.toMonoidHom))) :
    GlobalTheory.SuppIne.trGL i hi' (IrrGL.ofChar χ hχ) = IrrGL.ofChar (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) h' := by
  unfold GlobalTheory.SuppIne.trGL
  change _ = IrrGL.of (IrrRep.det (Fin 1) _ h').ρ (IrrRep.det (Fin 1) _ h').smooth (IrrRep.det (Fin 1) _ h').irr
  refine IrrGL.of_eq_of.2 ⟨?_⟩
  let E := (equivRep (IrrRep.det (Fin 1) χ hχ)).symm
  refine GlobalTheory.LocGL.equivOfBijective ⟨E.toLinearEquiv.toLinearMap, fun g => LinearMap.ext fun x => ?_⟩ E.toLinearEquiv.bijective
  have h1 := LinearMap.congr_fun (E.isIntertwining' (GeneralLinearGroup.map (n := Fin 1) i.symm.toRingHom g)) x
  change E.toLinearEquiv ((IrrRep.det (Fin 1) χ hχ).cl.rep.ρ _ x) = _
  refine h1.trans ?_
  change ((detChar (Fin 1) χ (GeneralLinearGroup.map (n := Fin 1) i.symm.toRingHom g) : ℂˣ) : ℂ) • E.toLinearEquiv x =
    ((detChar (Fin 1) (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) (g : GL (Fin 1) k') : ℂˣ) : ℂ) • E.toLinearEquiv x
  exact congrArg (fun z : ℂˣ => (z : ℂ) • E.toLinearEquiv x) (detChar_map i χ g)

end Char

section Norm

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem adicCompletionMap_eq (e : K ≃+* M) (he : ∀ x, e x = algebraMap K M x) {v : HeightOneSpectrum (𝓞 K)}
    {u : HeightOneSpectrum (𝓞 M)} [u.asIdeal.LiesOver v.asIdeal] (hO : Over e v u) (z : v.adicCompletion K) :
    GroundTheory.Global.adicCompletionMap v u z = cLoc hO z :=
  congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := K) v).equalizer
    (GroundTheory.Global.continuous_adicCompletionMap v u) (continuous_cLoc hO)
    (funext fun x => (GroundTheory.Global.adicCompletionMap_algebraMap v u x).trans
      (by rw [Function.comp_apply, cLoc_algebraMap hO x, he]))) z

theorem normU_apply (e : K ≃+* M) (he : ∀ x, e x = algebraMap K M x) {v : HeightOneSpectrum (𝓞 K)}
    {u : HeightOneSpectrum (𝓞 M)} [u.asIdeal.LiesOver v.asIdeal] (hO : Over e v u) (y : (u.adicCompletion M)ˣ) :
    ((GlobalTheory.BCChar.normU v u y : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (locEquiv hO).symm y := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  have hf : ∀ z, algebraMap (v.adicCompletion K) (u.adicCompletion M) z = locEquiv hO z :=
    adicCompletionMap_eq e he hO
  have hb : Function.Bijective (algebraMap (v.adicCompletion K) (u.adicCompletion M)) := by
    have : ⇑(algebraMap (v.adicCompletion K) (u.adicCompletion M)) = locEquiv hO := funext hf
    rw [this]
    exact (locEquiv hO).bijective
  have h1 : Module.finrank (v.adicCompletion K) (u.adicCompletion M) = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 hb
  obtain ⟨z, hz⟩ := hb.2 (y : u.adicCompletion M)
  change Algebra.norm (v.adicCompletion K) (y : u.adicCompletion M) = _
  rw [← hz, Algebra.norm_algebraMap, h1, pow_one, hf, RingEquiv.symm_apply_apply]

theorem normU_eq (e : K ≃+* M) (he : ∀ x, e x = algebraMap K M x) {v : HeightOneSpectrum (𝓞 K)}
    {u : HeightOneSpectrum (𝓞 M)} [u.asIdeal.LiesOver v.asIdeal] (hO : Over e v u) :
    GlobalTheory.BCChar.normU v u = Units.map (locEquiv hO).symm.toRingHom.toMonoidHom :=
  MonoidHom.ext fun y => Units.ext (normU_apply e he hO y)

theorem over_of_liesOver (e : K ≃+* M) (he : ∀ x, e x = algebraMap K M x) (v : HeightOneSpectrum (𝓞 K))
    (u : HeightOneSpectrum (𝓞 M)) [h : u.asIdeal.LiesOver v.asIdeal] : Over e v u := fun x => by
  have hx : RingOfIntegers.mapRingEquiv e x = algebraMap (𝓞 K) (𝓞 M) x := RingOfIntegers.ext (he x)
  rw [hx, h.over, Ideal.under_def, Ideal.mem_comap]

end Norm

section Lift

theorem ofChar_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {χ ψ : kˣ →* ℂˣ} (h : χ = ψ) (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) : IrrGL.ofChar χ hχ = IrrGL.ofChar ψ hψ := by
  subst h
  rfl

variable {K M : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M]
  [Algebra K M]

theorem charLift_of_isLift (h1 : Module.finrank K M = 1) {a : ℕ} {π : CuspSub K a} {P : CuspSub M a}
    (hP : IsLift π P) : CharLift π P := by
  refine ⟨hP, fun v u _ τ T hτ hT ξ hξ hs => ?_⟩
  let e : K ≃+* M := RingEquiv.ofBijective (algebraMap K M) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)
  have he : ∀ x, e x = algebraMap K M x := fun _ => rfl
  have hO : Over e v u := over_of_liesOver e he v u
  let i := locEquiv hO
  have hi : Continuous i := continuous_cLoc hO
  have hi' : Continuous i.symm := continuous_cLoc hO.symm
  obtain ⟨E, hE⟩ := hP.loc v u i hi (fun x => cLoc_algebraMap hO x) τ T hτ hT
  have hg : ∀ g : GL (Fin a) (u.adicCompletion M),
      GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
  let φ : Representation.Equiv (τ.ρ.comp (GeneralLinearGroup.map (n := Fin a) i.symm.toRingHom)) T.ρ :=
    GlobalTheory.LocGL.equivOfBijective ⟨E.toLinearMap, fun g => LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change E (τ.ρ (GeneralLinearGroup.map i.symm.toRingHom g) x) = T.ρ g (E x)
      rw [hE, hg]⟩ E.bijective
  have hs2 := (GlobalTheory.SuppIne.hasSupport_comp i hi hi' hs).of_equiv φ
  have hN := normU_eq e he hO
  have hc : (chars ξ hξ).map (GlobalTheory.SuppIne.trGL i hi') =
      chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU v u)) fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j) := by
    unfold chars
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun j _ => ?_
    have hj : IsSmoothChar ((ξ j).comp (Units.map i.symm.toRingHom.toMonoidHom)) := by
      have := GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j)
      rwa [hN] at this
    rw [Function.comp_apply, trGL_ofChar i hi' (ξ j) (hξ j) hj]
    exact ofChar_congr (by rw [hN]) _ _
  rw [← hc]
  exact hs2

end Lift

theorem exists_charLift : ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M], Module.finrank K M = 1 → ∀ (a : ℕ), 1 ≤ a → ∀ π : CuspSub K a, ∃ P : CuspSub M a, CharLift π P := by
  intro K M _ _ _ _ _ _ _ h1 a _ π
  obtain ⟨P, hP⟩ := GlobalTheory.DegOneLift.isLift K M h1 a π
  exact ⟨P, charLift_of_isLift h1 hP⟩

end GlobalTheory.DegOneChar
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.TwistSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nu_nu_neg (x : IrrGL (k := k)) (s : ℂ) : (x.nu s).nu (-s) = x := by
  rw [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero]

theorem nu_injective (s : ℂ) : Function.Injective fun x : IrrGL (k := k) => x.nu s := fun x y h => by
  have := congrArg (fun z : IrrGL (k := k) => z.nu (-s)) h
  simpa only [nu_nu_neg] using this

theorem chars_eq_map_nu {n : ℕ} (ξ ξ' : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j))
    (hξ' : ∀ j, IsSmoothChar (ξ' j)) (s : ℂ) (h : ∀ j, ξ' j = ξ j * absPow k s) :
    chars ξ' hξ' = (chars ξ hξ).map fun y => y.nu s := by
  unfold chars
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun j _ => ?_
  simp only [Function.comp_apply, IrrGL.nu, IrrGL.tw_ofChar]
  exact IrrGL.ofChar_inj.2 (h j)

theorem unlinked_map_nu (m : Multiset (IrrGL (k := k))) (s : ℂ) :
    Unlinked (m.map fun y => y.nu s) ↔ Unlinked m := by
  constructor
  · intro h y hy z hz e
    refine h (y.nu s) (Multiset.mem_map_of_mem _ hy) (z.nu s) (Multiset.mem_map_of_mem _ hz) ?_
    rw [e, IrrGL.nu_nu, IrrGL.nu_nu, add_comm]
  · intro h y' hy' z' hz' e
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hy'
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hz'
    refine h y hy z hz (nu_injective s ?_)
    simp only
    rw [e, IrrGL.nu_nu, IrrGL.nu_nu, add_comm]

theorem supp_nu_chars : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (n : ℕ) (ξ ξ' : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (hξ' : ∀ j, IsSmoothChar (ξ' j)) (s : ℂ), (∀ j, ξ' j = ξ j * absPow k s) → (HasSupport x.rep (chars ξ hξ) ↔ HasSupport (x.nu s).rep (chars ξ' hξ')) ∧ (Unlinked (chars ξ hξ) ↔ Unlinked (chars ξ' hξ')) := by
  intro k _ _ _ _ _ x n ξ ξ' hξ hξ' s h
  rw [chars_eq_map_nu ξ ξ' hξ hξ' s h, unlinked_map_nu]
  refine ⟨⟨fun H => SupportRing.hasSupport_nu H s, fun H => ?_⟩, Iff.rfl⟩
  have H' := SupportRing.hasSupport_nu H (-s)
  rw [nu_nu_neg, Multiset.map_map] at H'
  simpa only [Function.comp_def, nu_nu_neg, Multiset.map_id'] using H'

end GlobalTheory.RoadU.TwistSupp
end
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnlinkedFirst

theorem single_linked_single_nu {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ρ ρ' : IrrGL (k := k)} (hρ : ρ.IsCusp) (hρ' : ρ'.IsCusp) (hne : ρ ≠ ρ.nu 1) (he : ρ' = ρ.nu 1) :
    (Segment.single ρ hρ).Linked (Segment.single ρ' hρ') := by
  subst he
  refine ⟨⟨Segment.ofFirst ρ hρ 2 two_pos, ?_⟩, ?_, ?_⟩
  · rw [Segment.carrier_single, Segment.carrier_single]
    ext z
    rw [Segment.mem_carrier]
    simp only [Segment.first_ofFirst, Segment.len_ofFirst, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      interval_cases i
      · left; simp
      · right; simp
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
  · rw [Segment.carrier_single, Segment.carrier_single, Set.singleton_subset_iff, Set.mem_singleton_iff]
    exact hne
  · rw [Segment.carrier_single, Segment.carrier_single, Set.singleton_subset_iff, Set.mem_singleton_iff]
    exact fun e => hne e.symm

theorem unlinked_first_of_len_one : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (rc : IrrGL (k := w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (c : ℕ) (Δ : Fin c → Segment (w.adicCompletion E)), (∀ i, (Δ i).len = 1) →
      (∀ i j, i ≠ j → ¬ (Δ i).Linked (Δ j)) →
      GlobalTheory.RoadU.Unlinked (Finset.univ.val.map fun i => (Δ i).first) := by
  intro E Ω _ _ _ _ _ A w h rc hrc c Δ hlen hun
  obtain ⟨a, ha, L⟩ := hrc
  intro y hy z hz hyz
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
  have hne : (Δ j).first ≠ (Δ j).first.nu 1 := by
    intro e0
    refine GlobalTheory.UnlinkedMono.lpTw_one_ne (rc (Δ j).first) (by rw [L.dim]; exact (Δ j).isCusp_first.1) ?_
    calc (rc (Δ j).first).lpTw 1 = rc ((Δ j).first.nu ((1 : ℝ) : ℂ)) := (L.nu _ 1).symm
      _ = rc (Δ j).first := by rw [Complex.ofReal_one, ← e0]
  have eΔ : ∀ k, Δ k = Segment.single (Δ k).first (Δ k).isCusp_first := fun k =>
    Segment.ext_first (by simp [Segment.single]) (by simp [Segment.single, hlen k])
  by_cases hij : j = i
  · subst hij; exact hne hyz
  exact hun j i hij (by
    rw [eΔ j, eΔ i]
    exact single_linked_single_nu (Δ j).isCusp_first (Δ i).isCusp_first hne hyz)

end GlobalTheory.UnlinkedFirst
end
end

section

open GlobalTheory.LocGL GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RoadU

namespace GlobalTheory.IwahoriSupport

theorem hasSupport_chars {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) k) V} (hi : ρ.IsIrreducible) (χ : Fin n → kˣ →* ℂˣ)
    (hχ : ∀ i, IsSmoothChar (χ i)) (h : GlobalTheory.SmGL.IsSubquotient ρ (prinSeries χ)) :
    HasSupport ρ (chars χ hχ) := by
  have H : GlobalTheory.SmGL.IsCuspSupport ρ (fun _ : Fin n => 1) fun a => detRep (Fin 1) (χ a) :=
    ⟨hi, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hχ a)⟩, _,
      h.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ)⟩
  exact hasSupport_of_isCuspSupport H

end GlobalTheory.IwahoriSupport
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU.PlainChars

theorem exists_fin_enum {S : Type*} (t : Multiset S) {n : ℕ} (hn : Multiset.card t = n) :
    ∃ ξ : Fin n → S, Finset.univ.val.map ξ = t := by
  subst hn
  refine ⟨fun j => t.toList.get (Fin.cast (by simp) j), ?_⟩
  rw [Fin.univ_val_map]
  conv_rhs => rw [← Multiset.coe_toList t]
  congr 1
  apply List.ext_get (by simp)
  intro i h1 h2
  simp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_eq_ofChar (x : IrrGL (k := k)) (hx : x.1 = 1) : ∃ θ hθ, x = IrrGL.ofChar θ hθ := by
  obtain ⟨n, c⟩ := x
  obtain rfl : n = 1 := hx
  obtain ⟨θ, hθ, ⟨e⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ c.rep.ρ c.rep.smooth c.rep.irr
  exact ⟨θ, hθ, congrArg (Sigma.mk 1) (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨e⟩))⟩

end GlobalTheory.RoadU.PlainChars

theorem GlobalTheory.RoadU.plainTor_exists_chars : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)), PlainTor x → ∃ (ξ : Fin x.1 → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport x.rep (chars ξ hξ) ∧ Unlinked (chars ξ hξ) := by
  intro k _ _ _ _ _ x ⟨s, hs, h1, hu⟩
  let S := {χ : kˣ →* ℂˣ // IsSmoothChar χ}
  let F : S → IrrGL (k := k) := fun χ => IrrGL.ofChar χ.1 χ.2
  obtain ⟨t, rfl⟩ : ∃ t : Multiset S, t.map F = s :=
    haveI : CanLift (IrrGL (k := k)) S F fun y => ∃ χ, F χ = y := ⟨fun _ hy => hy⟩
    (Multiset.canLift F (fun y => ∃ χ, F χ = y)).prf s fun y hy => by
      obtain ⟨χ, hχ, e⟩ := PlainChars.exists_eq_ofChar y (h1 y hy)
      exact ⟨⟨χ, hχ⟩, e.symm⟩
  have hcard : Multiset.card t = x.1 := by
    have h2 := hs.sum_fst
    rw [Multiset.map_map] at h2
    have h3 : t.map (Sigma.fst ∘ F) = Multiset.replicate (Multiset.card t) 1 :=
      Multiset.eq_replicate.2 ⟨by simp, fun b hb => by
        obtain ⟨χ, -, rfl⟩ := Multiset.mem_map.1 hb
        rfl⟩
    rw [h3, Multiset.sum_replicate, smul_eq_mul, mul_one, Fintype.card_fin] at h2
    exact h2
  obtain ⟨ξ, hξ⟩ := PlainChars.exists_fin_enum t hcard
  have hc : chars (fun j => (ξ j).1) (fun j => (ξ j).2) = t.map F := by
    rw [← hξ, Multiset.map_map]
    rfl
  exact ⟨fun j => (ξ j).1, fun j => (ξ j).2, hc ▸ hs, hc ▸ hu⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.RoadU


open UpperTheory.V.Af in
theorem frobEig_of_dec {E Ω : Type} [Field E] [NumberField E]
    [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (π : CuspSub E a) (Q : GlobalTheory.RealGal.QCM E Ω) (P : CuspSub ↥Q.K a) (r : _root_.Formalism.ConjugateSelfDual.G ↥Q.K Ω →* GL (Fin a) (Qbar l))
    (ρ : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ)
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (hdec : ∀ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → _root_.ReciprocityTheory.Gal.Dec (F := E) A ≤ (Bc.res E Ω ↥Q.K).range)
    (hsph : ∀ w' : HeightOneSpectrum (𝓞 ↥Q.K), w'.under (𝓞 E) = w → (CG.mk P).HasSat w' B → SphAt .unr P ι r w' B)
    (hP : IsLift π P) (hB : (CG.mk π).HasSat w B) (hiso : RepIso r (ρ.comp (Bc.res E Ω ↥Q.K)))
    (hunr : ∀ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → ∀ s ∈ Ine (F := E) A, ρ s = 1) :
    FrobEig ι ρ w (algSat a (normV w) B) := by
  intro A hA
  refine ⟨hunr A hA, fun σ hσ => ?_⟩
  obtain ⟨w', hw', hA', hq⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A hA (hdec A hA)
  obtain ⟨τ, rfl⟩ := hdec A hA hσ.1
  have hτ : IsFrob (F := ↥Q.K) A (normV w') τ := by
    rw [hq]
    exact ⟨hσ.1, hσ.2⟩
  have hl' : ((l : ℕ) : 𝓞 ↥Q.K) ∉ w'.asIdeal := by
    intro h
    apply hl
    rw [← hw']
    change ((l : ℕ) : 𝓞 E) ∈ Ideal.comap (algebraMap (𝓞 E) (𝓞 ↥Q.K)) w'.asIdeal
    simpa using h
  have hB' : (CG.mk P).HasSat w' B := by
    have := hP.sat w' 1 B (by rw [pow_one, hw', hq]) (by rw [hw']; exact hB)
    simpa using this
  have key := ((hsph w' hw' hB' hl') A hA').2 τ hτ
  obtain ⟨g, hg⟩ := hiso
  have e : ρ (Bc.res E Ω ↥Q.K τ)⁻¹ = g * r τ⁻¹ * g⁻¹ := by
    rw [← map_inv]
    exact hg τ⁻¹
  rw [e, ← hq, ← key, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mul]


end GlobalTheory.RoadU
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU.CharTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hasSupport_rep_tw {x : IrrGL (k := k)} {s : Multiset (IrrGL (k := k))} (hx : HasSupport x.rep s) (χ : kˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) : HasSupport (x.tw χ hχ).rep (s.map (·.tw χ hχ)) :=
  (hx.tw χ hχ).of_equiv (x.twEquiv χ hχ)

theorem chars_tw {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (chars ξ hξ).map (·.tw χ hχ) = chars (fun j => ξ j * χ) fun j => (hξ j).mul hχ := by
  simp only [chars, Multiset.map_map, Function.comp_def, IrrGL.tw_ofChar]

end GlobalTheory.RoadU.CharTwist
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

theorem _root_.GlobalTheory.T.infinite_quadraticCM_goodBaseChange_split : AutomorphicFormsFiniteGL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ) (π : CuspSub E a) (w₀ : HeightOneSpectrum (𝓞 E)), {Q : GlobalTheory.RealGal.QCM E Ω | (∀ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w₀ → _root_.ReciprocityTheory.Gal.Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range) ∧ (∀ w : HeightOneSpectrum (𝓞 ↥Q.K), w.under (𝓞 E) = w₀ → GlobalTheory.UnitaryBC.IsSplitAt w) ∧ (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) ∧ ∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P}.Infinite := by
  first | exact @GlobalTheory.GalCut.infinite_qcm_split_good | exact GlobalTheory.GalCut.infinite_qcm_split_good | (intros; apply GlobalTheory.GalCut.infinite_qcm_split_good <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters

theorem _root_.GlobalTheory.T.exists_periodProduct_eq_of_invertible_character : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V) (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1) (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) (y : ↥(Dpst P ρm)) (y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P), GlobalTheory.Pst.TwistLetters.mulB (L := L) P (Fin 1 → ↥L.1) y' (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) → ∀ z : ↥(Dpst P ρt), ∃ x : ↥(Dpst P ρs), GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht x y = z := by
  first | exact @GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv | exact GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv | (intros; apply GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv <;> assumption)
end
