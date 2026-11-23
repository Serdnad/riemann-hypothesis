module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle815
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle701
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle920
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle687
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle241
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle272
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle620
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle616
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle652
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle651
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesEqThetaLiftDefiniteGroupForm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodSetupCountEqZeroOffBadPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle913
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle918
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

namespace GlobalTheory.AdjUp



theorem adjFormula_holds : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, AdjFormula R i t := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t th hth v hv n b
  refine (GlobalTheory.T.petersson_integral_formula hP D G Pl0 T A Ks R F hL i v hv).elim fun P hPx => ?_
  refine (GlobalTheory.T.inner_product_integral_formula D G Pl0 T A Ks R F hL i t).elim fun c hcx => ?_
  have hval : ∀ u, val R i v (th u) = R.thF i t u (fun ρ => v ρ) := fun u => by
    show (R.HW i (sg0 D A)).e (th u) (fun ρ => v ρ) = _
    rw [hth u]
  have hK0 : ∀ k h, upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v 0) h = 0 := fun k h => by
    rw [val_zero]; exact upLift_zero _ _ _ _ h
  exact adjoint_formula_of_kernel th b ((R.νW i).restrict (R.fdW i)) ((R.νV i t).restrict (R.fdV i t)) (val R i v)
    (fun u => R.thF i t u (fun ρ => v ρ)) (R.extV i t)
    (fun k y h => upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h) P c hPx.1 hcx.1 hPx.2
    hval (val_zero R i v) hK0 hcx.2 (fun y u => GlobalTheory.T.adjoint_pairing_unfolding_downward_lift hP D G Pl0 T A Ks R F hL hF i t v n b y u)
    (fun y => GlobalTheory.T.upwardVectorLift_mem_range_coefficientExtension hP D G Pl0 T A Ks R F hL hF i t v n b y)

end GlobalTheory.AdjUp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.GoodLift

theorem sum_translates {H X W ι : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] [Mul X] [Fintype ι]
    (E : H →ₗ[ℂ] (X → W)) (y : H) (yg : ι → H) (a c : ι → ℂ) (κ : ι → X)
    (hext : ∀ g h, E (yg g) h = (c g)⁻¹ • E y (h * κ g))
    (hy : ∀ (l : W →ₗ[ℂ] ℂ) h, ∑ g, a g * ((c g)⁻¹ * l (E y (h * κ g))) = l (E y h)) :
    E (∑ g, a g • yg g) = E y := by
  funext h
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_)

  rw [map_sub, sub_eq_zero, ← hy l h, map_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, Pi.smul_apply, map_smul, hext g h, map_smul, smul_eq_mul, smul_eq_mul]

theorem gaL_apply_choose {D : D7} {G : Type} [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (hk : ∀ g, ∃ κ, IsLevelLift V β L (eG g) κ)
    (F : GA D V → ℂ) (h : GA D V) :
    gaL V β L eG c F h = ∑ g, c g * ((levChi V β (flagL L) (hk g).choose)⁻¹ * F (h * (hk g).choose)) := by
  unfold gaL
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  show c g * actG0 V β L (eG g) F h = _
  unfold actG0
  rw [dite_eq_left (hk g)]

end GlobalTheory.GoodLift

namespace GlobalTheory.GoodLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)



theorem liftsW_of_core (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) : LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
  obtain ⟨c, hc⟩ := hR.lev.βW i
  exact GlobalTheory.T.finite_group_lifts_to_parahoric_level _ _ _ _ _ hc rfl (GlobalTheory.T.typePlaces_not_pairwise_conjugate R.C.P R.Pg hR.lev.Pg)



theorem liftsV_of_core (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (g : G) :
    ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ := by
  obtain ⟨q, hq⟩ := (R.B.L i t).act_tie.red_surj g
  have h1 := hR.grp.red_L i t q
  obtain ⟨⟨_, h, rfl⟩, hq2⟩ := q
  obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (Vc D i)).1 h
  have e : finHom (Vc D i) (a * k) = finHom (Vc D i) k := by
    rw [map_mul, show finHom (Vc D i) a = 1 from ha, one_mul]
  refine ⟨k, hk, ?_, ?_⟩
  · rw [finE_eq, ← e]; exact hq2.1
  · rw [finE_eq, ← e, ← hq]; exact h1.symm



theorem translate_of_core (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) (κ : GA D (Vc D i))
    (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ) (y : (R.HV i t).H) :
    ∃ y' : (R.HV i t).H, (∀ h, (R.HV i t).e y' h = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ •
        (R.HV i t).e y (h * (finHom (Vc D i)).rangeRestrict κ)) ∧
      ∀ h, R.extV i t y' h = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ) := by
  obtain ⟨y', hy', -⟩ := GlobalTheory.RowClassSum.exists_translate (Vc D i) (R.βV i) (R.datVt i t) (R.cV i) (hR.models.cV i)
    (R.HV i t) _ (R.B.L i t).pres.reps (hR.models.HV i t) g0 κ hκ y
  have hc0 : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ ≠ 0 := levChi_ne_zero _ _
  refine ⟨y', hy', fun h => ?_⟩
  have e := GlobalTheory.ThetaProjEquiv.extV_shift R hR.models.cV i t κ hκ.1 _ hc0 y y' hy' h
  rw [LinearMap.map_smul, Pi.smul_apply] at e
  rw [← e, smul_smul, inv_mul_cancel₀ hc0, one_smul]



theorem thF_translate_low (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (g : G) (κ : GA D (Vc D i))
    (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ) (y y' : (R.HV i t).H)
    (hy : ∀ h, (R.HV i t).e y' h = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ •
        (R.HV i t).e y (h * (finHom (Vc D i)).rangeRestrict κ))
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    R.thF i t y' (fun ρ => v ρ) = actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (R.thF i t y (fun ρ => v ρ)) := by
  obtain ⟨κ', hκ'⟩ := liftsW_of_core R F hR i (R.eG g)
  funext x
  exact (GlobalTheory.ThetaProjEquiv.thF_shift_core R F hR i t (R.eG g) κ κ' hκ hκ'.1 y y' _ (levChi_ne_zero _ _)
    (GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hR.lev hR.models.inf hR.thP.ωP hR.thP.vP i t (R.eG g) κ κ' hκ hκ') hy v x).trans
    (GlobalTheory.ThetaProjEquiv.finiteGroup_acts_by_lift_translation_principalType R i (R.eG g) κ' hκ' _ (GlobalTheory.ThetaProjEquiv.thF_type R hR.thP.thF_mem i t y _) x).symm



theorem thF_low_eq (hP : R.IsThP) (i : Fin D.R.m) (t : T) (y z : (R.HV i t).H) (hz : R.extV i t z = R.extV i t y)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) : R.thF i t z (fun ρ => v ρ) = R.thF i t y (fun ρ => v ρ) := by
  obtain ⟨thP, hthP, hthF⟩ := hP.thF i t
  funext w
  refine ((congrFun (hthF _ v) w).trans (hthP.eq _ (PiTensorProduct.tprod ℂ v) w)).trans ?_
  refine Eq.trans ?_ ((congrFun (hthF y v) w).trans (hthP.eq _ (PiTensorProduct.tprod ℂ v) w)).symm
  have e1 : (((R.extV i t).rangeRestrict z : LinearMap.range (R.extV i t)) : GA D (Vc D i) → (R.cV i).W) =
      R.extV i t y := hz
  have e2 : (((R.extV i t).rangeRestrict y : LinearMap.range (R.extV i t)) : GA D (Vc D i) → (R.cV i).W) =
      R.extV i t y := rfl
  unfold Formalism.IndefR.Lift.thetaPInt
  rw [e1, e2]



theorem eWf_apply_sum (i : Fin D.R.m) (f : GA D (Wc D i) → ℂ) :
    R.eWf i (sg0 D A) f = ∑ g, RealDat.eC (A := A) (sg0 D A) g • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) f := by
  unfold RealDat.eWf gaL
  rw [LinearMap.sum_apply]
  rfl

end GlobalTheory.GoodLift

namespace GlobalTheory.GoodLift



theorem goodMem_of_given : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GoodMem R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t y hy
  have hR := hG.core
  have hLV := liftsV_of_core R F hR i t
  choose yg hyg hext using fun g : G => translate_of_core R F hR i t (R.eG g) _ (hLV g).choose_spec y
  have hz : R.extV i t (∑ g, RealDat.eC (A := A) (sg0 D A) g • yg g) = R.extV i t y :=
    sum_translates (R.extV i t) y yg _ _ (fun g => (hLV g).choose) hext
      (fun l h => (gaL_apply_choose (Vc D i) (R.βV i) (R.datVt i t) R.eG _ hLV _ h).symm.trans (congrFun (hy l) h))
  have hmem : (R.HW i (sg0 D A)).e (R.thG i t y) ∈ R.Wall i (sg0 D A) := by
    rw [← (hR.models.HW i (sg0 D A)).2.1]; exact ⟨_, rfl⟩
  refine sub_eq_zero.1 (GlobalTheory.LiftRows.spanP_of_given R F hG i _ (Submodule.sub_mem _ hmem (hR.thP.thF_mem i t y))
    fun v => ?_)
  refine sub_eq_zero.2 ?_
  rw [hR.thP.thG i t y]
  show R.eWf i (sg0 D A) (R.thF i t y (fun ρ => v ρ)) = _
  rw [eWf_apply_sum R i]
  calc ∑ g, RealDat.eC (A := A) (sg0 D A) g •
        actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (R.thF i t y (fun ρ => v ρ))
      = ∑ g, RealDat.eC (A := A) (sg0 D A) g • R.thF i t (yg g) (fun ρ => v ρ) :=
        Finset.sum_congr rfl fun g _ => by
          rw [thF_translate_low R F hR i t g _ (hLV g).choose_spec y (yg g) (hyg g) v]
    _ = R.thF i t (∑ g, RealDat.eC (A := A) (sg0 D A) g • yg g) (fun ρ => v ρ) := by

        rw [map_sum, MultilinearMap.sum_apply]
        simp only [map_smul, MultilinearMap.smul_apply]
    _ = R.thF i t y (fun ρ => v ρ) := thF_low_eq R hR.thP i t y _ hz v

end GlobalTheory.GoodLift
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.ConjTwist

def IsTraceFn {H Γ W : Type} [Group H] [Group Γ] [AddCommGroup W] [Module ℂ W] (ι : Γ →* H)
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup H) (χ : J →* ℂˣ) (z₀ : H) (w : W) (f : H → W) : Prop :=
  (∀ z, (¬ ∃ (γ : Γ) (k : J), z = ι γ * z₀ * k) → f z = 0) ∧
    ∀ L : W →ₗ[ℂ] ℂ, (∀ (γ : Γ) (hγ : z₀⁻¹ * ι γ * z₀ ∈ J), L ((χ ⟨_, hγ⟩ : ℂ) • ρ γ⁻¹ w) = L w) →
      L (f z₀) = (Nat.card (Bridge.stab ι J z₀) : ℂ) * L w

theorem IsTraceFn.post {H Γ W : Type} [Group H] [Group Γ] [AddCommGroup W] [Module ℂ W] (ι : Γ →* H)
    (ρ : Γ →* Module.End ℂ W) {J J' : Subgroup H} (hJ : J' = J) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (τ : ℂ ≃+* ℂ) (T : W →+ W)
    (hs : ∀ (a : ℂ) w, T (a • w) = τ a • T w) (hρ : ∀ γ w, T (ρ γ w) = ρ γ (T w))
    (hχ : ∀ k (hk : k ∈ J) (hk' : k ∈ J'), ((χ' ⟨k, hk'⟩ : ℂˣ) : ℂ) = τ ((χ ⟨k, hk⟩ : ℂˣ) : ℂ))
    {z₀ : H} {w : W} {f : H → W} (hf : IsTraceFn ι ρ J χ z₀ w f) :
    IsTraceFn ι ρ J' χ' z₀ (T w) (fun g => T (f g)) := by
  subst hJ
  refine ⟨fun z hz => ?_, fun L hL => ?_⟩
  · show T (f z) = 0
    rw [hf.1 z hz, map_zero]
  · let L' : W →ₗ[ℂ] ℂ :=
      { toFun := fun v => τ.symm (L (T v))
        map_add' := fun a b => by rw [map_add (f := _), map_add (f := _), map_add (f := _)]
        map_smul' := fun a v => by
          rw [hs, map_smul, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
          rfl }
    have hL' : ∀ v, L' v = τ.symm (L (T v)) := fun v => rfl
    have key := hf.2 L' fun γ hγ => by
      rw [hL', hL', hs, hρ, ← hχ _ hγ hγ, hL γ hγ]
    rw [hL', hL'] at key
    have := congrArg τ key
    rwa [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, map_natCast] at this

theorem IsTraceFn.sum_eq {H Hf W : Type} [Group H] [Group Hf] [AddCommGroup W] [Module ℂ W] (p : H →* Hf)
    (hp : Function.Surjective p) (Γ F R : Subgroup H) (ρ : H →* Module.End ℂ W) (J : Subgroup Hf) (χ : J →* ℂˣ)
    (hdec : ∀ u : H, ∃ k ∈ F, ∃ a ∈ R, u = k * a ∧ p k = p u) (hρ : ∀ k ∈ F, ρ k = 1)
    (Cl : Type) [Fintype Cl] (y : Cl → Hf) (hy : Bridge.IsReps (p.comp Γ.subtype) J y)
    (hfin : ∀ k, Finite (Bridge.stab (p.comp Γ.subtype) J (y k))) (h₀ : H) (hh₀ : h₀ ∈ F) (v : W) (f : Hf → W)
    (hf : IsTraceFn (p.comp Γ.subtype) (ρ.comp Γ.subtype) J χ (p h₀) v f) :
    ∃ r : Cl → H, (∀ k, r k ∈ F) ∧
      Bridge.IsReps (p.comp Γ.subtype) J (fun k => p (r k)) ∧
      ∀ {G' X : Type} [Group G'] (x₀ : X) (om : H × G' →* Module.End ℂ (X → ℂ)) (Λ : W →ₗ[ℂ] (X → ℂ)),
        (∀ γ ∈ Γ, ∀ z v, om (γ, 1) (om z (Λ v)) x₀ = om z (Λ v) x₀) → (∀ a ∈ R, ∀ v, om (a, 1) (Λ v) = Λ (ρ a v)) →
        (∀ k ∈ F, ∀ hk : p k ∈ J, ∀ v, om (k, 1) (Λ v) = ((χ ⟨p k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ v) →
        ∀ g : G', ∑ k, ((J.relIndex J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab (p.comp Γ.subtype) J (p (r k))) : ℕ) : ℂ)⁻¹ *
          om (r k, g) (Λ (f (p (r k)))) x₀ = om (h₀, g) (Λ v) x₀ := by
  obtain ⟨y', c₀, hy', e₀⟩ := GlobalTheory.TraceLift.exists_isReps_through _ _ hy (p h₀)
  have hlift : ∀ z : Hf, ∃ k ∈ F, p k = z := fun z => by
    obtain ⟨u, hu⟩ := hp z
    obtain ⟨k, hk, -, -, -, e⟩ := hdec u
    exact ⟨k, hk, e.trans hu⟩
  choose σ hσ hσ' using hlift
  let r : Cl → H := Function.update (fun k => σ (y' k)) c₀ h₀
  have hr : ∀ k, r k ∈ F ∧ p (r k) = y' k := fun k => by
    by_cases hk : k = c₀
    · subst hk
      simp only [r, Function.update_self]
      exact ⟨hh₀, e₀.symm⟩
    · simp only [r, Function.update_of_ne hk]
      exact ⟨hσ _, hσ' _⟩
  have hr0 : r c₀ = h₀ := Function.update_self _ _ _
  have hyr : (fun k => p (r k)) = y' := funext fun k => (hr k).2
  have hf0 := GlobalTheory.TraceLift.finite_stab _ _ hy hfin (p h₀)
  obtain ⟨hz, hv⟩ := hf
  refine ⟨r, fun k => (hr k).1, by rw [hyr]; exact hy', fun {G' X} _ x₀ om Λ hom hΛa hΛk g => ?_⟩
  rw [Finset.sum_eq_single c₀ ?_ (fun h => absurd (Finset.mem_univ _) h)]
  · let L₀ : W →ₗ[ℂ] ℂ := (LinearMap.proj x₀ : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (om (h₀, g)) ∘ₗ Λ
    have hL₀ : ∀ v, L₀ v = om (h₀, g) (Λ v) x₀ := fun v => rfl
    have key := hv L₀ fun γ hγ => ?_
    · have hN : ((Nat.card (Bridge.stab (p.comp Γ.subtype) J (p h₀)) : ℕ) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.2 (Nat.card_pos).ne'
      rw [hr0, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_mul, ← hL₀, key, inv_mul_cancel_left₀ hN, hL₀]
    · obtain ⟨k, hk, b, hb, e, e'⟩ := hdec ((γ : H)⁻¹ * h₀)
      have hκ : h₀⁻¹ * k ∈ F := mul_mem (inv_mem hh₀) hk
      have eκ : p (h₀⁻¹ * k) = ((p h₀)⁻¹ * (p.comp Γ.subtype) γ * p h₀)⁻¹ := by
        show p (h₀⁻¹ * k) = ((p h₀)⁻¹ * p γ * p h₀)⁻¹
        rw [map_mul, e', map_mul, map_inv, map_inv]
        group
      have hκ' : p (h₀⁻¹ * k) ∈ J := by rw [eκ]; exact inv_mem hγ
      have eχ : ((χ ⟨_, hκ'⟩ : ℂˣ) : ℂ)⁻¹ = χ ⟨_, hγ⟩ := by
        rw [show (⟨_, hκ'⟩ : J) = ⟨_, hγ⟩⁻¹ from Subtype.ext eκ, map_inv, Units.val_inv_eq_inv_val, inv_inv]
      have eρ : (ρ.comp Γ.subtype) γ⁻¹ v = ρ b v := by
        have h1 := congrArg ρ e
        rw [map_mul, map_mul, hρ _ hh₀, hρ _ hk, mul_one, one_mul] at h1
        rw [← h1]
        rfl
      have e3 : ((h₀, g) : H × G') * (h₀⁻¹ * k, 1) * (b, 1) = (((γ : H)⁻¹, 1) : H × G') * (h₀, g) := by
        rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_inv_cancel_left, e, mul_one, mul_one, one_mul]
      rw [hL₀, hL₀, map_smul, eρ, ← eχ, ← hΛk _ hκ hκ', ← hΛa b hb, ← Module.End.mul_apply, ← Module.End.mul_apply,
        ← map_mul, ← map_mul, e3, map_mul]
      exact hom _ (inv_mem γ.2) _ _
  · intro k _ hk
    rw [hz _ ?_, map_zero, map_zero]
    · simp
    · intro hex
      obtain ⟨j, -, hu⟩ := hy' (y' k)
      refine hk ((hu k ⟨1, 1, by simp⟩).trans (hu c₀ ?_).symm)
      show ∃ (γ : Γ) (m : J), y' k = (p.comp Γ.subtype) γ * y' c₀ * m
      rw [e₀, ← (hr k).2]
      exact hex



theorem thF_eq_ser_of_isTraceFn {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (hV : VStd D i) (t : T0) (h : GA D (Vc D i)) (hh : h ∈ GfC (Vc D i))
    (w : (R.cV i).W) (x : (R.HV i t).H)
    (hx : IsTraceFn (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ (Formalism.IndefR.FWT.fin (Vc D i) h) w ((R.HV i t).e x))
    (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    R.thF i t x (fun ρ => u ρ) g = ser R i t (R.vP i t) u h w g := by
  refine (hR.thP.thF i t).elim fun thP hPF => ?_
  refine (IsTraceFn.sum_eq (finHom (Vc D i)).rangeRestrict (finHom (Vc D i)).rangeRestrict_surjective (GQ (Vc D i))
    (GfC (Vc D i)) (GinfC (Vc D i)) (R.cV i).ρ (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ
    (GlobalTheory.LiftUnfold.exists_fin_mul_real (Vc D i)) (hR.models.cV i).1 _ (R.B.L i t).pres.y (R.B.L i t).pres.reps
    (fun c => Finite.of_equiv _ ((R.B.L i t).pres.stabI c).toEquiv) h hh w ((R.HV i t).e x) hx).elim fun r hr => ?_
  have hf : (R.HV i t).e x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hR.models.HV i t).2.1.le (LinearMap.mem_range_self _ x)
  have hfin : ∀ k ∈ GfC (Vc D i), ∀ hk : Formalism.IndefR.FWT.fin (Vc D i) k ∈ levJ R i t, ∀ P, R.ωP i t (k, 1) (R.ptP i t P) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨Formalism.IndefR.FWT.fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.ptP i t P := fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hR.models.inf
      (hR.thP.ωP i t) _ _ _ _ _ (hR.thP.pt_theta i t) k hk 1 (one_mem _) _
      (GlobalTheory.AdTh.LevelLawCore.omega_level_vP_core D G Pl0 T0 A Ks R F hR i t k hV hk hk')
  have key := GlobalTheory.LiftUnfold.integral_theta (hR.thP.ωP i t) (D.sp.V_sig _) (hR.models.vpos i) (R.cV i) (hR.models.cV i) (R.βV i)
    (R.datVt i t) (fun _ => Iff.rfl) hf
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u)) (fun w => hR.thP.pt_theta i t _)
    (fun a ha w => (hR.thP.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hR.models.νV i t) _ _ r le_rfl (by rw [Subgroup.relIndex_self]; exact one_ne_zero) hr.2.1 hr.1 g
  have key2 := hr.2.2 (0 : WO (Vc D i) (Wc D i)) (R.ωP i t)
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u))
    (fun γ hγ z v => (hR.thP.ωP i t).om_aut γ hγ 1 (one_mem _) _ ((hR.thP.ωP i t).om_pres _ _ (hR.thP.pt_theta i t _)))
    (fun a ha w => (hR.thP.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _) g
  have h1 := congrFun (hPF.2 x u) g
  have h2 := hPF.1.eq ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ u) g
  refine h1.trans (h2.trans (Eq.trans ?_ (key.trans key2)))
  rfl



theorem exists_conjForm_thF_eq_ser : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), FixBase T R i τ → ConjTup R τ t t' → ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ∃ (y : (R.HV i t).H) (y' : (R.HV i t').H), ConjForm R i τ c t t' y y' ∧ ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)), R.thF i t y (fun ρ => u ρ) g = ser R i t (R.vP i t) u h (c x) g ∧ R.thF i t' y' (fun ρ => u ρ) g = ser R i t' (R.vP i t') u h (c x') g := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hCore hFW i Tp tup M hPins c hc τ t t' hFix hConj h hh x x' hxx
  have hX := GlobalTheory.CoefExtC.exists_extC_bijective_unique D G Pl0 T0 A T R F κ v₀ hCore hFW i Tp tup M hPins
  refine hX.elim fun c₁ hc₁ => ?_
  have hb : Function.Bijective c :=
    (congrArg (fun f : VsV D i ℂ →ₗ[ℂ] (R.cV i).W => Function.Bijective f) (hc₁.2.2 c hc)).mpr hc₁.2.1
  refine (exists_conjW M hPins c hc hb τ hFix.host).elim fun TW hTW => ?_
  have hs := hTW.1
  have hTc := hTW.2.1
  have hρ := hTW.2.2
  have hZ := (GlobalTheory.T.conjugate_tuples_conjugate_residue_levels D G Pl0 T0 A T R F κ v₀ hCore τ t t' hConj).2.2.2 i hFix
  have hJ := hZ.1
  have hχ := hZ.2
  have hV := hCore.models.HV i t
  have hV' := hCore.models.HV i t'
  have hfin := GlobalTheory.TraceLift.finite_stab (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.reps
    (fun k => Finite.of_equiv _ ((R.B.L i t).pres.stabI k).toEquiv) (Formalism.IndefR.FWT.fin (Vc D i) h)
  refine (GlobalTheory.TraceLift.exists_traceForm (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
    (levEnv _ (R.βV i) (R.datVt i t)).χ (Formalism.IndefR.FWT.fin (Vc D i) h) hfin (c x)).elim fun f hf => ?_
  have hf1 : IsTraceFn (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ (Formalism.IndefR.FWT.fin (Vc D i) h) (c x) f := hf.2
  have hf2 := IsTraceFn.post (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ hJ _ _ τ TW.toAddMonoidHom hs hρ hχ hf1
  have hm2 := post_mem (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ hJ _ _ τ TW.toAddMonoidHom hs hρ hχ hf.1
  refine (LinearMap.mem_range.1 (hV.2.1.ge hf.1)).elim fun y hy => ?_
  refine (LinearMap.mem_range.1 (hV'.2.1.ge hm2)).elim fun y' hy' => ?_
  have hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x :=
    Subtype.ext (hxx.trans (GlobalTheory.CoefModel.mapVV_coe _ _ _).symm)
  have hcx : TW.toAddMonoidHom (c x) = c x' := (hTc x).trans (congrArg c hx').symm
  refine ⟨y, y', fun k => ?_, fun u g => ⟨?_, ?_⟩⟩
  · refine (hb.2 (f (Formalism.IndefR.FWT.fin (Vc D i) k))).elim fun z hz => ?_
    refine ⟨z, GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) z, GlobalTheory.CoefModel.mapVV_coe _ _ _,
      (congrFun hy _).trans hz.symm, (congrFun hy' _).trans ?_⟩
    exact (congrArg TW hz.symm).trans (hTc z)
  · refine thF_eq_ser_of_isTraceFn R F hCore i hPins.lift.std t h hh (c x) y ?_ u g
    rw [hy]
    exact hf1
  · refine thF_eq_ser_of_isTraceFn R F hCore i hPins.lift.std t' h hh (c x') y' ?_ u g
    rw [hy', ← hcx]
    exact hf2

end GlobalTheory.ConjTwist
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlaces_translation_lattice_bounded_norm : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (Q : Finset (Pl D.host.E)) (h hQ : GA D (Vc D j)), SplitSet Q → SuppAt (idem Q) (Vc D j) hQ → ∃ c : ℕ, (∀ x ∈ (ρ.B i j b).latAt (finPt (Vc D j) h), ((normProd Q ^ c : ℕ) : 𝓞 D.host.E) • x ∈ (ρ.B i j b).latAt (finPt (Vc D j) (h * hQ))) ∧ ∀ x ∈ (ρ.B i j b).latAt (finPt (Vc D j) (h * hQ)), ((normProd Q ^ c : ℕ) : 𝓞 D.host.E) • x ∈ (ρ.B i j b).latAt (finPt (Vc D j) h) := by
  first | exact @GlobalTheory.LatCmpQ.latAt_translate_bounded | exact GlobalTheory.LatCmpQ.latAt_translate_bounded | (intros; apply GlobalTheory.LatCmpQ.latAt_translate_bounded <;> assumption)
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


theorem _root_.GlobalTheory.T.weilRep_real_point_fockVector_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ →
    ∀ (p : ℕ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) p) →
    ∀ a ∈ GinfC V, ∀ u : GlobalTheory.ExportSeries.GLR D V.rank,
    (∀ τ, ((u τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a)) →
    ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (sW τ)) f) →
    ∀ P : MvPolynomial (FVar D W.rank V.rank) ℂ,
      om (a, 1) (stdF ψ θ V W sW BW f P) =
        stdF ψ θ V W sW BW (om (a, 1) f) (GlobalTheory.ExportSeries.fockSubst (fun _ => p) u P) := by
  first | exact @GlobalTheory.RealFockVac.om_stdF_subst | exact GlobalTheory.RealFockVac.om_stdF_subst | (intros; apply GlobalTheory.RealFockVac.om_stdF_subst <;> assumption)
end
