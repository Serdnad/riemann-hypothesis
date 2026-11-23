module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2997
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle208
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle066
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle207
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle209
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle202
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle204
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2931
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2984
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3272
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2856
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3379
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalInjectionsAgreeCanonicalFamilyCoordinates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.QUnit

theorem FF_mem {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : S.J × (T → ZMod ((S.r * S.N) ^ 2))) : S.FF T c k ∈ S.R := by
  unfold ThetaSys.FF
  refine finsum_induction (fun v => v ∈ S.R) (zero_mem _) (fun _ _ => add_mem) fun t => ?_
  exact mul_mem (Subalgebra.algebraMap_mem _ _) (sum_mem fun i _ => mul_mem (Subalgebra.algebraMap_mem _ _) (S.ev_mem _ _))

theorem main : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ α₀ : D.toPre.X, ∃ mu : D.toPre.X, CongMod S.N mu α₀ ∧ (∀ α, CongMod S.N α α₀ → ∀ r s, PsiCoord D.toPre mu r → PsiCoord D.toPre α s → r ∣ s) ∧ ∃ (e : Ω) (a : M.Z.presheaf.stalk x), e ≠ 0 ∧ (∃ (T₀ : AddSubgroup S.Gam) (c' : T₀ →+ ZMod S.N) (κ : S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) (x₀ : S.Gam), S.IsoFree T₀ ∧ e = S.FF T₀ c' κ / S.th x₀) ∧ M.stalkHom x a = e ^ S.N ∧ ∀ r, PsiCoord D.toPre mu r → Associated (j a) r := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hB hj G _ _ gm hpb D A U hLB hPsi α₀
  obtain ⟨hiso, hc⟩ := GlobalTheory.T.thetaConstant_fourierParts_bounded_classMinima o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hB hj G gm hpb D A U hLB hPsi
  obtain ⟨c', hc'⟩ := hc α₀
  have hO := hAdm.1
  obtain ⟨x₀, hx₀⟩ := hO.div x
  have hRU : ∀ v ∈ S.R, v ∈ M.ringOn (U₀ : Set M.Z) := fun v hv => hO.le hv
  have hext : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ x y →
      ∃ ev : R →+* OO p, IsLocalHom ev ∧ spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y := by
    intro p _ y hy
    obtain ⟨V, _, _, _, ev₀, i, -, hl₀, hli, -, hev, -⟩ := GlobalTheory.ClassicalPt.extend_completion o' Ω M x R j hj p y hy.1
    haveI := hl₀
    haveI := hli
    exact ⟨i.comp ev₀, RingHom.isLocalHom_comp _ _, hev⟩
  obtain ⟨p₁, hp₁, y₁, hy₁⟩ := GlobalTheory.Poinc.exists_cen_main o' Ω M x hx U₀ hO.ne
  obtain ⟨ev₁, hl₁, hev₁⟩ := hext p₁ y₁ hy₁
  have hN0 : S.N ≠ 0 := by have := S.N_ge; omega
  have hFFne : S.FF (S.TT M x) c' ≠ 0 := by
    intro h0
    obtain ⟨hlow, κ₂, hup⟩ := hc' p₁ y₁ ev₁ hy₁ hev₁ x₀ hx₀
    obtain ⟨α, s, hα, hs, -⟩ := hlow κ₂
    have h1 := hup α s hα hs
    rw [show S.FF (S.TT M x) c' κ₂ = 0 from congrFun h0 κ₂, zero_div, RatModel.val_zero, norm_zero,
      zero_pow hN0] at h1
    exact GlobalTheory.T.thetaTrivialisation_coordinate_ne_zero_classical o' Ω S ρ M U₀ EE FinalForm hO x R j D hPsi p₁ y₁ ev₁ hy₁ hev₁ α s hs (norm_le_zero_iff.1 h1)
  obtain ⟨κ₁, hκ₁⟩ := hAdm.2 (S.TT M x) c' hiso hFFne x
  have he0 : S.FF (S.TT M x) c' κ₁ / S.th x₀ ≠ 0 := div_ne_zero hκ₁.1 hx₀.1
  have heU : S.FF (S.TT M x) c' κ₁ / S.th x₀ ∈ M.ringOn (U₀ : Set M.Z) := by
    rw [div_eq_mul_inv]
    exact mul_mem (hRU _ (FF_mem S (S.TT M x) c' κ₁)) (hO.th_unit x₀ hx₀.1)
  have heU' : (S.FF (S.TT M x) c' κ₁ / S.th x₀)⁻¹ ∈ M.ringOn (U₀ : Set M.Z) := by
    rw [inv_div, div_eq_mul_inv]
    exact mul_mem (hRU _ (S.th_mem x₀)) (hO.FF_unit (S.TT M x) c' κ₁ hiso hκ₁.1)
  have hpt : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y →
      spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y →
      0 < ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ ∧
      ‖M.val (gPt p ≫ y) ((S.FF (S.TT M x) c' κ₁ / S.th x₀) ^ S.N)‖ = ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ ^ S.N ∧
      (∀ α s, CongMod S.N α α₀ → PsiCoord D.toPre α s →
        ‖(ev s : PadicAlgCl p)‖ ≤ ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ ^ S.N) ∧
      ∃ mu s, CongMod S.N mu α₀ ∧ PsiCoord D.toPre mu s ∧
        ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ ^ S.N ≤ ‖(ev s : PadicAlgCl p)‖ := by
    intro p _ y ev hy hev
    have hrange : Set.range (gPt p ≫ y) = {(gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))} :=
      RatModel.range_eq_singleton _ _
    have hsp := RatModel.specializes_of_range_eq hrange
    have hz'U : (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ (U₀ : Set M.Z) := hy.2 ⟨_, rfl⟩
    have hz'x := RatModel.gPt_specializes hy.1 (IsLocalRing.closedPoint (PadicAlgCl p))
    have heO := RatModel.ringOn_le_O hz'U heU
    have heO' := RatModel.ringOn_le_O hz'U heU'
    have hpos : 0 < ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ :=
      norm_pos_iff.2 ((RatModel.val_ne_zero_iff hrange ⟨_, heO⟩).2 ((RatModel.isUnit_O_iff _).2 ⟨he0, heO'⟩))
    have hpow : ‖M.val (gPt p ≫ y) ((S.FF (S.TT M x) c' κ₁ / S.th x₀) ^ S.N)‖ =
        ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ ^ S.N := by
      have := map_pow (RatModel.valHomOf (gPt p ≫ y) _ hsp) ⟨_, heO⟩ S.N
      rw [RatModel.valHomOf_apply, RatModel.valHomOf_apply] at this
      rw [← norm_pow, ← this]
      rfl
    have hle : ∀ κ, ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ≤
        ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ := by
      intro κ
      have hq : S.FF (S.TT M x) c' κ / S.FF (S.TT M x) c' κ₁ ∈ M.O x := hκ₁.2 κ
      have hq' := RatModel.O_le_of_specializes hz'x hq
      have eq : S.FF (S.TT M x) c' κ / S.th x₀ =
          (S.FF (S.TT M x) c' κ / S.FF (S.TT M x) c' κ₁) * (S.FF (S.TT M x) c' κ₁ / S.th x₀) := by
        have := hκ₁.1
        have := hx₀.1
        field_simp
      rw [eq, RatModel.val_mul hsp hq' heO, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one hy.1 hq)
    obtain ⟨hlow, κ₂, hup⟩ := hc' p y ev hy hev x₀ hx₀
    refine ⟨hpos, hpow, fun α s hα hs => (hup α s hα hs).trans (pow_le_pow_left₀ (norm_nonneg _) (hle κ₂) _), ?_⟩
    exact hlow κ₁
  have hmem : (S.FF (S.TT M x) c' κ₁ / S.th x₀) ^ S.N ∈ M.O x := by
    refine GlobalTheory.T.mem_stalk_of_classicalValues_norm_le_one o' Ω M hO.normal U₀ hO.ne x hx _ (pow_mem heU _) fun p _ y hy => ?_
    obtain ⟨ev, -, hev⟩ := hext p y hy
    obtain ⟨-, hpow, -, mu, s, -, -, h⟩ := hpt p y ev hy hev
    rw [hpow]
    exact h.trans ((mem_OO_iff _).1 (ev s).2)
  have hstalk : M.stalkHom x ((M.stalkEquiv x).symm ⟨_, hmem⟩) = (S.FF (S.TT M x) c' κ₁ / S.th x₀) ^ S.N := by
    rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
  have ha0 : (M.stalkEquiv x).symm ⟨_, hmem⟩ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hstalk
    exact pow_ne_zero _ he0 hstalk.symm
  have hva : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y →
      spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y →
      ((ev (j ((M.stalkEquiv x).symm ⟨_, hmem⟩)) : OO p) : PadicAlgCl p) =
        M.val (gPt p ≫ y) ((S.FF (S.TT M x) c' κ₁ / S.th x₀) ^ S.N) := by
    intro p _ y ev hy hev
    have hφ : spMap (ev.comp j) ≫ M.Z.fromSpecStalk x = y := by
      rw [← hev]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have := GlobalTheory.CplDiv.val_stalkHom_eq o' Ω M x p y (ev.comp j) hy.1 hφ ((M.stalkEquiv x).symm ⟨_, hmem⟩)
    rw [hstalk] at this
    exact this.symm
  have hdvd : ∀ α s, CongMod S.N α α₀ → PsiCoord D.toPre α s → j ((M.stalkEquiv x).symm ⟨_, hmem⟩) ∣ s := by
    intro α s hα hs
    refine GlobalTheory.CplDiv.dvd_of_norm_le_at_classical o' Ω M hO.normal U₀ hO.ne x hx R j hj _ s ha0
      fun p _ y ev hy hev => ?_
    obtain ⟨-, hpow, hup, -⟩ := hpt p y ev hy hev
    rw [hva p y ev hy hev, hpow]
    exact hup α s hα hs
  obtain ⟨hpos₁, hpow₁, -, mu, smu, hmu, hsmu, hlow₁⟩ := hpt p₁ y₁ ev₁ hy₁ hev₁
  obtain ⟨t, ht⟩ := hdvd mu smu hmu hsmu
  have ht1 : 1 ≤ ‖((ev₁ t : OO p₁) : PadicAlgCl p₁)‖ := by
    have h := hlow₁
    rw [ht, map_mul, MulMemClass.coe_mul, norm_mul, hva p₁ y₁ ev₁ hy₁ hev₁, hpow₁] at h
    exact (le_mul_iff_one_le_right (pow_pos hpos₁ _)).1 h
  have htu : IsUnit t := by
    have hu : IsUnit (ev₁ t) := by
      by_contra hn
      exact absurd ((not_isUnit_OO_iff _).1 hn) (not_lt.2 ht1)
    exact isUnit_of_map_unit ev₁ t hu
  have hassoc : Associated (j ((M.stalkEquiv x).symm ⟨_, hmem⟩)) smu := ⟨htu.unit, by rw [ht, IsUnit.unit_spec]⟩
  refine ⟨mu, hmu, fun α hα r s hr hs => ?_, _, _, he0, ⟨S.TT M x, c', κ₁, x₀, hiso, rfl⟩, hstalk, fun r hr => ?_⟩
  · obtain ⟨u, hu⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord hsmu hr
    have : Associated (j ((M.stalkEquiv x).symm ⟨_, hmem⟩)) r := hassoc.trans ⟨u, by rw [hu, mul_comm]⟩
    exact this.symm.dvd.trans (hdvd α s hα hs)
  · obtain ⟨u, hu⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord hsmu hr
    exact hassoc.trans ⟨u, by rw [hu, mul_comm]⟩

end GlobalTheory.QUnit
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.connectedSpace_pullback_closedFibre_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (K : Type) [Field K] (κ : ResidueField R →+* K), ConnectedSpace (pullback M.π (spMap (κ.comp (residue R))) : Scheme.{0}) := by
  intro R _ _ _ hA M K _ κ
  obtain ⟨hN, -, hIC, -⟩ := hA
  haveI := hN
  haveI := hIC
  obtain ⟨hbij, hsurj⟩ := Modif.appTop_bijective_surjective R M
  haveI := M.proper
  haveI := hsurj
  have hcomp : ∀ {A : Type} [CommRing A] (ψ : ResidueField R →+* A),
      spMap ψ ≫ spMap (residue R) = spMap (ψ.comp (residue R)) := fun ψ => by
    rw [← Spec.map_comp]; rfl
  have pc : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) [PreconnectedSpace X], PreconnectedSpace Y :=
    fun h _ => ⟨by rw [← h.surjective.range_eq, ← Set.image_univ]; exact isPreconnected_univ.image _ h.continuous.continuousOn⟩
  let f := pullback.snd M.π (spMap (residue R))
  have e : ∀ {A : Type} [CommRing A] (ψ : ResidueField R →+* A),
      pullback f (spMap ψ) ≅ pullback M.π (spMap (ψ.comp (residue R))) := fun ψ =>
    pullbackLeftPullbackSndIso M.π (spMap (residue R)) (spMap ψ) ≪≫ pullback.congrHom rfl (hcomp ψ)
  have hP : PreconnectedSpace (pullback f (spMap κ) : Scheme.{0}) := by
    refine GlobalTheory.T.preconnectedSpace_of_finGen_subfield_baseChanges (ResidueField R) _ f inferInstance inferInstance K κ fun L hL n c hc => ?_
    have hc' := GlobalTheory.T.connectedSpace_closedFibre_finitelyGenerated_ext R M.S M.π inferInstance hsurj hbij K κ L hL n c hc
    exact @pc _ _ _ _ (Scheme.homeoOfIso (e _)).symm hc'.toPreconnectedSpace
  haveI : PreconnectedSpace (pullback M.π (spMap (κ.comp (residue R))) : Scheme.{0}) :=
    pc (Scheme.homeoOfIso (e κ))
  obtain ⟨q⟩ : Nonempty (Sp K) := inferInstance
  obtain ⟨z, -⟩ := (pullback.snd M.π (spMap (κ.comp (residue R)))).surjective q
  exact ConnectedSpace.mk ⟨z⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finExt_cp_factor_even : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (A₀ : PolAV (Sp (FractionRing R₀))) (gen₀ : (Over.pullback (jK R₀)).obj G₀ ≅ A₀.A), FinExt ρ₀ ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P ∧ IsMonHom gen₀.hom ∧ LBIso (A₀.L.pull gen₀.hom.left) (P.L.L.pull (pullback.fst G₀.hom (jK R₀))) := by
  intro R _ _ _ hR D D' F hA A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi
  obtain ⟨R₁, _, _, _, ρ₁, G₁, _, _, β₁, β₁₂, A₁, gen₁, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.T.factorPairing_mumfordBundle_principal_polarisation R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi
  exact GlobalTheory.T.exists_evenCubicalStructure_of_idempotentFactor_biextension R hR D D' F A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi R₁ ρ₁ G₁ β₁ β₁₂ A₁ gen₁
    h1 h2 h3 h4 h5

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.LamBound

theorem exists_not_dvd_le {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (hβ : ∀ y, y ≠ 0 → 0 < β y y) (m : ℕ) (hm : 2 ≤ m) :
    ∀ (k : ℕ) (x : X), (β x x).toNat = k → x ≠ 0 →
      ∃ x', x' ≠ 0 ∧ (¬ ∃ v, x' = m • v) ∧ β x' x' ≤ β x x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hk hx
    by_cases hd : ∃ v, x = m • v
    · obtain ⟨v, rfl⟩ := hd
      have hv : v ≠ 0 := by rintro rfl; simp at hx
      have hvv := hβ v hv
      have e : β (m • v) (m • v) = (m : ℤ) * ((m : ℤ) * β v v) := by
        simp [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
      have h2 : 2 * β v v ≤ (m : ℤ) * β v v := mul_le_mul_of_nonneg_right hm' hvv.le
      have h3 : 2 * ((m : ℤ) * β v v) ≤ (m : ℤ) * ((m : ℤ) * β v v) :=
        mul_le_mul_of_nonneg_right hm' (by linarith)
      have hlt : β v v < β (m • v) (m • v) := by rw [e]; linarith
      obtain ⟨x', h1, h2, h3⟩ := ih (β v v).toNat (by omega) v rfl hv
      exact ⟨x', h1, h2, h3.trans hlt.le⟩
    · exact ⟨x, hx, hd, le_rfl⟩

theorem isE8_apply_zero_zero_pos {W : Matrix (Fin 8) (Fin 8) ℤ} (h : IsE8 W) : 0 < W 0 0 := by
  have h1 := h.1.diag_pos (i := 0)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_add] at h1
  have : (0 : ℝ) < W 0 0 := by linarith
  exact_mod_cast this

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem beta_pos (T : Trait F) (x : T.D.toPre.X) (hx : x ≠ 0) : 0 < T.β x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem sc_pos {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁) : 0 < c.sc := by
  have hϖ0 : algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 c.T.irr.ne_zero
  have h0 : c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (c.int _).1 hinv
    apply c.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective c.T.V (FractionRing c.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold CTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem exists_shortest {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (N : ℕ) (a : X) :
    ∃ v : X, ∀ v0, q (a + N • v) ≤ q (a + N • v + N • v0) := by
  have hfin : {x | ¬ q a < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop (q a))
  obtain ⟨b, ⟨hb, v, rfl⟩, hmin⟩ := Set.exists_min_image ({x | ¬ q a < q x} ∩ Set.range fun v => a + N • v) q
    (hfin.inter_of_left _) ⟨a, lt_irrefl _, 0, by simp⟩
  refine ⟨v, fun v0 => ?_⟩
  by_cases h : q a < q (a + N • v + N • v0)
  · exact (not_lt.1 hb).trans h.le
  · exact hmin _ ⟨h, v + v0, by simp [add_assoc]⟩

theorem pos_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (a : X) (ha : a ≠ 0) : 0 < q a := by
  by_contra h
  have h : q a ≤ 0 := not_lt.1 h
  have hfin : {x | ¬ (0 : ℝ) < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • a) (smul_left_injective ℤ ha) (fun n => ?_) hfin
  simp only [Set.mem_setOf_eq, not_lt, QuadraticMap.map_smul, zsmul_eq_mul]
  push_cast
  exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) h

theorem qW_single {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (x : X) :
    qW W β (Pi.single 0 x) = W 0 0 * β x x := by
  simp [qW, Fin.sum_univ_succ]

theorem lab : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ ε yy, IsLab X₁ ε c yy := by
  intro g n F W Z i X₁ hg hn ho hi hE hT hP p _ z₁ c
  obtain ⟨ε, hε, -⟩ := GlobalTheory.Poinc.exists_diagEnd_isMonHom g n F W _ X₁.ρ.P X₁.u X₁.sharp
  exact ⟨ε, GlobalTheory.Poinc.exists_isLab g n F W Z i X₁ hg hn ho hi hE hT hP ε hε p z₁ c⟩

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ C : ℝ, ∀ (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X), x ≠ 0 → ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(C * (c.sc * c.T.β x x))) ≤ ‖c.val h‖ := by
  intro g n F W Z i X₁ hg hn ho hi hE hT hP p _ z₁ hz
  obtain ⟨hL, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hU, hUT⟩ := GlobalTheory.ZH.thmU_and_uTors
  have hdiv : X₁.M.HasDiv X₁.S.th :=
    hT X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.u X₁.sharp X₁.gen X₁.M X₁.π X₁.normal X₁.comp
  refine ⟨(W 0 0 : ℝ) / X₁.S.N, fun c x hx => ?_⟩
  obtain ⟨x', hx', hnd, hle⟩ :=
    exists_not_dvd_le c.T.β (beta_pos c.T) X₁.S.N X₁.S.N_ge _ x rfl hx
  obtain ⟨ε, yy, c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, hR, y₀, hat, u, l, j, hq, -⟩ :=
    lab g n F W Z i X₁ hg hn ho hi hE hT hP p z₁ c
  let S' := X₁.S.rechart c₀ hc R' fg frac hth hev
  have hdiv' : X₁.M.HasDiv S'.th := fun z => (hdiv z).imp fun k hk => (RatModel.div_mul_iff hc).2 hk
  have htests : S'.HasTests :=
    (hasTests_of_real GlobalTheory.SS.semistableReductionSt hU hL hL2 hUT X₁.o₁ X₁.Ω₁ S' ρ').1
  have hy : ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ S'.R a)‖ ≤ 1 := fun a => by
    rw [hat]
    exact RatModel.norm_val_le_one c.cen ((X₁.M.O z₁).algebraMap_mem a)
  obtain ⟨τ, e, hτ, -⟩ := exists_test_match X₁.o₁ X₁.Ω₁ S' ρ' p y₀ u l
    (GlobalTheory.T.thetaConstant_bounded_by_shortestVector hL hL2 hUT _ _ S' ρ' p y₀ u l hy) (GlobalTheory.T.unitThetaConstants_generate_integralTorsion hL hL2 hUT _ _ S' ρ' p y₀ u l hy)
    (GlobalTheory.T.weightSpace_values_integralTorsion_bound_shortestVector hL hL2 hUT _ _ S' ρ' p y₀ u l hy) (GlobalTheory.T.exists_norm_torsionSum_shortestVector_eq hL hL2 hUT _ _ S' ρ' p y₀ u l hy)
    (GlobalTheory.T.exists_weightZeroSection_unit_integralTorsionPoint hL hL2 hUT _ _ S' ρ' p y₀ u l hy)
  let α₀ : τ.X := e.symm (j.symm (Pi.single 0 x'))
  obtain ⟨v, hv⟩ := exists_shortest τ.q τ.pos X₁.S.N α₀
  have hne : α₀ + X₁.S.N • v ≠ 0 := fun h0 => hnd ⟨-(j (e v) 0), by
    have h1 := congrFun (congrArg (fun t => j (e t)) h0) 0
    simp only [α₀, map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, map_zero, Pi.add_apply, Pi.single_eq_same,
      Pi.smul_apply, Pi.zero_apply] at h1
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_left h1⟩
  have hqle : τ.q (α₀ + X₁.S.N • v) ≤ (W 0 0 : ℝ) * (c.sc * c.T.β x' x') := by
    have h1 := hv (-v)
    rw [smul_neg, add_neg_cancel_right] at h1
    refine h1.trans_eq ?_
    rw [hτ, hq]
    simp only [α₀, AddEquiv.apply_symm_apply, qW_single]
    push_cast
    ring
  obtain ⟨h, hm, hh⟩ := GlobalTheory.exists_mem_maximalIdeal_exp_le_norm_val X₁.o₁ X₁.Ω₁ S' X₁.M X₁.normal hdiv' htests z₁ hz p
    c.y y₀ c.cen (fun a ha => hR ha) hat τ _ hv (pos_of_tendsto τ.q τ.pos _ hne)
  refine ⟨h, hm, le_trans (Real.exp_le_exp.2 ?_) hh⟩
  have hsc := sc_pos c
  have hW : (0 : ℝ) ≤ W 0 0 := by exact_mod_cast (isE8_apply_zero_zero_pos hE).le
  have hNpos : (0 : ℝ) < X₁.S.N := by
    have := X₁.S.N_ge
    exact_mod_cast (by omega : 0 < X₁.S.N)
  have hb : (c.T.β x' x' : ℝ) ≤ c.T.β x x := by exact_mod_cast hle
  have h1 : τ.q (α₀ + X₁.S.N • v) ≤ (W 0 0 : ℝ) * (c.sc * c.T.β x x) :=
    hqle.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hsc.le) hW)
  rw [neg_le_neg_iff, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right h1 hNpos.le

end GlobalTheory.Poinc.LamBound
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem torsion_theta_points_defOver : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o' : Type) [CommRing o'] (ζ' : o') (g' n' : ℕ) (F' : SFam g' n' ζ') (lam : Sp V ⟶ F'.X) (β : Q.B.left ⟶ F'.univ.A.left) (β₂ : (G2 Q.B).left ⟶ (G2 F'.univ.A).left), 1 ≤ n' → DefOver k₀ (spMap (ev.comp ρ) ≫ lam ≫ F'.s) → IsGrpPullback Q.B F'.univ.A lam β → IsSquare β β₂ → LBIso (abelian₂ Q.B Q.M.L) (F'.univ.P.pull β₂) → ∀ a, DefOver k₀ (spMap (ev.comp ρ) ≫ (Q.c a).left ≫ β) := by
  intro g l hl hlo W hW
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.conjugate_torsion_point_polarised_fibre_image g l hl hlo W hW
  refine ⟨j₀, ?_⟩
  intro j hj V V₁ _ _ _ _ _ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K _ _ ev k₀ hk₀ hu o' _ ζ' g' n' F' lam β β₂ hn' hdef hpb hsq hLB a
  obtain ⟨hpb0, φ₀₂, hsq0⟩ := GlobalTheory.GrpPB.baseChange_square F'.univ.A Q.B lam β hpb (spMap (ev.comp ρ))
  have hp : (spMap (ev.comp ρ) ≫ (Q.c a).left) ≫ Q.B.hom = 𝟙 _ ≫ spMap (ev.comp ρ) := by
    rw [Category.assoc, Over.w (Q.c a)]; simp
  let p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left :=
    pullback.lift (spMap (ev.comp ρ) ≫ (Q.c a).left) (𝟙 _) hp
  have hpf : p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left :=
    pullback.lift_fst _ _ _
  apply GlobalTheory.Poinc.Sep.defOver_of_finite_orbit K k₀ hk₀ _ _
  apply (GlobalTheory.SiegFibreFinite.finite_identifications o' ζ' g' n' F' hn' K _ _ _ φ₀₂ hpb0 hsq0 p).subset
  rintro P' ⟨σ, hσ, rfl⟩
  obtain ⟨x', φ, φ₂, h1, h2, h3, h4, h5⟩ := hj₀ j hj V V₁ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K ev k₀ hk₀ hu
    o' ζ' g' n' F' lam β β₂ hn' hdef hpb hsq hLB φ₀₂ hsq0 σ hσ a p hpf (pullback.lift_snd _ _ _)
  refine ⟨x', φ, φ₂, ?_, h2, h3, h4, ?_⟩
  · simpa only [Category.assoc] using h1
  · rw [← h5, reassoc_of% hpf]

end GlobalTheory.Poinc.Sep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_sections_prescribed_reduction_finite_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (C₁ : LabCover D₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ Nonempty (Secs C₁.toModif C₁.G C₁.P.L.L C₁.α) := by
  first | exact @GlobalTheory.Mum.exists_secs_finExt | exact GlobalTheory.Mum.exists_secs_finExt | (intros; apply GlobalTheory.Mum.exists_secs_finExt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tautologicalChart_centre_isCompletedEtaleLocalMap : GlobalTheory.Poinc.Sep.SepSt → ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧ ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified := by
  first | exact @GlobalTheory.TChartEt.isEtaleCompletion_tautChart | exact GlobalTheory.TChartEt.isEtaleCompletion_tautChart | (intros; apply GlobalTheory.TChartEt.isEtaleCompletion_tautChart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.localInjections_agree_canonicalFamily_coordinates : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], GlobalTheory.Mum.Base R' → ∀ θ₁ θ₂ : R →+* R', Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK R = jK R' ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → ∀ k, θ₁ (Cn.ψ (MvPolynomial.X k)) = θ₂ (Cn.ψ (MvPolynomial.X k)) := by
  first | exact @GlobalTheory.UInj.coords_eq | exact GlobalTheory.UInj.coords_eq | (intros; apply GlobalTheory.UInj.coords_eq <;> assumption)
end
