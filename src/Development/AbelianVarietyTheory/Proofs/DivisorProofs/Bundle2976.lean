module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppEqZeroOfValR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullCubicalOfGenericOfExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle960
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle539
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle677
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle154
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle046
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle005
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2851
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.MvPowerSeries.Equiv
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn
open GlobalTheory.KS.GlueDer (rsT_eq res_app pre_mono)
open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_sub)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

theorem exists_descData : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) (ν : R), (∀ a, IsField ⊤ (dd a)) → (∀ a V r, dd a V (constFn Y.H.hom V r) = 0) → (∀ a α V f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∃ (V : h.J → Q.P.A.left.Opens) (E : h.J → Fld Q.P.A.left) (P : ∀ i, Γ(Q.P.A.left, V i)), (∀ i, h.W i = Y.q.left ⁻¹ᵁ V i) ∧ (∀ i, IsLift Q.P.A D (V i) (E i)) ∧ (∀ i V', V' ≤ V i → ∀ f, (Y.q.left.app V').hom (E i V' f) = GlobalTheory.HeatConn.dE h ν i _ ((Y.q.left.app V').hom f)) ∧ ∀ i, (Y.q.left.app (V i)).hom (P i) = rsT (GlobalTheory.HeatConn.pE h ν i) (Y.q.left ⁻¹ᵁ V i) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h ν hfield hconst hwt hB
  choose V hV using fun i => (hB i).1
  have hlift : ∀ i, IsLift Y.H D (Y.q.left ⁻¹ᵁ V i) (dE h ν i) := fun i => by
    rw [← hV i]
    refine ⟨isField_dE h ν hfield i, fun O hO r => ?_⟩
    show h.d i O _ + constFn Y.H.hom O ν * ∑ a, constFn Y.H.hom O (h.u a) * dd a O (constFn Y.H.hom O r) = _
    simp only [hconst, mul_zero, Finset.sum_const_zero, add_zero]
    exact (h.lift i).2 O hO r
  have hwt0 : ∀ i (V' : Q.P.A.left.Opens), V' ≤ V i → ∀ f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V') f →
      IsWt Y 0 (Y.q.left ⁻¹ᵁ V') (dE h ν i _ f) := by
    intro i V' hV' f hf
    exact WtAlg.isWt_add ((hB i).2.2.2 0 V' ((GlobalTheory.KS.GlueDer.pre_mono _ hV').trans (hV i).ge) f hf)
      (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ ν)
        (WtAlg.isWt_sum _ _ fun a _ => WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ _) (hwt a 0 _ f hf)))
  choose E hE hq using fun i => AbConst.exists_desc Y (V i) (dE h ν i) D (hlift i) (hwt0 i)
  have hP : ∀ i, ∃ a, (Y.q.left.app (V i)).hom a = rsT (pE h ν i) (Y.q.left ⁻¹ᵁ V i) := fun i => by
    refine AbConst.exists_app_eq Y ?_
    have hw : IsWt Y 0 (h.W i) (pE h ν i) :=
      WtAlg.isWt_add (hB i).2.1 (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ ν) (hB i).2.2.1)
    have tr : ∀ (W : Y.H.left.Opens) (s : Γ(Y.H.left, W)), W = Y.q.left ⁻¹ᵁ V i → IsWt Y 0 W s →
        IsWt Y 0 _ (rsT s (Y.q.left ⁻¹ᵁ V i)) := by
      rintro W s rfl hs
      rwa [WtAlg.rsT_self]
    exact tr _ _ (hV i) hw
  choose P hP using hP
  exact ⟨V, E, P, hV, hE, hq, hP⟩

theorem exists_glue_desc : ∀ {R K : Type} [CommRing R] [Field K] (G : Over (Sp R)) (A₀ : Over (Sp K)) (m₀ : A₀.left ⟶ G.left) (φ : R →+* K), m₀ ≫ G.hom = A₀.hom ≫ spMap φ → ∀ (D : R → R) {I : Type} (V : I → G.left.Opens), ⨆ i, V i = ⊤ → ∀ (E : I → Fld G.left), (∀ i, IsLift G D (V i) (E i)) → (∀ i i' O, O ≤ V i ⊓ V i' → ∀ f, (m₀.app O).hom (E i O f) = (m₀.app O).hom (E i' O f)) → ∃ ed : ∀ W : G.left.Opens, Γ(G.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom G.hom m₀ (fun r => φ (D r)) ⊤ ed ∧ ∀ i U, U ≤ V i → ∀ f, ed U f = (m₀.app U).hom (E i U f) := by
  intro R K _ _ G A₀ m₀ φ hm D I V hV E hE hc
  have hW : ∀ y, ∃ i, m₀ y ∈ V i := fun y => by
    have hy : m₀ y ∈ ⨆ i, V i := by rw [hV]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hy
  have he : ∀ i, GlobalTheory.KS.LocDerK A₀.hom G.hom m₀ (fun r => φ (D r)) (V i) (fun W f => (m₀.app W).hom (E i W f)) := by
    intro i
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h' hW f => ?_, fun W hW r => ?_⟩
    · rw [(hE i).1.1 W hW, map_add (f := _)]
    · rw [(hE i).1.2.1 W hW, map_add (f := _), map_mul, map_mul]
    · rw [(hE i).1.2.2 W W' h' hW, GlobalTheory.KS.GlueDer.rsT_eq (GlobalTheory.KS.GlueDer.pre_mono m₀ h'), GlobalTheory.KS.GlueDer.res_app m₀ h']
    · rw [(hE i).2 W hW, GlobalTheory.KS.GlueDer.app_const φ _ _ m₀ hm]
  obtain ⟨ed, hed, hchar⟩ := GlobalTheory.InteriorKS.glue_along A₀.hom G.hom m₀ (fun r => φ (D r)) V hW
    (fun i W f => (m₀.app W).hom (E i W f)) he fun i i' O hO f => hc i i' O hO f
  refine ⟨ed, hed, fun i U hU f => hchar U f _ fun i' => ?_⟩
  have h1 := (he i).res U (U ⊓ V i') inf_le_left hU f
  rw [GlobalTheory.KS.GlueDer.rsT_eq (GlobalTheory.KS.GlueDer.pre_mono m₀ inf_le_left)] at h1
  rw [← h1]
  exact hc i i' _ (le_inf (inf_le_left.trans hU) inf_le_right) _

theorem connK_transition : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] {φ : R →+* K} {e : ℕ} {ν : R} {A₀ : Over (Sp K)} [GrpObj A₀] {m₀ : A₀.left ⟶ Q.P.A.left}, GlobalTheory.HeatConn.IsFibre Y h φ e ν A₀ m₀ → ∀ {V : h.J → Q.P.A.left.Opens} {ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)} {pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)}, GlobalTheory.HeatConn.IsDesc Y h ν m₀ V ed pb → (∀ i, V i ≤ Q.P.L.U (h.j i)) → ∀ (i i' : h.J), ed (V i ⊓ V i') (rsT (Q.P.L.g (h.j i) (h.j i')).val (V i ⊓ V i')) = pbT m₀ (Q.P.L.g (h.j i) (h.j i')).val (m₀ ⁻¹ᵁ (V i ⊓ V i')) * (rsT (pb i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) - rsT (pb i) (m₀ ⁻¹ᵁ (V i ⊓ V i'))) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hD hV i i'
  have he0 : e ≠ 0 := by
    rintro rfl
    have := hF.inv
    rw [Nat.cast_zero, mul_zero] at this
    exact zero_ne_one this
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he0
  have hUL : V i ⊓ V i' ≤ Q.P.L.U (h.j i) ⊓ Q.P.L.U (h.j i') := inf_le_inf (hV i) (hV i')
  refine ext_lift Y m₀ fun Z a b w z hz => ?_
  have hz' : (a ≫ Y.q.left) z ∈ V i ⊓ V i' := by rw [w]; exact hz
  have haΩ : a z ∈ Y.q.left ⁻¹ᵁ (V i ⊓ V i') := hz'
  have hΩW : Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ h.W i ⊓ h.W i' := by
    rw [hD.1 i, hD.1 i']; exact le_inf (pre_mono _ inf_le_left) (pre_mono _ inf_le_right)
  have hΩL : Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h.j i')) := pre_mono _ hUL
  have hG : (Y.q.left.app (V i ⊓ V i')).hom (rsT (Q.P.L.g (h.j i) (h.j i')).val (V i ⊓ V i')) =
      pbT Y.q.left (Q.P.L.g (h.j i) (h.j i')).val (Y.q.left ⁻¹ᵁ (V i ⊓ V i')) := by
    rw [rsT_eq hUL, ← res_app Y.q.left hUL (pre_mono _ hUL), pbT, dif_pos hΩL]; rfl
  have hz1 : (b ≫ m₀) z ∈ V i := hz.1
  have hz2 : (b ≫ m₀) z ∈ V i' := hz.2
  rw [hD.2.1 Z a b w z i _ inf_le_left hz, hG, gs_mul b z _ hz, gs_sub b z _ hz, gs_pbT b m₀ z (pre_mono _ hUL) hz,
    gs_rsT b z (pre_mono m₀ inf_le_right) hz, gs_rsT b z (pre_mono m₀ inf_le_left) hz, hD.2.2 Z a b w z i' hz2,
    hD.2.2 Z a b w z i hz1, ← w, ← gs_pbT a Y.q.left z hΩL haΩ, ← gs_rsT a z (hΩW.trans inf_le_right) haΩ,
    ← gs_rsT a z (hΩW.trans inf_le_left) haΩ]
  simp only [gs_eq_gsH a z _ haΩ]
  set π := gsH a z _ haΩ
  set G := pbT Y.q.left (Q.P.L.g (h.j i) (h.j i')).val (Y.q.left ⁻¹ᵁ (V i ⊓ V i'))
  have hΘ : ∀ a' b', π (constFn Y.H.hom _ (h.Θ a' b')) = 0 := fun a' b' => by
    rw [← gs_eq_gsH, hF.gs_const w z _ haΩ, hF.symb, cst_eq_cstH, map_zero]
  have hpow : ∀ (m : ℕ) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ (V i ⊓ V i'))),
      dE h ν i _ (f ^ (m + 1)) = ((m + 1 : ℕ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ (V i ⊓ V i'))) * f ^ m * dE h ν i _ f := by
    intro m f
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, (isField_dE h ν hF.field i).2.1 _ (hΩW.trans inf_le_left), ih]
      push_cast; ring
  have e1 := congrArg π (h.glue (k + 1) i i' _ hΩW 1)
  rw [_root_.mul_one, map_op h ν (k + 1) hF.inv i _ (hΩW.trans inf_le_left) π hΘ, map_mul,
    map_op h ν (k + 1) hF.inv i' _ (hΩW.trans inf_le_right) π hΘ, hpow,
    AbConst.isField_one (isField_dE h ν hF.field i') (hΩW.trans inf_le_right)] at e1
  simp only [map_mul, map_pow, map_natCast, map_one, map_zero, zero_add, _root_.mul_one] at e1
  have h2 : IsUnit (2 : Z.presheaf.stalk z) := by
    simpa only [map_ofNat] using (two_ne_zero (α := K)).isUnit.map (cstH (b ≫ A₀.hom) z)
  have hk : IsUnit (((k + 1 : ℕ)) : Z.presheaf.stalk z) := by
    simpa only [map_natCast] using
      (Nat.cast_ne_zero.2 (Nat.succ_ne_zero k) : ((k + 1 : ℕ) : K) ≠ 0).isUnit.map (cstH (b ≫ A₀.hom) z)
  have hGu : IsUnit G := by
    simp only [G, pbT, dif_pos hΩL]; exact (Units.isUnit _).map _
  have hc : IsUnit (2 * ((k + 1 : ℕ) : Z.presheaf.stalk z) ^ 2 * π G ^ k) := (h2.mul (hk.pow 2)).mul ((hGu.map π).pow k)
  refine hc.mul_left_cancel ?_
  push_cast at e1 ⊢
  linear_combination e1

theorem exists_connK_desc : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∃ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb ∧ IsDesc Y h ν m₀ V ed pb := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF
  have := (AbConst.surjective_q Y).1
  obtain ⟨V, E, P, hW, hE, hq, hP⟩ := exists_descData Y h ν hF.field hF.const hF.wt hF.basic
  have hm : m₀ ≫ Q.P.A.hom = A₀.hom ≫ spMap φ := hF.pull.1.w
  have hcov : ⨆ i, V i = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, rfl⟩ := Y.q.left.surjective x
    have hy : y ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    rw [hW] at hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  have hVL : ∀ i, V i ≤ Q.P.L.U (h.j i) := fun i x hx => by
    obtain ⟨y, rfl⟩ := Y.q.left.surjective x
    have hy : y ∈ h.W i := by rw [hW]; exact hx
    exact h.le i hy
  have hc : ∀ i i' O, O ≤ V i ⊓ V i' → ∀ f, (m₀.app O).hom (E i O f) = (m₀.app O).hom (E i' O f) := by
    intro i i' O hO f
    refine ext_lift Y m₀ fun Z a b w z hz => ?_
    have hz' : (a ≫ Y.q.left) z ∈ O := by rw [w]; exact hz
    rw [gs_pull b m₀ z O hz, gs_pull b m₀ z O hz, ← w, ← gs_pull a Y.q.left z O hz', ← gs_pull a Y.q.left z O hz',
      hq i O (hO.trans inf_le_left), hq i' O (hO.trans inf_le_right)]
    refine hF.dE_agree w z i i' _ ?_ hz' _
    rw [hW i, hW i']
    exact le_inf (GlobalTheory.KS.GlueDer.pre_mono _ (hO.trans inf_le_left)) (GlobalTheory.KS.GlueDer.pre_mono _ (hO.trans inf_le_right))
  obtain ⟨ed, hed, hedE⟩ := exists_glue_desc Q.P.A A₀ m₀ φ hm D V hcov E hE hc
  let pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i) := fun i => (m₀.app (V i)).hom (P i)
  have hD : IsDesc Y h ν m₀ V ed pb := by
    refine ⟨hW, fun Z a b w z i U hU hz f => ?_, fun Z a b w z i hz => ?_⟩
    · have hz' : (a ≫ Y.q.left) z ∈ U := by rw [w]; exact hz
      rw [hedE i U hU f, gs_pull b m₀ z U hz, ← w, ← gs_pull a Y.q.left z U hz', hq i U hU f]
    · have hz' : (a ≫ Y.q.left) z ∈ V i := by rw [w]; exact hz
      show gs b z _ ((m₀.app (V i)).hom (P i)) = _
      rw [gs_pull b m₀ z (V i) hz, ← w, ← gs_pull a Y.q.left z (V i) hz', hP i]
      exact GlobalTheory.KS.DlogPol.gs_rsT a z (hW i).ge hz' _
  exact ⟨V, ed, pb, ⟨hed, hcov, hVL, fun i i' => connK_transition Y h hF hD hVL i i'⟩, hD⟩

end GlobalTheory.HeatConn
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatConn
open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub)

theorem cancel_unit {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (δ : A → B) (u : Aˣ) (L Δ : B)
    (h₁ : δ u.val = π u.val * L) (h₂ : δ u.val = π u.val * Δ) : L = Δ :=
  ((Units.isUnit u).map π).mul_left_cancel (h₁.symm.trans h₂)

section ChartFreeProof

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa} {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} {h : Heat Y.H Y.q.left Q.P.L dd D}
  {K : Type} [Field K] {ν : R} {A₀ : Over (Sp K)} {m₀ : A₀.left ⟶ Q.P.A.left} {V : h.J → Q.P.A.left.Opens}
  {ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)} {pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)}

theorem dE_trans_unit {D' : R → K} (hC : IsConnK Q.P.A Q.P.L A₀ m₀ D' V h.j ed pb) (hD : IsDesc Y h ν m₀ V ed pb)
    (hCo : Commutes Q m₀ ed) (α : Q.X) (j : Fin 4) (T : A₀.left ⟶ A₀.left) (h₁ : T ≫ m₀ = m₀ ≫ Q.famφB α j)
    (h₂ : T ≫ A₀.hom = A₀.hom) {Z : Scheme.{0}} {a : Z ⟶ Y.H.left} {b : Z ⟶ A₀.left} (w : a ≫ Y.q.left = b ≫ m₀)
    (z : Z) (i₀ : h.J) (hi₀ : (b ≫ m₀) z ∈ V i₀)
    (δ : Y.H.left.presheaf.stalk (a z) → Z.presheaf.stalk z)
    (hδ : ∀ W, W ≤ h.W i₀ → a z ∈ W → ∀ f, δ (gs (𝟙 _) (a z) W f) = gs a z W (dE h ν i₀ W f))
    (c c' : h.J) (hc : (b ≫ T ≫ m₀) z ∈ V c) (hc' : (b ≫ T ≫ m₀) z ∈ V c') :
    δ (gs (Y.q.left ≫ Q.famφB α j) (a z) (Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c')) (Q.P.L.g (h.j c) (h.j c')).val) =
      (a.stalkMap z).hom (gs (Y.q.left ≫ Q.famφB α j) (a z) (Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c'))
        (Q.P.L.g (h.j c) (h.j c')).val) *
        (gs (b ≫ T) z (m₀ ⁻¹ᵁ V c') (pb c') - gs (b ≫ T) z (m₀ ⁻¹ᵁ V c) (pb c)) := by
  have e : a ≫ Y.q.left ≫ Q.famφB α j = b ≫ T ≫ m₀ := by rw [h₁, reassoc_of% w]
  have hVL : V c ⊓ V c' ≤ Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c') := inf_le_inf (hC.2.2.1 c) (hC.2.2.1 c')
  have hpV : (Q.famφB α j) (Y.q.left (a z)) ∈ V c ⊓ V c' := by
    show (a ≫ Y.q.left ≫ Q.famφB α j) z ∈ V c ⊓ V c'
    rw [e]; exact ⟨hc, hc'⟩
  have hq0 : Y.q.left (a z) ∈ V i₀ := by
    show (a ≫ Y.q.left) z ∈ V i₀
    rw [w]; exact hi₀
  have hqU : Y.q.left (a z) ∈ V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c') := ⟨hq0, hpV⟩
  have hbU : (b ≫ m₀) z ∈ V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c') := by
    show (b ≫ m₀) z ∈ _
    rw [← w]; exact hqU
  set g := (Q.P.L.g (h.j c) (h.j c')).val
  set F := ((Q.famφB α j).app (V c ⊓ V c')).hom (rsT g (V c ⊓ V c'))
  set f := resG Q.P.A.left (inf_le_right : V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c') ≤ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) F
  have s₁ : gs (Y.q.left ≫ Q.famφB α j) (a z) (Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c')) g =
      gs (𝟙 _) (a z) (Y.q.left ⁻¹ᵁ (V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c'))) ((Y.q.left.app _).hom f) := by
    rw [gs_pull (𝟙 _) Y.q.left (a z) _ hqU f, Category.id_comp, gs_res Y.q.left (a z) inf_le_right hqU F,
      gs_pull Y.q.left (Q.famφB α j) (a z) _ hpV _, gs_rsT (Y.q.left ≫ Q.famφB α j) (a z) hVL hpV]
  have hle : Y.q.left ⁻¹ᵁ (V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) ≤ h.W i₀ := by
    rw [hD.1 i₀]; exact fun _ hx ↦ hx.1
  have hbT : (b ≫ T) z ∈ m₀ ⁻¹ᵁ (V c ⊓ V c') := ⟨hc, hc'⟩
  have m : (Y.q.left ≫ Q.famφB α j) (a z) ∈ Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c') := hVL hpV
  have hπ : (a.stalkMap z).hom (gs (Y.q.left ≫ Q.famφB α j) (a z) _ g) = gs (b ≫ T ≫ m₀) z _ g := by
    rw [← e, ← gs_pull a (Y.q.left ≫ Q.famφB α j) z _ m g, gs_stalkMap a z _ m, gs_pull (𝟙 _) _ (a z) _ m g,
      Category.id_comp]
  rw [hπ, s₁, hδ _ hle hqU, ← hD.2.1 Z a b w z i₀ _ inf_le_left hbU f,
    hC.1.res _ _ inf_le_right le_top F, gs_rsT b z (show m₀ ⁻¹ᵁ (V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) ≤ m₀ ⁻¹ᵁ (Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) from fun _ hx ↦ hx.2) hbU,
    hCo α j T h₁ h₂ (V c ⊓ V c') (rsT g (V c ⊓ V c')) Z b z ⟨hc, hc'⟩, hC.2.2.2 c c',
    gs_mul _ z _ hbT, gs_sub _ z _ hbT, gs_rsT (b ≫ T) z (show m₀ ⁻¹ᵁ (V c ⊓ V c') ≤ m₀ ⁻¹ᵁ V c' from fun _ hx ↦ hx.2) hbT, gs_rsT (b ≫ T) z (show m₀ ⁻¹ᵁ (V c ⊓ V c') ≤ m₀ ⁻¹ᵁ V c from fun _ hx ↦ hx.1) hbT,
    gs_pbT (b ≫ T) m₀ z (fun _ hx ↦ hVL hx) hbT, Category.assoc]

end ChartFreeProof

theorem chartFree : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → Commutes Q m₀ ed → ∀ α : Q.X, ChartFree Y h ν m₀ V pb α := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hC hD hCo α T h₁ h₂ Z a b hw z i i' hi hi' w H
  unfold CoordAt at H ⊢
  have hV : ∀ c, V c ≤ Q.P.L.U (h.j c) := hC.2.2.1
  have hm := hF.mem_chart hD hV h₁ hw hi
  have hm' := hF.mem_chart hD hV h₁ hw hi'
  have hT0 := hF.T_zero (h₁ 0) (h₂ 0)
  have hi₀ : (b ≫ m₀) z ∈ V (i 0) := by
    have := hi 0
    rwa [hT0, Category.id_comp] at this
  obtain ⟨δ, -, hδm, hδ⟩ := exists_stalkDer_field (isField_dE h ν hF.field (i 0)) a z hm.1
  obtain ⟨l, hl⟩ := exists_dlog (a.stalkMap z).hom δ hδm
  have hx : gs a z (h.W (i 0) ⊓ xU Y α fun j ↦ h.j (i j))
      (dE h ν (i 0) _ (rsT (xc Y α fun j ↦ h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j ↦ h.j (i j)))) =
      δ (gm (𝟙 _) (a z) (xU Y α fun j ↦ h.j (i j)) (xc Y α fun j ↦ h.j (i j))).val := by
    rw [← hδ _ inf_le_left hm, gs_rsT (𝟙 _) (a z) inf_le_right hm, gs_unit (𝟙 _) (a z) _ hm.2]
  have hx' : gs a z (h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j))
      (dE h ν (i' 0) _ (rsT (xc Y α fun j ↦ h.j (i' j)).val (h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j)))) =
      δ (gm (𝟙 _) (a z) (xU Y α fun j ↦ h.j (i' j)) (xc Y α fun j ↦ h.j (i' j))).val := by
    have hU : a z ∈ h.W (i 0) ⊓ h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j) := ⟨⟨hm.1, hm'.1⟩, hm'.2⟩
    have hle : h.W (i 0) ⊓ h.W (i' 0) ⊓ (xU Y α fun j ↦ h.j (i' j)) ≤ h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j) :=
      fun _ hy ↦ ⟨hy.1.2, hy.2⟩
    rw [← gs_res a z hle hU, ← (isField_dE h ν hF.field (i' 0)).2.2 _ _ hle inf_le_left,
      ← hF.dE_agree hw z (i 0) (i' 0) _ inf_le_left hU, ← hδ _ (inf_le_left.trans inf_le_left) hU, gs_res (𝟙 _) (a z) hle hU,
      gs_rsT (𝟙 _) (a z) inf_le_right hm', gs_unit (𝟙 _) (a z) _ hm'.2]
  have ht := gen_trans ((Y.Φ Y.H (𝟙 _)).isGen α) (𝟙 Y.H.left) (a z) hm.2 hm'.2
  have hu : ∀ k, (l (gm (𝟙 Y.H.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k) (a z)
      (Q.P.L.U (h.j (i (![1, 2, 0, 3] k))) ⊓ Q.P.L.U (h.j (i' (![1, 2, 0, 3] k))))
      (Q.P.L.g (h.j (i (![1, 2, 0, 3] k))) (h.j (i' (![1, 2, 0, 3] k)))))).toAdd =
      gs (b ≫ T (![1, 2, 0, 3] k)) z (m₀ ⁻¹ᵁ V (i' (![1, 2, 0, 3] k))) (pb (i' (![1, 2, 0, 3] k))) -
      gs (b ≫ T (![1, 2, 0, 3] k)) z (m₀ ⁻¹ᵁ V (i (![1, 2, 0, 3] k))) (pb (i (![1, 2, 0, 3] k))) := by
    intro k
    have mem : (𝟙 Y.H.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k) (a z) ∈
        Q.P.L.U (h.j (i (![1, 2, 0, 3] k))) ⊓ Q.P.L.U (h.j (i' (![1, 2, 0, 3] k))) :=
      ⟨Set.mem_iInter.1 hm.2 k, Set.mem_iInter.1 hm'.2 k⟩
    refine cancel_unit _ δ _ _ _ (hl _) ?_
    rw [← gs_unit _ _ _ mem, Category.id_comp, gtφT_eq]
    exact dE_trans_unit hC hD hCo α _ (T _) (h₁ _) (h₂ _) hw z (i 0) hi₀ δ hδ _ _ (hi _) (hi' _)
  have e2 := congrArg (fun u ↦ (l u).toAdd) ht
  simp only [map_mul, toAdd_mul, trF, map_prod, map_zpow, toAdd_prod, toAdd_zpow, Fin.sum_univ_four] at e2
  rw [hu 0, hu 1, hu 2, hu 3] at e2
  simp only [DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, neg_smul, one_smul, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at e2
  rw [hx, gs_stalkMap a z _ hm.2, gs_unit (𝟙 _) (a z) _ hm.2] at H
  have eH := cancel_unit _ δ _ _ _ (hl _) H
  rw [hx', hl, gs_stalkMap a z _ hm'.2, gs_unit (𝟙 _) (a z) _ hm'.2]
  congr 1
  linear_combination eH - e2

end GlobalTheory.HeatConn
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartCubExt

theorem extendGenAt_chartRing : ∀ (k : Type) [Field k] (m n : ℕ),
    GlobalTheory.ChartCubExt.ExtendGenAt (ChartRing k m n) (FractionRing (ChartRing k m n)) := by
  intro k _ m n
  have : IsRegularLocalRing (ChartRing k m n) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin n)
  have := GlobalTheory.isRegularRing_of_isRegularLocalRing (ChartRing k m n)
  have : IsDomain (ChartRing k m n) :=
    (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (ChartRing k m n)).1
  have : UniqueFactorizationMonoid (ChartRing k m n) := GlobalTheory.ThetaExtend.ufd_of_regular _
  intro G _ _ hG eA heA N r hr hc
  have := hG.smooth
  have := hG.quasiCompact
  have := hG.geomConnected
  obtain ⟨a, u, hu, hf⟩ := GlobalTheory.T.exists_const_mul_eq_generator_factorial_base _ _ G _ _ _ N.L r inferInstance inferInstance inferInstance
    (IsPullback.of_hasPullback _ _) N.isLB hr
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_baseUnit_rigidifiedGenericGenerator _ _ G (eSec G) (Over.w η[G]) eA heA N.L N.rig r N.isLB N.rigGen hc a u hu hf
  exact GlobalTheory.T.exists_globalGenerator_div_baseUnit_eq_generic _ _ G _ _ _ pullback.condition N.L r a b hb u hu hf

end GlobalTheory.ChartCubExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Desc.OpenChart

theorem completedStalk_chart (X : Scheme.{0}) (x : X) [IsNoetherianRing (X.presheaf.stalk x)] :
    GlobalTheory.fromSpecCompletedStalk X x (closedPoint _) = x ∧
    IsEtaleCompletion (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom ∧
      Function.Surjective ((residue (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
        (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom) := by
  have fg : (maximalIdeal (X.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  let φ := algebraMap (X.presheaf.stalk x) (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
  haveI : IsLocalHom φ := ((IsLocalRing.local_hom_tfae φ).out 1 3).mpr hm.symm.le
  have hres : Function.Surjective ((residue _).comp φ) := by
    intro r
    obtain ⟨a, ha⟩ := (AdicCompletion.residueField_map_bijective (X.presheaf.stalk x)).2 r
    obtain ⟨b, rfl⟩ := residue_surjective a
    refine ⟨b, ?_⟩
    rw [← ha, RingHom.comp_apply, ResidueField.map_residue]
  have hx : GlobalTheory.fromSpecCompletedStalk X x (closedPoint _) = x := by
    rw [GlobalTheory.fromSpecCompletedStalk]
    erw [Scheme.Hom.comp_apply]
    have hc : Spec.map (CommRingCat.ofHom φ) (closedPoint _) = closedPoint (X.presheaf.stalk x) :=
      IsLocalRing.comap_closedPoint φ
    erw [hc]
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨e, he, hψ⟩ := GlobalTheory.GenFan.stalk_factor_eq hx (CommRingCat.ofHom φ)
    (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x))
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _)
  refine ⟨hx, ?_, ?_⟩
  · rw [hψ]
    exact GlobalTheory.TorRef.isEtaleCompletion_comp_bij e he φ ⟨RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _),
      hm.symm, RingHom.Finite.of_surjective _ hres⟩
  · rw [hψ, ← RingHom.comp_assoc]
    exact hres.comp he.2

theorem nonempty_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) [IsOpenImmersion j]
    (A : Over (Xo.XF c)) [GrpObj A], IsSemiAbelian A → ∀ x ∈ Set.range j, Nonempty (GlobalTheory.Desc.Chart j A x) := by
  intro E _ _ _ H Dw l Xo c S j _ A _ hA x hx
  obtain ⟨x', rfl⟩ := hx
  haveI : Smooth Xo.s := by haveI := Xo.smooth; exact SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  haveI hreg : IsRegularLocalRing ((Xo.XF c).presheaf.stalk x') :=
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth_field
      (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) x'
  obtain ⟨hcen, hEt, hres⟩ := completedStalk_chart (Xo.XF c) x'
  obtain ⟨ιF⟩ := GlobalTheory.GenFan.exists_ringHom_stalk c.F (Xo.XF c)
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) x'
  set St := (Xo.XF c).presheaf.stalk x'
  set R := AdicCompletion (maximalIdeal St) St
  haveI : IsRegularLocalRing R := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion St
  haveI : IsDomain R := GlobalTheory.isDomain_of_isRegularLocalRing R
  let g : Sp R ⟶ Xo.XF c := GlobalTheory.fromSpecCompletedStalk (Xo.XF c) x'
  have hcz : CharZero R := (RingHom.charZero_iff ((algebraMap St R).comp ιF).injective).1 inferInstance
  have hb : Function.Bijective (j.stalkMap (g (closedPoint R))).hom :=
    ConcreteCategory.bijective_of_isIso _
  refine ⟨{
    R := R
    complete := inferInstance
    charZero := hcz
    ξ := g ≫ j
    centre := by
      show j (g (closedPoint R)) = j x'
      rw [hcen]
    etc := GlobalTheory.MemberEt.isEtaleCompletion_comp_openImmersion _ _ j R g hEt
    unr := by
      apply RingHom.FormallyUnramified.of_surjective
      rw [Scheme.stalkClosedPointTo_comp]
      exact hres.comp hb.2
    G := (Over.pullback g).obj A
    semi := IsSemiAbelian.pullback (f := g) A hA
    y := jK R ≫ g
    hy := Category.assoc _ _ _
    α := pullback.fst ((Over.pullback g).obj A).hom (jK R) ≫ pullback.fst A.hom g
    gen := IsGrpPullback.comp (isGrpPullback_pullback _ (jK R)) (isGrpPullback_pullback A g) }⟩

end GlobalTheory.Desc.OpenChart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.splitTorus_hom_eq_of_bcMap_comp_eq : ∀ (A κ : Type) [CommRing A] [IsLocalRing A] [CommRing κ] (π : A →+* κ), Function.Surjective π → IsNilpotent (RingHom.ker π) → ∀ (X : Type) [AddCommGroup X] (H : Over (Sp A)) [GrpObj H] [IsCommMonObj H] (i₁ i₂ : splitTorus (Sp A) X ⟶ H), IsMonHom i₁ → IsMonHom i₂ → GlobalTheory.SplitTorus.bcMap (spMap π) X ≫ i₁.left = GlobalTheory.SplitTorus.bcMap (spMap π) X ≫ i₂.left → i₁ = i₂ := by
  first | exact @GlobalTheory.splitTorus_hom_eq_of_nilpotent | exact GlobalTheory.splitTorus_hom_eq_of_nilpotent | (intros; apply GlobalTheory.splitTorus_hom_eq_of_nilpotent <;> assumption)
end
