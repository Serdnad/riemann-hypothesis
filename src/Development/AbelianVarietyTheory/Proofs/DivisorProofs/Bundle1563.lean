module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1538
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1476
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1492
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle167
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationUniformisedAbelianVarietyUniqueVec
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1520
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1493
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem same_id_map {S : Scheme.{0}} {A T U : Over S} [GrpObj A] {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left}
    (hN : Fam A N) (hM : Fam A M) (u : T ⟶ U) :
    Same A N M (𝟙 T) u ↔ (addF A).map u.op (famCls hM) = famCls hN := by
  rw [same_iff_map hN hM, op_id, CategoryTheory.Functor.map_id]
  exact eq_comm

theorem glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (Ix : Type) (U : Ix → Over S) (M : ∀ i, LB (A ⊗ U i).left), (∀ i, IsChart A (M i)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N → ∃ (i : Ix) (u : Over.mk s ⟶ U i), Same A N (M i) (𝟙 _) u) → ∃ (B : Over S) (P : LB (A ⊗ B).left) (j : ∀ i, U i ⟶ B), Rep A (toUnit B) P ∧ (∀ i, IsOpenImmersion (j i).left) ∧ (∀ p : B.left, ∃ i, p ∈ Set.range (j i).left) ∧ ∀ i, Same A (M i) P (𝟙 _) (j i) := by
  intro S A _ hA Ix U M hM hcov
  obtain ⟨B, x, hu, j, ho, hc, hj⟩ := GlobalTheory.RepOver.representable_over S (addF A) (GlobalTheory.PicGlue.addF_separated S A hA) (GlobalTheory.PicGlue.addF_glue S A hA) Ix U
    (fun i ↦ famCls (hM i).fam)
    (fun i Y u u' h ↦ (hM i).inj Y u u' ((same_iff_map (hM i).fam (hM i).fam u u').2 h))
    (fun i T y ↦ by
      obtain ⟨N, hN, rfl⟩ := famCls_surj y
      obtain ⟨W, hW⟩ := (hM i).chart T N hN
      exact ⟨W, fun Y a ↦ (exists_congr fun u ↦ (same_iff_map hN (hM i).fam a u).symm).trans (hW Y a)⟩)
    (fun T y p ↦ by
      obtain ⟨K, _, _, s, hs⟩ := GlobalTheory.exists_geomPoint_through T.left p
      let a : Over.mk (s ≫ T.hom) ⟶ T := Over.homMk s rfl
      obtain ⟨N, hN, e⟩ := famCls_surj ((addF A).map a.op y)
      obtain ⟨i, u, h⟩ := hcov K (s ≫ T.hom) N hN
      exact ⟨i, _, a, u, hs, e.symm.trans ((same_id_map hN (hM i).fam u).1 h).symm⟩)
  obtain ⟨P, hP, rfl⟩ := famCls_surj x
  refine ⟨B, P, j, ⟨hP, fun T t N hN ↦ ?_⟩, ho, hc, fun i ↦ (same_id_map (hM i).fam hP _).2 (hj i)⟩
  obtain ⟨g, hg, hg'⟩ := hu T (famCls hN)
  have k : ∀ g : T ⟶ B, LBIso N (ev P (fst A T) (snd A T ≫ g)) ↔ (addF A).map g.op (famCls hP) = famCls hN :=
    fun g ↦ (same_id_iff hN.isLB hP.isLB g).symm.trans (same_id_map hN hP g)
  exact ⟨g, ⟨toUnit_unique _ _, (k g).2 hg⟩, fun g' h ↦ hg' g' ((k g').1 h.2)⟩

end GlobalTheory.PicGlue
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem GlobalTheory.CMModel.modelAt_of_stable_torsion : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ (F : IntermediateField ℚ ℂ) (ι : Type) [Fintype ι] (T : ι → ℂ), L.g₂ ∈ F → L.g₃ ∈ F → u ∈ F → Stable L F T → (∀ i, T i ∉ L.lattice ∧ (N : ℂ) * T i ∈ L.lattice) → V.valuation (Fintype.card ι : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  intro L β u V N hβ hβim hu12 hN hNodd F ι _ T hg2 hg3 huF hst hT hcard
  have hΔ := latticeCurve_Δ_ne_zero L
  have hu : u ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_pow (by norm_num)] at hu12
    exact hΔ ((Valuation.zero_iff _).mp hu12.symm)
  have hj : (latticeCurve L).j ∈ V := by
    have hi : _root_.IsIntegral V (latticeCurve L).j := (GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L β hβ hβim).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    rw [← hy]; exact y.2
  obtain ⟨r, s, t, hint⟩ := GlobalTheory.T.exists_variableChange_intV_of_j_mem (latticeCurve L) V (Units.mk0 u hu) hj hu12
  have htm := fun i => GlobalTheory.T.torsion_weierstrass_coords_mem_of_intV L β u V N hβ hβim hu12 hN hNodd hu r s t hint (T i) (hT i).1 (hT i).2
  have hud := fun i => GlobalTheory.T.valuation_derivWeierstrassP_oddTorsion L β u V N hβ hβim hu12 hN hNodd (T i) (hT i).1 (hT i).2
  have havg := GlobalTheory.T.weierstrassCoeffs_integral_average_change_of_variables V (-L.g₂ / 4) (-L.g₃ / 4) r s t (Units.mk0 u hu) ι
    (fun i => L.weierstrassP (T i)) (fun i => L.derivWeierstrassP (T i) / 2) hint hcard
    (fun i => (htm i).1) (fun i => (htm i).2)
    (fun i => by
      show V.valuation (2 * (L.derivWeierstrassP (T i) / 2)) = V.valuation u ^ 3
      rw [mul_div_cancel₀ _ two_ne_zero]; exact hud i)
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.galoisStable_lattice_points_symmetric_mem F L ι T hg2 hg3 hst (fun i => (hT i).1)
  have hnF : ((Fintype.card ι : ℕ) : ℂ) ∈ F := natCast_mem F _
  refine ⟨⟨Units.mk0 u hu, (∑ i, L.weierstrassP (T i)) / Fintype.card ι,
    (∑ i, (3 * L.weierstrassP (T i) ^ 2 + -L.g₂ / 4) / (2 * (L.derivWeierstrassP (T i) / 2))) / Fintype.card ι,
    (∑ i, L.derivWeierstrassP (T i) / 2) / Fintype.card ι⟩, huF, div_mem h1 hnF, div_mem h3 hnF,
    div_mem h2 hnF, havg, ?_⟩
  have hv : V.valuation u ^ 12 ≠ 0 := by
    rw [hu12]; exact (Valuation.ne_zero_iff _).mpr hΔ
  rw [variableChange_Δ, map_mul, map_pow, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, map_one,
    ← hu12, inv_pow, inv_mul_cancel₀ hv]
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_datum_sqProd_mem :
    ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p →
      Datum p F L t → ∃ (L' : PeriodPair) (t' : ℂ), Datum p F L' t' ∧
        (latticeCurve L').j = (latticeCurve L).j ∧ sqProd p L' t' ∈ F := by
  intro p F L t hp h4 h3 hD
  set c := sqProd p L t with hc
  have hc0 : c ≠ 0 := (GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp h4 h3 hD).2
  have hc2 : c ^ 2 ∈ F := (GlobalTheory.T.prodDerivWeierstrassPOverSquares_sq_mem_stable p F L t hp h4 h3 hD).1
  obtain ⟨L', hlat, hg₂, hg₃, hder, hj⟩ := GlobalTheory.T.exists_scaled_periodPair_invariants L c hc0
  obtain ⟨hcard, -⟩ := GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp h4
  refine ⟨L', c * t, ⟨?_, ?_, ?_, ?_, ?_⟩, hj, ?_⟩
  · intro ω hω
    have hz : c * (c⁻¹ * ω) ∈ L'.lattice := by rwa [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    have hz' := (hlat _).1 hz
    have := (hlat _).2 (hD.mul _ hz')
    rwa [← mul_assoc, mul_comm c, mul_assoc, ← mul_assoc c, mul_inv_cancel₀ hc0, one_mul] at this
  · rw [hg₂]
    have : (c ^ 4)⁻¹ = ((c ^ 2) ^ 2)⁻¹ := by ring
    rw [this]
    exact mul_mem (inv_mem (pow_mem hc2 _)) hD.g₂_mem
  · rw [hg₃]
    have : (c ^ 6)⁻¹ = ((c ^ 2) ^ 3)⁻¹ := by ring
    rw [this]
    exact mul_mem (inv_mem (pow_mem hc2 _)) hD.g₃_mem
  · rw [hlat]; exact hD.notMem
  · have := (hlat _).2 hD.ker
    rwa [← mul_assoc, mul_comm c, mul_assoc] at this
  · have hprod : sqProd p L' (c * t) = ((c ^ 3)⁻¹) ^ Fintype.card (Sq p) * c := by
      unfold sqProd
      have : ∀ k : Sq p, L'.derivWeierstrassP (sqPt p (c * t) k) =
          (c ^ 3)⁻¹ * L.derivWeierstrassP (sqPt p t k) := by
        intro k
        unfold sqPt
        rw [← hder, ← mul_assoc, mul_comm ((k.1 : ℕ) : ℂ) c, mul_assoc]
      rw [Finset.prod_congr rfl (fun k _ => this k), Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, hc]
      rfl
    rw [hprod]
    set n := Fintype.card (Sq p) with hn
    have : ((c ^ 3)⁻¹) ^ n * c = ((c ^ 2) ^ (3 * ((n - 1) / 2) + 1))⁻¹ := by
      obtain ⟨m, hm⟩ : Odd n := (GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp h4).2
      rw [hm]
      have : (2 * m + 1 - 1) / 2 = m := by omega
      rw [this]
      apply eq_inv_of_mul_eq_one_left
      rw [inv_pow, mul_assoc, show c * (c ^ 2) ^ (3 * m + 1) = (c ^ 3) ^ (2 * m + 1) by ring,
        inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hc0))]
    rw [this]
    exact inv_mem (pow_mem hc2 _)

end GlobalTheory.CMModel
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.detDegree_nonpos_of_adelicDegree_nonpos : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty → IsFrame s → admitted g → (∀ v, LocFrame x s v (g v)) → deg g ≤ 0 → interNum k (GlobalTheory.structureModule C) ![det W r] ≤ 0 := by
  first | exact @GlobalTheory.Nef.interNum_det_nonpos_of_deg_nonpos | exact GlobalTheory.Nef.interNum_det_nonpos_of_deg_nonpos | (intros; apply GlobalTheory.Nef.interNum_det_nonpos_of_deg_nonpos <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
noncomputable section
namespace GlobalTheory.MBLow.Cl

theorem fst_vE_eq_one : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    (ν : NumOf D ℂ N) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → ∀ (χ : D.X),
    (vE (gm.s χ) (𝟙 _) ν.J).fst = 1 := by
  intro R _ _ D _ N ν gm ⟨o, hz, hp⟩ χ
  have hJ : Good D.P.L (IsLocalRing.closedPoint ℂ) ν.J := fun ψ => ν.good ψ trivial
  have hm : redE ℂ (IsLocalRing.closedPoint ℂ) ∈ LB.wchart D.P.L (DegPre.gtφT D (TE R ℂ) gm.b χ)
      (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)) := by
    simpa only [Category.id_comp] using hJ.mem (DegPre.gtφT D (TE R ℂ) gm.b χ) (redE ℂ)
  have h : ⊤ ≤ (𝟙 (Sp (DualNumber ℂ))) ⁻¹ᵁ LB.wchart D.P.L (DegPre.gtφT D (TE R ℂ) gm.b χ)
      (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)) := by
    refine (GlobalTheory.KS.TangentAt.top_le_iff_dual _ _).2 ((GlobalTheory.ZH.CrdCalc.top_le_iff _ _).2 ?_)
    rw [Category.comp_id]
    exact hm
  have e1 : valR (redE ℂ ≫ 𝟙 (Sp (DualNumber ℂ))) (LB.wchart D.P.L (DegPre.gtφT D (TE R ℂ) gm.b χ)
      (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)))
      ((gm.s χ).s fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)).val = (vE (gm.s χ) (𝟙 _) ν.J).fst :=
    (GlobalTheory.ZH.CrdCalc.valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (𝟙 _) _ h).2 _
  rw [Category.comp_id] at e1
  have e2 := GlobalTheory.ZH.ThetaData.valR_eq_gs (redE ℂ) _ hm
    ((gm.s χ).s fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)).val
  have e3 := gs_unit (redE ℂ) (IsLocalRing.closedPoint ℂ) _ hm
    ((gm.s χ).s fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k))
  have e4 := val_of (gm.s χ) (redE ℂ) (IsLocalRing.closedPoint ℂ) ν.J
    (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)) (fun k => by rw [Category.id_comp])
  have v1 := val_pull hJ (gm.s χ) (redE ℂ) (𝟙 _)
  rw [Category.id_comp] at v1
  have v2 := (val_corr hJ (hp.2 χ) (𝟙 _)).symm.trans ((val_corr hJ (hz.2 χ) (𝟙 _)).trans (val_one _))
  rw [v1] at v2
  refine e1.symm.trans (e2.trans ?_)
  rw [e3, ← e4, v2, Units.val_one, map_one]

end GlobalTheory.MBLow.Cl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.DualMult

theorem redE_closedPoint :
    (redE ℂ) (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint (DualNumber ℂ) := by
  have hl : IsLocalHom (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).hom :=
    ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
  exact Spec_closedPoint (f := CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)

variable {X : Scheme.{0}} {L : LB X}

theorem good_dual (J : (Sp ℂ ⟶ X) → L.ι) (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) :
    Good L (IsLocalRing.closedPoint (DualNumber ℂ) : Sp (DualNumber ℂ)) (fun ψ => J (redE ℂ ≫ ψ)) := by
  intro ψ
  have h := hJ (redE ℂ ≫ ψ) (x := IsLocalRing.closedPoint ℂ) trivial
  change ψ ((redE ℂ) (IsLocalRing.closedPoint ℂ)) ∈ L.U (J (redE ℂ ≫ ψ)) at h
  rwa [redE_closedPoint] at h

theorem vE_eq_val (J : (Sp ℂ ⟶ X) → L.ι) (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {K : Type} [Fintype K]
    {φ : K → (Sp (DualNumber ℂ) ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) :
    vE t (𝟙 _) J = (stalkClosedPointIso (CommRingCat.of (DualNumber ℂ))).hom.hom
      (val t (𝟙 _) (IsLocalRing.closedPoint (DualNumber ℂ) : Sp (DualNumber ℂ)) (fun ψ => J (redE ℂ ≫ ψ))).val := by
  have hm := (good_dual J hJ).mem φ (𝟙 _)
  unfold vE val
  exact (GlobalTheory.ZH.ThetaData.valR_eq_gs _ _ hm _).trans (congrArg _ (gs_unit _ _ _ hm _))

end GlobalTheory.DualMult

namespace GlobalTheory.DualMult
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}

theorem mult_vE (ν : NumOf D ℂ N) (gm : GtPt D (TE R ℂ)) (χ χ' : D.X) :
    vE (gm.s (χ + χ')) (𝟙 _) ν.J *
        vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      vE (gm.s χ) (𝟙 _) ν.J * vE (gm.s χ') (𝟙 _) ν.J := by
  have hJ := good_dual (L := D.P.L) ν.J ν.good
  have e := val_corr hJ (gm.mult χ χ') (𝟙 _)
  replace e := (val_mul hJ _ _ _).symm.trans (e.trans (val_mul hJ _ _ _))
  refine (congrArg₂ (· * ·) (vE_eq_val ν.J ν.good _) (vE_eq_val ν.J ν.good _)).trans
    (Eq.trans ?_ (congrArg₂ (· * ·) (vE_eq_val ν.J ν.good _) (vE_eq_val ν.J ν.good _)).symm)
  rw [← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul]
  exact congrArg (fun u => (stalkClosedPointIso (CommRingCat.of (DualNumber ℂ))).hom.hom (Units.val u)) e

end GlobalTheory.DualMult
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict


open GlobalTheory.HolRead in
theorem extWt_arr_eq_wtCol {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : HCParam D.R) (p q : ℕ)
    (hpq : p + q = D.R.r) (hr : V.rank = D.R.r) (ρ : D.what₂.Tau)
    (hS : S ρ = Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) (c : Fin V.rank) :
    extWt M ρ (arr (nNeg (M.ε ρ)) c) = (wtCol h p q c : ℝ) := by
  have hn : p + q = V.rank := hpq.trans hr.symm
  have hp : p ≤ V.rank := by omega
  have he : IsEnum (Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) (M.lam ρ) (M.ε ρ) := hS ▸ M.enum ρ
  have hε : ∀ a, M.ε ρ a = decide ((a : ℕ) < p) := fun a => (isEnum_holPar_kapW h hr hn he a).2
  obtain ⟨hn', hx⟩ := GlobalTheory.HolDS.lowK_holPar (Formalism.L2.NTheta.holOK_kapW h p q hpq) he
  have hc := c.2
  by_cases hcq : (c : ℕ) < q
  · rw [extWt_arr M ρ hp hε c (Fin.cast hn' (finSumFinEquiv (Sum.inr ⟨c, hcq⟩ : Fin p ⊕ Fin q)))
      (by rw [if_pos (by omega)]; simp), hx]
    simp only [wtCol, if_pos hcq, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, Sum.elim_inr]
  · rw [extWt_arr M ρ hp hε c (Fin.cast hn' (finSumFinEquiv (Sum.inl ⟨c - q, by omega⟩ : Fin p ⊕ Fin q)))
      (by rw [if_neg (by omega)]; simp; omega), hx]
    simp only [wtCol, if_neg hcq, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, Sum.elim_inl]

theorem muVal_castDict {D : D7} {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) :
    MuVal W χ (castDict hV mu) := by
  subst hV
  exact h

theorem extWt_eq_laU_add : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ w, WtIs (R.MW i σ) w → ∃ e : D.what₂.Tau → ℤ, (∀ u ∈ GinfC (Wc D i), castDict hV (T.mu ((i : ℕ) + 1) (res T σ)) u = ∏ ρ, (archM (Wc D i) (R.θ ρ) u).det ^ e ρ) ∧ ∀ k ρ (τ : ((T.U ((i : ℕ) + 1) (res T σ)).X k).Ψ), τ.1 = tauE D ρ → ∀ a : Fin (Wc D i).rank, w ρ a = (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) k τ (Fin.cast (rank_Wc i) a) + e ρ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hM ht i σ hσ hV w hw
  choose e he using fun ρ => (D.hc (lab σ ρ)).e_int i
  refine ⟨fun ρ => -e ρ, ?_, fun k ρ τ hτ a => ?_⟩
  · exact GlobalTheory.HolRead.mu_real_eq_prod_det D R.θ _ _ _ e hM.inf (muVal_castDict hV (ht.laws.muVal _ (inR i) _ hσ))
      fun ρ => he ρ ▸ (ht.chiR i σ hσ).2.2.1 ρ
  · have hs : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
    have hr : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.r := by
      have := D.R.m_add_three_le_k
      have hi := i.2
      simp only [Ranks.sigW, Ranks.r]
      omega
    have h1 := extWt_arr_eq_wtCol (R.MW i σ) (D.hc (lab σ ρ)) _ _ (hs ▸ hr :
      ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = D.R.r) (rank_Wc i) ρ
      (if_pos ((GlobalTheory.ConjReading.branch_of_pins T ht.alg ht.laws.pins σ ρ).1 hσ)) a
    rw [← hw ρ a, hs] at h1
    rw [GlobalTheory.HolRead.SecWt.laU_eq_wtCol D T κ ht.laws ht.alg ht.kap i σ hσ e (fun ρ => (he ρ).symm) k ρ τ hτ,
      Int.cast_injective h1]
    simp

end GlobalTheory.HolDict
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem encard_mul_le_at_level : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ),
    (P.Bl N m 1).Finite → (P.Bl N m 1).encard * (P.Bl 0 (b * N) 1).encard ≤
      {f | f ∈ P.H N 0 ∧ f * s ^ m ∈ P.Bl N m 2}.encard * (P.Bl 0 (b * N + m) 2).encard := by
  intro k _ X _ p D hX P b s t hg N m hfin

  have hnu : ∀ (a c : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a c σ y f := by
    intro a c σ y f
    unfold Pair.nu
    positivity
  have hs0 : s ^ m ≠ 0 := pow_ne_zero _ hg.s_ne

  obtain ⟨hsH, hsnu⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hg.s_mem.1 m
  obtain ⟨htH, htnu⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P (-1) b t hg.t_mem.1 N
  have hsle : ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (↑m * 0) (↑m * 1) σ y (s ^ m) ≤ 1 := by
    intro σ y
    rw [hsnu]
    exact pow_le_one₀ (hnu _ _ _ _ _) (hg.s_mem.2 σ y)
  have htle : ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (↑N * (-1)) (↑N * ↑b) σ y (t ^ N) ≤ 1 := by
    intro σ y
    rw [htnu]
    exact pow_le_one₀ (hnu _ _ _ _ _) (hg.t_mem.2 σ y)

  let Λ₀ : AddSubgroup X.functionField := (P.H N 0).comap (AddMonoidHom.mulRight (s ^ m)⁻¹)
  let Λ₀' : AddSubgroup X.functionField := (P.H 0 (b * N)).comap (AddMonoidHom.mulRight (s ^ m)⁻¹)
  have key := GlobalTheory.VolBr.encard_mul_le_of_quot_embed X.functionField (P.H N m) (P.H 0 (b * N + m)) Λ₀ Λ₀'
    (P.Bl N m) (P.Bl 0 (b * N + m)) (AddMonoidHom.mulRight (t ^ N))
    (GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P N m) (GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P 0 (b * N + m)) ?_ ?_ hfin
  rotate_left
  ·
    intro u hu
    obtain ⟨hH, hn⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P N m (↑N * (-1)) (↑N * ↑b) u (t ^ N) hu.1 htH
    have e1 : (N : ℤ) + ↑N * (-1) = 0 := by ring
    have e2 : (m : ℤ) + ↑N * ↑b = ↑b * ↑N + ↑m := by ring
    rw [e1, e2] at hH hn
    refine ⟨hH, fun σ y => ?_⟩
    simp only [AddMonoidHom.coe_mulRight]
    rw [hn]
    exact mul_le_one₀ (hu.2 σ y) (hnu _ _ _ _ _) (htle σ y)
  ·
    intro u hu hT
    simp only [Λ₀, Λ₀', AddSubgroup.mem_comap, AddMonoidHom.coe_mulRight] at hT ⊢
    rw [← div_eq_mul_inv] at hT ⊢
    exact GlobalTheory.T.div_pow_mem_sections_of_mul_pow_mem k X p D hX P b s t hg N m u hu hT

  have hE : (P.Bl 0 (b * N) 1).encard ≤ (P.Bl 0 (b * N + m) 1 ∩ (Λ₀' : Set X.functionField)).encard := by
    rw [← (mul_left_injective₀ hs0).injOn.encard_image]
    apply Set.encard_le_encard
    rintro _ ⟨g, hg', rfl⟩
    obtain ⟨hH, hn⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P 0 (↑b * ↑N) (↑m * 0) (↑m * 1) g (s ^ m) hg'.1 hsH
    have e1 : (0 : ℤ) + ↑m * 0 = 0 := by ring
    have e2 : (↑b * ↑N : ℤ) + ↑m * 1 = ↑b * ↑N + ↑m := by ring
    rw [e1, e2] at hH hn
    refine ⟨⟨hH, fun σ y => ?_⟩, ?_⟩
    · rw [hn]
      exact mul_le_one₀ (hg'.2 σ y) (hnu _ _ _ _ _) (hsle σ y)
    · show g * s ^ m * (s ^ m)⁻¹ ∈ P.H 0 (↑b * ↑N)
      rw [mul_inv_cancel_right₀ hs0]
      exact hg'.1

  have hB : (P.Bl N m 2 ∩ (Λ₀ : Set X.functionField)) =
      (fun f => f * s ^ m) '' {f | f ∈ P.H N 0 ∧ f * s ^ m ∈ P.Bl N m 2} := by
    ext u
    constructor
    · rintro ⟨hu, hu0⟩
      refine ⟨u * (s ^ m)⁻¹, ⟨hu0, ?_⟩, ?_⟩
      · rw [inv_mul_cancel_right₀ hs0]
        exact hu
      · exact inv_mul_cancel_right₀ hs0 u
    · rintro ⟨f, ⟨hf, hfs⟩, rfl⟩
      refine ⟨hfs, ?_⟩
      show f * s ^ m * (s ^ m)⁻¹ ∈ P.H N 0
      rw [mul_inv_cancel_right₀ hs0]
      exact hf
  rw [hB, (mul_left_injective₀ hs0).injOn.encard_image] at key
  refine le_trans ?_ key
  gcongr

end GlobalTheory.VolBr
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.hermPairWithSections_represents_tensor : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b a' b' : ℤ) (M M' : HermLB p), P.Rep a b M → P.Rep a' b' M' → P.Rep (a + a') (b + b') (M.tens M') := by
  first | exact @GlobalTheory.VolBr.Pair.rep_tens | exact GlobalTheory.VolBr.Pair.rep_tens | (intros; apply GlobalTheory.VolBr.Pair.rep_tens <;> assumption)
end
