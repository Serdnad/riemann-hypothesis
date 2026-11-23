module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLevelPointTangentVectorTransportIff
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyProjCoordsConvergentCoefficients
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSectionsExtendGermRingsAndSpanFibres
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsChartLoc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.arcLevelPoint_tangentVector_transport_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S S' : Scheme.{0}) (A : AnArc (𝓞 E)) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (y' : Sp ℂ⸨X⸩ ⟶ S') (y : Sp ℂ⸨X⸩ ⟶ S) (Φ' : GenPts A t' y') (Φ : GenPts A t y), w.IsGen → GenPts.Rel m w Φ' Φ → (∀ (k : ℕ) [NeZero k] (p' : Over.mk y' ⟶ t'.G) (p : Over.mk y ⟶ t.G) la, p'.left ≫ m.φ = p.left → (Φ'.LevelPt k p' la ↔ Φ.LevelPt k p la)) ∧ ∀ z₀ (ν' : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t'.G.hom y') (ν : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t.G.hom y), ν' ≫ pullback.fst _ _ ≫ m.φ = ν ≫ pullback.fst _ _ → ν' ≫ pullback.snd _ _ = ν ≫ pullback.snd _ _ → (Φ'.IsTan z₀ ν' ↔ Φ.IsTan z₀ ν) := by
  first | exact @GlobalTheory.LevelTransport.levelPt_isTan_iff | exact GlobalTheory.LevelTransport.levelPt_isTan_iff | (intros; apply GlobalTheory.LevelTransport.levelPt_isTan_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem exp_eq_of_matching_markings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (P P' : (Fu.Di i).La →+ (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (inferInstance : StarRing (𝓞 E)) = H.starRing → IsPeriod (Fu.Di i) ty P → IsPeriod (Fu.Di i) ty P' → (∀ u v, (Fu.Di i).EF (gam u) (gam v) = (Fu.Di i).EF u v) → (∀ v ∈ idealPart D l, ∃ e, gam (Fu.t i v) = Fu.t i v + l.M • e) → (∀ v, ∃ e, gam (Fu.t i v) = Fu.t i v + l.A • e) → (∀ u, P' (gam u) = h (P u)) → Fu.u i P = Fu.u i P' ∧ ∀ z, (Fu.ex i P' (h z)).left = (Fu.ex i P z).left := by
  intro E _ _ _ H _ D l Xo σ g ty Fu i P P' gam h _ hP hP' hiso hM hA hh
  have hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (Fu.Di i).La),
      ∃ e, gam a = a + l.M • e := by
    intro a ha
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro v hv b _
      obtain ⟨c, e, rfl⟩ := Fu.t_surj i b
      obtain ⟨e₁, he₁⟩ := hM (v • c) (Submodule.smul_mem_smul hv Submodule.mem_top)
      obtain ⟨r, hr⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
      refine ⟨e₁ + r • (gam (v • e) - v • e), ?_⟩
      rw [smul_add, ← map_smul, smul_comm v, map_add (f := _), he₁, map_nsmul, hr, smul_add, smul_smul,
        smul_sub]
      abel
    · rintro x y ⟨e, he⟩ ⟨e', he'⟩
      exact ⟨e + e', by rw [map_add (f := _), he, he', smul_add]; abel⟩
  have hA' : ∀ a, ∃ e, gam a = a + l.A • e := by
    intro b
    obtain ⟨c, e, rfl⟩ := Fu.t_surj i b
    obtain ⟨e₁, he₁⟩ := hA c
    obtain ⟨r, hr⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
    refine ⟨e₁ + r • (gam e - e), ?_⟩
    rw [map_add (f := _), he₁, map_nsmul, hr, smul_add, smul_smul, smul_sub]
    abel
  have hm : ∀ z, (LinearMap.toMatrix' h.toLinearMap).mulVec z = h z := fun z =>
    LinearMap.toMatrix'_mulVec _ z
  obtain ⟨-, h1, h2⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H D l Xo σ g ty Fu i P P' gam
    (LinearMap.toMatrix' h.toLinearMap) hP hP' hiso hM' hA' (fun a => by rw [hm, hh])
  exact ⟨h1, fun z => by rw [← hm]; exact h2 z⟩

end GlobalTheory.ArcPts
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPoint

theorem eq_spMap_of_injective {K A B : Type} [CommRing K] [CommRing A] [CommRing B] (i : A →+* B)
    (hi : Function.Injective i) (x : Sp A ⟶ Sp K) (ρ : K →+* A) (h : spMap i ≫ x = spMap (i.comp ρ)) :
    x = spMap ρ := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  have h' : Spec.map (φ ≫ CommRingCat.ofHom i) = Spec.map (CommRingCat.ofHom (i.comp ρ)) := by
    rw [Spec.map_comp]; exact h
  have h2 := Spec.map_injective h'
  congr 1
  ext k
  exact hi (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h2) k)

theorem sumsAt_of_halfRing {K F : Type} [CommRing K] [CommRing F] {X Y : Scheme.{0}} (s : X ⟶ Sp K) (κ : K →+* F)
    (bF : F →+* ℂ) (j : pullback s (spMap κ) ⟶ Y) (χ : Sp ℂ⟦X⟧ ⟶ Y) (y : Sp ℂ⸨X⸩ ⟶ pullback s (spMap κ))
    (hj : y ≫ j = spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) ≫ χ)
    (hs : y ≫ pullback.snd _ _ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF))
    {T : ℝ} (yT : Sp (Conv.halfRing T) ⟶ X)
    (hT : spMap (Conv.halfRing T).val.toRingHom ≫ yT = y ≫ pullback.fst _ _)
    (U : Y.Opens) (f : Γ(Y, U)) (hU : ⊤ ≤ χ ⁻¹ᵁ U) :
    ∃ T' ≥ T, ∀ (w : ℂ) (hw : T < w.im), T' < w.im → ∀ z : Sp ℂ ⟶ pullback s (spMap κ),
      z ≫ pullback.fst _ _ = spMap (Conv.ev T w hw).toRingHom ≫ yT → z ≫ pullback.snd _ _ = spMap bF →
      ⊤ ≤ (z ≫ j) ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (z ≫ j) U f) := by
  have hval : (Conv.halfRing T).val.toRingHom.comp ((algebraMap ℂ (Conv.halfRing T)).comp bF) =
      (algebraMap ℂ ℂ⸨X⸩).comp bF := RingHom.ext fun _ => rfl
  have hover : yT ≫ s = spMap ((algebraMap ℂ (Conv.halfRing T)).comp bF) ≫ spMap κ := by
    rw [← spMap_comp]
    refine eq_spMap_of_injective (Conv.halfRing T).val.toRingHom Subtype.val_injective _ _ ?_
    rw [← Category.assoc, hT, Category.assoc, pullback.condition, ← Category.assoc, hs, ← spMap_comp,
      ← RingHom.comp_assoc, hval]
  let yF : Sp (Conv.halfRing T) ⟶ pullback s (spMap κ) := pullback.lift yT _ hover
  have hgen : spMap (Conv.halfRing T).val.toRingHom ≫ yF = y := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hT]
    · rw [Category.assoc, pullback.lift_snd, hs, ← spMap_comp, hval]
  obtain ⟨T', hle, hw'⟩ := Conv.exists_sumsAt_halfCurve (yT := yF ≫ j) (χ := χ) rfl (RingHom.id _) (by
    rw [RingHom.id_comp, RingHom.id_comp, ← hj, ← hgen, Category.assoc, ← Category.assoc (spMap _) (spMap _),
      ← spMap_comp]
    rfl) hU
  refine ⟨T', hle, fun w hw hw2 z hz1 hz2 => ?_⟩
  have hz : z = spMap (Conv.ev T w hw).toRingHom ≫ yF := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hz1]
    · rw [Category.assoc, pullback.lift_snd, hz2, ← spMap_comp]
      congr 2
      ext x
      exact ((Conv.ev T w hw).commutes (bF x)).symm
  have hzj : z ≫ j = Conv.halfCurve (yF ≫ j) w := by
    rw [hz, Conv.halfCurve_eq _ hw, Category.assoc]
    rfl
  rw [hzj]
  exact ⟨(hw' w hw2).1, (hw' w hw2).2 f⟩

theorem point_sumsAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GlobalTheory.ArcPts.GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), ∀ (U : Y.X.Opens) (f : Γ(Y.X, U)), ⊤ ≤ χ ⁻¹ᵁ U → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u K.i (K.Pw w) → yF ≫ pullback.snd _ _ = spMap bF → ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (yF ≫ Y.j) U f) := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ g ty Fu laA laM K U f hU
  obtain ⟨T', hle, h⟩ := sumsAt_of_halfRing Xo.s _ bF Y.j χ C.yF C.yF_j C.yF_over Ψ.yT Ψ.yT_gen U f hU
  refine ⟨max T' K.T, fun w hw z hz1 hz2 => ?_⟩
  have h1 : T' < w.im := (le_max_left _ _).trans_lt hw
  have h2 : Ψ.T < w.im := hle.trans_lt h1
  exact h w h2 h1 z (hz1.trans ((K.u_eq w ((le_max_right _ _).trans_lt hw)).trans (Ψ.yw_eq w h2))) hz2

end GlobalTheory.ArcPoint
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.GenericTan

section Charts

variable {R : Type} [CommRing R] [IsLocalRing R] {Z Z' : Scheme.{0}} {L : LB Z}

theorem valR_cocycle (hL : L.IsLB) (x : Sp R ⟶ Z) {i j k : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    valR x (L.U i ⊓ L.U j) (L.g i j).val * valR x (L.U j ⊓ L.U k) (L.g j k).val =
      valR x (L.U i ⊓ L.U k) (L.g i k).val := by
  apply toStkA_injective
  rw [map_mul, FormalValue.toStkA_valR_eq_gs x (L.U i ⊓ L.U j) _ (fun _ hz => ⟨hi hz, hj hz⟩) _, gs_unit x (cpt R) (L.U i ⊓ L.U j) ⟨hi trivial, hj trivial⟩ (L.g i j),
    FormalValue.toStkA_valR_eq_gs x (L.U j ⊓ L.U k) _ (fun _ hz => ⟨hj hz, hk hz⟩) _, gs_unit x (cpt R) (L.U j ⊓ L.U k) ⟨hj trivial, hk trivial⟩ (L.g j k),
    FormalValue.toStkA_valR_eq_gs x (L.U i ⊓ L.U k) _ (fun _ hz => ⟨hi hz, hk hz⟩) _, gs_unit x (cpt R) (L.U i ⊓ L.U k) ⟨hi trivial, hk trivial⟩ (L.g i k), ← Units.val_mul,
    gm_cocycle hL x _ (hi trivial) (hj trivial) (hk trivial)]

theorem valR_self (hL : L.IsLB) (x : Sp R ⟶ Z) {j : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valR x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  apply toStkA_injective
  rw [FormalValue.toStkA_valR_eq_gs x (L.U j ⊓ L.U j) _ (fun _ hz => ⟨h hz, h hz⟩) _, gs_unit x (cpt R) (L.U j ⊓ L.U j) ⟨h trivial, h trivial⟩ (L.g j j), map_one]
  exact congrArg Units.val (gm_self hL x _ (h trivial))

theorem isFrm_spread (hL : L.IsLB) (x : Sp R ⟶ Z) {k : L.ι} (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) {a : R} (ha : IsUnit a) :
    IsFrm L x (fun j => valR x (L.U j ⊓ L.U k) (L.g j k).val * a) := by
  refine ⟨fun j hj => (FormalValue.isUnit_valR x (L.U j ⊓ L.U k) (fun _ hz => ⟨hj hz, hk hz⟩) _).mul ha,
    fun j j' h => ?_⟩
  rw [← _root_.mul_assoc, valR_cocycle hL x (fun _ hz => (h hz).1) (fun _ hz => (h hz).2) hk]

theorem sval_chart {p : Z' ⟶ Z} {m : ℕ} (s : SecP L p m) (q : Sp R ⟶ Z') {j k : L.ι}
    (hj : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U j) (hk : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U k) :
    ArcPts.sval s q j = valR (q ≫ p) (L.U j ⊓ L.U k) (L.g j k).val ^ m * ArcPts.sval s q k := by
  have wj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) :=
    fun z hz => Set.mem_iInter.2 fun _ => hj hz
  have wk : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => k) :=
    fun z hz => Set.mem_iInter.2 fun _ => hk hz
  apply toStkA_injective
  rw [map_mul, map_pow, FormalValue.toStkA_valR_eq_gs (q ≫ p) (L.U j ⊓ L.U k) _ (fun _ hz => ⟨hj hz, hk hz⟩) _, gs_unit (q ≫ p) (cpt R) (L.U j ⊓ L.U k) ⟨hj trivial, hk trivial⟩ (L.g j k)]
  refine (FormalValue.toStkA_valR_eq_gs q _ _ wj _).trans ((sec_trans s q _ (wj trivial) (wk trivial)).trans
    (congrArg₂ (· * ·) ?_ (FormalValue.toStkA_valR_eq_gs q _ _ wk _).symm))
  rw [trF, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]

theorem hasVal_of_chart {p : Z' ⟶ Z} {m : ℕ} (s : SecP L p m) (q : Sp R ⟶ Z') {τ : L.ι → R}
    (hτ : IsFrm L (q ≫ p) τ) {k : L.ι} (hk : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U k) {r : R}
    (h : ArcPts.sval s q k = r * τ k ^ m) : HasVal s q τ r := fun j hj => by
  rw [sval_chart s q hj hk, h, hτ.2 j k (fun _ hz => ⟨hj hz, hk hz⟩), mul_pow, mul_left_comm]

def pullPow (p : Z' ⟶ Z) {m : ℕ} (σ : Out.H0 L m) : SecP L p m :=
  have l : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => p) j ≤ p ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 Z) j :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  { f := fun j => (p.appLE _ _ (l j)).hom (σ.f j)
    compat := fun (j j' : Fin 1 → L.ι) => fn_ext fun y hy => by
      have v : ∀ j : Fin 1 → L.ι, y ∈ LB.wchart L (fun _ : Fin 1 => p) j →
          gs (𝟙 Z') y _ ((p.appLE _ _ (l j)).hom (σ.f j)) =
          gs (𝟙 Z' ≫ p) y (LB.wchart L (fun _ : Fin 1 => 𝟙 Z) j) (σ.f j) := fun j hj =>
        (gs_res (𝟙 Z') y (l j) hj _).trans (gs_pull _ p y _ (l j hj) _)
      refine ((gs_res (𝟙 Z') y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Z') y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Z') y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Z') y j j' hy.1 hy.2)))
          ((gs_res (𝟙 Z') y _ hy _).trans (v j' hy.2)))).symm)
      rw [sec_trans σ (𝟙 Z' ≫ p) y (l j hy.1) (l j' hy.2)]
      simp only [trF, Category.comp_id] }

omit [IsLocalRing R] in
theorem sval_pullPow (p : Z' ⟶ Z) {m : ℕ} (σ : Out.H0 L m) (q : Sp R ⟶ Z') {k : L.ι}
    (hk : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U k) : ArcPts.sval (pullPow p σ) q k =
      valR (q ≫ p) (LB.wchart L (fun _ : Fin 1 => 𝟙 Z) (fun _ => k)) (σ.f (fun _ => k)) :=
  HolHom.valR_appLE q p _ _ _ _ (fun z hz => Set.mem_iInter.2 fun _ => hk hz)

omit [IsLocalRing R] in
theorem le_powChart {x : Sp R ⟶ Z} {k : L.ι} (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 Z) (fun _ => k) :=
  fun _ hz => Set.mem_iInter.2 fun _ => hk hz

end Charts

theorem isTan_of_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (A : AnArc (𝓞 E)) (t : SAB H (Sp ℂ⟦X⟧)) (Φ : GenPts A t gen) (L : RigLB t.G) (x : A.V → (Sp ℂ⟦X⟧ ⟶ t.G.left)) (τ : A.V → L.L.ι → ℂ⟦X⟧) (z : A.V) (v : Sp (DualNumber ℂ⟦X⟧) ⟶ t.G.left) (k₀ : L.L.ι) (τ₁ : DualNumber ℂ⟦X⟧) (ρ : DualNumber ℂ⟦X⟧ →+* DualNumber ℂ⸨X⸩) (νK : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t.G.hom gen), L = t.PP → (∀ u, (Φ.x u).left = gen ≫ x u ∧ ∀ (k : L.L.ι) (k' : t.PP.L.ι), HEq k k' → ⊤ ≤ x u ⁻¹ᵁ L.L.U k → Φ.τ u k' = algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (τ u k)) → spMap (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom ≫ v = x 0 → ⊤ ≤ v ⁻¹ᵁ L.L.U k₀ → IsUnit τ₁ → (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r)) → ρ DualNumber.eps = DualNumber.eps → νK ≫ pullback.fst _ _ = spMap ρ ≫ v → νK ≫ pullback.snd _ _ = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) → (∀ (j : ℕ) [NeZero j] (α : A.X), ∀ th ∈ A.Theta j α, ∀ F, IsDFSum A j α th z F → ∃ (m : ℕ) (σ : Out.H0 L.L j), (∀ u k, ⊤ ≤ x u ⁻¹ᵁ L.L.U k → algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (valR (x u) (LB.wchart L.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k)) (σ.f (fun _ => k))) = HahnSeries.single (m : ℤ) (1 : ℂ) * A.FSum j α th u * algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (τ u k) ^ j) ∧ ρ (valR v (LB.wchart L.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k₀)) (σ.f (fun _ => k₀))) = TrivSqZeroExt.inl (HahnSeries.single (m : ℤ) (1 : ℂ)) * (TrivSqZeroExt.inl (A.FSum j α th 0) + TrivSqZeroExt.inr F) * ρ τ₁ ^ j) → Φ.IsTan z νK := by
  intro E _ _ _ H _ A t Φ L x τ z v k₀ τ₁ ρ νK hL hx hv hk₀ hτ₁ hρ hε hfst hsnd hsec
  subst hL
  have hρ' := eq_dualMapR _ ρ hρ hε
  have hK : ⊤ ≤ (νK ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U k₀ := by
    rw [hfst]; exact FormalValue.top_le_comp hk₀ _
  haveI := isLocalRing_dual ℂ⸨X⸩
  have hfrm := isFrm_spread t.PP.isLB (νK ≫ pullback.fst _ _) hK (hτ₁.map ρ)
  refine ⟨hsnd, ?_, _, hfrm, fun j _ α th hth F hF => ?_⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hfst, fib, pullback.lift_fst, (hx 0).1, ← hv, ← Category.assoc, ← Category.assoc,
        ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext1
      refine RingHom.ext fun a => ?_
      rw [hρ']
      exact fst_dualMapR _ a
    · rw [Category.assoc, hsnd, fib, pullback.lift_snd, ← Spec.map_comp, ← Spec.map_id]
      congr 1
  · obtain ⟨m, σ, h₁, h₂⟩ := hsec j α th hth F hF
    have key := sval_eq_sum_of_hasVal E H _ A t gen Φ j (pullPow (pullback.fst t.G.hom gen) σ) 1
      (fun _ => HahnSeries.single (m : ℤ) (1 : ℂ)) (fun _ => α) (fun _ => th) (fun _ => hth) (fun u => by
        have e : fib (Φ.x u) ≫ pullback.fst t.G.hom gen = gen ≫ x u := by
          rw [fib, pullback.lift_fst, (hx u).1]
        obtain ⟨k, hk⟩ := exists_chart t.PP.isLB (x u (cpt ℂ⟦X⟧))
        have hk' := (top_le_iff_cpt _ _).2 hk
        have hk'' : ⊤ ≤ (fib (Φ.x u) ≫ pullback.fst t.G.hom gen) ⁻¹ᵁ t.PP.L.U k := by
          rw [e]; exact FormalValue.top_le_comp hk' _
        refine hasVal_of_chart _ _ ?_ hk'' ?_
        · rw [e, ← (hx u).1]; exact Φ.frm u
        · rw [sval_pullPow _ _ _ hk'', e, Fin.sum_univ_one, (hx u).2 k k HEq.rfl hk', ← h₁ u k hk']
          exact FormalValue.valR_spMap _ _ _ (le_powChart hk') _)
      _ _ νK hsnd k₀ hK
    refine hasVal_of_chart _ _ hfrm hK ?_
    rw [sval_pullPow _ _ _ hK, hfst, Fin.sum_univ_one, TrivSqZeroExt.algebraMap_eq_inl] at key
    replace key := (h₂.symm.trans (FormalValue.valR_spMap ρ v _ (le_powChart hk₀) _).symm).trans key
    rw [_root_.mul_assoc] at key
    have hu : IsUnit (TrivSqZeroExt.inl (HahnSeries.single (m : ℤ) (1 : ℂ)) : DualNumber ℂ⸨X⸩) :=
      TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit (by simp))
    rw [valR_self t.PP.isLB _ hK, _root_.one_mul]
    exact (hu.mul_left_cancel key).symm

end GlobalTheory.GenericTan
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

theorem holArc_nilpotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), ∃ nn : (Fu.Di Ha.i).La →ₗ[𝓞 E] (Fu.Di Ha.i).La, (∀ v, Ha.N v = Ha.P₀ (nn v)) ∧ (∀ v v', -(Fu.Di Ha.i).EF (nn v) v' = a.be (Ha.y v) (Ha.y v')) ∧ (∀ v, Ha.y (nn v) = 0) ∧ (∀ v, Ha.y v = 0 → nn v = 0) ∧ (∀ t, (∀ v', Ha.y v' = 0 → (Fu.Di Ha.i).EF t v' = 0) → Ha.y t = 0) ∧ ∀ ξ : Module.Dual ℤ a.D₀.X, ∃! t, ∀ v', -(Fu.Di Ha.i).EF t v' = ξ (Ha.y v') := by
  intro E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha
  letI := GlobalTheory.TorusExt.gtGroup a.D₀ ℂ
  have hadj := (Fu.Di Ha.i).adj
  have hb := (Fu.Di Ha.i).unimod
  have hle : ∀ t, (∀ v', Ha.y v' = 0 → (Fu.Di Ha.i).EF t v' = 0) → Ha.y t = 0 := fun t ht => ((Ha.riemann t).1 ht).1
  let n := GlobalTheory.KerPerp.nilTo (bar := fun x => H.bar x) hadj hb Ha.y_onto a.be_adj
  have hn : ∀ v v', -(Fu.Di Ha.i).EF (n v) v' = a.be (Ha.y v) (Ha.y v') :=
    GlobalTheory.KerPerp.neg_apply_nilTo (bar := fun x => H.bar x) hadj hb Ha.y_onto a.be_adj
  refine ⟨(Submodule.subtype _).comp n, fun v => ?_, hn, fun v => hle _ (n v).2, fun v hv => ?_, hle, fun ξ => ?_⟩
  · let ex : (Fin g → ℂ) →+ Out.GtPtF a.D₀ ℂ :=
      AddMonoidHom.mk' Ha.ex₀ fun z z' => (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 (Ha.add z z')
    have hO : Countable (𝓞 E) := Finsupp.Countable.of_moduleFinite (R := ℤ)
    have hfin := (Fu.Di Ha.i).fin
    have hL : Countable (Fu.Di Ha.i).La := Finsupp.Countable.of_moduleFinite (R := 𝓞 E)
    rw [← sub_eq_zero]
    refine GlobalTheory.eq_zero_of_forall_smul_mem_countable (Set.countable_range Ha.P₀) fun s => ?_
    obtain ⟨x, hx, hx'⟩ := ((Ha.riemann (n v)).1 (n v).2).2 s
    have hxe : x = fun z => eTwoPi (s * a.be (Ha.y v) z) := funext fun z => by
      obtain ⟨v', rfl⟩ := Ha.y_onto z
      rw [hx', ← hn]
      congr 1
      push_cast
      ring
    subst hxe
    have he : ex (s • Ha.N v) = ex (s • Ha.P₀ (n v)) :=
      GlobalTheory.TorusExt.IsTorusPtF.unique ((GlobalTheory.TorusExt.isTorusPtF_iff_isTorusPt _ _).2 (Ha.shift s v))
        ((GlobalTheory.TorusExt.isTorusPtF_iff_isTorusPt _ _).2 hx)
    have h0 : ex (s • (Ha.N v - Ha.P₀ (n v))) = 0 := by rw [smul_sub, map_sub, he, sub_self]
    obtain ⟨u, -, hu⟩ := (Ha.ker _).1 ((GlobalTheory.TorusExt.isZero_iff_eq _).2 h0)
    exact ⟨u, hu.symm⟩
  · exact GlobalTheory.KerPerp.nil_eq_zero (nn := fun v => (n v : (Fu.Di Ha.i).La)) hb.1 hn hv
  · obtain ⟨t, -, ht⟩ := GlobalTheory.KerPerp.exists_of_dual (bar := fun x => H.bar x) (hadj := hadj) (y := Ha.y) hb.2 ξ
    exact ⟨t, ht, fun t' ht' => hb.1 (LinearMap.ext fun v => neg_injective ((ht' v).trans (ht v).symm))⟩

end GlobalTheory.ArcQ
end

section

namespace GlobalTheory.ConstTan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem exists_tanRel : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (ν : Out.GtPt a.D₀ (epsR ℂ)), ∃ g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧), TanRel W ν g₁ := by
  intro _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W ν
  haveI := isLocalRing_dual ℂ⟦X⟧
  obtain ⟨gp, hw, -, -, hc, -⟩ := W.spec
  obtain ⟨g, hg⟩ := ConstPoint.exists_gtPt_genRelR (A := DualNumber ℂ⟦X⟧) globalFns_holds gp hw
    W.e.symm.toAddEquiv.toAddMonoidHom
    (fun y => by have := hc (W.e.symm y); rwa [LinearEquiv.apply_symm_apply] at this)
    (T := epsR ℂ) (spMap (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧))) (spMap constEps)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun r => dualMapR_inl _ r)).trans (spMap_comp _ _))) ν
  refine ⟨g, fun x => ?_⟩
  have := hg (W.e x)
  rw [show W.e.symm.toAddEquiv.toAddMonoidHom (W.e x) = x from W.e.symm_apply_apply x] at this
  exact this

end GlobalTheory.ConstTan
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.two_rigidified_theta_frames_on_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (A : AnArc (𝓞 E)) lin cst (w : ℂ) (y₀ : Sp ℂ ⟶ Xo.X) (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) fr (g : ℕ) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left)) (ϑ : (Fin g → ℂ) → ℂ) fr', IsFibAt A Xo.univ.t lin cst w y₀ π fr → (∀ v, e (h v) = (π v).left) → IsThetaFrameAt Xo.univ.t.PP y₀ e ϑ fr' → (∃ z, ϑ z ≠ 0) → ∀ th ∈ A.Theta 1 0, (∃ v, A.Sum 1 0 th w v ≠ 0) → ∃ (lam : ℂ) (f : A.V → ℂ), lam ≠ 0 ∧ Differentiable ℂ f ∧ (∀ v, f v ≠ 0) ∧ f 0 = 1 ∧ (∀ v j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h v) = f v * fr j v) ∧ ∀ v, A.Sum 1 0 th w v = lam * ϑ (h v) * f v := by
  first | exact @GlobalTheory.TwoFrames.two_frames | exact GlobalTheory.TwoFrames.two_frames | (intros; apply GlobalTheory.TwoFrames.two_frames <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.nonempty_projCoords_convergent_coefficients : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) , AnFin A → Φ.Rational → ∀ (N : ℕ) [NeZero N], 4 ≤ N → Nonempty (Coords Φ N) := by
  first | exact @GlobalTheory.SpanFrame.nonempty_coords | exact GlobalTheory.SpanFrame.nonempty_coords | (intros; apply GlobalTheory.SpanFrame.nonempty_coords <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.thetaSections_extend_germRings_and_span_fibres : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ (j : ℕ) [NeZero j], ∃ T' ≥ Ψ.T, ∀ (w : ℂ) (hw : Ψ.T < w.im), T' < w.im → ∃ σt : A.X → ((Fin A.gB → ℂ) → ℂ) → SecP o.t.PP.L (pullback.fst o.t.G.hom (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT)) j, (∀ α, ∀ th ∈ A.Theta j α, ∀ (q : Over.mk (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ⟶ o.t.G) (q' : Over.mk y ⟶ o.t.G) jj, spMap (Γ.R w).val.toRingHom ≫ q.left = q'.left → ⊤ ≤ q.left ⁻¹ᵁ o.t.PP.L.U jj → ((sval (σt α th) (fib q) jj : Γ.R w) : ℂ⸨X⸩) = sval (Φ.sig j α th) (fib q') jj) ∧ ∃ σ₀ : A.X → ((Fin A.gB → ℂ) → ℂ) → SecP o.t.PP.L (pullback.fst o.t.G.hom (Ψ.yw w)) j, (∀ α th (q : Over.mk (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ⟶ o.t.G) (q₀ : Over.mk (Ψ.yw w) ⟶ o.t.G) jj, q₀.left = spMap (Γ.ev w).toRingHom ≫ q.left → ⊤ ≤ q₀.left ⁻¹ᵁ o.t.PP.L.U jj → sval (σ₀ α th) (fib q₀) jj = Γ.ev w (sval (σt α th) (fib q) jj)) ∧ (∀ α, ∀ th ∈ A.Theta j α, ∀ v, HasVal (σ₀ α th) (fib (Ψ.pi w v)) (fun jj => Ψ.fr w jj v) (A.Sum j α th w v)) ∧ ∀ s : SecP o.t.PP.L (pullback.fst o.t.G.hom (Ψ.yw w)) j, ∃ (n : ℕ) (r : Fin n → ℂ) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ), (∀ i, th i ∈ A.Theta j (α i)) ∧ ∀ (q₀ : Over.mk (Ψ.yw w) ⟶ o.t.G) jj, ⊤ ≤ q₀.left ⁻¹ᵁ o.t.PP.L.U jj → sval s (fib q₀) jj = ∑ i, r i * sval (σ₀ (α i) (th i)) (fib q₀) jj := by
  first | exact @GlobalTheory.FibreFrame.sections_extend_and_span | exact GlobalTheory.FibreFrame.sections_extend_and_span | (intros; apply GlobalTheory.FibreFrame.sections_extend_and_span <;> assumption)
end

section

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace SecTransport

variable {X Z : Scheme.{0}}

abbrev valH {L : LB X} {m : ℕ} (σ : Out.H0 L m) {R : Type} [CommRing R] (x : Sp R ⟶ X) (i : L.ι) : R :=
  valR x (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i)) (σ.f (fun _ => i))

theorem exists_pull {L L' : LB X} (h : L = L') (hL : L'.IsLB) {m : ℕ} (σ : Out.H0 L m) (π : Z ⟶ X) :
    ∃ s : SecP L' π m,
      (∀ (R : Type) [CommRing R] (p : Sp R ⟶ Z) (x : Sp R ⟶ X) (i : L.ι) (i' : L'.ι), p ≫ π = x → HEq i i' →
        ⊤ ≤ x ⁻¹ᵁ L'.U i' → ArcPts.sval s p i' = valH σ x i) ∧
      ∀ (A K : Type) [CommRing A] [IsLocalRing A] [Field K] (ρ : A →+* K) (x : Sp A ⟶ X) (p : Sp K ⟶ Z)
        (τ : L.ι → A) (τ' : L'.ι → K) (f : K), p ≫ π = spMap ρ ≫ x → IsFrm L' (p ≫ π) τ' →
        (∀ i i', HEq i i' → ⊤ ≤ x ⁻¹ᵁ L.U i → τ' i' = ρ (τ i)) →
        (∀ i, ⊤ ≤ x ⁻¹ᵁ L.U i → ρ (valH σ x i) = f * ρ (τ i) ^ m) → HasVal s p τ' f := by
  subst h
  have ex : ∀ π' : Z ⟶ X, π' = π ≫ 𝟙 X → ∃ s : SecP L π' m, ∀ (R : Type) [CommRing R] (p : Sp R ⟶ Z) (x : Sp R ⟶ X)
      (i : L.ι), p ≫ π = x → ⊤ ≤ x ⁻¹ᵁ L.U i → ArcPts.sval s p i = valH σ x i := by
    rintro _ rfl
    refine ⟨DVR.pullSec L (fun _ : Fin 1 => 𝟙 X) (fun _ => (m : ℤ)) σ π, fun R _ p x i hx hi => ?_⟩
    subst hx
    exact (HolHom.valR_res p _ _ (GenericPoints.le_wchart hi)).trans (HolHom.valR_comp p π _ _).symm
  obtain ⟨s, hs⟩ := ex π (Category.comp_id _).symm
  refine ⟨s, fun R _ p x i i' hx hi hi' => ?_, fun A K _ _ _ ρ x p τ τ' f hp hτ h₁ h₂ => ?_⟩
  · obtain rfl := eq_of_heq hi
    exact hs R p x i hx hi'
  · obtain ⟨i, hi⟩ := GenericPoints.exists_chart_loc hL x
    have hi' := FormalValue.top_le_comp hi (spMap ρ)
    refine GenericPoints.hasVal_of_chart s p hτ (j := i) (hp ▸ hi') ?_
    rw [hs K p _ i hp hi', h₁ i i HEq.rfl hi, ← h₂ i hi]
    exact HolHom.valR_spMap ρ x (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i))
      (fun _ hz => Set.mem_iInter.2 fun _ => hi hz) _

end SecTransport

theorem secVal_eq_mul_sval_sig : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GlobalTheory.ArcPts.GtAn a) (Ξ : ConstPts W Λ) (Φ : GenPts Λ.A W.t gen) (j : ℕ) [NeZero j] (α : Λ.A.X) (th : (Fin Λ.A.gB → ℂ) → ℂ) (r : ℂ⸨X⸩) (σ : Out.H0 W.P.U.LG.L j), Ξ.IsGen Φ → th ∈ Λ.A.Theta j α → Ξ.Vals σ (fun v => r * Λ.A.FSum j α th v) → ∀ (q : Over.mk gen ⟶ W.t.G) (jL : W.P.U.LG.L.ι) (i : W.t.PP.L.ι), HEq jL i → ⊤ ≤ q.left ⁻¹ᵁ W.t.PP.L.U i → FormalValue.secVal (S := ℂ⸨X⸩) W.P.U.toUnifPre σ q.left jL = r * sval (Φ.sig j α th) (fib q) i := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ Φ j _ α th r σ hgen hth hval q jL i hi hq
  obtain ⟨s, hs₁, hs₂⟩ := SecTransport.exists_pull (congrArg RigLB.L W.P.bundle) W.t.PP.isLB σ
    (pullback.fst W.t.G.hom gen)
  have hfib : ∀ p : Over.mk gen ⟶ W.t.G, fib p ≫ pullback.fst W.t.G.hom gen = p.left := fun p =>
    pullback.lift_fst _ _ _
  have hv : ∀ v, HasVal s (fib (Φ.x v)) (Φ.τ v) (r * Λ.A.FSum j α th v) := fun v =>
    hs₂ ℂ⟦X⟧ ℂ⸨X⸩ (algebraMap _ _) (Ξ.x v).left (fib (Φ.x v)) (Ξ.τ v) (Φ.τ v) _ ((hfib _).trans (hgen v).1)
      (by rw [hfib]; exact Φ.frm v) (hgen v).2 (hval v)
  have hq₂ : fib q ≫ pullback.snd W.t.G.hom gen = spMap (RingHom.id _) := by
    rw [fib, pullback.lift_snd]
    exact (Spec.map_id _).symm
  have key := sval_eq_sum_of_hasVal E H _ Λ.A W.t gen Φ j s 1 (fun _ => r) (fun _ => α) (fun _ => th) (fun _ => hth)
    (fun v => by rw [Fin.sum_univ_one]; exact hv v) ℂ⸨X⸩ (RingHom.id _) (fib q) hq₂ i (by rw [hfib]; exact hq)
  rw [Fin.sum_univ_one] at key
  exact (hs₁ _ (fib q) q.left jL i (hfib q) hi hq).symm.trans key

end GlobalTheory.ArcPts
end
end
