module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFptsPull
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOfSameRatios
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentConstantDirectionSpecialisesDeriv
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle029
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
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001

@[expose] public section

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanRed
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

theorem comp_gtφT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T T' : Over (Sp R)} (ρ : T' ⟶ T)
    (b : T ⟶ D.P.A) (b' : T' ⟶ D.P.A) (hb : ρ ≫ b = b') (χ : D.X) (k : Fin 4) :
    ρ.left ≫ DegPre.gtφT D T b χ k = DegPre.gtφT D T' b' χ k := by
  subst hb
  fin_cases k
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul ρ (cP D T χ) b).trans
      (congrArg (· * (ρ ≫ b)) (comp_cP D ρ χ)))
  · exact congrArg (fun q => q.left) (comp_cP D ρ χ)
  · rfl
  · exact congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one ρ)

theorem val_eq_of_genRelR {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
    {B B₀ Y Y' : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen)
    (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K] {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt' : K → (Sp A' ⟶ B)}
    {ψ : K → (Y ⟶ B₀)} {ψ' : K → (Y' ⟶ B₀)} {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M pt' ε)}
    {u : LB.Gen (LB.LinComb M₀ ψ ε)} {u' : LB.Gen (LB.LinComb M₀ ψ' ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    (hu : u.IsGen) (hu' : u'.IsGen) {h : Sp A ⟶ Y} {h' : Sp A' ⟶ Y'} (H : GenRelR w t (LB.pullGen _ _ _ u h))
    (H' : GenRelR w t' (LB.pullGen _ _ _ u' h')) (q : Sp A ⟶ Sp A') (hq : ∀ k, q ≫ pt' k = pt k)
    {Z : Scheme.{0}} (r : Z ⟶ Sp A) (z : Z)
    (hv : ∀ J, Good M₀ z J → val u' ((r ≫ q) ≫ h') z J = val u (r ≫ h) z J) {J'} (hJ' : Good M z J') :
    val t' (r ≫ q) z J' = val t r z J' := by
  obtain ⟨J, hJ⟩ := TLinPf.idx_exists M₀ hM₀ z
  have hw' := (isGen_iff w).1 hw
  have e := CubTransport.val_pmaps (fun k => (H.1 k).trans (Category.id_comp _).symm)
    (ConstGrp.pmaps_of_genRelR hw' hM hM₀ ht (pullGen_isGen _ _ _ _ hu h) H) r hJ hJ'
  have e' := CubTransport.val_pmaps (fun k => (H'.1 k).trans (Category.id_comp _).symm)
    (ConstGrp.pmaps_of_genRelR hw' hM hM₀ ht' (pullGen_isGen _ _ _ _ hu' h') H') (r ≫ q) hJ hJ'
  rw [val_pull hJ, Category.comp_id] at e e'
  rw [hv J hJ, e] at e'
  simp only [Category.assoc r q, hq] at e'
  exact (mul_left_cancel e').symm

theorem corr_pull_of_valR {A F : Type} [CommRing A] [IsLocalRing A] [Field F] (p : A →+* F) [IsLocalHom p]
    {B : Scheme.{0}} {M : LB B} (hM : M.IsLB) {K : Type} [Fintype K] {ε : K → ℤ} {pt : K → (Sp F ⟶ B)}
    {pt' : K → (Sp A ⟶ B)} (t : LB.Gen (LB.LinComb M pt ε)) (t' : LB.Gen (LB.LinComb M pt' ε))
    (hp : ∀ k, spMap p ≫ pt' k = pt k)
    (hv : ∀ j, ⊤ ≤ LB.wchart M pt' j → p (valR (𝟙 (Sp A)) (LB.wchart M pt' j) (t'.s j).val) =
      valR (𝟙 (Sp F)) (LB.wchart M pt j) (t.s j).val) :
    LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ t' (spMap p)) t := by
  refine corr_of_val hM fun y J hJ => ?_
  obtain rfl : y = cpt F := Subsingleton.elim (α := PrimeSpectrum F) _ _
  have hc : spMap p (cpt F) = cpt A := IsLocalRing.comap_closedPoint p
  rw [val_pull hJ, Category.id_comp, val_of t' _ _ J (fun k => J (pt k)) (fun k => by rw [hp]),
    val_of t _ _ J (fun k => J (pt k)) (fun k => by rw [Category.id_comp])]
  have m : ⊤ ≤ (𝟙 (Sp F)) ⁻¹ᵁ LB.wchart M pt (fun k => J (pt k)) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun k => hJ (pt k))
  have m' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart M pt' (fun k => J (pt k)) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun k => by
      have := hJ (pt k)
      rw [← hc]
      exact (congrArg (fun q => q (cpt F) ∈ M.U (J (pt k))) (hp k)).mpr this)
  have m'' := FormalValue.top_le_comp m' (spMap p)
  have e := FormalValue.valR_spMap p _ _ m' (t'.s (fun k => J (pt k))).val
  rw [Category.comp_id] at m'' e
  refine Units.ext ?_
  exact (toStkA_valR _ _ _ m'' _).symm.trans ((congrArg _ (e.trans (hv _ m'))).trans (toStkA_valR _ _ _ m _))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GlobalTheory.ArcPts.GtAn a) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (Ξ : ConstPts W Λ) (v : epsR ℂ⟦X⟧ ⟶ W.t.G) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)), DiffHyp W (fun z => Λ.ex0 (h.symm z)) z₀ ν v → TanRel W ν g₁ → FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v.left → spMap (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom ≫ v.left = (Ξ.x 0).left := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ g h z₀ ν Ξ v g₁ hd ht hf
  haveI := isLocalRing_dual ℂ
  haveI := isLocalRing_dual ℂ⟦X⟧
  let p : DualNumber ℂ⟦X⟧ →+* ℂ⟦X⟧ := (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom
  let p₀ : DualNumber ℂ →+* ℂ := (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
  haveI : IsLocalHom p₀ := ⟨fun x hx => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hx⟩
  obtain ⟨h₁, h₂, -⟩ := hd
  have h₁' := h₁.1
  simp only [map_zero] at h₁' h₂
  have sq : spMap p ≫ spMap constEps = spMap (PowerSeries.C (R := ℂ)) ≫ spMap p₀ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun x => fst_dualMapR _ x)
  let ρ₀ : TF (R := ℂ) ℂ ⟶ epsR ℂ := Over.homMk (spMap p₀) (by
    show spMap p₀ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
      spMap (algebraMap (FractionRing ℂ) ℂ) ≫ spMap (algebraMap ℂ (FractionRing ℂ))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
    rfl)
  let ρ : selfR ⟶ epsR ℂ⟦X⟧ := Over.homMk (spMap p) (by
    show spMap p ≫ spMap (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧)) = spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl)
  have hb₀ : ρ₀ ≫ ν.b = (Λ.ex0 0).b := Over.OverMorphism.ext h₁'
  have hb : ρ ≫ g₁.b = (Ξ.g 0).b := Over.OverMorphism.ext (W.spec.1.1.hom_ext
    ((Category.assoc _ _ _).trans ((congrArg (spMap p ≫ ·) ((ht 0).1 2)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ν.b.left) sq).trans ((Category.assoc _ _ _).trans
        ((congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) h₁').trans ((Ξ.g_rel 0 0).1 2).symm))))))
    ((Over.w _).trans (Over.w _).symm))
  have hc : ∀ x, LB.Gen.Corr a.D₀.P.L _ _ _ _ (LB.pullGen a.D₀.P.L _ _ (ν.s x) (spMap p₀)) ((Λ.ex0 0).s x) :=
    fun x => corr_pull_of_valR p₀ a.D₀.P.isLB _ _ (comp_gtφT a.D₀ ρ₀ ν.b _ hb₀ x) fun j hj =>
      (congrArg p₀ (h₂ x j hj)).trans ((TrivSqZeroExt.fst_add _ _).trans (add_zero _))
  have hv : ∀ y (Z : Scheme.{0}) (r : Z ⟶ Sp ℂ⟦X⟧) (z : Z) J', Good W.P.D.toPre.P.L z J' →
      val (g₁.s y) (r ≫ spMap p) z J' = val ((Ξ.g 0).s y) r z J' := fun y Z r z J' hJ' => by
    obtain ⟨x, rfl⟩ := W.e.surjective y
    refine val_eq_of_genRelR W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB ((Ξ.g 0).isGen _) (g₁.isGen _)
      ((Λ.ex0 0).isGen x) (ν.isGen x) (Ξ.g_rel 0 x) (ht x) (spMap p) (comp_gtφT W.P.D.toPre ρ g₁.b _ hb _) r z
      (fun J hJ => ?_) hJ'
    have e : (r ≫ spMap p) ≫ spMap constEps = (r ≫ spMap (PowerSeries.C (R := ℂ))) ≫ spMap p₀ := by
      rw [Category.assoc, sq, Category.assoc]
    exact (congrArg (fun q => val (ν.s x) q z J) e).trans ((val_pull hJ _ _ _).symm.trans (val_corr hJ (hc x) _))
  let I : Ideal ℂ⟦X⟧ := (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)
  haveI : IsAdicComplete I ℂ⟦X⟧ := by
    simp only [I]
    rw [Algebra.algebraMap_self, Ideal.map_id]
    infer_instance
  refine hom_ext_of_isHausdorff I fun e => ?_
  obtain ⟨xe, hxe⟩ := FormalValue.exists_lift_thick (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}) W.t.G
    (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (ρ ≫ v).left (Over.w (ρ ≫ v)) e
  have hs : spMap ((Ideal.Quotient.mk (I ^ (e + 1))).comp p) = adicLevelι I (e + 1) ≫ spMap p := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hk : idealEps ^ (e + 1) ≤ RingHom.ker ((Ideal.Quotient.mk (I ^ (e + 1))).comp p) := fun s hs => by
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    simp only [I]
    rw [Algebra.algebraMap_self, Ideal.map_id, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (mem_idealEps_pow hs).1
  have H₁ := hf.hasCoords _ hk (xe := xe) (hxe.trans (by rw [hs, Category.assoc]; rfl))
  rw [hs] at H₁
  obtain ⟨k₁, k₂⟩ := (FormalPoint.hasCoords_iff W.P.U.toUnifPre e g₁ _ xe).1 H₁.2
  have H₂ : FormalPoint.HasCoords W.P.U.toUnifPre e (Ξ.g 0) (adicLevelι I (e + 1)) xe :=
    (FormalPoint.hasCoords_iff W.P.U.toUnifPre e _ _ xe).2
      ⟨k₁.trans ((Category.assoc _ _ _).trans (congrArg (fun q => adicLevelι I (e + 1) ≫ q.left) hb)),
        fun y z J hJ => (k₂ y z J hJ).trans (hv y _ _ z J hJ)⟩
  exact hxe.symm.trans ((Ξ.x_pt 0).comp_fstG_eq H₂)

end GlobalTheory.ConstTanRed
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ThetaOverField

theorem exists_ne_zero_iff {K : Type} [Field K] (D₀ : Out.DegPre K) (th : D₀.P.L.Sec) :
    (∃ j, th.f j ≠ 0) ↔ ThNZ th := by
  have := D₀.P.isAb.smooth
  have : IsReduced D₀.P.A.left := isReduced_scheme_of_smooth_of_isIntegrallyClosed K D₀.P.A.hom
  constructor
  · rintro ⟨j, hj⟩ y
    by_contra hn
    refine hj ((basicOpen_eq_bot_iff _).1 (eq_bot_iff.2 fun z hz => hn ⟨z, ?_, ?_⟩))
    · exact Subsingleton.elim (α := PrimeSpectrum K) _ _
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hz⟩
  · intro h
    obtain ⟨x, -, hx⟩ := h (IsLocalRing.closedPoint K)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine ⟨j, fun e => ?_⟩
    rw [e, Scheme.basicOpen_zero] at hj
    exact hj

theorem nonzero_generates : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] (D₀ : Out.DegPre K) (th : D₀.P.L.Sec), ((∃ j, th.f j ≠ 0) ↔ ThNZ th) ∧ (ThNZ th → ∀ th' : D₀.P.L.Sec, ∃! r : K, ThMul r th th') ∧ ∃ th₀ : D₀.P.L.Sec, ThNZ th₀ := by
  intro hL _ K _ D₀ th
  refine ⟨exists_ne_zero_iff D₀ th, fun h th' => ?_, ?_⟩
  · have refl : LBIso D₀.P.L (D₀.P.L.pull (𝟙 _)) :=
      LBIso.chartPull (chartPullUnpull D₀.P.L _ rfl) (chartPullId _)
        (exists_iso_linComb (F := 𝟙 D₀.P.A.left) D₀.P.isLB (fun _ : PUnit => 𝟙 _) (fun _ => 1) fun _ _ _ => rfl)
    exact GlobalTheory.SectionBaseChange.generates hL.secBaseChange D₀.P (t := 𝟙 _) (φ := 𝟙 _)
      (IsPullback.of_horiz_isIso ⟨by simp⟩) D₀.P.isLB refl th h th'
  · obtain ⟨b, hb, -⟩ := GlobalTheory.KeyOnPol.exists_generator hL.secBaseChange D₀.P
    exact ⟨b, hb⟩

end GlobalTheory.ThetaOverField
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.LevelRespect

open GlobalTheory.FibrePull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]

theorem valR_zero {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) : valR x U 0 = 0 := by
  unfold valR
  split_ifs
  · rw [map_zero, map_zero]
  · rfl

theorem sval_of_zero {A : Type} [CommRing A] {X Z : Scheme.{0}} {L : LB Z} {π : X ⟶ Z} {n : ℕ} (u : SecP L π n)
    (hu : ∀ i, u.f i = 0) (x : Sp A ⟶ X) (j : L.ι) : ArcPts.sval u x j = 0 :=
  (congrArg (valR x _) (hu fun _ => j)).trans (valR_zero _ _)

section One
variable {S : Scheme.{0}} {t : SAB H S} {F : Type} [Field F] {V : Type} [AddCommGroup V] {act : 𝓞 E → V → V}
  {I : ℕ → Type} {φ : ∀ j, I j → V → F} {y : Sp F ⟶ S}

omit [StarRing (𝓞 E)] in
theorem fib_fst (a : Over.mk y ⟶ t.G) : fib a ≫ pullback.fst t.G.hom y = a.left := pullback.lift_fst _ _ _


omit [StarRing (𝓞 E)] in
theorem sval_eq_sum (Θ : FPts act t y φ) {k : ℕ} (hk : 1 ≤ k) (s : SecP t.PP.L (pullback.fst t.G.hom y) k) {n : ℕ}
    (r : Fin n → F) (i : Fin n → I k) (hs : ∀ v, HasVal s (fib (Θ.x v)) (Θ.τ v) (∑ a, r a * φ k (i a) v))
    (q : Over.mk y ⟶ t.G) (j : t.PP.L.ι) (hj : ⊤ ≤ q.left ⁻¹ᵁ t.PP.L.U j) :
    ArcPts.sval s (fib q) j = ∑ a, r a * ArcPts.sval (Θ.sig k (i a)) (fib q) j := by
  have key : ∀ (q : Over.mk y ⟶ t.G) (j : t.PP.L.ι), ⊤ ≤ (fib q ≫ pullback.fst t.G.hom y) ⁻¹ᵁ t.PP.L.U j →
      ArcPts.sval (FibreFrame.comb (pullback.snd t.G.hom y) (Fin.cons (-1) r : Fin (n + 1) → F)
        (Fin.cons s fun a => Θ.sig k (i a)) : SecP t.PP.L (pullback.fst t.G.hom y) k) (fib q) j =
      ∑ a, r a * ArcPts.sval (Θ.sig k (i a)) (fib q) j - ArcPts.sval s (fib q) j := fun q j hj => by
    rw [FibreFrame.sval_comb _ _ _ (RingHom.id F) (fib q)
      ((pullback.lift_snd _ _ _).trans (Spec.map_id _).symm) hj, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, RingHom.id_apply]
    ring
  have h0 := Θ.sep k hk _ fun v j hj => by
    rw [key _ j hj, hs v j hj, Finset.sum_mul, MulZeroClass.zero_mul, sub_eq_zero]
    exact Finset.sum_congr rfl fun a _ => by rw [Θ.val k hk (i a) v j hj, _root_.mul_assoc]
  have e := key q j (by rw [fib_fst]; exact hj)
  rw [sval_of_zero _ h0] at e
  exact (sub_eq_zero.1 e.symm).symm


omit [StarRing (𝓞 E)] in
theorem sval_lev (Θ : FPts act t y φ) {k : ℕ} (hk : 1 ≤ k) {p : Over.mk y ⟶ t.G} {ψ : I k → V → F}
    (hp : Θ.Lev k p ψ) (s : SecP t.PP.L (pullback.fst t.G.hom y) k) {n : ℕ}
    (r : Fin n → F) (i : Fin n → I k) (hs : ∀ v, HasVal s (fib (Θ.x v)) (Θ.τ v) (∑ a, r a * φ k (i a) v))
    (i₀ : I k) (z : V) (j : t.PP.L.ι) (hj : ⊤ ≤ (Θ.x z * p).left ⁻¹ᵁ t.PP.L.U j) :
    ArcPts.sval s (fib (Θ.x z * p)) j * ψ i₀ z =
      ArcPts.sval (Θ.sig k i₀) (fib (Θ.x z * p)) j * ∑ a, r a * ψ (i a) z := by
  rw [sval_eq_sum Θ hk s r i hs _ j hj, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [_root_.mul_assoc, hp.2.2 (i a) i₀ z j hj]; ring

end One

theorem level_eq (h₁ : Out.Laws) (h₂ : Out.Laws2) {D : Datum H} {l : Level H} {B : Type} [CommRing B] {bb : Base l B}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l bb s) {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' o.t f)
    (w : LB.Iso t'.PP.L (o.t.PP.L.pull m.φ)) (hw : w.IsGen) {F : Type} [Field F] [IsAlgClosed F] [CharZero F]
    {V : Type} [AddCommGroup V] {act : 𝓞 E → V → V} {I : ℕ → Type} {φ : ∀ j, I j → V → F} (y' : Sp F ⟶ S')
    (y : Sp F ⟶ S) (hy : y' ≫ f = y) (Θ' : FPts act t' y' φ) (Θ : FPts act o.t y φ) {k : ℕ} (hk : 1 ≤ k)
    {ψ : I k → V → F} {p' : Over.mk y' ⟶ t'.G} {p : Over.mk y ⟶ o.t.G}
    (rel : ∀ v, (Θ'.x v).left ≫ m.φ = (Θ.x v).left ∧ ∀ j j',
        ⊤ ≤ (Θ'.x v).left ⁻¹ᵁ (LB.div (o.t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') →
        Θ.τ v j = valR (Θ'.x v).left _ (w.s (fun _ => j, j')).val * Θ'.τ v j')
    (l' : Θ'.Lev k p' ψ) (l₀ : Θ.Lev k p ψ) : p'.left ≫ m.φ = p.left := by
  subst hy
  have hL := o.t.PP.isLB
  have hL' := t'.PP.isLB
  let ρ : (Over.mk y' ⟶ t'.G) →* (Over.mk (y' ≫ f) ⟶ o.t.G) := pushHom m.cart (Over.mk y')
  have ρl : ∀ x, (ρ x).left = x.left ≫ m.φ := fun _ => rfl
  have hx : ∀ v, ρ (Θ'.x v) = Θ.x v := fun v => Over.OverMorphism.ext (rel v).1
  have sq : IsPullback (pullback.fst t'.G.hom y' ≫ m.φ) (pullback.snd t'.G.hom y') o.t.G.hom (y' ≫ f) :=
    (IsPullback.of_hasPullback t'.G.hom y').paste_horiz m.cart.1
  let h : pullback t'.G.hom y' ⟶ pullback o.t.G.hom (y' ≫ f) := sq.isoPullback.hom
  have hp : pullback.fst t'.G.hom y' ≫ m.φ = h ≫ pullback.fst o.t.G.hom (y' ≫ f) := sq.isoPullback_hom_fst.symm
  have fh : ∀ a : Over.mk y' ⟶ t'.G, fib a ≫ h = fib (ρ a) := fun a => pullback.hom_ext
    (by rw [Category.assoc, ← hp, ← Category.assoc, fib_fst]; exact (pullback.lift_fst _ _ _).symm)
    (by rw [Category.assoc, sq.isoPullback_hom_snd]
        exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm)
  have hv : ∀ {a : SecP t'.PP.L (pullback.fst t'.G.hom y') k} {b : SecP o.t.PP.L (pullback.fst o.t.G.hom (y' ≫ f)) k},
      TransportedAlt w a b h → ∀ v c, HasVal a (fib (Θ'.x v)) (Θ'.τ v) c ↔ HasVal b (fib (Θ.x v)) (Θ.τ v) c := fun T v c => by
    rw [← hx v, ← fh]
    exact T.hasVal_iff hL hL' hp _ (by
      rw [fib_fst]; exact fun j j' hj hj' => (rel v).2 j j' ((le_div_iff _ j j').2 ⟨hj, hj'⟩)) c
  obtain ⟨-, i₀, i₁, hgood, z₀, hz₀⟩ := l₀.2.1
  have main := LevelUnique.torsion_eq_of_same_ratios h₁ h₂ E H D l B bb S s o F (y' ≫ f) V Θ.x k (ρ p') p
    (fun z => ψ i₀ z ≠ 0) (Θ.sig k i₁) hk (by rw [← map_pow, l'.1, map_one]) l₀.1
    (fun n hn u hu => Θ.sep n hn u fun v j hj => by
      rw [MulZeroClass.zero_mul]; exact hu v j (by rwa [fib_fst] at hj))
    (by
      by_contra hne
      push_neg at hne
      obtain ⟨j, hj⟩ := exists_chart_pt hL (Θ.x z₀).left
      have e := Θ.val k hk i₁ z₀ j (by rw [fib_fst]; exact hj)
      rw [sval_of_zero _ hne] at e
      exact mul_ne_zero hz₀ (pow_ne_zero _ ((Θ.frm z₀).1 j hj).ne_zero) e.symm)
    (fun v j hj hne => hgood v fun h0 => hne (by
      rw [Θ.val k hk i₁ v j (by rw [fib_fst]; exact hj), h0, MulZeroClass.zero_mul]))
    (fun z hz t₁ t₂ j j₂ hj hj₂ => by
      obtain ⟨j', hj'⟩ := exists_chart_pt hL' (Θ'.x z * p').left
      have hj₁ : ⊤ ≤ ((fib (Θ'.x z * p') ≫ pullback.fst t'.G.hom y') ≫ m.φ) ⁻¹ᵁ o.t.PP.L.U j := by
        rw [fib_fst, ← ρl, map_mul, hx]; exact hj
      have hj₃ : ⊤ ≤ (fib (Θ'.x z * p') ≫ pullback.fst t'.G.hom y') ⁻¹ᵁ t'.PP.L.U j' := by rw [fib_fst]; exact hj'
      have both : ∀ b : SecP o.t.PP.L (pullback.fst o.t.G.hom (y' ≫ f)) k, ∃ c : F,
          ArcPts.sval b (fib (Θ.x z * ρ p')) j * ψ i₀ z =
            wv w (fib (Θ'.x z * p') ≫ pullback.fst t'.G.hom y') j j' ^ k *
              ArcPts.sval (Θ'.sig k i₀) (fib (Θ'.x z * p')) j' * c ∧
          ArcPts.sval b (fib (Θ.x z * p)) j₂ * ψ i₀ z = ArcPts.sval (Θ.sig k i₀) (fib (Θ.x z * p)) j₂ * c := fun b => by
        obtain ⟨n, r, i, hi⟩ := Θ.span k hk b
        obtain ⟨a, ha⟩ := ConstFam.exists_secThrough (K := Fin 1) (φ' := fun _ => pullback.fst t'.G.hom y')
          hw hL hL' (fun _ => hp) b
        refine ⟨∑ a, r a * ψ (i a) z, ?_, sval_lev Θ hk l₀ b r i hi i₀ z j₂ hj₂⟩
        rw [← hx, ← map_mul, ← fh, TransportedAlt.sval_eq hp ha _ hj₁ hj₃, _root_.mul_assoc,
          sval_lev Θ' hk l' a r i (fun v => (hv ha v _).2 (hi v)) i₀ z j' hj', _root_.mul_assoc]
      obtain ⟨c₁, a₁, b₁⟩ := both t₁
      obtain ⟨c₂, a₂, b₂⟩ := both t₂
      refine mul_right_cancel₀ (mul_ne_zero hz hz) ?_
      rw [_root_.mul_mul_mul_comm, a₁, b₂, _root_.mul_mul_mul_comm (ArcPts.sval t₂ _ j), a₂, b₁]
      ring)
  exact congrArg (fun q => q.left) main

theorem level_pt_eq : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (s : Sp F ⟶ Sp B) (o₁ o₂ : Obj D l bb s) (Θ₁ : FPts act o₁.t (𝟙 _) φ) (Θ₂ : FPts act o₂.t (𝟙 _) φ) (m : SABMap o₁.t o₂.t (𝟙 _)) (w : LB.Iso o₁.t.PP.L (o₂.t.PP.L.pull m.φ)) (k : ℕ) (ψ : I k → V → F) (p₁ : Over.mk (𝟙 (Sp F)) ⟶ o₁.t.G) (p₂ : Over.mk (𝟙 (Sp F)) ⟶ o₂.t.G), 1 ≤ k → w.IsGen → (∀ v, (Θ₁.x v).left ≫ m.φ = (Θ₂.x v).left ∧ ∀ j j', ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull m.φ) o₁.t.PP.L).U (fun _ => j, j') → Θ₂.τ v j = valR (Θ₁.x v).left _ (w.s (fun _ => j, j')).val * Θ₁.τ v j') → Θ₁.Lev k p₁ ψ → Θ₂.Lev k p₂ ψ → p₁.left ≫ m.φ = p₂.left := by
  intro h₁ h₂ E _ _ _ H _ D l B _ bb F _ _ _ V _ act I φ s o₁ o₂ Θ₁ Θ₂ m w k ψ p₁ p₂ hk hw rel l₁ l₂
  exact level_eq h₁ h₂ o₂ m w hw (𝟙 _) (𝟙 _) (Category.id_comp _) Θ₁ Θ₂ hk rel l₁ l₂

end GlobalTheory.LevelRespect
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.tangent_constant_direction_specialises_deriv : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ (z₀ : A.V) (ν : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback o.t.G.hom y), Φ.IsTan z₀ ν → ∃ T' ≥ Ψ.T, ∀ (w : ℂ) (hw : Ψ.T < w.im), T' < w.im → ∃ νt : Sp (DualNumber (Γ.R w)) ⟶ o.t.G.left, νt ≫ o.t.G.hom = spMap (algebraMap (Γ.R w) (DualNumber (Γ.R w))) ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT ∧ (∀ ρ : DualNumber (Γ.R w) →+* DualNumber ℂ⸨X⸩, (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (r : ℂ⸨X⸩)) → ρ DualNumber.eps = DualNumber.eps → spMap ρ ≫ νt = ν ≫ pullback.fst _ _) ∧ ∀ ρ : DualNumber (Γ.R w) →+* DualNumber ℂ, (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Γ.ev w r)) → ρ DualNumber.eps = DualNumber.eps → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ ≫ νt = (Ψ.pi w 0).left ∧ ∀ (W : o.t.G.left.Opens) (f : Γ(o.t.G.left, W)), ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ W → TrivSqZeroExt.snd (valR (spMap ρ ≫ νt) W f) = fderiv ℂ (fun v => valAt' (Ψ.pi w v).left W f) 0 z₀ := by
  first | exact @GlobalTheory.SpecTangent.spec_tangent | exact GlobalTheory.SpecTangent.spec_tangent | (intros; apply GlobalTheory.SpecTangent.spec_tangent <;> assumption)
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts
open ConstGrp

theorem constPts_add_smul : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GlobalTheory.ArcPts.GtAn a) (Ξ : ConstPts W Λ) , (∀ v v', Ξ.x (v + v') = Ξ.x v * Ξ.x v') ∧ ∀ (e : 𝓞 E) v, Ξ.x (Λ.A.actV e v) = Ξ.x v ≫ W.t.act.act e := by
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ
  obtain ⟨hadd, -, hact⟩ := GlobalTheory.T.analyticDictionaryExp_additive_surjective_linear hL hL2 E H D l c O β b a Λ
  have hG := hL.globalFns
  obtain ⟨gp, hw, -, ho, -, -⟩ := W.spec
  have hw' := (isGen_iff _).1 hw
  have hb : ∀ v, (Ξ.g v).b.left ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.ex0 v).b.left :=
    fun v => (Ξ.g_rel v 0).1 2
  let ρ : Over.mk (selfR.hom ≫ spMap (PowerSeries.C (R := ℂ))) ⟶ Out.TF (R := ℂ) ℂ :=
    Over.homMk (spMap (PowerSeries.C (R := ℂ))) (by
      rw [← Over.w (Λ.ex0 0).b]
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (hb 0).symm).trans ?_)
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) gp.1.w).trans ?_)
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w (Ξ.g 0).b)))
  have r : ∀ v, Rel gp W.w W.e ρ (Ξ.g v) (Λ.ex0 v) := fun v =>
    rel_of_pmaps (fun x => (Ξ.g_rel v x).1) fun x =>
      pmaps_of_genRelR hw' W.P.D.toPre.P.isLB a.D₀.P.isLB ((Ξ.g v).isGen _)
        (DVR.pullGen_isGen _ _ _ _ ((Λ.ex0 v).isGen x) _) (Ξ.g_rel v x)
  have hc : ∀ x, pushHom gp selfR (DVR.cP W.P.D.toPre selfR (W.e x)) = ρ ≫ DVR.cP a.D₀ _ x := fun x =>
    Over.OverMorphism.ext ((Ξ.g_rel 0 x).1 1)
  have : IsHausdorff ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
    rw [Algebra.algebraMap_self, Ideal.map_id]
    infer_instance
  refine ⟨fun v v' => (Ξ.x_pt (v + v')).unique (((Ξ.x_pt v).mul hG (Ξ.x_pt v')
    (isAdd_of_rel hG hw' hc W.e.surjective (r v) (r v') (r (v + v')) (hadd v v')))), fun e v => ?_⟩
  have hs := hact e v
  clear hact hadd
  have r₁ := r v
  have r₂ := r (Λ.A.actV e v)
  have x₁ := Ξ.x_pt v
  have x₂ := Ξ.x_pt (Λ.A.actV e v)
  letI := H.starRing
  exact x₂.unique (x₁.smul hG W.P.lin e
    (isSmulPt_of_rel hG hw' hc W.e.surjective W.P.oD a.oa (fun s x => W.e.map_smul s x) ho e r₁ r₂ hs))

end GlobalTheory.ArcPts
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

theorem _root_.GlobalTheory.T.tangentValue_eq_jet_constantExpansion : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GlobalTheory.ArcPts.GtAn a) (Ξ : ConstPts W Λ) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) (v : Sp (DualNumber ℂ⟦X⟧) ⟶ W.t.G.left) (z : Λ.A.V) (jL : W.P.U.LG.L.ι) (jM : W.P.D.toPre.P.L.ι) (ω φ₁ τ : DualNumber ℂ⟦X⟧) (j : ℕ) (σ : Out.H0 W.P.U.LG.L j), FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v → ⊤ ≤ v ⁻¹ᵁ W.P.U.LG.L.U jL → ⊤ ≤ FormalValue.basePt g₁ ⁻¹ᵁ W.P.D.toPre.P.L.U jM → IsUnit ω → IsUnit τ → ω * τ = (FormalValue.tau W.P.U.toUnifPre idealEps v jL jM).val * φ₁ → (∀ (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (f : W.P.D.toPre.SecB j (W.e (Λ.ε α))) (r : ℂ⟦X⟧) jf jt, IsConstMul W j (Λ.ε α) s₀ f r → FormalValue.CohCharts g₁ (W.e (Λ.ε α)) jM jf jt → ω ^ j * (FormalValue.famVal g₁ f jf * FormalValue.coordVal g₁ (W.e (Λ.ε α)) jt) = TrivSqZeroExt.inl r * constEps (jet (fun u : Λ.A.V => Λ.fn j α s₀ u.2 * eTwoPi (u.1 α)) z) * φ₁ ^ j) → HasConstExp W σ → ∃ (x : Λ.A.V → ℂ⟦X⟧) (y : DualNumber ℂ⟦X⟧), IsJet x z y ∧ (∀ u k, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k → FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left k = x u * Ξ.τ u k ^ j) ∧ FormalValue.secVal W.P.U.toUnifPre σ v jL = y * τ ^ j := by
  first | exact @GlobalTheory.ConstTanExp.main | exact GlobalTheory.ConstTanExp.main | (intros; apply GlobalTheory.ConstTanExp.main <;> assumption)
end
