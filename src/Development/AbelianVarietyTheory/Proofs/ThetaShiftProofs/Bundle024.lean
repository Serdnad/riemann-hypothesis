module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QkRelQkScaleEquiv
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle022
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle021
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle012
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ArcQBC

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

section Bundles

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
  {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}

theorem pmaps_unique (hL : L.IsLB) {a a' : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)}
    (H : PMaps w φ' φ ε a t h) (H' : PMaps w φ' φ ε a' t h) : a = a' := by
  obtain ⟨s⟩ := a
  obtain ⟨s'⟩ := a'
  refine congrArg _ (funext fun q => unit_ext fun y hy => ?_)
  choose p hp using fun k => exists_chart hL (F (φ' k y))
  exact mul_left_cancel ((H _ (𝟙 _) y p q hp (Set.mem_iInter.1 hy)).symm.trans
    (H' _ (𝟙 _) y p q hp (Set.mem_iInter.1 hy)))

theorem pmaps_of_val (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} (ha : a.IsGen) (ht : t.IsGen)
    (H : ∀ (y : Y') J J', Good L y J → Good L' y J' → val t (𝟙 _ ≫ h) y J =
      (∏ k, ConstFam.wVal w y J J' (𝟙 _ ≫ φ' k) ^ ε k) * val a (𝟙 _) y J') : PMaps w φ' φ ε a t h := by
  obtain ⟨a', ha', H'⟩ := DegPull.exists_pmaps ((isGen_iff w).1 hw) hL hL' h hψ t ht
  obtain rfl : a = a' := by
    obtain ⟨s⟩ := a
    obtain ⟨s'⟩ := a'
    refine congrArg _ (funext fun q => unit_ext fun y hy => ?_)
    obtain ⟨J, hJ⟩ := DegPull.exists_good' hL y
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' hL' y
    have e := mul_left_cancel ((H y J J' hJ hJ').symm.trans (ConstFam.pmaps_val hψ H' (𝟙 _) hJ hJ'))
    exact (gen_trans ha (𝟙 _) y hy (hJ'.mem _ (𝟙 _))).trans ((congrArg _ e).trans
      (gen_trans ha' (𝟙 _) y hy (hJ'.mem _ (𝟙 _))).symm)
  exact H'

theorem exists_pullSec (F : X' ⟶ X) (s : LB.Sec L) : ∃ θ : LB.Sec (L.pull F), PullSec F s θ := by
  have le : ∀ j, (L.pull F).U j ≤ F ⁻¹ᵁ L.U (j PUnit.unit) := fun j y hy => mem_pull.1 hy
  refine ⟨⟨fun j => (F.appLE _ _ (le j)).hom (s.f (j PUnit.unit)), fun j j' => fn_ext fun y hy => ?_⟩, fun j h => rfl⟩
  refine ((gs_res _ y _ hy _).trans ((gs_appLE F _ _ (le j) (𝟙 _) y hy.1 _).trans
    (gs_compat s (𝟙 _ ≫ F) y (le j hy.1) (le j' hy.2)))).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val (gm_pull_g L F (𝟙 _) y j j' hy.1 hy.2)))
        ((gs_res _ y _ hy _).trans (gs_appLE F _ _ (le j') (𝟙 _) y hy.2 _)))))

theorem through_iff (s : LB.Sec L) (s' : LB.Sec L') :
    (∃ θ : LB.Sec (L.pull F), PullSec F s θ ∧ IsoMaps w s' θ) ↔
      ∀ (y : X') j k, F y ∈ L.U j → y ∈ L'.U k →
        gs (𝟙 _ ≫ F) y _ (s.f j) = (gw w (𝟙 _) y j k).val * gs (𝟙 _) y _ (s'.f k) := by
  have le : ∀ j, (L.pull F).U j ≤ F ⁻¹ᵁ L.U (j PUnit.unit) := fun j y hy => mem_pull.1 hy
  have key : ∀ θ : LB.Sec (L.pull F), PullSec F s θ → ∀ (y : X') (j : PUnit → L.ι), y ∈ (L.pull F).U j →
      gs (𝟙 _) y _ (θ.f j) = gs (𝟙 _ ≫ F) y _ (s.f (j PUnit.unit)) := fun θ hθ y j hy => by
    rw [hθ j (le j)]
    exact gs_appLE F _ _ (le j) (𝟙 _) y hy _
  constructor
  · rintro ⟨θ, hθ, hm⟩ y j k hj hk
    have hy : (𝟙 X' : X' ⟶ X') y ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    refine (key θ hθ y (fun _ => j) hy.1).symm.trans ((gs_res _ y _ hy _).symm.trans
      ((congrArg (gs (𝟙 _) y _) (hm (fun _ => j) k)).trans ((gs_mul _ y _ hy _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _)))))
  · intro H
    obtain ⟨θ, hθ⟩ := exists_pullSec F s
    refine ⟨θ, hθ, fun (j : PUnit → L.ι) k => fn_ext fun y hy => ?_⟩
    exact (gs_res _ y _ hy _).trans ((key θ hθ y j hy.1).trans ((H y _ k (le j hy.1) hy.2).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _))))))

end Bundles

section Data

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {f : A →+* A'} {D₀ : DegPre A}
  {D₁ : DegPre A'} (p : IsPullDeg f D₀ D₁)

theorem letBC_iff (ν : GtPt D₀ (epsR A)) (ν₁ : GtPt D₁ (epsR A')) :
    LetBC p ν ν₁ ↔ ν₁.b.left ≫ prj p = spMap (dualMap f) ≫ ν.b.left ∧ ∀ χ,
      (∀ i, DegPre.gtφT D₁ (epsR A') ν₁.b χ i ≫ prj p = spMap (dualMap f) ≫ DegPre.gtφT D₀ (epsR A) ν.b (p.xe χ) i) ∧
      PMaps p.w _ _ DegPre.gtε (ν₁.s χ) (ν.s (p.xe χ)) (spMap (dualMap f)) :=
  and_congr Iff.rfl (forall_congr' fun χ =>
    ⟨fun ⟨hψ, hm⟩ => ⟨hψ, (maps_iff p.w _ _ _ (ν₁.s χ) (ν.s (p.xe χ)) _ _
      (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1 hm⟩,
    fun ⟨hψ, hm⟩ => ⟨hψ, (maps_iff p.w _ _ _ (ν₁.s χ) (ν.s (p.xe χ)) _ _
      (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).2 hm⟩⟩)

omit [IsDomain A] [IsDomain A'] in
theorem dual_base (f : A →+* A') : spMap (dualMap f) ≫ (epsR A).hom = (epsR A').hom ≫ spMap f := by
  refine (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap ?_) (spMap_comp _ _))
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

omit [IsDomain A] [IsDomain A'] in
theorem dual_fst (f : A →+* A') : spMap (TrivSqZeroExt.fstHom A' A' A').toRingHom ≫ spMap (dualMap f) =
    spMap f ≫ spMap (TrivSqZeroExt.fstHom A A A).toRingHom := by
  refine (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap ?_) (spMap_comp _ _))
  refine RingHom.ext fun x => ?_
  simp [dualMap]

theorem existsUnique_letBC (hG : GlobalFnsSt) (ν : GtPt D₀ (epsR A)) : ∃! ν', LetBC p ν ν' := by
  have gp := pull_grp p
  obtain ⟨g, hg⟩ := ConstPoint.exists_gtPt_through hG gp p.w_gen p.xe.toAddMonoidHom p.c_pr
    (T := epsR A) (T' := epsR A') (spMap (dualMap f)) (dual_base f) ν
  refine existsUnique_of_exists_of_unique ⟨g, (letBC_iff p _ _).2 ⟨(hg 0).1 2, fun χ => ⟨(hg χ).1,
    pmaps_of_val p.w_gen D₀.P.isLB D₁.P.isLB (hg χ).1 (g.isGen χ) (ν.isGen _) fun y J J' hJ hJ' =>
      (hg χ).2 _ (𝟙 _) y J J' hJ hJ'⟩⟩⟩ fun g₁ g₂ h₁ h₂ => ?_
  rw [letBC_iff] at h₁ h₂
  obtain ⟨b₁, s₁, _, _, _⟩ := g₁
  obtain ⟨b₂, s₂, _, _, _⟩ := g₂
  obtain rfl : b₁ = b₂ :=
    Over.OverMorphism.ext (gp.1.hom_ext (h₁.1.trans h₂.1.symm) ((Over.w b₁).trans (Over.w b₂).symm))
  obtain rfl : s₁ = s₂ := funext fun χ => pmaps_unique D₀.P.isLB (h₁.2 χ).2 (h₂.2 χ).2
  rfl

theorem gtTanR_of_letBC (hG : GlobalFnsSt) {ν : GtPt D₀ (epsR A)} {ν' : GtPt D₁ (epsR A')} (h : LetBC p ν ν')
    (ht : GtTanR ν) : GtTanR ν' := by
  have gp := pull_grp p
  rw [letBC_iff] at h
  obtain ⟨g₀, ⟨z₁, z₂⟩, q₁, q₂⟩ := ht
  obtain ⟨g, hg⟩ := ConstPoint.exists_gtPt_through hG gp p.w_gen p.xe.toAddMonoidHom p.c_pr
    (T := Over.mk (𝟙 (Sp A))) (T' := Over.mk (𝟙 (Sp A'))) (spMap f)
    ((Category.comp_id _).trans (Category.id_comp _).symm) g₀
  let ρ : Over.mk (𝟙 (Sp A')) ⟶ epsR A' := Over.homMk (spMap (TrivSqZeroExt.fstHom A' A' A').toRingHom) (by
    refine (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap ?_) (Spec.map_id _))
    exact RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl])
  have hb : g.b.left ≫ prj p = spMap f ≫ g₀.b.left := (hg 0).1 2
  have b₀ : g.b = 1 := Over.OverMorphism.ext (gp.1.hom_ext (hb.trans (by
    rw [z₁]; exact ((hg 0).1 3).symm)) ((Over.w _).trans (Over.w _).symm))
  have b₁ : g.b = ρ ≫ ν'.b := Over.OverMorphism.ext (gp.1.hom_ext (hb.trans (by
    rw [q₁, ← Category.assoc, ← dual_fst, Category.assoc, ← h.1]
    exact (Category.assoc _ _ _).symm)) ((Over.w _).trans (Over.w _).symm))
  have v : ∀ χ (y : (Over.mk (𝟙 (Sp A'))).left) J J', Good D₀.P.L y J → Good D₁.P.L y J' → val (g₀.s (p.xe χ)) (𝟙 _ ≫ spMap f) y J =
      (ConstFam.wVal p.w y J J' (cP D₁ (Over.mk (𝟙 (Sp A'))) χ * (𝟙 _ ≫ g.b)).left)⁻¹ *
        ConstFam.wVal p.w y J J' (cP D₁ (Over.mk (𝟙 (Sp A'))) χ).left * ConstFam.wVal p.w y J J' (𝟙 _ ≫ g.b).left *
        (ConstFam.wVal p.w y J J' (1 : Over.mk (𝟙 (Sp A')) ⟶ D₁.P.A).left)⁻¹ * val (g.s χ) (𝟙 _) y J' :=
    fun χ y J J' hJ hJ' => ((hg χ).2 _ (𝟙 _) y J J' hJ hJ').trans (congrArg (· * _)
      (FormalPoint.prod_gtφT (𝟙 (Over.mk (𝟙 (Sp A')))) g.b χ (ConstFam.wVal p.w y J J')))
  refine ⟨g, ⟨b₀, fun χ => corr_of_val D₁.P.isLB fun y J' hJ' => ?_⟩, congrArg (fun q => q.left) b₁,
    fun χ => corr_of_val D₁.P.isLB fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := DegPull.exists_good' D₀.P.isLB y
    have e := ((val_corr hJ (z₂ _) _).trans (val_one _)).symm.trans (v χ y J J' hJ hJ')
    have b₂ : 𝟙 _ ≫ g.b = 1 := (Category.id_comp _).trans b₀
    rw [b₂, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul] at e
    exact e.symm.trans (val_one _).symm
  · obtain ⟨J, hJ⟩ := DegPull.exists_good' D₀.P.isLB y
    have e := ((val_corr hJ (q₂ _) _).trans (val_pull hJ _ _ _)).symm.trans (v χ y J J' hJ hJ')
    have b₂ : 𝟙 _ ≫ g.b = ρ ≫ ν'.b := (Category.id_comp _).trans b₁
    have e' := (ConstFam.pmaps_val (h.2 χ).1 (h.2 χ).2 ρ.left hJ hJ').trans (congrArg (· * _)
      (FormalPoint.prod_gtφT ρ ν'.b χ (ConstFam.wVal p.w y J J')))
    rw [b₂] at e
    have m : ρ.left ≫ spMap (dualMap f) = (𝟙 _ ≫ spMap f) ≫ spMap (TrivSqZeroExt.fstHom A A A).toRingHom :=
      (dual_fst f).trans (by rw [Category.id_comp])
    have e'' := mul_left_cancel (e.symm.trans ((congrArg (fun r => val (ν.s (p.xe χ)) r y J) m).symm.trans e'))
    exact e''.trans ((congrArg (fun r => val (ν'.s χ) r y J') (Category.id_comp _).symm).trans
      (val_pull hJ' _ _ _).symm)

theorem existsUnique_thBC (th : D₀.P.L.Sec) : ∃! th', ThBC p th th' := by
  obtain ⟨s, hs⟩ := sec_pull_down ((isGen_iff p.w).1 p.w_gen) D₀.P.isLB D₁.P.isLB th
  refine existsUnique_of_exists_of_unique ⟨s, (through_iff _ _).2 fun y j k hj hk => hs _ (𝟙 _) y j k hj hk⟩
    fun s₁ s₂ h₁ h₂ => ?_
  have k₁ := (through_iff _ _).1 h₁
  have k₂ := (through_iff _ _).1 h₂
  obtain ⟨f₁, _⟩ := s₁
  obtain ⟨f₂, _⟩ := s₂
  obtain rfl : f₁ = f₂ := funext fun k => fn_ext fun y hy => by
    obtain ⟨j, hj⟩ := exists_chart D₀.P.isLB (prj p y)
    exact (Units.mul_right_inj _).1 ((k₁ y j k hj hy).symm.trans (k₂ y j k hj hy))
  rfl

theorem thNZ_of_thBC {th : D₀.P.L.Sec} {th' : D₁.P.L.Sec} (h : ThBC p th th') (hn : ThNZ th) : ThNZ th' := by
  intro y
  obtain ⟨x₀, hx₀, hm⟩ := hn (spMap f y)
  obtain ⟨x, hx₁, hx₂⟩ := Scheme.exists_preimage_of_isPullback (pull_grp p).1 x₀ y hx₀
  obtain rfl : prj p x = x₀ := hx₁
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  have hj' : prj p x ∈ D₀.P.L.U j := D₀.P.A.left.basicOpen_le _ hj
  obtain ⟨k, hk⟩ := exists_chart D₁.P.isLB x
  have u₀ : IsUnit (gs (𝟙 _) (prj p x) _ (th.f j)) := by
    rw [gs_eq (𝟙 _) (prj p x) _ hj']; exact (D₀.P.A.left.mem_basicOpen _ _ hj').1 hj
  have u₁ : IsUnit (gs (prj p) x _ (th.f j)) := by rw [gs_stalkMap (prj p) x _ hj']; exact u₀.map _
  have e := (through_iff _ _).1 h x j k hj' hk
  rw [Category.id_comp] at e
  have u₂ := isUnit_of_mul_isUnit_right (e ▸ u₁)
  refine ⟨x, hx₂, TopologicalSpace.Opens.mem_iSup.2 ⟨k, (D₁.P.A.left.mem_basicOpen _ _ hk).2 ?_⟩⟩
  rwa [gs_eq _ _ _ hk] at u₂

end Data

theorem baseChanges : Out.Laws → Out.Laws2 → Out.UnifBaseChangeSt → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A A' : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing A'] [IsDomain A'] [IsPrincipalIdealRing A'] (b : O →+* A) (a : ArcIn Dw l β A b) (f : A →+* A'), Function.Injective f → ∀ b' : O →+* A', b' = f.comp b → (∃ (a' : ArcIn Dw l β A' b') (p : Out.IsPullDeg f a.D₀ a'.D₀), InBC f a a' p) ∧ ∀ (a' : ArcIn Dw l β A' b') (p : Out.IsPullDeg f a.D₀ a'.D₀), InBC f a a' p → (∀ (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ), ∃ W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ), WitBC f p W W') ∧ (∀ ν, ∃! ν', LetBC p ν ν') ∧ (∀ ν ν', LetBC p ν ν' → GtTanR ν → GtTanR ν') ∧ (∀ th, ∃! th', ThBC p th th') ∧ ∀ th th', ThBC p th th' → ThNZ th → ThNZ th' := by
  intro hL _ hU h5 E _ _ _ H Dw l Xo c O _ β Y A A' _ _ _ _ _ _ b a f hf b' hb'
  subst hb'
  refine ⟨?_, fun a' p h => ⟨fun χ W => ?_, existsUnique_letBC p hL.globalFns,
    fun ν ν' => gtTanR_of_letBC p hL.globalFns, existsUnique_thBC p, fun th th' => thNZ_of_thBC p⟩⟩
  · obtain ⟨a', p, h, -⟩ := ArcPull.exists_isBC hL.polBaseChange hL.globalFns a f hf
    exact ⟨a', p, rfl, h.xe_smul, h.be_eq, h.act, h.eta, h.etaA⟩
  · obtain ⟨-, h₁, h₂, h₃, h₄, h₅⟩ := h
    exact ArcPull.exists_witness_powerSeries hL.globalFns hL.polBaseChange hU h5 ⟨h₁, h₂, h₃, h₄, h₅⟩ W

end GlobalTheory.ArcQBC
end
end

section

noncomputable section

namespace GlobalTheory.TauTwist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusExt
open NumberField

theorem exists_compatible_roots {O X F : Type} [CommRing O] [StarRing O] [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] [Module.Free ℤ O] [Field F] [IsAlgClosed F] {w : O} (hw : w + star w = 1) {s : X → X → Fˣ}
    (hs : IsScalarForm O s) : ∃ r : ℕ → X → X → Fˣ, (∀ n, IsScalarForm O (r n)) ∧
      (∀ n, 0 < n → ∀ y x, r n y x ^ n = s y x) ∧ ∀ n m, 0 < n → 0 < m → ∀ y x, r (n * m) y x ^ m = r n y x := by
  letI : DivisibleBy (Additive Fˣ) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u.toMul : F) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact Units.ne_zero _ hz.symm
    exact ⟨Additive.ofMul (Units.mk0 z hz0), Units.ext hz⟩
  letI : DivisibleBy (Additive Fˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨T, hT, h⟩ := Forms.exists_balForms_lift hw (AddMonoidHom.eval (1 : ℚ) : (ℚ →+ Additive Fˣ) →+ Additive Fˣ)
    (fun u => by
      obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive Fˣ)).extension_property_addMonoidHom
        (Int.castAddHom ℚ) Int.cast_injective (zmultiplesHom _ u)
      exact ⟨ρ, by simpa using DFunLike.congr_fun hρ 1⟩) hs.mem_balForms
  refine ⟨fun n y x => (T y x (n : ℚ)⁻¹).toMul, fun n => ⟨fun y x x' => by beta_reduce; rw [map_add (f := _)]; rfl,
    fun y x => by beta_reduce; rw [hT.1 y x], fun a y x => by beta_reduce; rw [hT.2 a y x]⟩, fun n hn y x => ?_, fun n m hn hm y x => ?_⟩
  · have : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    show (n • T y x (n : ℚ)⁻¹).toMul = _
    rw [← map_nsmul, nsmul_eq_mul, mul_inv_cancel₀ this]
    exact h y x
  · have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    show (m • T y x ((n * m : ℕ) : ℚ)⁻¹).toMul = (T y x (n : ℚ)⁻¹).toMul
    rw [← map_nsmul, nsmul_eq_mul, Nat.cast_mul, mul_inv, mul_left_comm, mul_inv_cancel₀ this, _root_.mul_one]

theorem QkRel.qkExt_of {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {ψ : PsiFam D} {hψ : ∀ χ, (ψ χ).IsGen}
    {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] {k : ℕ} {f : F →+* F'}
    {r : D.X → D.X → Fˣ} {r' : D.X → D.X → F'ˣ} (hr : ∀ y x, r' y x = Units.map f.toMonoidHom (r y x))
    {p : QkPt D F k} {q : QkPt D F' k} {p' : QkPt (withPsi D ψ hψ) F k} {q' : QkPt (withPsi D ψ hψ) F' k}
    (hp : QkRel r p p') (hq : QkRel r' q q') (h : QkExt f p' q') : QkExt f p q :=
  QkRel.qkExt (D := withPsi D ψ hψ) (fun y x => by rw [map_inv, hr]) hp.symm hq.symm h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem halfUnit_add_star (H : Host E) : letI := H.starRing; H.w0 + star H.w0 = 1 := by
  show H.w0 + H.bar H.w0 = 1
  rw [HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]

section Tate

variable {R : Type} [CommRing R] [IsDomain R] {D₀ : DegPre R} [Module (𝓞 E) D₀.X] {w : 𝓞 E}
  {t : D₀.X → D₀.X → (FractionRing R)ˣ} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_tateIsoQ_of_roots (hB : D₀.TauBimult) : letI := H.starRing
    ∀ (hw : w + star w = 1) (ht : IsScalarForm (𝓞 E) t) (oa : D₀.OAct (𝓞 E)) (r : ℕ → D₀.X → D₀.X → Fˣ),
      (∀ n, 0 < n → IsRootForm (𝓞 E) n t (r n)) → (∀ n m, 0 < n → 0 < m → ∀ y x, r (n * m) y x ^ m = r n y x) →
      ∀ I : TateIsoQ D D₀ oa F, ∃ I' : TateIsoQ D (twist D₀ w t) (twistAct hw ht oa) F,
        I'.ζ = I.ζ ∧ ∀ n, 0 < n → ∀ a, QkRel (r n) (I.ev n a) (I'.ev n a) := by
  letI := H.starRing
  intro hw ht oa r hr hc I
  have hq := psiRel_rescale D₀ fun y => t y (w • y)
  have ex : ∀ n a, ∃ p : QkPt (twist D₀ w t) F n, 0 < n → QkRel (r n) (I.ev n a) p := fun n a => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨qkZero (tauBimult_twist hw ht hB) F 0, fun h => absurd h (lt_irrefl 0)⟩
    · exact ⟨_, fun _ => qkRel_qkScale hw ht hq (hr n hn) _⟩
  choose ev hev using ex
  exact ⟨{ ζ := I.ζ
           ζ_prim := I.ζ_prim
           ζ_pow := I.ζ_pow
           ev := ev
           add := fun n hn a b => (hev n a hn).qkAdd hw ht hq (hr n hn) (hev n b hn) (hev n _ hn) (I.add n hn a b)
           lin := fun n hn x a => (hev n a hn).qkAct hw ht hq (hr n hn) rfl (hev n _ hn) (I.lin n hn x a)
           ker := fun n hn a b => ((hev n a hn).equiv_iff hw ht hq (hr n hn) (hev n b hn)).trans (I.ker n hn a b)
           onto := fun n hn p' => by
             obtain ⟨p, rfl⟩ := (qkScaleEquiv hw ht hq (hr n hn) _).surjective p'
             obtain ⟨a, ha⟩ := I.onto n hn p
             exact ⟨a, (hev n a hn).equiv hw ht hq (hr n hn) (qkRel_qkScaleEquiv hw ht hq (hr n hn) p) ha⟩
           tower := fun n m hn hm a => by
             obtain ⟨q, h₁, h₂, h₃⟩ := I.tower n m hn hm a
             have e := qkRel_qkScale (D := D₀) (hψ := (twist D₀ w t).psi_gen) hw ht hq (hr n hn) q
             have e' := hev (n * m) a (Nat.mul_pos hn hm)
             exact ⟨_, h₁.trans e'.1.symm, e'.2.isNsmul e.2 (fun χ => by rw [h₁, hc n m hn hm]) h₂,
               e.equiv hw ht hq (hr n hn) (hev n a hn) h₃⟩
           isom := fun n hn a b => ((hev n a hn).weilQkIs_iff hw ht hq (hr n hn) (hev n b hn) _).2 (I.isom n hn a b) },
    rfl, fun n hn a => hev n a hn⟩

theorem exists_tateIsoQ_twist [IsAlgClosed F] (hB : D₀.TauBimult) : letI := H.starRing
    ∀ (hw : w + star w = 1) (ht : IsScalarForm (𝓞 E) t) (oa : D₀.OAct (𝓞 E)) (N : ℕ) (s : D₀.X → D₀.X → Fˣ),
      IsRootForm (𝓞 E) N t s → ∀ I : TateIsoQ D D₀ oa F,
      ∃ (r : ℕ → D₀.X → D₀.X → Fˣ) (I' : TateIsoQ D (twist D₀ w t) (twistAct hw ht oa) F),
        (∀ n, 0 < n → IsRootForm (𝓞 E) n t (r n)) ∧ (∀ n m, 0 < n → 0 < m → ∀ y x, r (n * m) y x ^ m = r n y x) ∧
        (∀ n, 0 < n → n ∣ N → ∀ y x, r n y x = s y x ^ (N / n)) ∧
        I'.ζ = I.ζ ∧ ∀ n, 0 < n → ∀ a, QkRel (r n) (I.ev n a) (I'.ev n a) := by
  letI := H.starRing
  intro hw ht oa N s hs I
  have := Forms.projective_of_int (𝓞 E) D₀.X
  have : Module.Finite (𝓞 E) D₀.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨r, h₁, h₂, h₃⟩ := exists_compatible_roots hw hs.1
  have a₁ : ∀ n, 0 < n → IsRootForm (𝓞 E) n t fun y x => r n y x ^ N := fun n hn =>
    ⟨(h₁ n).pow N, fun y x => by rw [pow_right_comm, h₂ n hn, hs.2]⟩
  have a₂ : ∀ n m, 0 < n → 0 < m → ∀ y x, (r (n * m) y x ^ N) ^ m = r n y x ^ N := fun n m hn hm y x => by
    rw [pow_right_comm, h₃ n m hn hm]
  obtain ⟨I', hI⟩ := exists_tateIsoQ_of_roots hB hw ht oa (fun n y x => r n y x ^ N) a₁ a₂ I
  refine ⟨_, I', a₁, a₂, fun n hn hN y x => ?_, hI⟩
  rw [← h₂ n hn, ← pow_mul, Nat.mul_div_cancel' hN]

end Tate

section ThetaShiftProofs

variable {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O']
  {b : O →+* O'} (a : ArcIn D l β O' b)

variable {ρ : a.D₀.X → a.D₀.X → O'ˣ}

variable (hρ : letI := H.starRing; IsScalarForm (𝓞 E) ρ)

end ThetaShiftProofs

end GlobalTheory.TauTwist
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.GtRep

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem exists_rep_and_shift : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GlobalTheory.ArcPts.GtAn a) (k : ℕ), 1 ≤ k → (∀ p, ∃ la, Λ.Rep k p la) ∧ ∀ p la e, Λ.Rep k p la → ∃ q : Out.QkPt a.D₀ ℂ k, q.y = Λ.ε (la + k • e).y ∧ q.g = Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 (la + k • e)) ∧ ∀ q', QkExt (algebraMap _ ℂ) p q' → Out.QkPt.Equiv a.D₀ ℂ q q' := by
  intro h1 h2 E _ _ _ H _ D l c O _ β _ _ b a Λ k hk
  obtain ⟨hadd, hsurj, -⟩ := GlobalTheory.T.analyticDictionaryExp_additive_surjective_linear h1 h2 E H D l c O β b a Λ
  obtain ⟨hker, hio, -⟩ := GlobalTheory.T.analyticDictionaryExp_kernel_iota_torusPoints E H D l c O β b a Λ
  have hB := a.bimult
  let ex : Λ.A.V →+ Out.GtPtF a.D₀ ℂ :=
    AddMonoidHom.mk' Λ.ex0 fun z z' => (isAdd_iff_eq _ _ _).1 (hadd z z')
  have hex : ∀ z, Λ.ex0 z = ex z := fun _ => rfl
  have hio' : ∀ la : Λ.A.La, ex (Λ.A.P0 la) = iota hB ℂ (Λ.ε la.y) := fun la => (isIota_iff_eq hB _ _).1 (hio la)
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hf : (algebraMap (FractionRing ℂ) ℂ).comp (algebraMap (FractionRing ℂ) (FractionRing ℂ)) =
      algebraMap (FractionRing ℂ) ℂ := RingHom.ext fun _ => rfl
  have hkk : ∀ v : Λ.A.V, (k : ℂ)⁻¹ • k • v = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk0]
  have hkk' : ∀ v : Λ.A.V, k • (k : ℂ)⁻¹ • v = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk0]
  refine ⟨fun p => ?_, fun p la e hrep => ?_⟩
  · obtain ⟨q, -, huniq⟩ := existsUnique_qkExt hB _ hf p
    obtain ⟨z, hz⟩ := hsurj q.g
    let l0 : Λ.A.La := AnArc.La.mk (Λ.ε.symm q.y) 0 0
    have hl0 : Λ.ε l0.y = q.y := Λ.ε.apply_symm_apply _
    have hzero : (Λ.ex0 (k • z - Λ.A.P0 l0)).IsZero := by
      rw [isZero_iff_eq, hex, map_sub, map_nsmul, ← hex z, hz, qk_nsmul hB, hio', hl0, sub_self]
    obtain ⟨l1, hl1, hl1'⟩ := (hker _).1 hzero
    refine ⟨l1 + l0, fun q' hq' => ?_⟩
    obtain rfl := huniq q' hq'
    refine ⟨by rw [AnArc.La.add_y, hl1, zero_add, hl0], ?_⟩
    rw [map_add (f := _), ← hl1', sub_add_cancel, hkk, hz]
  · refine ⟨qkMk hB (Λ.ε (la + k • e).y) (Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 (la + k • e)))
      (by rw [hex, ← map_nsmul, hkk', hio']), rfl, rfl, fun q' hq' => ?_⟩
    obtain ⟨hy, hg⟩ := hrep q' hq'
    refine equiv_symm hB ((equiv_iff hB _ _).2 ⟨Λ.ε e.y, ?_, ?_⟩)
    · rw [qkMk_y, hy, AnArc.La.add_y, AnArc.La.nsmul_y, map_add (f := _), map_nsmul]
    · rw [qkMk_g, hg, hex, hex, map_add (f := _), map_nsmul, smul_add, hkk, map_add (f := _), hio']

end GlobalTheory.GtRep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem gtAn_orth_ker_iff : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GlobalTheory.ArcPts.GtAn a) (v : Λ.A.La), (∀ v' : Λ.A.La, Λ.ε v'.y = 0 → Λ.A.EF v v' = 0) ↔ (Λ.ε v.y = 0 ∧ ∀ s : ℂ, ∃ x, IsTorusPt (Λ.ex0 (s • Λ.A.P0 v)) x ∧ ∀ v' : Λ.A.La, x (Λ.ε v'.y) = eTwoPi (-(s * Λ.A.EF v v'))) := by
  intro _ _ E _ _ _ H _ D l c O _ β _ _ b a Λ v
  obtain ⟨-, -, htor, hlam⟩ := GlobalTheory.T.analyticDictionaryExp_kernel_iota_torusPoints E H D l c O β b a Λ
  have hε : ∀ x : Λ.A.X, Λ.ε x = 0 ↔ x = 0 := fun x => map_eq_zero_iff _ Λ.ε.injective
  simp only [hε]
  constructor
  · intro h
    refine ⟨((Λ.A.orth_ker_iff v).1 h).1, fun s => ?_⟩
    obtain ⟨h2, h1⟩ := Λ.A.smul_periodMap_of_orthogonal_ker h s
    have hz : s • Λ.A.P0 v = ((s • Λ.A.P0 v).1, 0) := Prod.ext rfl h2
    refine ⟨fun x => eTwoPi ((s • Λ.A.P0 v).1 (Λ.ε.symm x)), ?_, fun v' => ?_⟩
    · have := htor (s • Λ.A.P0 v).1
      rwa [← hz] at this
    · have h3 : Λ.ε.symm (Λ.ε v'.y) = v'.y := Λ.ε.symm_apply_apply _
      simp only [h3, h1]
  · rintro ⟨hv, h⟩
    refine (Λ.A.orth_ker_iff_forall_smul_mem v).2 ⟨hv, fun s => ?_⟩
    obtain ⟨x, hx, -⟩ := h s
    exact hlam _ x hx

end GlobalTheory.ArcPts
end

section

namespace GlobalTheory.ConstPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem nonempty_constPts : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GlobalTheory.ArcPts.GtAn a) , Nonempty (ConstPts W Λ) := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ
  choose g x τ h₁ h₂ h₃ h₄ using fun v : Λ.A.V => exists_constPoint W Λ.u (Λ.ex0 v) v.2 (Λ.ex0_b v)
  exact ⟨⟨g, h₁, x, h₂, h₃, τ, h₄⟩⟩

end GlobalTheory.ConstPoint
end
