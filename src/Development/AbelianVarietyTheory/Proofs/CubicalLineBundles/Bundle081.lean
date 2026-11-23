module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle072
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle076
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle083
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

@[expose] public section

section



noncomputable section

namespace GlobalTheory.SecTieEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.SecTransport

section Calc

variable {X X' Y : Scheme.{0}}

theorem exists_sec_back {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB)
    (hL' : L'.IsLB) (s : LB.Sec (L.pull F)) : ∃ σ : LB.Sec L', ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z)
      (J : PUnit → L.ι) (k : L'.ι), r z ∈ (L.pull F).U J → r z ∈ L'.U k →
      gs r z _ (s.f J) = (gw w r z (J PUnit.unit) k).val * gs r z _ (σ.f k) := by
  have glue : ∀ k : L'.ι, ∃ a : Γ(X', L'.U k), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (J : PUnit → L.ι),
      r z ∈ (L.pull F).U J → r z ∈ L'.U k →
        gs r z _ a = ((gw w r z (J PUnit.unit) k)⁻¹).val * gs r z _ (s.f J) := by
    intro k
    obtain ⟨u, hu⟩ : ∃ u : ∀ J : PUnit → L.ι, Γ(X', (L.pull F).U J ⊓ L'.U k),
        ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (J : PUnit → L.ι), r z ∈ (L.pull F).U J ⊓ L'.U k →
          gs r z _ (u J) = ((gw w r z (J PUnit.unit) k)⁻¹).val * gs r z _ (s.f J) :=
      ⟨fun J => (show Γ(X', (L.pull F).U J ⊓ L'.U k) from ((w.s (J, k))⁻¹).val) * resG X' inf_le_left (s.f J),
        fun Z r z J hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit r z _ hz _).trans (congrArg Units.val (map_inv _ _))) (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' (fun J : PUnit → L.ι => (L.pull F).U J ⊓ L'.U k) (L'.U k)
      (fun J => homOfLE inf_le_right) (fun y hy => by
        obtain ⟨j, hj⟩ := exists_chart hL (F y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => j, mem_pull.2 hj, hy⟩) u
      (fun J J' => fn_ext (V := ((L.pull F).U J ⊓ L'.U k) ⊓ ((L.pull F).U J' ⊓ L'.U k)) fun y hy => by
        refine (gs_res (𝟙 X') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X') y inf_le_right hy _).symm)
        have hj : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy.1.1
        have hj' : F y ∈ L.U (J' PUnit.unit) := mem_pull.1 hy.2.1
        rw [hu _ _ y J hy.1, hu _ _ y J' hy.2, gs_compat s (𝟙 X') y hy.1.1 hy.2.1,
          gm_pull_g L F (𝟙 X') y J J' hy.1.1 hy.2.1,
          hw _ (𝟙 X') y (J PUnit.unit) (J' PUnit.unit) k k hj hj' hy.1.2 hy.1.2, gm_self hL' (𝟙 X') y hy.1.2,
          inv_one, _root_.mul_one, mul_inv_rev, Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left])
    refine ⟨a, fun Z r z J h₁ h₂ => ?_⟩
    have hz : r z ∈ (L.pull F).U J ⊓ L'.U k := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_right hz a).symm.trans ((congrArg (gs r z _) (ha J)).trans (hu Z r z J hz))
  choose a ha using glue
  refine ⟨⟨a, fun k k' => fn_ext fun y hy => ?_⟩, fun Z r z J k h₁ h₂ => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart hL (F y)
    have hJ : (𝟙 X' : X' ⟶ X') y ∈ (L.pull F).U (fun _ => j) := mem_pull.2 hj
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy,
      ha k _ (𝟙 X') y (fun _ => j) hJ hy.1, ha k' _ (𝟙 X') y (fun _ => j) hJ hy.2,
      hw _ (𝟙 X') y j j k k' hj hj hy.1 hy.2, gm_self hL (𝟙 X' ≫ F) y hj, _root_.one_mul, mul_inv, inv_inv,
      Units.val_mul, _root_.mul_assoc]
  · show gs r z _ (s.f J) = _ * gs r z _ (a k)
    rw [ha k Z r z J h₁ h₂, Units.mul_inv_cancel_left]

theorem chart_le_preimage' (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (g : X' ⟶ Y) (e : g ≫ φ = F) (J : PUnit → L.ι) :
    (L.pull F).U J ≤ g ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) (fun _ => J PUnit.unit) := fun y hy =>
  Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ L.U (J PUnit.unit)) e).mpr (mem_pull.1 hy)

def secPullBack (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (g : X' ⟶ Y) (e : g ≫ φ = F)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1))) : LB.Sec (L.pull F) where
  f := fun (J : PUnit → L.ι) => (g.appLE _ _ (chart_le_preimage' L g e J)).hom (s.f (fun _ => J PUnit.unit))
  compat := fun (J J' : PUnit → L.ι) => fn_ext fun y hy => by
    have h₁ := chart_le_preimage' L g e J hy.1
    have h₂ := chart_le_preimage' L g e J' hy.2
    have e₁ : gm (𝟙 X' ≫ g) y _ ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)).g
        (fun _ => J PUnit.unit) (fun _ => J' PUnit.unit)) =
        gm ((𝟙 X' ≫ g) ≫ φ) y (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) (L.g (J PUnit.unit) (J' PUnit.unit)) :=
      (gm_linComb L _ _ (𝟙 X' ≫ g) y _ _ h₁ h₂).trans (by rw [Fin.prod_univ_one, zpow_one])
    have eφ : (𝟙 X' ≫ g) ≫ φ = 𝟙 X' ≫ F := by rw [Category.assoc, e]
    rw [eφ] at e₁
    exact (gs_res _ y _ hy _).trans ((gs_appLE g _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat s (𝟙 X' ≫ g) y h₁ h₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val ((gm_pull_g L F (𝟙 X') y J J' hy.1 hy.2).trans e₁.symm)))
        ((gs_res _ y _ hy _).trans (gs_appLE g _ _ _ (𝟙 _) y hy.2 _)))))))

theorem isoMaps_iff {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (σ : LB.Sec L')
    (s : LB.Sec (L.pull F)) : IsoMaps w σ s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z)
      (J : PUnit → L.ι) (k : L'.ι), r z ∈ (L.pull F).U J → r z ∈ L'.U k →
      gs r z _ (s.f J) = (gw w r z (J PUnit.unit) k).val * gs r z _ (σ.f k) := by
  constructor
  · intro H Z r z J k h₁ h₂
    have hz : r z ∈ (L.pull F).U J ⊓ L'.U k := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz _).symm.trans ((congrArg (gs r z _) (H J k)).trans
      ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hz _) (gs_res r z _ hz _))))
  · intro H J k
    refine fn_ext fun y hy => ?_
    exact (gs_res _ y inf_le_left hy _).trans ((H _ (𝟙 X') y J k hy.1 hy.2).trans
      ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _))).symm)

end Calc



theorem secTie_exists_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S)) (m : SABMap t' Xo.univ.t x), (∀ th, ∃ s : LB.Sec (PPx x), SecTie m th s) ∧ (∀ s : LB.Sec (PPx x), ∃ th, SecTie m th s) ∧ ∀ th (s : LB.Sec (PPx x)), SecTie m th s → (∀ th' (s' : LB.Sec (PPx x)), SecTie m th' s' → ((∀ i, th'.f i = th.f i) ↔ ∀ i, s'.f i = s.f i)) ∧ (SecNZ x s ↔ ∀ p : Sp S, ∃ q : t'.G.left, t'.G.hom q = p ∧ q ∈ Out.nonzeroLocus th) := by
  intro E _ _ _ H Dw l Xo S _ x t' m
  obtain ⟨w, gw1, rw1, -⟩ := m.lin
  have hrig : RigIso m w := ⟨gw1, rw1⟩
  have hw := (isGen_iff w).1 gw1
  have hL := Xo.univ.t.PP.isLB
  have hL' := t'.PP.isLB
  have hG : Out.GlobalFnsSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  haveI hpr : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 Xo.univ.proper
  have hA := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  have wu : ∀ w', RigIso m w' → w' = w := fun w' h' =>
    iso_unique_of_rig hG t'.G hA hL' hL h'.1 gw1 h'.2 rw1
  let A := Xo.univ.t.G
  have cond : (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x :=
    (Over.w (snd (Over.mk x) A)).trans (Over.w (fst (Over.mk x) A)).symm
  obtain ⟨h, hφ, hh⟩ : ∃ h : Gx x ⟶ t'.G.left, h ≫ m.φ = (snd (Over.mk x) A).left ∧
      h ≫ t'.G.hom = (fst (Over.mk x) A).left :=
    ⟨m.cart.1.lift _ _ cond, m.cart.1.lift_fst _ _ cond, m.cart.1.lift_snd _ _ cond⟩
  obtain ⟨g, gf, gs'⟩ : ∃ g : t'.G.left ⟶ Gx x, g ≫ (fst (Over.mk x) A).left = t'.G.hom ∧
      g ≫ (snd (Over.mk x) A).left = m.φ := by
    let a0 : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t'.G.hom rfl
    let b0 : Over.mk (t'.G.hom ≫ x) ⟶ A := Over.homMk m.φ m.cart.1.w
    exact ⟨(lift a0 b0).left, congrArg (fun q => q.left) (lift_fst a0 b0), congrArg (fun q => q.left) (lift_snd a0 b0)⟩
  have hgh : g ≫ h = 𝟙 _ := m.cart.1.hom_ext (by rw [Category.assoc, hφ, gs', Category.id_comp])
        (by rw [Category.assoc, hh, gf, Category.id_comp])
  have hhg : h ≫ g = 𝟙 _ := SecCalc.pm_ext _ _ (by rw [Category.assoc, Category.id_comp]; exact (congrArg _ gs').trans hφ)
    (by rw [Category.assoc, Category.id_comp]; exact (congrArg _ gf).trans hh)
  have gu : ∀ g' : t'.G.left ⟶ Gx x, g' ≫ (snd (Over.mk x) A).left = m.φ →
      g' ≫ (fst (Over.mk x) A).left = t'.G.hom → g' = g := fun g' a b =>
    SecCalc.pm_ext _ _ (a.trans gs'.symm) (b.trans gf.symm)

  have tie : ∀ (th : LB.Sec t'.PP.L) (s : LB.Sec (PPx x)), SecTie m th s → ∀ (Z : Scheme.{0}) (r : Z ⟶ t'.G.left) (z : Z)
      (j : Xo.univ.t.PP.L.ι) (k : t'.PP.L.ι), m.φ (r z) ∈ Xo.univ.t.PP.L.U j → r z ∈ t'.PP.L.U k →
      gs (r ≫ g) z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (th.f k) := by
    rintro th s ⟨w', s1, a, b, c⟩ Z r z j k hj hk
    obtain rfl := wu w' a
    have hJ : r z ∈ (Xo.univ.t.PP.L.pull m.φ).U (fun _ => j) := mem_pull.2 hj
    refine Eq.trans ?_ ((isoMaps_iff _ th s1).1 b Z r z (fun _ => j) k hJ hk)
    rw [c g gs' gf (fun _ => j) (chart_le_preimage' _ g gs' _)]
    exact (gs_appLE g _ _ _ r z hJ _).symm
  have hmem : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (y : Gx x), y ∈ (PPx x).U i → m.φ (h y) ∈ Xo.univ.t.PP.L.U (i 0) :=
    fun i y hy => mem_pull.1 (chart_le_preimage Xo.univ.t.PP.L h hφ i hy)
  have tie' : ∀ (th : LB.Sec t'.PP.L) (s : LB.Sec (PPx x)), SecTie m th s → ∀ (y : Gx x)
      (i : Fin 1 → Xo.univ.t.PP.L.ι) (k : t'.PP.L.ι), y ∈ (PPx x).U i → h y ∈ t'.PP.L.U k →
      gs (𝟙 (Gx x)) y _ (s.f i) = (gw w h y (i 0) k).val * gs h y _ (th.f k) := by
    intro th s ht y i k hi hk
    obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun a => congrArg i (Subsingleton.elim _ _)⟩
    rw [← hhg]
    exact tie th s ht _ h y j k (hmem _ y hi) hk
  refine ⟨fun th => ?_, fun s => ?_, fun th s ht => ⟨fun th' s' ht' => ⟨fun e i => ?_, fun e k => ?_⟩, ?_, ?_⟩⟩
  · obtain ⟨s1, hs1⟩ := exists_sec_along_iso hw hL hL' th
    refine ⟨secPullOne Xo.univ.t.PP.L h hφ s1, w, s1, hrig, (isoMaps_iff _ _ _).2 hs1, fun g' a b J hJ => ?_⟩
    obtain rfl := gu g' a b
    refine fn_ext fun y hy => Eq.symm ?_
    refine (gs_appLE g' _ _ hJ (𝟙 _) y hy _).trans ?_
    refine (gs_appLE h _ _ (chart_le_preimage _ h hφ _) (𝟙 _ ≫ g') y (hJ hy) _).trans ?_
    rw [Category.assoc, hgh, Category.id_comp]
  · obtain ⟨th, hth⟩ := exists_sec_back hw hL hL' (secPullBack Xo.univ.t.PP.L g gs' s)
    refine ⟨th, w, _, hrig, (isoMaps_iff _ _ _).2 hth, fun g' a b J hJ => ?_⟩
    obtain rfl := gu g' a b
    rfl
  · refine fn_ext fun y hy => ?_
    obtain ⟨k, hk⟩ := exists_chart hL' (h y)
    rw [tie' th s ht y i k hy hk, tie' th' s' ht' y i k hy hk, e k]
  · refine fn_ext fun y hy => ?_
    obtain ⟨j, hj⟩ := exists_chart hL (m.φ y)
    have e₁ := tie th s ht _ (𝟙 _) y j k hj hy
    have e₂ := tie th' s' ht' _ (𝟙 _) y j k hj hy
    exact (Units.mul_right_inj _).1 (e₂.symm.trans ((congrArg (gs _ y _) (e (fun _ => j))).trans e₁))
  · intro hnz p
    obtain ⟨q, i, hq, hi⟩ := hnz p
    have hiU : q ∈ (PPx x).U i := (Gx x).basicOpen_le _ hi
    obtain ⟨k, hk⟩ := exists_chart hL' (h q)
    refine ⟨h q, (congrArg (fun r => r q) hh).trans hq, TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩⟩
    refine (isUnit_gs_iff h q _ hk _).1 ?_
    have hu := (isUnit_gs_iff (𝟙 _) q _ hiU _).2 hi
    rw [tie' th s ht q i k hiU hk] at hu
    exact isUnit_of_mul_isUnit_right hu
  · intro hnz p
    obtain ⟨q, hq, hqn⟩ := hnz p
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hqn
    have hkU : q ∈ t'.PP.L.U k := t'.G.left.basicOpen_le _ hk
    obtain ⟨j, hj⟩ := exists_chart hL (m.φ q)
    have mg : g q ∈ (PPx x).U (fun _ => j) :=
      Set.mem_iInter.2 fun _ => (congrArg (fun r => r q ∈ Xo.univ.t.PP.L.U j) gs').mpr hj
    refine ⟨g q, fun _ => j, (congrArg (fun r => r q) gf).trans hq, ?_⟩
    refine (isUnit_gs_iff g q _ mg _).1 ?_
    have e := tie th s ht _ (𝟙 _) q j k hj hkU
    rw [Category.id_comp] at e
    rw [e]
    exact (Units.isUnit _).mul ((isUnit_gs_iff (𝟙 _) q _ hkU _).2 hk)

end GlobalTheory.SecTieEx
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.FrameEval

theorem univFrame_borelPairs : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p A : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R) (π : p.R →ₐ[c.F] A.R) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R)) (s : (A.R)ˣ) (u : FrPt Xo c A.R), OpenChart j y₀ → UnivFrame y₀ π X s u → ∃ (B : TRing c.F) (uB uB' : FrPt Xo c B.R) (tB : Ix Dw → (B.R)ˣ) (q q' : A.R →ₐ[c.F] B.R), FrMap q u uB ∧ FrMap q' u uB' ∧ FrBor tB uB uB' ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (a a' : A.R →ₐ[c.F] T) (z z' : FrPt Xo c T) (t : Ix Dw → Tˣ), FrMap a u z → FrMap a' u z' → FrBor t z z' → ∃ b : B.R →ₐ[c.F] T, b.comp q = a ∧ b.comp q' = a' ∧ ∀ i, b (tB i : B.R) = (t i : T) := by
  intro hS E _ _ _ H Dw l Xo c p A j y₀ π X s u hj hU
  obtain ⟨B, q, Y, r, hYd, hYz, hY⟩ := GlobalTheory.T.exists_triangularFrameRing_over_testRing c.F (E →+* ℂ) (fun τ => Dw.mult τ) A
  obtain ⟨uB, huB⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c A.R B.R q u
  obtain ⟨uB', huB', -⟩ := GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c B.R uB Y r
    fun τ => lowerTri_isUnit_det _ (hYz τ) (hYd τ)
  have hux : u.x = spMap π.toRingHom ≫ y₀.x := by
    obtain ⟨-, u₀, h₀, h₁⟩ := hU
    exact h₁.1.trans h₀.1
  have hx' : uB'.x = spMap (q.comp π).toRingHom ≫ y₀.x := by
    rw [huB'.1, huB.1, hux, spMap_algHom_comp, Category.assoc]
  obtain ⟨q', ⟨-, hq'⟩, -⟩ := GlobalTheory.T.universalFrame_classifies_framedPoints hS E H Dw l Xo c p.R A.R y₀ π X s u hU B.R uB' (q.comp π) hx'
  refine ⟨B, uB, uB', fun k => match k with
    | none => r
    | some ⟨τ, i⟩ => (hYd τ i).unit, q, q', huB, hq',
    (frBor_iff_frChg uB uB' _).2 ⟨Y, hYz, fun τ i => (hYd τ i).unit_spec.symm, huB'⟩, ?_⟩
  intro T _ _ a a' z z' t hz hz' hb
  obtain ⟨g, hgz, hgd, hgc⟩ := (frBor_iff_frChg z z' t).1 hb
  obtain ⟨b, ⟨hb1, hb2, hb3⟩, -⟩ := hY T a g (t none)
    (fun τ i => by rw [hgd]; exact Units.isUnit _) hgz
  have h1 : FrMap b uB z :=
    frMap_cancel (Xo := Xo) (c := c) _ _ _ q b u uB z huB (by rw [hb1]; exact hz)
  have h2 : FrMap b uB' z' := by
    refine (GlobalTheory.T.frameChange_comm_baseChange E H Dw l Xo c B.R T b uB uB' z z' Y r huB' h1).2 ?_
    rw [hb3, funext hb2]
    exact hgc
  have h3 : FrMap (b.comp q') u z' := frMap_trans (Xo := Xo) (c := c) _ _ _ q' b u uB' z' hq' h2
  refine ⟨b, hb1, GlobalTheory.T.universalFrame_classifies_unique_openChart hS E H Dw l Xo c p.R A.R j y₀ π X s u hj hU T _ _ z' h3 hz', ?_⟩
  rintro (_ | ⟨τ, i⟩)
  · exact hb3
  · show b (Y τ i i) = _
    rw [← hgd, ← hb2 τ]
    rfl

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem ChartCover.exists_lift {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) :
    ∃ xF : Sp S ⟶ Xo.XF c, xF ≫ pullback.fst _ _ = w.x ∧ xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by
  refine ⟨pullback.lift w.x (spMap (algebraMap c.F S)) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  rw [w.x_over, spMap_comp_ring]
  rfl

theorem ChartCover.near (hS : Out.SecBaseChangeSt) {R A : Type} [CommRing R] [Algebra c.F R] [CommRing A]
    [Algebra c.F A] {j : Sp R ⟶ Xo.XF c} {y₀ : FrPt Xo c R} {π : R →ₐ[c.F] A}
    {X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A} {s : Aˣ} {u : FrPt Xo c A}
    (hj : OpenChart j y₀) (hu : UnivFrame y₀ π X s u) {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S)
    (xF : Sp S ⟶ Xo.XF c) (h1 : xF ≫ pullback.fst _ _ = w.x)
    (h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (p : Sp S) (hp : xF p ∈ Set.range j) :
    ∃ g : S, g ∉ p.asIdeal ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (lam : S →ₐ[c.F] T), IsUnit (lam g) →
      ∃ (z : FrPt Xo c T) (a : A →ₐ[c.F] T), FrMap lam w z ∧ FrMap a u z := by
  obtain ⟨g, hg, hT⟩ := openChart_factor_near_prime E H Dw l Xo c R j y₀ hj S xF h2 p hp
  refine ⟨g, hg, fun T _ _ lam hl => ?_⟩
  obtain ⟨ψ, hψ⟩ := hT T lam hl
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c S T lam w
  have hx : z.x = spMap ψ.toRingHom ≫ y₀.x := by
    rw [hz.1, ← h1, ← hj.2.1, ← Category.assoc, hψ, Category.assoc]
  obtain ⟨a, ⟨_, ha⟩, _⟩ := GlobalTheory.T.universalFrame_classifies_framedPoints hS E H Dw l Xo c R A y₀ π X s u hu T z ψ hx
  exact ⟨z, a, hz, ha⟩

theorem ChartCover.cls_loc (hS : Out.SecBaseChangeSt) {R : Type} [CommRing R] [Algebra c.F R] {A : TRing c.F}
    {j : Sp R ⟶ Xo.XF c} {y₀ : FrPt Xo c R} {π : R →ₐ[c.F] A.R}
    {X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R} {s : (A.R)ˣ} {u : FrPt Xo c A.R}
    (hj : OpenChart j y₀) (hu : UnivFrame y₀ π X s u) {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S)
    (xF : Sp S ⟶ Xo.XF c) (h1 : xF ≫ pullback.fst _ _ = w.x)
    (h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (m : Ideal S) [hm : m.IsPrime]
    (hp : xF (⟨m, hm⟩ : PrimeSpectrum S) ∈ Set.range j) :
    ∃ cw : A.R →ₐ[c.F] Localization.AtPrime m,
      ChartCls (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m u cw ∧
      ChartLoc (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m A u := by
  obtain ⟨g, hg, hT⟩ := ChartCover.near hS hj hu w xF h1 h2 (⟨m, hm⟩ : PrimeSpectrum S) hp
  obtain ⟨z, a, hz, ha⟩ := hT (Localization.AtPrime m) (locM c.F m)
    (IsLocalization.map_units (Localization.AtPrime m) (⟨g, hg⟩ : m.primeCompl))
  refine ⟨a, ⟨z, hz, ha⟩, ?_⟩
  intro p φ y hy
  obtain ⟨yF, k1, k2⟩ := ChartCover.exists_lift y
  have e : spMap φ.toRingHom ≫ yF = xF := by
    apply pullback.hom_ext
    · rw [Category.assoc, k1, h1, hy.1]
    · rw [Category.assoc, k2, h2, spMap_comp_ring]
      congr 1
      exact φ.comp_algebraMap
  have hq : yF (spMap φ.toRingHom (⟨m, hm⟩ : PrimeSpectrum S)) ∈ Set.range j := by
    rw [← e] at hp
    exact hp
  obtain ⟨g', hg', hT'⟩ := ChartCover.near hS hj hu y yF k1 k2 _ hq
  obtain ⟨p', lam, hl, hlam⟩ := GlobalTheory.testRing_localizationAway c.F p g'
  obtain ⟨z', a', hz', ha'⟩ := hT' p'.R lam hl
  exact ⟨g', hg', p', lam, z', a', hlam, hz', ha'⟩

end

theorem chartCoverF_of_secBaseChange : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ChartCoverF Xo c := by
  intro hS E _ _ _ H Dw l Xo c S _ _ w w' hw m hm
  obtain ⟨xF, h1, h2⟩ := ChartCover.exists_lift w
  obtain ⟨p, j, y₀, hj, hp⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (xF (⟨m, hm.isPrime⟩ : PrimeSpectrum S))
  obtain ⟨A, π, X, s, u, hu⟩ := GlobalTheory.T.exists_universalFrame_testRing hS E H Dw l Xo c p y₀
  obtain ⟨cw, hc, hl⟩ := ChartCover.cls_loc hS hj hu w xF h1 h2 m hp
  obtain ⟨cw', hc', hl'⟩ := ChartCover.cls_loc hS hj hu w' xF (h1.trans hw.symm) h2 m hp
  exact ⟨A, u, cw, cw', GlobalTheory.T.universalFrame_classifies_unique_openChart hS E H Dw l Xo c p.R A.R j y₀ π X s u hj hu,
    univFrame_borelPairs hS E H Dw l Xo c p A j y₀ π X s u hj hu, hc, hl, hc', hl'⟩

theorem evR_frMap_of_isReduced (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (f : Rul Xo c)
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {K₁ K₂ : Type} [CommRing K₁] [Algebra c.F K₁] [CommRing K₂] [Algebra c.F K₂] [_root_.IsReduced K₁] (φ : K₁ →ₐ[c.F] K₂)
    (y₁ : FrPt Xo c K₁) (y₂ : FrPt Xo c K₂) (hm : FrMap φ y₁ y₂) : evR Xo c f y₂ = φ (evR Xo c f y₁) := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
    evalWD_fr (frChartF_of (chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have hT1 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y₁ :=
    GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c _ y₁
  have hT2 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y₂ := by
    obtain ⟨p, ψ, y', hy'⟩ := hT1
    exact ⟨p, φ.comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ φ y' y₁ y₂ hy' hm⟩
  unfold evR evalAt
  rw [dite_eq_left hT2, dite_eq_left hT1]
  exact hWD f hf K₂ _ _ _ _ _ _ y₂ hT2.choose_spec.choose_spec.choose_spec
    (frMap_trans (Xo := Xo) (c := c) _ _ _ _ φ _ y₁ y₂ hT1.choose_spec.choose_spec.choose_spec hm)

theorem evR_frBor (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [_root_.IsReduced S]
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) (hf : f ∈ sec Xo c a n) (t : Formalism.L2.Pj.Ix Dw → Sˣ)
    (y y' : FrPt Xo c S) (hb : FrBor t y y') : evR Xo c f y' = wchar (Formalism.L2.Pj.ex Dw a n) t * evR Xo c f y := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hall : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  exact wtAll_of_borChart (borChartF_of_cover (chartCoverF_of_secBaseChange hS E H Dw l Xo c)) (Formalism.L2.Pj.ex Dw a n)
    hf.1 hf.2 S t y y' (hall S y) (hall S y') hb

end GlobalTheory.FrameEval
end
