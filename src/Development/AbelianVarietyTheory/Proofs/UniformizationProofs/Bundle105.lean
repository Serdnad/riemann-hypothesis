module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle123
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefVal
open TWM TWO SectionScalarValuation

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem isPullback_jO : IsPullback (jO hϖ hv (D := D)).left (fst (TF (R := V) F) D.toPre.P.A).left
    (fst (TO hϖ hv) D.toPre.P.A).left (Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F))) := by
  have H₁ : IsPullback (snd (TO hϖ hv) D.toPre.P.A).left (fst (TO hϖ hv) D.toPre.P.A).left D.toPre.P.A.hom
      (TO hϖ hv).hom := (IsPullback.of_hasPullback (TO hϖ hv).hom D.toPre.P.A.hom).flip
  have H₀ : IsPullback (DegPre.prB D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left D.toPre.P.A.hom
      (TF (R := V) F).hom := (IsPullback.of_hasPullback (TF (R := V) F).hom D.toPre.P.A.hom).flip
  rw [← jO_snd hϖ hv, ← Over.w (ιS hϖ hv)] at H₀
  exact H₀.of_right (jO_fst hϖ hv) H₁


include hϖ hv in
theorem exists_vge (hTW : TwistBCSpanStatement) {k : ℕ} (hk : 1 ≤ k) {α : D.toPre.X}
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))) : ∃ r : ℚ, VGe D F v k α s r := by
  have hL := D.toPre.P.isLB
  have := D.toPre.P.isAb.proper
  have hp : IsProper (fst (TO hϖ hv) D.toPre.P.A).left :=
    inferInstanceAs (IsProper (pullback.fst (TO hϖ hv).hom D.toPre.P.A.hom))
  have : CompactSpace (TO hϖ hv).left := inferInstanceAs (CompactSpace (Spec (CommRingCat.of (Ov v))))
  have : QuasiSeparatedSpace (TO hϖ hv).left := inferInstanceAs (QuasiSeparatedSpace (Spec (CommRingCat.of (Ov v))))
  have : CompactSpace (TO hϖ hv ⊗ D.toPre.P.A).left :=
    QuasiCompact.compactSpace_of_compactSpace (fst (TO hϖ hv) D.toPre.P.A).left
  have : QuasiSeparatedSpace (TO hϖ hv ⊗ D.toPre.P.A).left :=
    (quasiSeparated_iff_quasiSeparatedSpace (fst (TO hϖ hv) D.toPre.P.A).left).mp inferInstance
  obtain ⟨s₁, hs₁⟩ := exists_sec hL (φ' := fun i => (jO hϖ hv (D := D)).left ≫
      (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α i) (ε' := DegPre.famε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      rw [GC.famφ_eq, ← jO_snd hϖ hv, Category.assoc]) s
  obtain ⟨t, ht, S, hS⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors (Ov v)) (isPullback_jO hϖ hv (D := D)) hL
    (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) s₁
  obtain ⟨n, rr, σ, hσ⟩ := hTW V D.toPre k hk α (Ov v) (fO v hϖ hv) inferInstance S
  choose σF hσF using fun i => FamInt.exists_pull (D := D) (F := F) (σ i)
  have ht0 : (t : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := F) ht
  obtain ⟨r, hr⟩ := wt_coe_of_ne (v := v) (inv_ne_zero ht0)
  refine ⟨r, n, fun i => (t : F)⁻¹ * ιr (v := v) (rr i), σ, σF, hσF, fun i => ?_, fun j => ?_⟩
  · rw [AddValuation.map_mul, hr]
    exact le_add_of_nonneg_right (v_ιr _)
  refine (sec_ext_val hL (s' := FamInt.secLin (fun i => gF D.toPre F ((t : F)⁻¹ * ιr (v := v) (rr i))) σF)
    (fun y J hJ => ?_) j).trans rfl
  rw [sval_lin (s := FamInt.secLin _ _) (fun i => gF D.toPre F ((t : F)⁻¹ * ιr (v := v) (rr i))) σF (fun _ => rfl) _ y hJ]
  have e₁ : sval S (𝟙 _ ≫ (jO hϖ hv (D := D)).left) y J = gs (𝟙 _) y ⊤ (gF D.toPre F t) * sval s (𝟙 _) y J := by
    rw [← hs₁ _ _ y J hJ, sval_of S (𝟙 _ ≫ (jO hϖ hv (D := D)).left) y J (fun a => J (𝟙 _ ≫ (jO hϖ hv (D := D)).left ≫
      (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α a)) (fun a => by rw [Category.assoc])]
    refine (hS _ (𝟙 _) y _ (hJ.mem (fun a => (jO hϖ hv (D := D)).left ≫
      (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α a) (𝟙 _))).trans (congrArg₂ (· * ·) ?_ rfl)
    have e := gs_jO hϖ hv (D := D) (𝟙 _) y ((Scheme.ΓSpecIso (CommRingCat.of (Ov v))).inv.hom t)
    rw [show ιr (v := v) ((Scheme.ΓSpecIso (CommRingCat.of (Ov v))).inv.hom t) = (t : F) by simp [ιr]] at e
    rw [← e, ← Category.assoc]
    exact (gs_pull _ _ y ⊤ trivial _).symm
  have e₂ := sval_lin (fun l => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (rr l))
      (fun l => pullSec D.toPre.P.L _ _ (σ l) (snd (TO hϖ hv) D.toPre.P.A).left) (fun j => hσ j)
      (𝟙 _ ≫ (jO hϖ hv).left) y hJ
  have g : ∀ a b : F, gs (𝟙 _) y ⊤ (gF D.toPre F (a * b)) =
      gs (𝟙 _) y ⊤ (gF D.toPre F a) * gs (𝟙 _) y ⊤ (gF D.toPre F b) := fun a b => by
    rw [map_mul, gs_mul _ y ⊤ trivial]
  have g₁ : gs (𝟙 _) y ⊤ (gF D.toPre F (t : F)⁻¹) * gs (𝟙 _) y ⊤ (gF D.toPre F t) = 1 := by
    rw [← g, inv_mul_cancel₀ ht0, map_one, gs_eq _ _ ⊤ trivial, map_one, map_one]
  rw [← _root_.one_mul (sval s _ y J), ← g₁, _root_.mul_assoc, ← e₁, e₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [g, gs_jO, sval_pullSec _ _ _ _ _ y hJ, Category.assoc, jO_snd, secScal_sval (hσF i) _ y hJ, _root_.mul_assoc]


include hϖ hv in
theorem exists_nuGe (hTW : TwistBCSpanStatement) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {k : ℕ} (hk : 1 ≤ k)
    (s : Fam D.toPre F k) : ∃ r : ℚ, NuGe D Q F v k s r := by
  classical
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D.toPre.X k hk
  choose r hr using fun i => exists_vge hϖ hv hTW hk (s.s (e i))
  obtain ⟨m, hm⟩ := (Set.finite_range fun i => (Q (e i) : ℚ) / k - r i).bddAbove
  refine ⟨-m, ?_⟩
  rw [n1a V ϖ hϖ D Q hQ _ _ hv k hk (Finset.univ.image e) (fun χ => by
    obtain ⟨i, hi, -⟩ := he χ
    exact ⟨e i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩) s]
  intro α hα
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hα
  have := hm ⟨i, rfl⟩
  exact VGe.mono (hr i) (by linarith)


include hϖ in
theorem finite_sublevel {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {k : ℕ} (hk : 1 ≤ k) (l : D.toPre.X →+ ℚ)
    (q : ℚ) : {χ | (Q χ : ℚ) / k + l χ ≤ q}.Finite := by
  let β : LinearMap.BilinForm ℤ D.toPre.X := LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ D hQ a b)
    (fun a a' b => by simp) (fun c a b => by simp) (fun a b b' => by simp) (fun c a b => by simp)
  have hβ : ∀ a, β a a = 2 * Q a := fun a => (QForm.two_Q_eq hϖ D hQ a).symm
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine (ClassMin.finite_affine_sublevel (ClassMin.realExtension_ofIntBilin_posDef (β := β)
    (fun a b => QForm.bOf_comm D a b) (fun a ha => by have := QForm.Q_pos hϖ D hQ ha; rw [hβ]; omega))
    (inv_pos.2 hk') ((Rat.castHom ℝ).toAddMonoidHom.comp l) q).subset fun χ hχ => ?_
  have h : (((Q χ : ℚ) / k + l χ : ℚ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hχ
  show (k : ℝ)⁻¹ * ClassMin.ofIntBilin β χ + (l χ : ℝ) ≤ q
  rw [ClassMin.ofIntBilin_apply, hβ]
  push_cast at h ⊢
  refine le_of_eq_of_le ?_ h
  field_simp

end GlobalTheory.UT.CoefVal
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PhiLattice

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem trPt_inv_comp (m : TF (R := R) F ⟶ D.P.A) : DegPre.trPt D F m⁻¹ ≫ DegPre.trPt D F m = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, tr_fst, Category.id_comp]
  · show (DegPre.trPt D F m⁻¹ ≫ DegPre.trPt D F m) ≫ DegPre.prB D F = 𝟙 _ ≫ DegPre.prB D F
    rw [Category.assoc, tr_pr, MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, _root_.mul_assoc,
      ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.mul_one, Category.id_comp]

theorem zero_of_phiVal {n : ℕ} (p p' : QkPt D F n)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n)))
    (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n)))
    {s t : Fam D F n} (h : PhiVal p w s.s t.s) (h' : PhiVal p' w' s.s t.s) {α α' : D.X}
    (e : α' + p'.y = α + p.y) (h0 : ∀ j, (s.s α).f j = 0) : ∀ j, (s.s α').f j = 0 := by
  intro j
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  have e₁ := h α _ rfl _ (DegPre.trPt D F p'.g.b⁻¹) y J hJ
  have e₂ := h' α' _ e _ (DegPre.trPt D F p'.g.b⁻¹) y J hJ
  rw [UUA.sval_zero_of h0 _ y J (hJ.mem _ _), MulZeroClass.zero_mul] at e₁
  rw [e₁, trPt_inv_comp, Over.id_left] at e₂
  rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]
  exact (Units.mul_left_eq_zero _).1 e₂.symm

end GlobalTheory.PhiLattice

namespace GlobalTheory

theorem lattice_part_congr_of_phiRel : GlobalFnsSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p p' : QkPt D F n) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n))) (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n))), w.IsGen → w'.IsGen → (∀ s : Fam D F n, ∃ s' : Fam D F n, PhiRel D F n p w s s' ∧ PhiRel D F n p' w' s s') → ∃ z : D.X, p'.y = p.y + n • z := by
  intro hG hT R _ _ D hB F _ _ n hn p p' w w' hw hw' H
  obtain ⟨s, hs⟩ := FamFree.exists_fam_support (D := D) (F := F) hG hT hB hn 0
  obtain ⟨t, h, h'⟩ := H s
  rw [ReciprocityTheory.ChartRestriction.G.DVR.phiRel_iff hG p w hw] at h
  rw [ReciprocityTheory.ChartRestriction.G.DVR.phiRel_iff hG p' w' hw'] at h'
  have h0 : ¬ ∀ j, (s.s 0).f j = 0 := (hs 0).2 ⟨0, by rw [smul_zero, add_zero]⟩
  obtain ⟨z, hz⟩ := (hs (p'.y - p.y)).1 fun h1 =>
    h0 (PhiLattice.zero_of_phiVal p p' w w' h h' (by rw [zero_add, sub_add_cancel]) h1)
  exact ⟨z, by rw [zero_add] at hz; rw [hz, add_sub_cancel]⟩

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace OperatorPoint

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem trPt_inv_comp (b : TF (R := R) F ⟶ D.P.A) : DegPre.trPt D F b⁻¹ ≫ DegPre.trPt D F b = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, tr_fst, Category.id_comp]
  · have e : (DegPre.trPt D F b⁻¹ ≫ DegPre.trPt D F b) ≫ DegPre.prB D F = DegPre.prB D F := by
      rw [Category.assoc, tr_pr, MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, _root_.mul_assoc,
        ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.mul_one]
    exact e.trans (Category.id_comp _).symm

theorem phiVal_inv {n : ℕ} (p : QkPt D F n)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n)))
    {s t : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε n))} (h : PhiVal p w s t)
    (α β : D.X) (hβ : α + p.y = β) (b : TF (R := R) F ⟶ D.P.A) (hb : p.g.b = b) (y : (DegPre.BF D F).left) (J)
    (hJ : Good D.P.L y J) :
    sval (t β) (DegPre.trPt D F b⁻¹).left y J = sval (s α) (𝟙 _) y J *
      (uVal D F n α b (DegPre.trPt D F b⁻¹) y J * (val (p.g.s α) (fst (TF (R := R) F) D.P.A).left y J *
        val w (fst (TF (R := R) F) D.P.A).left y J)).val := by
  subst hb
  have e := h α β hβ _ (DegPre.trPt D F p.g.b⁻¹) y J hJ
  rw [trPt_inv_comp, tr_fst, val_mul hJ] at e
  exact e

end OperatorPoint


open ReciprocityTheory.ChartRestriction.G.DVR OperatorPoint in
theorem qkPt_g_eq_of_phiRel :
    GlobalFnsSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p p' : QkPt D F n) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n))) (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n))), w.IsGen → w'.IsGen → (∀ s : Fam D F n, ∃ s' : Fam D F n, PhiRel D F n p w s s' ∧ PhiRel D F n p' w' s s') → p'.y = p.y → p.g.b = p'.g.b → p.g = p'.g := by
  intro hG hT R _ _ D hB F _ _ n hn p p' w w' hw hw' H hy hb
  have hI := (degPre_abelianPart_isIntegral_and_isIntegrallyClosed_stalk R D F).1
  have key : ∀ (α : D.X) (y : (DegPre.BF D F).left) (J), Good D.P.L y J →
      val (p.g.s α) (fst (TF (R := R) F) D.P.A).left y J * val w (fst (TF (R := R) F) D.P.A).left y J =
        val (p'.g.s α) (fst (TF (R := R) F) D.P.A).left y J * val w' (fst (TF (R := R) F) D.P.A).left y J := by
    intro α y J hJ
    obtain ⟨σ, hσ⟩ := FamFree.exists_sec_ne_zero (D := D) (F := F) hT hn α
    obtain ⟨s, rfl, -⟩ := FamFree.exists_fam_single hG hB hn α σ
    obtain ⟨t, h₁, h₂⟩ := H s
    have e₁ := phiVal_inv p w ((phiRel_iff hG p w hw s t).1 h₁) α (α + p.y) rfl _ rfl y J hJ
    have e₂ := phiVal_inv p' w' ((phiRel_iff hG p' w' hw' s t).1 h₂) α (α + p.y) (by rw [hy]) _ hb.symm y J hJ
    have hne : sval (s.s α) (𝟙 _) y J ≠ 0 :=
      RootUnit.sec_gs_ne_zero (s.s α) (not_forall.1 hσ) y _ (hJ.mem _ (𝟙 _))
    exact mul_left_cancel (Units.ext (mul_left_cancel₀ hne (e₁.symm.trans e₂)))
  have key' : ∀ (α : D.X) (y : (DegPre.BF D F).left) (J), Good D.P.L y J →
      val (p.g.s α) (fst (TF (R := R) F) D.P.A).left y J = val (p'.g.s α) (fst (TF (R := R) F) D.P.A).left y J := by
    intro α y J hJ
    have e₀ := key 0 y J hJ
    rw [val_corr hJ p.g.s_zero, val_corr hJ p'.g.s_zero, val_one, _root_.one_mul, _root_.one_mul] at e₀
    have e := key α y J hJ
    rw [e₀] at e
    exact mul_right_cancel e
  refine TorusExt.gt_ext hb fun χ => corr_of_val D.P.isLB fun y J hJ => ?_
  have hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (p.g.s χ) (fst (TF (R := R) F) D.P.A).left)
      (LB.pullGen D.P.L _ _ (p'.g.s χ) (fst (TF (R := R) F) D.P.A).left) :=
    corr_of_val D.P.isLB fun y J hJ => by
      rw [val_pull hJ, val_pull hJ, Category.id_comp]; exact key' χ y J hJ
  have z₁ : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (show DegPre.zF D F ≫ fst _ _ = 𝟙 _ from lift_fst _ _)
  have e := val_corr hJ hc (DegPre.zF D F).left
  rwa [val_pull hJ, val_pull hJ, z₁] at e

end GlobalTheory
end
