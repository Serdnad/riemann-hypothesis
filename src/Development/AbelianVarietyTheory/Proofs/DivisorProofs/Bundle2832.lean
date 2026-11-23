module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderActionRosatiAdjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2743
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc


theorem _root_.GlobalTheory.T.zarhin_bundle_isomorphism : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → LBIso c.P ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (GlobalTheory.ZarhinFam.incZ c.A B ⊗ₘ GlobalTheory.ZarhinFam.incZ c.A B).left) := by
  first | (exact @GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion) | (exact GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion) | (intros; apply GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc


theorem _root_.GlobalTheory.T.zarhinProduct_relation_algebraic_clauses : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → IsMonHom (GlobalTheory.ZarhinFam.incZ c.A B) ∧ IsMonHom (GlobalTheory.ZarhinFam.prZ c.A B) ∧ GlobalTheory.ZarhinFam.incZ c.A B ≫ GlobalTheory.ZarhinFam.prZ c.A B = 𝟙 c.A ∧ GlobalTheory.ZarhinFam.prZ c.A B ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.idem d) ∧ ∀ a, c.lev a ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (GlobalTheory.ZarhinFam.jlMap h a) := by
  first | (exact @GlobalTheory.ZarhinFam.zRel_alg) | (exact GlobalTheory.ZarhinFam.zRel_alg) | (intros; apply GlobalTheory.ZarhinFam.zRel_alg  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc


theorem _root_.GlobalTheory.T.zarhinLevel_additive_killed_by_level : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → (∀ a b, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (a + b) = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a * (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) b) ∧ ∀ a, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a ^ M = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.LevAlg.levZ_add_tors) | (exact GlobalTheory.ZarhinFam.LevAlg.levZ_add_tors) | (intros; apply GlobalTheory.ZarhinFam.LevAlg.levZ_add_tors  <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinFam.Rig

section
variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem pull_pull_lift {Y W X₁ X₂ : Over S} {M : LB (X₁ ⊗ X₂).left} (hM : M.IsLB) (u : Y ⟶ W) (f : W ⟶ X₁)
    (g : W ⟶ X₂) : CechPic.pull u.left (CechPic.pull (lift f g).left (cls M hM)) = evc hM (u ≫ f) (u ≫ g) := by
  rw [← pull_comp, ← Over.comp_left, comp_lift]; rfl

theorem pull_zCls {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A)
    {Y : Over S} (z z' : Y ⟶ Zob A B) :
    CechPic.pull (lift z z').left (zCls A B hP hQ d mu) =
      (∑ i, evc hP (z ≫ pa A B i) (z' ≫ pa A B i)) +
      (∑ i, ∑ j, quat d j i • evc hQ (z ≫ pa A B i) (z' ≫ pb A B j)) +
      (∑ i, ∑ j, quat d j i • evc hQ (z' ≫ pa A B i) (z ≫ pb A B j)) +
      ∑ j, evc hQ (z' ≫ pb A B j ≫ mu) (z ≫ pb A B j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [zCls, map_add (f := _), map_sum, map_zsmul, pull_pull_lift, lift_fst_assoc, lift_snd_assoc]

theorem zarhinBundle_pull_trivial_iff {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ)
    (mu : B ⟶ A) {Y : Over S} (u : Y ⟶ Zob A B ⊗ Zob A B) :
    (∃ t : ((zP A B hP hQ d mu).pull u.left).Gen, t.IsGen) ↔
      CechPic.pull u.left (zCls A B hP hQ d mu) = 0 := by
  rw [← cls_eq_zero_iff (pull_isLB (zarhinBundle_isLineBundle A B hP hQ d mu) _), cls_pull (zarhinBundle_isLineBundle A B hP hQ d mu), cls_zP]

theorem one_pa {Y : Over S} (i : Fin 4) : (1 : Y ⟶ Zob A B) ≫ pa A B i = 1 := by
  simp [pa]

theorem one_pb {Y : Over S} (j : Fin 4) : (1 : Y ⟶ Zob A B) ≫ pb A B j = 1 := by
  simp [pb]

theorem one_pb_assoc {Y X : Over S} (j : Fin 4) (f : B ⟶ X) : (1 : Y ⟶ Zob A B) ≫ pb A B j ≫ f = 1 ≫ f := by
  rw [← Category.assoc, one_pb]

end

section Sym
variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem evc_symm {P : LB (A ⊗ A).left} (hP : P.IsLB) (hPs : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    {Y : Over S} (a a' : Y ⟶ A) : evc hP a a' = evc hP a' a := by
  have e₁ : cls P hP = evc hP (snd A A) (fst A A) := (CechPic.cls_eq_iff hP (pull_isLB hP _)).2 hPs
  change CechPic.pull (lift a a').left (cls P hP) = _
  rw [e₁, pull_evc, lift_snd, lift_fst]

theorem evc_mu_symm {P : LB (A ⊗ A).left} (hP : P.IsLB) (hPs : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    {Q : LB (A ⊗ B).left} (hQ : IsDual A B Q) (hQ' : IsDual B A (swap Q)) {d : ℕ} {la : A ⟶ B} {mu : B ⟶ A}
    (hmu : IsMonHom mu) (hlm : la ≫ mu = 𝟙 A ^ d) (hml : mu ≫ la = 𝟙 B ^ d)
    (hPQ : LBIso P (ev Q (fst A A) (snd A A ≫ la)))
    (htor : ∀ x y : B ⟶ A, IsMonHom x → IsMonHom y → x ^ d = y ^ d → x = y)
    {Y : Over S} (b b' : Y ⟶ B) : evc hQ.isLB (b' ≫ mu) b = evc hQ.isLB (b ≫ mu) b' := by
  have hQl := hQ.isLB
  have hs := hQ'.isLB
  have addL : ∀ (Y : Over S) (a a' : Y ⟶ A) (b : Y ⟶ B), evc hQl (a * a') b = evc hQl a b + evc hQl a' b :=
    (isAdditive_iff hQl).1 hQ.additive
  have addR : ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B), evc hQl a (b * b') = evc hQl a b + evc hQl a b' := by
    intro Y a b b'
    have k := (isAdditive_iff hs).1 hQ'.additive Y b b' a
    rwa [evc_swap hQl hs, evc_swap hQl hs, evc_swap hQl hs] at k
  have powL : ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ), evc hQl (a ^ n) b = n • evc hQl a b := by
    intro Y a b n
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact hQ.additive.evc_one hQl b
    | succ n ih => rw [pow_succ, addL, ih, succ_nsmul]
  have powR : ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ), evc hQl a (b ^ n) = n • evc hQl a b := by
    intro Y a b n
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact evc_one_right hQl hQ.zero a
    | succ n ih => rw [pow_succ, addR, ih, succ_nsmul]
  have PQ : ∀ (Y : Over S) (a a' : Y ⟶ A), evc hP a a' = evc hQl a (a' ≫ la) := by
    intro Y a a'
    have e₂ : cls P hP = evc hQl (fst A A) (snd A A ≫ la) := (CechPic.cls_eq_iff hP (pull_isLB hQl _)).2 hPQ
    change CechPic.pull (lift a a').left (cls P hP) = _
    rw [e₂, pull_evc, lift_fst, lift_snd_assoc]

  let Mb : LB (B ⊗ B).left := ev Q (fst B B ≫ mu) (snd B B)
  have hM : Mb.IsLB := pull_isLB hQl _
  have evcM : ∀ (Y : Over S) (b t : Y ⟶ B), evc hM b t = evc hQl (b ≫ mu) t := by
    intro Y b t
    rw [evc_ev hQl, lift_fst_assoc, lift_snd]
  have haM : IsAdditive Mb := (isAdditive_iff hM).2 fun Y b b' t => by
    rw [evcM, evcM, evcM, MonObj.mul_comp, addL]
  obtain ⟨x, hx, -⟩ := hQ'.univ B Mb hM haM
  have K : ∀ (Y : Over S) (b t : Y ⟶ B), evc hQl (b ≫ mu) t = evc hQl (t ≫ x) b := by
    intro Y b t
    have c := (CechPic.cls_eq_iff hM (pull_isLB hs _)).2 hx
    have k : evc hM b t = evc (pull_isLB hs _) b t := congrArg (CechPic.pull (lift b t).left) c
    rw [evc_ev hs, lift_fst, lift_snd_assoc, evc_swap hQl hs, evcM] at k
    exact k
  have hss : (swap (swap Q)).IsLB := pull_isLB hs _
  have ha' : IsAdditive (swap (swap Q)) := (isAdditive_iff hss).2 fun Y a a' t => by
    simp only [evc_swap hs hss, evc_swap hQl hs]; exact addL Y a a' t
  have hsM : (swap Mb).IsLB := pull_isLB hM _
  have haSM : IsAdditive (swap Mb) := (isAdditive_iff hsM).2 fun Y t t' b => by
    simp only [evc_swap hM hsM, evcM]; exact addR Y _ t t'
  have hxm : IsMonHom x := isMonHom_of_classifying S B B A Mb (swap Q) hQ' ha' hM haSM x hx
  have key : ∀ (Y : Over S) (b : Y ⟶ B) (a : Y ⟶ A), evc hQl (a ≫ la ≫ x) b = evc hQl (a ≫ la ≫ mu) b := by
    intro Y b a
    rw [← Category.assoc a la x, ← K, ← PQ, evc_symm hP hPs, PQ, Category.assoc, hml, hlm, comp_pow,
      Category.comp_id, comp_pow, Category.comp_id, powR, powL]
  have lx : la ≫ x = la ≫ mu := by
    apply hQ'.eq_of_evc
    simpa only [evc_swap hQl hs] using key _ (fst B A) (snd B A)
  have xd : x ^ d = mu ^ d := by
    have e₁ : (𝟙 B ^ d) ≫ x = x ^ d := by rw [MonObj.pow_comp, Category.id_comp]
    have e₂ : (𝟙 B ^ d) ≫ mu = mu ^ d := by rw [MonObj.pow_comp, Category.id_comp]
    rw [← e₁, ← e₂, ← hml, Category.assoc, lx, ← Category.assoc]
  have xm : x = mu := htor x mu hxm hmu xd
  rw [K, xm]

end Sym

theorem zarhinBundle_rigidified_symmetric₂ : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (1 : (GlobalTheory.ZarhinFam.Zob c.A B) ⟶ (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (1 : (GlobalTheory.ZarhinFam.Zob c.A B) ⟶ (GlobalTheory.ZarhinFam.Zob c.A B))).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.Zob c.A B)) (fst (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.Zob c.A B))).left) := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ hd _ hdu _
  have hQ := hZ.2.1
  haveI : IsMonHom mu := hZ.2.2.2.2.1
  refine ⟨(zarhinBundle_pull_trivial_iff _ _ _ _ _ _ _).2 ?_, (zarhinBundle_pull_trivial_iff _ _ _ _ _ _ _).2 ?_, ?_⟩
  · rw [pull_zCls]
    simp only [one_pa, one_pb, one_pb_assoc, MonObj.one_comp, Category.id_comp, evc_one_left c.isLB c.rig₁,
      hQ.additive.evc_one hQ.isLB, evc_one_right hQ.isLB hQ.zero, smul_zero, Finset.sum_const_zero, add_zero]
  · rw [pull_zCls]
    simp only [one_pa, one_pb, one_pb_assoc, MonObj.one_comp, Category.id_comp, evc_one_right c.isLB c.rig₂,
      hQ.additive.evc_one hQ.isLB, evc_one_right hQ.isLB hQ.zero, smul_zero, Finset.sum_const_zero, add_zero]
  · have hz := zarhinBundle_isLineBundle c.A B c.isLB hQ.isLB d mu
    refine (CechPic.cls_eq_iff hz (pull_isLB hz _)).1 ?_
    rw [cls_pull hz, cls_zP]
    conv_lhs => rw [← pull_id (zCls _ _ _ _ _ _), ← Over.id_left, ← lift_fst_snd]
    rw [pull_zCls, pull_zCls]
    have htor : ∀ x y : B ⟶ c.A, IsMonHom x → IsMonHom y → x ^ d = y ^ d → x = y :=
      GlobalTheory.T.abelianScheme_hom_eq_of_pow_eq S c.A B c.ab hZ.1 d hd hdu
    have h1 : ∑ i, evc c.isLB (fst (Zob c.A B) (Zob c.A B) ≫ pa c.A B i) (snd (Zob c.A B) (Zob c.A B) ≫ pa c.A B i) =
        ∑ i, evc c.isLB (snd (Zob c.A B) (Zob c.A B) ≫ pa c.A B i) (fst (Zob c.A B) (Zob c.A B) ≫ pa c.A B i) :=
      Finset.sum_congr rfl fun i _ => evc_symm c.isLB c.symm _ _
    have h4 : ∑ j, evc hQ.isLB (snd (Zob c.A B) (Zob c.A B) ≫ pb c.A B j ≫ mu) (fst (Zob c.A B) (Zob c.A B) ≫ pb c.A B j) =
        ∑ j, evc hQ.isLB (fst (Zob c.A B) (Zob c.A B) ≫ pb c.A B j ≫ mu) (snd (Zob c.A B) (Zob c.A B) ≫ pb c.A B j) :=
      Finset.sum_congr rfl fun j _ => by
        simpa only [Category.assoc] using evc_mu_symm c.isLB c.symm hQ hZ.2.2.1 hZ.2.2.2.2.1 hZ.2.2.2.2.2.1
          hZ.2.2.2.2.2.2.1 hZ.2.2.2.2.2.2.2 htor (fst (Zob c.A B) (Zob c.A B) ≫ pb c.A B j) (snd (Zob c.A B) (Zob c.A B) ≫ pb c.A B j)
    rw [h1, h4]
    abel

end GlobalTheory.ZarhinFam.Rig
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc


theorem _root_.GlobalTheory.T.exists_zarhinSymplecticTransfer : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ), GlobalTheory.ZarhinFam.KappaOK h M d κ := by
  first | (exact @GlobalTheory.ZarhinFam.exists_kappaOK) | (exact GlobalTheory.ZarhinFam.exists_kappaOK) | (intros; apply GlobalTheory.ZarhinFam.exists_kappaOK  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.zarhinBundle_kernel_firstCoord_equations : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i ≫ la) * ∏ j, (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  first | (exact @GlobalTheory.ZarhinKerA.zarhinBundle_kernel) | (exact GlobalTheory.ZarhinKerA.zarhinBundle_kernel) | (intros; apply GlobalTheory.ZarhinKerA.zarhinBundle_kernel  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.zarhinProductLevelStructure_eq_mkPoint : ∀ {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (d h h' : ℕ) (la : A ⟶ B) (mu : B ⟶ A) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) (κ : Fin 8 → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (a : Fin h' ⊕ Fin h' → ℤ), GlobalTheory.ZarhinFam.levZ lev (GlobalTheory.ZarhinFam.incZ A B) (GlobalTheory.ZarhinFam.actZ A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ a = GlobalTheory.ZarhinFam.mkZ A B (fun i => lev (κ (Fin.castAdd 4 i) a)) (fun j => lev (κ (Fin.natAdd 4 j) a) ≫ la) := by
  first | (exact @GlobalTheory.ZarhinFam.levZ_eq_mkZ) | (exact GlobalTheory.ZarhinFam.levZ_eq_mkZ) | (intros; apply GlobalTheory.ZarhinFam.levZ_eq_mkZ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.zarhinSymplecticTransfer_bijective_mod : ∀ (h M d : ℕ) (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), 1 ≤ M → GlobalTheory.ZarhinFam.KappaOK h M d κ → (∀ a, (∀ k, ∃ b, κ k a = M • b) ↔ ∃ b, a = M • b) ∧ ∀ cc : Fin 8 → (Fin h ⊕ Fin h → ℤ), ∃ a, ∀ k, ∃ b, κ k a = cc k + M • b := by
  first | (exact @GlobalTheory.ZarhinFam.kappaOK_mod) | (exact GlobalTheory.ZarhinFam.kappaOK_mod) | (intros; apply GlobalTheory.ZarhinFam.kappaOK_mod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.zarhinBundle_kernel_secondCoord_equations : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ j, ((∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i) ≫ la) * (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ d = 1 := by
  first | (exact @GlobalTheory.ZarhinKerB.zarhinBundle_kernel) | (exact GlobalTheory.ZarhinKerB.zarhinBundle_kernel) | (intros; apply GlobalTheory.ZarhinKerB.zarhinBundle_kernel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam.PtFacts

theorem mkZ_facts : ∀ {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T T' : Over S} (f : T' ⟶ T) (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (g : T ⟶ GlobalTheory.ZarhinFam.Zob A B) (n : ℕ), f ≫ GlobalTheory.ZarhinFam.mkZ A B u v = GlobalTheory.ZarhinFam.mkZ A B (fun i => f ≫ u i) (fun j => f ≫ v j) ∧ GlobalTheory.ZarhinFam.mkZ A B u v ^ n = GlobalTheory.ZarhinFam.mkZ A B (fun i => u i ^ n) (fun j => v j ^ n) ∧ (GlobalTheory.ZarhinFam.mkZ A B u v = 1 ↔ (∀ i, u i = 1) ∧ ∀ j, v j = 1) ∧ g = GlobalTheory.ZarhinFam.mkZ A B (fun i => g ≫ GlobalTheory.ZarhinFam.pa A B i) (fun j => g ≫ GlobalTheory.ZarhinFam.pb A B j) := by
  intro S A B _ _ _ _ T T' f u v g n
  refine ⟨?_, ?_, ⟨fun h => ⟨fun i => ?_, fun j => ?_⟩, fun ⟨hu, hv⟩ => ?_⟩, ?_⟩
  · apply LevAlg.zob_ext
    · intro i; simp only [Category.assoc, LevAlg.mkZ_pa]
    · intro j; simp only [Category.assoc, LevAlg.mkZ_pb]
  · apply LevAlg.zob_ext
    · intro i; rw [MonObj.pow_comp, LevAlg.mkZ_pa, LevAlg.mkZ_pa]
    · intro j; rw [MonObj.pow_comp, LevAlg.mkZ_pb, LevAlg.mkZ_pb]
  · rw [← LevAlg.mkZ_pa A B u v i, h, MonObj.one_comp]
  · rw [← LevAlg.mkZ_pb A B u v j, h, MonObj.one_comp]
  · apply LevAlg.zob_ext
    · intro i; rw [LevAlg.mkZ_pa, MonObj.one_comp, hu]
    · intro j; rw [LevAlg.mkZ_pb, MonObj.one_comp, hv]
  · apply LevAlg.zob_ext
    · intro i; rw [LevAlg.mkZ_pa]
    · intro j; rw [LevAlg.mkZ_pb]

end GlobalTheory.ZarhinFam.PtFacts
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinFam.KerC

theorem ker_zarhinPolarization_of_pullback : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → (∀ j, x ≫ GlobalTheory.ZarhinFam.pb c.A B j = 1) → ∀ j, ∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  intro h M d S t c B _ _ Q la mu hZ T x hx hv j
  obtain ⟨hB, hD1, hD2, hla, hmu, hlm, hml, hPiso⟩ := id hZ
  haveI : IsMonHom la := hla
  have hQ : Q.IsLB := hD1.isLB
  have hPQ : ∀ (Y : Over S) (a a' : Y ⟶ c.A), evc c.isLB a a' = evc hQ a (a' ≫ la) := by
    have e : cls c.P c.isLB = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
      (cls_eq_iff c.isLB (pull_isLB hQ _)).2 hPiso
    intro Y a a'
    show CechPic.pull (lift a a').left (cls c.P c.isLB) = _
    rw [e, pull_evc, lift_fst, lift_snd_assoc]
  have hz := zarhinBundle_isLineBundle c.A B c.isLB hQ d mu
  have h0 : CechPic.pull (lift (snd (Zob c.A B) T ≫ x) (fst (Zob c.A B) T)).left
      (zCls c.A B c.isLB hQ d mu) = 0 := by
    rw [← cls_zP c.A B c.isLB hQ d mu, ← cls_pull hz]
    exact (cls_eq_zero_iff (pull_isLB hz _)).2 hx
  have h1 := congrArg (CechPic.pull
    (lift (mkZ c.A B (fun _ => 1) (fun j' => if j' = j then snd T B else 1)) (fst T B) :
      T ⊗ B ⟶ Zob c.A B ⊗ T).left) h0
  rw [← pull_comp, ← Over.comp_left, comp_lift, map_zero, lift_snd_assoc, lift_fst,
    AdjPf.pull_zCls c.isLB hQ d la mu hPQ] at h1
  simp only [AdjPf.zf, Category.assoc, AdjPf.mkZ_pa, AdjPf.mkZ_pb, hv, MonObj.comp_one, MonObj.one_comp,
    evc_one_right hQ hD1.zero, hD1.additive.evc_one hQ, smul_zero, Finset.sum_const_zero, zero_add, add_zero] at h1
  simp only [apply_ite (evc hQ _), evc_one_right hQ hD1.zero, smul_ite, smul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h1
  refine (hD1.isPerfect hD2).ker_left T _ ((triv_ev_iff hQ _ _).2 ?_)
  let F : (T ⊗ B ⟶ c.A) →* Multiplicative (Pic (T ⊗ B).left) :=
    MonoidHom.mk' (fun a => Multiplicative.ofAdd (evc hQ a (snd T B))) fun a a' => by
      rw [(isAdditive_iff hQ).1 hD1.additive, ofAdd_add]
  have eF : ∀ a, evc hQ a (snd T B) = Multiplicative.toAdd (F a) := fun _ => rfl
  have ep : fst T B ≫ ∏ i, (x ≫ pa c.A B i) ^ quat d j i = ∏ i, (fst T B ≫ x ≫ pa c.A B i) ^ quat d j i := by
    have := map_prod (AdjPf.pre (G := c.A) (fst T B)) (fun i => (x ≫ pa c.A B i) ^ quat d j i) Finset.univ
    simp only [map_zpow] at this
    exact this
  rw [ep, eF, map_prod, toAdd_prod]
  simp only [map_zpow, toAdd_zpow, ← eF]
  exact h1

end GlobalTheory.ZarhinFam.KerC
end
end

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt

theorem _root_.GlobalTheory.T.seriesRationality_back_from_movedReadings : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ), (∀ i σ, w i σ ∈ Subgroup.center Γ) → ∃ (S' : NX.RatDat D.ntw) (YS' : NX.NExpRealS (fullHeckeRealDatMovedReadings Rl w) cG S'), ∀ (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), RatRow YS' v₀ hρ i j b → RatRow YS v₀ hρ i j b := by
  first | exact @GlobalTheory.UnframeForms.ratRow_back | exact GlobalTheory.UnframeForms.ratRow_back | (intros; apply GlobalTheory.UnframeForms.ratRow_back <;> assumption)
end
