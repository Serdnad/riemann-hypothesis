module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2849
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.Mum.PowData.CmpTwoProof

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  intro i j
  have e : (LB.LinComb L (Y := Y) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i j = 1 := by
    dsimp only [LB.LinComb]
    erw [Fintype.prod_empty]
    rfl
  show res _ (1 : Γ(Y, _)ˣ) = _ * res _ (1 : Γ(Y, _)ˣ)
  rw [map_one, map_one, e, _root_.one_mul]

theorem pull_cls_of_isPart {X X₁ : Scheme.{0}} {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι}
    (h : IsPart N M e π) (hN : N.IsLB) (hM : M.IsLB) : CechPic.pull e (cls N hN) = cls M hM := by
  have h1 := LB.isLB_linComb hN (fun _ : PUnit.{1} => 𝟙 X₁ ≫ e) (fun _ => 1)
  have h2 := LB.isLB_linComb hM (fun _ : PUnit.{1} => 𝟙 X₁) (fun _ => 1)
  have a := cls_linComb hN _ _ h1
  have b := cls_linComb hM _ _ h2
  have c := (cls_eq_iff h1 h2).2 (iso_of_chart h2 (h.up (fun _ : PUnit.{1} => 𝟙 X₁) (fun _ => 1)))
  have := (a.symm.trans c).trans b
  simpa only [Fintype.sum_unique, one_smul, Category.id_comp, pull_id] using this

theorem comp_one_pt {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit X) (toUnit Y)]

theorem one_comp_hom {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] (f : M ⟶ N) [IsMonHom f] :
    (1 : X ⟶ M) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

end GlobalTheory.Mum.PowData.CmpTwoProof

open GlobalTheory.Mum.PowData.CmpTwoProof in
theorem GlobalTheory.Mum.PowData.cmpTwo_of_adjCls : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (j : D₀.P.A ⟶ D.P.A), IsMonHom q → IsMonHom j → AdjCls (cls D.P.L D.P.isLB) (cls D₀.P.L D₀.P.isLB) q j → CmpTwo D D₀ q j := by
  intro R _ _ D D₀ q j hq hj hadj
  haveI := hq
  haveI := hj
  have hN : (JN D D₀).IsLB := jn_isLB D D₀
  have hG := GlobalTheory.globalFns_holds
  have pl := pull_cls_of_isPart (isPart_inl D.P.L D₀.P.L) hN D.P.isLB
  have pr := pull_cls_of_isPart (isPart_inr D.P.L D₀.P.L) hN D₀.P.isLB
  let φΓ : Fin 4 ⊕ Fin 4 → ((D.P.A ⊗ D₀.P.A).left ⟶ (D.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) :=
    Sum.elim (fun k => lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j) k ≫ coprod.inl)
      (fun k => lamPts (fst D.P.A D₀.P.A ≫ q) (snd D.P.A D₀.P.A) k ≫ coprod.inr)
  let εΓ : Fin 4 ⊕ Fin 4 → ℤ := Sum.elim Oε Oinvε
  have hL1 := LB.isLB_linComb hN φΓ εΓ

  have h0 : cls _ hL1 = 0 := by
    rw [cls_linComb hN _ _ hL1, Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_four]
    simp only [φΓ, εΓ, Sum.elim_inl, Sum.elim_inr, pull_comp, pl, pr]
    refine Eq.trans ?_ (sub_eq_zero.2 (hadj _ (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A)))
    simp only [lam, lamPts, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    abel
  obtain ⟨Γ₀, hΓ₀⟩ := (cls_eq_zero_iff hL1).1 h0

  let o : (D.P.A ⊗ D₀.P.A).left ⟶ (D.P.A ⊗ D₀.P.A).left :=
    (toUnit (D.P.A ⊗ D₀.P.A) ≫ lift (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A)).left
  have hz : ∀ k, o ≫ φΓ k = Sum.elim (fun _ : Fin 4 => (1 : D.P.A ⊗ D₀.P.A ⟶ D.P.A).left ≫ coprod.inl)
      (fun _ : Fin 4 => (1 : D.P.A ⊗ D₀.P.A ⟶ D₀.P.A).left ≫ coprod.inr) k := by
    rintro (k | k) <;> simp only [φΓ, Sum.elim_inl, Sum.elim_inr, ← Category.assoc] <;> congr 1 <;>
      fin_cases k <;>
      simp only [lamPts, o, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, ← Over.comp_left, Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
        lift_fst_assoc, lift_snd_assoc, comp_one_pt, one_comp_hom, _root_.mul_one, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  have fe0 : FormEq (Sum.elim φΓ (fun k => o ≫ φΓ k)) (Sum.elim εΓ (fun k => - εΓ k)) φΓ εΓ := by
    intro U _ h
    have hQ : ∏ k, h (o ≫ φΓ k) ^ (- εΓ k) = 1 := by
      simp only [hz]
      rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four]
      simp only [Sum.elim_inl, Sum.elim_inr, εΓ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      simp only [neg_neg, one_smul, neg_smul]
      abel
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hQ, _root_.mul_one]
  obtain ⟨Γ, hΓ, hΓv⟩ := exists_gen hN fe0 (LB.mulGen _ _ _ _ _ Γ₀ (LB.invGen _ _ _ (LB.pullGen _ _ _ Γ₀ o)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hΓ₀ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hΓ₀ o)))
  have hone : ∀ (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ D₀.P.A).left) (z : Z) (J), Good (JN D D₀) z J → r ≫ o = r →
      val Γ r z J = 1 := by
    intro Z r z J hJ hr
    rw [hΓv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, hr, mul_inv_cancel]
  have o₀ : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) = η[D₀.P.A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have o' : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = η[D.P.A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

  let ι₀ : D₀.P.A.left ⟶ (D.P.A ⊗ D₀.P.A).left := (lift (1 : D₀.P.A ⟶ D.P.A) (𝟙 D₀.P.A)).left
  have fe1 : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => ι₀ ≫ φΓ k) εΓ := by
    intro U _ h
    rw [Fintype.prod_empty, Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four]
    simp only [φΓ, εΓ, Sum.elim_inl, Sum.elim_inr, lamPts, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, ι₀, ← Category.assoc,
      ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd, comp_one_pt, one_comp_hom, Category.id_comp,
      _root_.one_mul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    simp only [one_smul, neg_smul]
    abel
  have e0 : (η[D₀.P.A] ≫ lift (1 : D₀.P.A ⟶ D.P.A) (𝟙 D₀.P.A)) ≫ toUnit _ ≫
      lift (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) =
      η[D₀.P.A] ≫ lift (1 : D₀.P.A ⟶ D.P.A) (𝟙 D₀.P.A) := by
    rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (𝟙 _), Category.id_comp, comp_lift, comp_one_pt,
      Category.comp_id, o₀]
  have key1 := gen_unique' hN (u := LB.pullGen _ _ _ Γ ι₀) (u' := LB.oneGen (JN D D₀) (Y := D₀.P.A.left)) fe1
    D₀.P.A.hom (eSec D₀.P.A) (Over.w η[D₀.P.A]) (hG _ _ D₀.P.isAb).2 (DVR.pullGen_isGen _ _ _ _ hΓ ι₀)
    (oneGen_isGen _) (fun y J hJ => by
      rw [val_pull hJ, val_one]
      refine hone _ _ y J hJ ?_
      have := congrArg (fun f => f.left) e0
      simpa only [eSec, ι₀, o, Over.comp_left] using this)
  have hΓ1 : ∀ (T : Over (Sp R)) (w : T ⟶ D₀.P.A) (y : T.left) (J), Good (JN D D₀) y J →
      val Γ (lift (1 : T ⟶ D.P.A) w).left y J = 1 := by
    intro T w y J hJ
    have := key1 T.left w.left y J hJ
    rw [val_pull hJ, val_one] at this
    rwa [show w.left ≫ ι₀ = (lift (1 : T ⟶ D.P.A) w).left by
      rw [← Over.comp_left, comp_lift, comp_one_pt, Category.comp_id]] at this
  refine ⟨Γ, hΓ, ?_⟩
  intro χ' χ hc u hu T x z J hJ
  let m : D.P.A.left ⟶ (D.P.A ⊗ D₀.P.A).left := (lift (𝟙 D.P.A) (toUnit D.P.A ≫ D₀.c χ)).left
  have pm : ∀ {X Y : Over (Sp R)} [GrpObj Y] (a b : X ⟶ Y), padd Y a b = a * b := fun _ _ => rfl
  have fe2 : FormEq (fun k => m ≫ φΓ k) εΓ
      (Sum.elim (fun k => D.Oφ (𝟙 _) χ' k ≫ coprod.inl) (fun k => D₀.Oφ q χ k ≫ coprod.inr)) (Sum.elim Oε Oinvε) := by
    intro U _ h
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_four,
      Fin.prod_univ_four]
    simp only [φΓ, εΓ, Sum.elim_inl, Sum.elim_inr, lamPts, DegPre.Oφ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, m, pm, ← Hom.one_def, hc,
      ← Category.assoc, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd, Category.id_comp, Category.comp_id, comp_one_pt]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    simp only [one_smul, neg_smul]
    abel
  have ev2 : ∀ y I, Good (JN D D₀) y I → val u (eSec D.P.A) y I = val (LB.pullGen _ _ _ Γ m) (eSec D.P.A) y I := by
    intro y I hI
    rw [val_pull hI]
    have c := hu.2 _ (𝟙 _) y I hI
    rw [Category.id_comp] at c
    have e2 : eSec D.P.A ≫ m = (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (toUnit _ ≫ D₀.c χ)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
        toUnit_unique (η[D.P.A] ≫ toUnit _) (toUnit _), o']
    rw [c, e2, hΓ1 _ _ y I hI]
  have key := gen_unique' hN (u := u) (u' := LB.pullGen _ _ _ Γ m) fe2 D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A])
    (hG _ _ D.P.isAb).2 hu.1 (DVR.pullGen_isGen _ _ _ _ hΓ m) ev2 T.left x.left z J hJ
  rw [key, val_pull hJ]
  congr 1
  rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit T)]
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.PowData

theorem tens_iso_psi : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D.P.A ⟶ D₀.P.A)) (j : Fin r → (D₀.P.A ⟶ D.P.A)) (h : Fin r → D₀.X → D.X) (k : Fin r → D.X → D₀.X), (∀ a χ, D.c (h a χ) = D₀.c χ ≫ j a) → (∀ a y, D₀.c (k a y) = D.c y ≫ pr a) → (∀ a, PeriodRel D D₀ (pr a) (h a) (k a)) → (∀ a, CmpTwo D D₀ (pr a) (j a)) → Expand D (fun ab : Fin r × Fin r => W ab.1 ab.2) (𝟙 D.P.A) (fun ab => pr ab.2 ≫ j ab.1) → PrimVal D (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) (fun y => ∑ ab : Fin r × Fin r, W ab.1 ab.2 • h ab.1 (k ab.2 y)) → ∃ w : LB.Iso D.P.L (LB.LinComb D₀.P.L (tensφ pr) (tensε W)), w.IsGen ∧ ∀ y z J J', Good D₀.P.L z J → Good D.P.L z J' → val (D.psi y) (𝟙 _) z J' = gm (D.xK y) z _ (w.s (fun k => J (D.xK y ≫ tensφ pr k), J' (D.xK y))) * ∏ a, ∏ b, val (D₀.tau (k a y) (k b y)) (𝟙 _) z J ^ W a b := by
  intro R _ _ D D₀ r W pr j h k h1 h2 h3 h4 h5 h6
  obtain ⟨u, hu, hu'⟩ := h6
  obtain ⟨κ, hκ, hκ'⟩ := h5
  choose Γ hΓ hΓ' using h4
  have hp₁ := isPart_inl D.P.L D₀.P.L
  let g : Fin r → (D.P.A.left ⟶ (D.P.A ⊗ D₀.P.A).left) := fun b => (lift (𝟙 D.P.A) (pr b)).left
  let Φ : Fin r → Fin 4 ⊕ Fin 4 → ((D.P.A ⊗ D₀.P.A).left ⟶ D.P.A.left ⨿ D₀.P.A.left) := fun a =>
    Sum.elim (fun k => lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j a) k ≫ coprod.inl)
      (fun k => lamPts (fst D.P.A D₀.P.A ≫ pr a) (snd D.P.A D₀.P.A) k ≫ coprod.inr)
  let P := prodZGen (JN D D₀) (fun ab : Fin r × Fin r => fun m => g ab.2 ≫ Φ ab.1 m) (fun _ => Sum.elim Oε Oinvε)
    (fun ab => -W ab.1 ab.2) (fun ab => LB.pullGen (JN D D₀) _ _ (Γ ab.1) (g ab.2))
  have hP : P.IsGen := prodZGen_isGen (jn_isLB D D₀) _ fun ab =>
    ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (hΓ ab.1) _
  let rig0 := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (toUnit D.P.A).left
  have hrig0 : rig0.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ D.rig_gen _
  let T0 := LB.mulGen (JN D D₀) _ _ _ _ (LB.mulGen (JN D D₀) _ _ _ _ (LB.mulGen (JN D D₀) _ _ _ _ (hp₁.gen u)
    (LB.invGen (JN D D₀) _ _ (hp₁.gen κ))) P) (LB.invGen (JN D D₀) _ _ (hp₁.gen rig0))
  have hT0 : T0.IsGen := by
    refine ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hp₁.gen_isGen hu) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _
        (hp₁.gen_isGen hκ))) hP) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hp₁.gen_isGen hrig0))
  obtain ⟨t, ht, htv⟩ := exists_gen (jn_isLB D D₀)
    (φ' := Sum.elim (fun k => tensφ pr k ≫ coprod.inr) (fun _ : PUnit => 𝟙 D.P.A.left ≫ coprod.inl))
    (ε' := Sum.elim (tensε W) (fun _ => -1)) (by
      intro U _ hh
      clear hu' hκ' hΓ' h3 h1 h2 hT0 hP hrig0
      have cl : ∀ {T T' : Over (Sp R)} {B : Over (Sp R)} [GrpObj B] (s : T' ⟶ T) (x y : T ⟶ B) (i : Fin 4),
          s.left ≫ lamPts x y i = lamPts (s ≫ x) (s ≫ y) i := by
        intro T T' B _ s x y i
        fin_cases i
        · exact congrArg (fun q => q.left) (MonObj.comp_mul s x y)
        · rfl
        · rfl
        · exact congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_one s)
      have hD1 : ∀ a b i, g b ≫ Φ a (Sum.inl i) = lamPts (𝟙 D.P.A) (pr b ≫ j a) i ≫ coprod.inl := by
        intro a b i
        show (lift (𝟙 D.P.A) (pr b)).left ≫ lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j a) i ≫ coprod.inl = _
        rw [← Category.assoc, cl, lift_fst, lift_snd_assoc]
      have hD2 : ∀ a b i, g b ≫ Φ a (Sum.inr i) = tensφ pr ((a, b), i) ≫ coprod.inr := by
        intro a b i
        show (lift (𝟙 D.P.A) (pr b)).left ≫ lamPts (fst D.P.A D₀.P.A ≫ pr a) (snd D.P.A D₀.P.A) i ≫ coprod.inr = _
        rw [← Category.assoc, cl, lift_fst_assoc, lift_snd, Category.id_comp]
        rfl
      have hOi : ∀ i, Oinvε i = - Oε i := by intro i; fin_cases i <;> rfl
      have hCD : (∏ p : (Fin r × Fin r) × Fin 4,
            hh (lamPts (𝟙 D.P.A) (pr p.1.2 ≫ j p.1.1) p.2 ≫ coprod.inl) ^ (- -(W p.1.1 p.1.2 * Oε p.2))) *
          (∏ p : (Fin r × Fin r) × (Fin 4 ⊕ Fin 4), hh (g p.1.2 ≫ Φ p.1.1 p.2) ^ (-W p.1.1 p.1.2 * Sum.elim Oε Oinvε p.2)) =
          ∏ p : (Fin r × Fin r) × Fin 4, hh (tensφ pr p ≫ coprod.inr) ^ (tensε W p) := by
        rw [Fintype.prod_prod_type (α₁ := Fin r × Fin r), Fintype.prod_prod_type (α₁ := Fin r × Fin r),
          Fintype.prod_prod_type (α₁ := Fin r × Fin r), ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun ab _ => ?_
        rw [Fintype.prod_sum_type, ← _root_.mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hD1, hD2, Sum.elim_inl, Sum.elim_inr, hOi]
        simp only [tensε, neg_neg, neg_mul, mul_neg, zpow_neg, mul_inv_cancel, _root_.one_mul, Prod.mk.eta]
      have hAB : (∏ i : Fin 4, hh (![(padd D.P.A (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2)).left,
            𝟙 D.P.A.left, (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2).left, (toUnit D.P.A ≫ η[D.P.A]).left] i ≫
              coprod.inl) ^ ((![1, -2, -1, 2] : Fin 4 → ℤ) i)) *
          (∏ i : Fin 4, hh (lamPts (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) i ≫ coprod.inl) ^
            (-Oε i)) =
          (hh (𝟙 D.P.A.left ≫ coprod.inl))⁻¹ * hh ((toUnit D.P.A ≫ η[D.P.A]).left ≫ coprod.inl) := by
        simp only [Fin.prod_univ_four, lamPts, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        have e0 : (𝟙 D.P.A * ∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) =
            padd D.P.A (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) := rfl
        have e1 : (1 : D.P.A ⟶ D.P.A) = toUnit D.P.A ≫ η[D.P.A] := rfl
        have e2 : (𝟙 D.P.A : D.P.A ⟶ D.P.A).left = 𝟙 D.P.A.left := rfl
        rw [e0, e1, e2]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
      have key : ∀ A B C D E Q I O : U, A * B = I⁻¹ * O → C * D = Q → E = O ^ (-1 : ℤ) →
          A * (B * C) * D * E = Q * I ^ (-1 : ℤ) := by
        intro A B C D E Q I O h₁ h₂ h₃
        rw [← _root_.mul_assoc A B C, h₁, _root_.mul_assoc _ C D, h₂, h₃]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.prod_singleton]
      exact key _ _ _ _ _ _ _ _ hAB hCD rfl) T0 hT0
  obtain ⟨w, hw, hwv⟩ := exists_iso_of_joinGen D.P.isLB D₀.P.isLB t ht
  refine ⟨w, hw, fun y z J J' hJ hJ' => ?_⟩
  obtain ⟨Jn, hJn, e1, e2⟩ := exists_good_join D.P.isLB D₀.P.isLB hJ' hJ
  subst e1 e2
  rw [hwv _ (D.xK y) z Jn hJn, htv _ _ z Jn hJn]
  have hp₂ := isPart_inr D.P.L D₀.P.L
  have hJ1 : Good D.P.L z (rl Jn) := hp₁.good hJn
  have vT : val T0 (D.xK y) z Jn = val u (D.xK y) z (rl Jn) * (val κ (D.xK y) z (rl Jn))⁻¹ *
      (∏ ab : Fin r × Fin r, val (Γ ab.1) (D.xK y ≫ g ab.2) z Jn ^ (-W ab.1 ab.2)) *
      (val D.rig (D.xK y ≫ (toUnit D.P.A).left) z (rl Jn))⁻¹ := by
    simp only [T0, P, rig0, val_mul hJn, val_inv, hp₁.val_gen _ _ _ hJn, val_prodZGen _ _ _ _ _ hJn, val_pull hJn,
      val_pull hJ1]
  have c1 := val_corr hJ1 (hu' y) (𝟙 _)
  rw [val_mul hJ1, val_mul hJ1, val_pull hJ1, Category.id_comp] at c1
  have cE := hκ' (toUnit (TK R) ≫ D.c y) y (fun ab => h ab.1 (k ab.2 y)) (Category.comp_id _)
    (fun ab => by simp only [h1, h2, Category.assoc]) z (rl Jn) hJ1
  have hrig : D.xK y ≫ (toUnit D.P.A).left = 𝟙 _ ≫ (toUnit (TK R)).left := by
    rw [Category.id_comp]
    show (toUnit (TK R) ≫ D.c y).left ≫ (toUnit D.P.A).left = _
    rw [← Over.comp_left, Category.assoc, comp_toUnit, comp_toUnit]
  have vrig : val D.rig (D.xK y ≫ (toUnit D.P.A).left) z (rl Jn) = val D.rigK (𝟙 _) z (rl Jn) := by
    rw [hrig]; exact (val_pull hJ1 _ _ _).symm
  have hper : ∀ a b, val (D₀.tau (k a y) (k b y)) (𝟙 _) z (rr Jn) =
      val (D.tau y (h a (k b y))) (𝟙 _) z (rl Jn) * val (Γ a) (D.xK y ≫ g b) z Jn := by
    intro a b
    obtain ⟨u', hu'n, hu'v⟩ := h3 a (k b y)
    rw [hu'v y z Jn hJn]
    refine congrArg (_ * ·) ((hΓ' a (h a (k b y)) (k b y) (h1 a (k b y)) u' hu'n (TK R) (toUnit _ ≫ D.c y) z Jn hJn).trans
      (congrArg (fun q => val (Γ a) q z Jn) ?_))
    show (lift (toUnit (TK R) ≫ D.c y) (toUnit (TK R) ≫ D₀.c (k b y))).left =
      (toUnit (TK R) ≫ D.c y).left ≫ (lift (𝟙 D.P.A) (pr b)).left
    rw [h2, ← Over.comp_left, comp_lift, Category.comp_id, Category.assoc]
  have hG : ∏ ab : Fin r × Fin r, val (Γ ab.1) (D.xK y ≫ g ab.2) z Jn ^ (-W ab.1 ab.2) =
      (∏ a, ∏ b, val (Γ a) (D.xK y ≫ g b) z Jn ^ W a b)⁻¹ := by
    rw [Fintype.prod_prod_type]; simp only [zpow_neg, Finset.prod_inv_distrib]
  have key2 : ∀ {V : Type} [CommGroup V] (ψ ρ Tm Uu Kk Tp Gp : V), Tm * Uu = ψ * ρ → Tm * Kk = Tp →
      ψ = Uu * Kk⁻¹ * Gp⁻¹ * ρ⁻¹ * (Tp * Gp) := by
    intro V _ ψ ρ Tm Uu Kk Tp Gp e₁ e₂
    rw [eq_inv_mul_of_mul_eq e₁, eq_inv_mul_of_mul_eq e₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [vT, vrig, hG]
  simp only [hper, mul_zpow, Finset.prod_mul_distrib]
  have cE' : val (D.tau y (∑ ab : Fin r × Fin r, W ab.1 ab.2 • h ab.1 (k ab.2 y))) (𝟙 _) z (rl Jn) *
      val κ (D.xK y) z (rl Jn) = ∏ a, ∏ b, val (D.tau y (h a (k b y))) (𝟙 _) z (rl Jn) ^ W a b := by
    refine Eq.trans cE ?_
    rw [Fintype.prod_prod_type]
  exact key2 _ _ _ _ _ _ _ c1 cE'

end GlobalTheory.Mum.PowData
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp.AddFst

theorem prod_pair {S : Scheme.{0}} {A B : Over S} [GrpObj B] [IsCommMonObj B] (f g : A ⟶ B) {T : Over S} (x y : T ⟶ A)
    {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h ((lift x y).left ≫ (psum B ![fst A A ≫ f, snd A A ≫ g] I.down).left) ^
        ((-1 : ℤ) ^ (2 - I.down.card)) =
      h ((x ≫ f) * (y ≫ g)).left * (h (x ≫ f).left)⁻¹ * (h (y ≫ g).left)⁻¹ * h (1 : T ⟶ B).left := by
  have e : ∀ I : Finset (Fin 2), (lift x y).left ≫ (psum B ![fst A A ≫ f, snd A A ≫ g] I).left =
      (psum B ![x ≫ f, y ≫ g] I).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) ![fst A A ≫ f, snd A A ≫ g] I).trans
      (congrArg (fun q => psum B q I) (funext fun i => by fin_cases i <;> simp [preHom])))
  refine (Fintype.prod_equiv Equiv.ulift _ (fun I => h (psum B ![x ≫ f, y ≫ g] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    fun I => congrArg (fun q => h q ^ ((-1 : ℤ) ^ (2 - I.down.card))) (e I.down)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  have p₀ : psum B ![x ≫ f, y ≫ g] ∅ = 1 := rfl
  have p₁ : psum B ![x ≫ f, y ≫ g] {0} = x ≫ f := _root_.mul_one (x ≫ f)
  have p₂ : psum B ![x ≫ f, y ≫ g] {1} = y ≫ g := _root_.mul_one (y ≫ g)
  have p₃ : psum B ![x ≫ f, y ≫ g] {0, 1} = (x ≫ f) * (y ≫ g) := congrArg ((x ≫ f) * ·) (_root_.mul_one (y ≫ g))
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem prod_cmp {S : Scheme.{0}} (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) {T : Over S}
    (x y : T ⟶ P₀.A) {U : Type} [CommGroup U] (h : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → U) :
    ∏ i, h ((lift x y).left ≫ cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂ i) ^ cmpε i =
      (h (((x ≫ f₂) * (y ≫ g₂)).left ≫ coprod.inr) * (h ((x ≫ f₂).left ≫ coprod.inr))⁻¹ *
          (h ((y ≫ g₂).left ≫ coprod.inr))⁻¹ * h ((1 : T ⟶ P₂.A).left ≫ coprod.inr)) *
        (h (((x ≫ f₁) * (y ≫ g₁)).left ≫ coprod.inl) * (h ((x ≫ f₁).left ≫ coprod.inl))⁻¹ *
          (h ((y ≫ g₁).left ≫ coprod.inl))⁻¹ * h ((1 : T ⟶ P₁.A).left ≫ coprod.inl))⁻¹ := by
  refine DVR.prod_sum₂ _ ?_ ?_
  · refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_) (prod_pair f₂ g₂ x y fun q => h (q ≫ coprod.inr))
    rw [Category.assoc]; rfl
  · refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_)
      (DVR.prod_neg _ _ (prod_pair f₁ g₁ x y fun q => h (q ≫ coprod.inl)))
    rw [Category.assoc]; rfl

theorem cmp_add_fst : GlobalFnsSt → ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], ∀ (r₁ : LB.Gen (P₁.L.pull (eSec P₁.A))) (hr₁ : r₁.IsGen) (c₁ : CubicalStr P₁.A ⟨P₁.L, r₁, P₁.isLB, hr₁⟩) (r₂ : LB.Gen (P₂.L.pull (eSec P₂.A))) (hr₂ : r₂.IsGen) (c₂ : CubicalStr P₂.A ⟨P₂.L, r₂, P₂.isLB, hr₂⟩) (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u (r ≫ zero2 P₀.A) z J = 1) → ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → (join P₁.L P₂.L).ι), Good (join P₁.L P₂.L) z J → ∀ (x x' y : T ⟶ P₀.A), val u (lift (x * x') y).left z J * cubV c₁ z (rl J) (x ≫ f₁) (x' ≫ f₁) (y ≫ g₁) = cubV c₂ z (rr J) (x ≫ f₂) (x' ≫ f₂) (y ≫ g₂) * (val u (lift x y).left z J * val u (lift x' y).left z J) := by
  intro hG S P₀ P₁ P₂ _ _ f₁ g₁ f₂ g₂ _ _ _ _ r₁ hr₁ c₁ r₂ hr₂ c₂ u hu h₀ T z J hJ x x' y
  have hA := P₀.isAb
  let p₀ := x3 P₀.A 0
  let p₁ := x3 P₀.A 1
  let p₂ := x3 P₀.A 2
  have vp : ∀ {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J → ∀ a b : T ⟶ P₀.A,
      val (LB.pullGen (join P₁.L P₂.L) _ _ u (lift a b).left) ρ.left z J = val u (lift (ρ ≫ a) (ρ ≫ b)).left z J :=
    fun ρ z J hJ a b => by rw [val_pull hJ, ← Over.comp_left, comp_lift]
  have v1 : ∀ {y : (𝟙_ (Over S)).left} {J}, Good (join P₁.L P₂.L) y J →
      val u (lift (1 : 𝟙_ (Over S) ⟶ P₀.A) (1 : 𝟙_ (Over S) ⟶ P₀.A)).left y J = 1 := fun {y J} hJ => by
    have e : lift (1 : 𝟙_ (Over S) ⟶ P₀.A) (1 : 𝟙_ (Over S) ⟶ P₀.A) = lift η[P₀.A] η[P₀.A] := by simp [Hom.one_def]
    have := h₀ _ (𝟙 S) y J hJ
    rw [e]
    exact (congrArg (fun q => val u q y J) (Category.id_comp _)).symm.trans this
  let e : 𝟙_ (Over S) ⟶ G3 P₀.A := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have sj : Function.Surjective ((snd P₀.A (P₀.A ⊗ P₀.A)).left ≫ (snd P₀.A P₀.A).left ≫ P₀.A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
  have he : e.left ≫ (snd P₀.A (P₀.A ⊗ P₀.A)).left ≫ (snd P₀.A P₀.A).left ≫ P₀.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  let ρ : T ⟶ G3 P₀.A := lift x (lift x' y)
  have s₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
  have s₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
  have s₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
  have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
  have o₂ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [s₀, s₁])
  have hl := isPart_inl P₁.L P₂.L
  have hr := isPart_inr P₁.L P₂.L
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 P₀.A) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J →
      val (LB.mulGen (join P₁.L P₂.L) _ _ _ _ (LB.pullGen (join P₁.L P₂.L) _ _ u (lift (p₀ * p₁) p₂).left)
        (hl.gen (LB.pullGen P₁.L (thφ P₁.A (x3 P₁.A)) thε c₁.t
          (lift (p₀ ≫ f₁) (lift (p₁ ≫ f₁) (p₂ ≫ g₁))).left))) σ.left z J =
        val u (lift (σ ≫ (p₀ * p₁)) (σ ≫ p₂)).left z J *
          cubV c₁ z (rl J) (σ ≫ p₀ ≫ f₁) (σ ≫ p₁ ≫ f₁) (σ ≫ p₂ ≫ g₁) ∧
      val (LB.mulGen (join P₁.L P₂.L) _ _ _ _ (hr.gen (LB.pullGen P₂.L (thφ P₂.A (x3 P₂.A)) thε c₂.t
          (lift (p₀ ≫ f₂) (lift (p₁ ≫ f₂) (p₂ ≫ g₂))).left))
        (LB.mulGen (join P₁.L P₂.L) _ _ _ _ (LB.pullGen (join P₁.L P₂.L) _ _ u (lift p₀ p₂).left)
          (LB.pullGen (join P₁.L P₂.L) _ _ u (lift p₁ p₂).left))) σ.left z J =
        cubV c₂ z (rr J) (σ ≫ p₀ ≫ f₂) (σ ≫ p₁ ≫ f₂) (σ ≫ p₂ ≫ g₂) *
          (val u (lift (σ ≫ p₀) (σ ≫ p₂)).left z J * val u (lift (σ ≫ p₁) (σ ≫ p₂)).left z J) := fun σ z J hJ =>
    ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _)
        ((hl.val_gen _ _ _ hJ).trans (val_cub c₁ σ (hl.good hJ) _ _ _))),
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((hr.val_gen _ _ _ hJ).trans (val_cub c₂ σ (hr.good hJ) _ _ _))
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))))⟩
  have key := (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' (join_isLB P₁.isLB P₂.isLB) (fun V _ k => ?_) _ e.left he sj
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (hl.gen_isGen (DVR.pullGen_isGen _ _ _ _ c₁.isGen _)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (hr.gen_isGen (DVR.pullGen_isGen _ _ _ _ c₂.isGen _)) (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))) (fun y I hI => ?_) _ ρ.left z J hJ) (ev ρ hJ).2)
  · simp only [← Category.assoc] at key
    rwa [o₂, s₀, s₁, s₂] at key
  · refine (DVR.prod_sum₂ (K := thK) (K' := KK ⊕ KK) (U := V) _
        (prod_cub (p₀ ≫ f₂) (p₁ ≫ f₂) (p₂ ≫ g₂) fun q => k (q ≫ coprod.inr))
        (DVR.prod_sum₂ (K := KK) (K' := KK) (U := V) _ (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₀ p₂ k)
          (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₁ p₂ k))).trans
        (Eq.trans ?_ (DVR.prod_sum₂ (K := KK) (K' := thK) (U := V) _ (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ (p₀ * p₁) p₂ k)
          (prod_cub (p₀ ≫ f₁) (p₁ ≫ f₁) (p₂ ≫ g₁) fun q => k (q ≫ coprod.inl))).symm)
    rw [MonObj.mul_comp p₀ p₁ f₁, MonObj.mul_comp p₀ p₁ f₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have C₁ := isCub_cubV c₁ (hl.good hI)
    have C₂ := isCub_cubV c₂ (hr.good hI)
    refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
    rw [← Category.assoc e p₀, ← Category.assoc e p₀, o₁, e₀, e₁, e₂, MonObj.one_comp, MonObj.one_comp, v1 hI]
    rw [C₁.face, C₂.face]
    simp

end GlobalTheory.Mum.Two.WeilCmp.AddFst
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

theorem _root_.GlobalTheory.T.powerData_tensorBundleIso_with_psi_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D.P.A ⟶ D₀.P.A)) (j : Fin r → (D₀.P.A ⟶ D.P.A)) (h : Fin r → D₀.X → D.X) (k : Fin r → D.X → D₀.X), (∀ a χ, D.c (h a χ) = D₀.c χ ≫ j a) → (∀ a y, D₀.c (k a y) = D.c y ≫ pr a) → (∀ a, PeriodRel D D₀ (pr a) (h a) (k a)) → (∀ a, CmpTwo D D₀ (pr a) (j a)) → Expand D (fun ab : Fin r × Fin r => W ab.1 ab.2) (𝟙 D.P.A) (fun ab => pr ab.2 ≫ j ab.1) → PrimVal D (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) (fun y => ∑ ab : Fin r × Fin r, W ab.1 ab.2 • h ab.1 (k ab.2 y)) → ∃ w : LB.Iso D.P.L (LB.LinComb D₀.P.L (tensφ pr) (tensε W)), w.IsGen ∧ ∀ y z J J', Good D₀.P.L z J → Good D.P.L z J' → val (D.psi y) (𝟙 _) z J' = gm (D.xK y) z _ (w.s (fun k => J (D.xK y ≫ tensφ pr k), J' (D.xK y))) * ∏ a, ∏ b, val (D₀.tau (k a y) (k b y)) (𝟙 _) z J ^ W a b := by
  first | exact @GlobalTheory.Mum.PowData.tens_iso_psi | exact GlobalTheory.Mum.PowData.tens_iso_psi | (intros; apply GlobalTheory.Mum.PowData.tens_iso_psi <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

theorem _root_.GlobalTheory.T.isBiextensionComparisonGenerator_of_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (j : D₀.P.A ⟶ D.P.A), IsMonHom q → IsMonHom j → AdjCls (cls D.P.L D.P.isLB) (cls D₀.P.L D₀.P.isLB) q j → CmpTwo D D₀ q j := by
  first | exact @GlobalTheory.Mum.PowData.cmpTwo_of_adjCls | exact GlobalTheory.Mum.PowData.cmpTwo_of_adjCls | (intros; apply GlobalTheory.Mum.PowData.cmpTwo_of_adjCls <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

theorem _root_.GlobalTheory.T.weilComparisonGenerator_additive_first_variable : GlobalFnsSt → ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], ∀ (r₁ : LB.Gen (P₁.L.pull (eSec P₁.A))) (hr₁ : r₁.IsGen) (c₁ : CubicalStr P₁.A ⟨P₁.L, r₁, P₁.isLB, hr₁⟩) (r₂ : LB.Gen (P₂.L.pull (eSec P₂.A))) (hr₂ : r₂.IsGen) (c₂ : CubicalStr P₂.A ⟨P₂.L, r₂, P₂.isLB, hr₂⟩) (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u (r ≫ zero2 P₀.A) z J = 1) → ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → (join P₁.L P₂.L).ι), Good (join P₁.L P₂.L) z J → ∀ (x x' y : T ⟶ P₀.A), val u (lift (x * x') y).left z J * cubV c₁ z (rl J) (x ≫ f₁) (x' ≫ f₁) (y ≫ g₁) = cubV c₂ z (rr J) (x ≫ f₂) (x' ≫ f₂) (y ≫ g₂) * (val u (lift x y).left z J * val u (lift x' y).left z J) := by
  first | exact @GlobalTheory.Mum.Two.WeilCmp.AddFst.cmp_add_fst | exact GlobalTheory.Mum.Two.WeilCmp.AddFst.cmp_add_fst | (intros; apply GlobalTheory.Mum.Two.WeilCmp.AddFst.cmp_add_fst <;> assumption)

end
end
