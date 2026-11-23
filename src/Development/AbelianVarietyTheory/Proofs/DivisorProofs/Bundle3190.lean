module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3135
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoLatticePartSurjectiveCoisotropicKernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwo
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3136
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousPeriodLatticeBasisArc
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem pull_inv_cls {R : Type} [CommRing R] [IsLocalRing R] (P : PolAV (Sp R)) :
    pull (GrpObj.inv : P.A ⟶ P.A).left (cls P.L P.isLB) = cls P.L P.isLB := by
  obtain ⟨U, hU, t, ht⟩ := P.sym (IsLocalRing.closedPoint R)
  obtain rfl : U = ⊤ := DVR.eq_top_of_closedPoint_mem U hU
  have h := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 ⟨t, ht⟩
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul, pull_comp] at h
  obtain ⟨m, hm⟩ : ∃ m : P.A.left ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme, m ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨P.A.left.topIso.inv, P.A.left.topIso.inv_hom_id⟩
  have h' := congrArg (pull m) h
  rw [map_add (f := _), map_neg, map_zero, ← pull_comp m, ← pull_comp m, hm, pull_id, pull_id, add_neg_eq_zero] at h'
  exact h'

theorem pull_one_eq_zero {R : Type} [CommRing R] [IsLocalRing R] {G Y : Over (Sp R)} [GrpObj G] (d : Pic G.left) :
    pull (1 : Y ⟶ G).left d = 0 := by
  have e : (1 : Y ⟶ G) = toUnit Y ≫ η[G] := rfl
  rw [e, Over.comp_left, pull_comp, GlobalTheory.DualOpen.pic_sp_local_eq_zero R (pull η[G].left d), map_zero]

theorem exists_translate_of_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D₀ D : DegPre R)
  (β : D₀.P.A ≅ D.P.A), IsMonHom β.hom →
  (∃ wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L)
      ((abelian₂ D.P.A D.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) : G2 D₀.P.A ⟶ G2 D.P.A).left),
    wΛ.IsGen) →
  ∃ b : 𝟙_ (Over (Sp R)) ⟶ D.P.A, padd D.P.A b b = η[D.P.A] ∧
    ∃ w : LB.Iso D₀.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₀ D β.hom b) GlobalTheory.MumCmp.twε), w.IsGen := by
  intro R _ _ _ _ D₀ D β hβ hw
  have := D.P.isAb.comm
  have := D₀.P.isAb.comm
  have hL₀ := D₀.P.isLB
  have hL := D.P.isLB
  set c₀ := cls D₀.P.L hL₀ with hc₀
  set c := cls D.P.L hL with hc
  have hd : IsDual D.P.A D.P.A (abelian₂ D.P.A D.P.L) :=
    CompanionTheory.PfDual.kTrivDual R D.P.A D.P.g D.P.isAb D.P.smoothDim D.P.L hL D.P.ktriv
  have hΛ : (abelian₂ D.P.A D.P.L).IsLB := hd.isLB
  have e : ∀ (Y : Over (Sp R)) (a t : Y ⟶ D.P.A), evc hΛ a t = lam c a t := fun Y a t ↦ by
    rw [evc, show cls _ hΛ = lam c (fst D.P.A D.P.A) (snd D.P.A D.P.A) from
      cls_cube_two hL _ _ hΛ, pull_lam, lift_fst, lift_snd]
  have l₁ : ∀ (Y : Over (Sp R)) (a a' t : Y ⟶ D.P.A), lam c (a * a') t = lam c a t + lam c a' t :=
    fun Y a a' t ↦ by
      rw [← e, ← e, ← e]
      exact (isAdditive_iff hΛ).1 hd.additive Y a a' t
  have l₂ : ∀ (Y : Over (Sp R)) (a t t' : Y ⟶ D.P.A), lam c a (t * t') = lam c a t + lam c a t' :=
    fun Y a t t' ↦ by rw [lam_comm, l₁, lam_comm _ t, lam_comm _ t']

  obtain ⟨wΛ, hwΛ⟩ := hw
  have hΛ₀ : (abelian₂ D₀.P.A D₀.P.L).IsLB := LB.isLB_linComb hL₀ _ _
  have eΛ : lam c₀ (fst D₀.P.A D₀.P.A) (snd D₀.P.A D₀.P.A) =
      lam c (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) := by
    have h := (cls_eq_iff hΛ₀ (pull_isLB hΛ _)).2 ⟨wΛ, hwΛ⟩
    have h₁ : cls _ hΛ₀ = lam c₀ (fst D₀.P.A D₀.P.A) (snd D₀.P.A D₀.P.A) := cls_cube_two hL₀ _ _ hΛ₀
    have h₂ : cls _ hΛ = lam c (fst D.P.A D.P.A) (snd D.P.A D.P.A) := cls_cube_two hL _ _ hΛ
    rw [← h₁, h, cls_pull hΛ, h₂, pull_lam, lift_fst, lift_snd]
  have s₁ : ∀ (Y : Over (Sp R)) (u v : Y ⟶ D₀.P.A), lam c₀ u v = lam c (u ≫ β.hom) (v ≫ β.hom) := fun Y u v ↦ by
    have h := congrArg (pull (lift u v).left) eΛ
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h

  have Fadd : ∀ (Y : Over (Sp R)) (a a' : Y ⟶ D.P.A),
      pull ((a * a') ≫ β.inv).left c₀ - pull (a * a').left c =
        (pull (a ≫ β.inv).left c₀ - pull a.left c) + (pull (a' ≫ β.inv).left c₀ - pull a'.left c) := by
    intro Y a a'
    have h := s₁ Y (a ≫ β.inv) (a' ≫ β.inv)
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, lam, pull_one_eq_zero, add_zero] at h
    rw [MonObj.mul_comp, ← sub_eq_zero]
    have h' := sub_eq_zero.2 h
    convert h' using 1
    abel
  let N : LB (D.P.A ⊗ 𝟙_ (Over (Sp R))).left :=
    tens (D₀.P.L.pull (fst D.P.A (𝟙_ (Over (Sp R))) ≫ β.inv).left)
      (dual (D.P.L.pull (fst D.P.A (𝟙_ (Over (Sp R)))).left))
  have hN : N.IsLB := isLB_tens (pull_isLB hL₀ _) (isLB_dual (pull_isLB hL _))
  have clsN : cls N hN = pull (fst D.P.A (𝟙_ (Over (Sp R))) ≫ β.inv).left c₀ -
      pull (fst D.P.A (𝟙_ (Over (Sp R)))).left c := by
    rw [show cls N hN = _ from cls_tens (pull_isLB hL₀ _) (isLB_dual (pull_isLB hL _)) hN,
      cls_dual (pull_isLB hL _), cls_pull hL₀, cls_pull hL, sub_eq_add_neg]
  have evN : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A) (t : Y ⟶ 𝟙_ (Over (Sp R))),
      evc hN a t = pull (a ≫ β.inv).left c₀ - pull a.left c := by
    intro Y a t
    rw [evc, clsN, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, lift_fst_assoc, lift_fst]
  have hadd : IsAdditive N := (isAdditive_iff hN).2 fun Y a a' t ↦ by rw [evN, evN, evN, Fadd]
  obtain ⟨b, hb, -⟩ := hd.univ _ N hN hadd
  have eb := (cls_eq_iff hN (pull_isLB hΛ _)).2 hb
  have key : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A),
      pull (a ≫ β.inv).left c₀ - pull a.left c = lam c a (toUnit Y ≫ b) := by
    intro Y a
    have h : evc hN a (toUnit Y) = evc hΛ a (toUnit Y ≫ b) := by
      have h := congrArg (pull (lift a (toUnit Y)).left) eb
      rw [cls_pull hΛ] at h
      change evc hN a (toUnit Y) = pull (lift a (toUnit Y)).left
        (evc hΛ (fst D.P.A (𝟙_ (Over (Sp R)))) (snd D.P.A (𝟙_ (Over (Sp R))) ≫ b)) at h
      rw [pull_evc, lift_fst, lift_snd_assoc] at h
      exact h
    rw [← evN Y a (toUnit Y), h, e]
  refine ⟨b, ?_, ?_⟩
  ·
    have sym₀ : pull (GrpObj.inv : D₀.P.A ⟶ D₀.P.A).left c₀ = c₀ := pull_inv_cls D₀.P
    have sym : pull (GrpObj.inv : D.P.A ⟶ D.P.A).left c = c := pull_inv_cls D.P
    have odd : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A), lam c a (toUnit Y ≫ b) + lam c a (toUnit Y ≫ b) = 0 := by
      intro Y a
      have ia : a⁻¹ = a ≫ GrpObj.inv := rfl
      have ia' : (a ≫ β.inv)⁻¹ = (a ≫ β.inv) ≫ GrpObj.inv := rfl
      have h₁ : lam c a⁻¹ (toUnit Y ≫ b) = lam c a (toUnit Y ≫ b) := by
        rw [← key, ← key, GrpObj.inv_comp, ia, ia']
        simp only [Over.comp_left, pull_comp, sym₀, sym]
      have h₂ : lam c (a⁻¹ * a) (toUnit Y ≫ b) = 0 := by rw [inv_mul_cancel, lam_one_left]
      rw [l₁, h₁] at h₂
      exact h₂
    have two : b * b = 1 := by
      refine hd.eq_one (b * b) ((triv_ev_iff hΛ _ _).2 ?_)
      have hs : snd D.P.A (𝟙_ (Over (Sp R))) = toUnit _ := toUnit_unique _ _
      rw [e, hs, MonObj.comp_mul, l₂, odd]
    have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = η[D.P.A] := by
      rw [show (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = toUnit _ ≫ η[D.P.A] from rfl,
        toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    exact two.trans e₁
  ·
    have hC : (LB.LinComb D.P.L (twφ D₀ D β.hom b) twε).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_iff hL₀ hC).1 ?_
    have h := key D₀.P.A β.hom
    rw [Iso.hom_inv_id, Over.id_left, pull_id, sub_eq_iff_eq_add] at h
    have e₁ : padd D.P.A β.hom (toUnit D₀.P.A ≫ b) = β.hom * (toUnit D₀.P.A ≫ b) := rfl
    have e₂ : toUnit D₀.P.A ≫ η[D.P.A] = 1 := rfl
    rw [cls_linComb hL, Fin.sum_univ_three]
    simp only [twφ, twε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, one_smul, neg_smul, e₁, e₂]
    rw [← hc, ← hc₀, h, lam]
    abel

end GlobalTheory.MumCmp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

theorem GlobalTheory.HomMum.exists_gen_level : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ [ConnectedSpace (thickObj R I e G₁).left] (u : LB.Gen (LB.LinComb (join U₁.LG.L U₂.LG.L) (mφ G₁ G₂ f g) mε)), IsNrm u → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ G₁.left ⨿ G₂.left) → (join U₁.LG.L U₂.LG.L).ι), Good (join U₁.LG.L U₂.LG.L) z J → ∀ x x' y : T ⟶ G₁, val u (lift (x * x') y).left z J * cubV U₁.cubG z (rl J) x x' y = cubV U₂.cubG z (rr J) (x ≫ f) (x' ≫ f) (y ≫ g) * (val u (lift x y).left z J * val u (lift x' y).left z J) ∧ val u (lift y (x * x')).left z J * cubV U₁.cubG z (rl J) y x x' = cubV U₂.cubG z (rr J) (y ≫ f) (x ≫ g) (x' ≫ g) * (val u (lift y x).left z J * val u (lift y x').left z J)) → ∃ t : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => pullback.fst (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom (thick R I e) ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k) mε), t.IsGen := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e f g _ _ fB gB _ _ hf hg _ u hu hadd
  obtain ⟨W, hW, h₁, h₂⟩ := GlobalTheory.T.exists_glued_uniformisation_iso_one_level U₁ U₂ e
  obtain ⟨v, hv, hm⟩ := GlobalTheory.T.exists_generator_multiplicative_on_quotient_kernel U₁ U₂ e hf hg W hW h₁ h₂ u hu.1 hadd
  exact GlobalTheory.T.exists_descended_generator_thickened_abelian_part U₁ U₂ e hf hg v hv (GlobalTheory.T.generator_torus_invariant_of_multiplicative U₁ U₂ e hf hg v hv hm)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.uniformisedGroupIso_abelianPart_character_isos : ∀ (R : Type) [CommRing R] [IsDomain R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂) (a : G₁ ≅ G₂), IsMonHom a.hom → ∃ (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X ≃+ D₁.toPre.X), IsIso b ∧ Lin U₁ U₂ a.hom b h.toAddMonoidHom ∧ Coord U₁ U₂ a.hom b h.toAddMonoidHom := by
  first | exact @GlobalTheory.TInj.iso_lin_coord | exact GlobalTheory.TInj.iso_lin_coord | (intros; apply GlobalTheory.TInj.iso_lin_coord <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange
open GlobalTheory.Mum.Two.Mix

noncomputable section
namespace GlobalTheory.Mum.Two.Mix

theorem core : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁ U₂ a b h → Coord U₁ U₂ a b h → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (j j' : ℕ) (N : Type) [Fintype N] (ρ : N → R) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j') (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α), (∀ ν e, U₂.ExpandsAt e j (σ ν) (f ν)) → (∀ ν e, U₁.ExpandsAt e j' (σ' ν) (f' ν)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J₁ J₂), Good U₁.LG.L z J₁ → Good U₂.LG.L z J₂ → ∑ ν, constVal (r ≫ G₁.hom) z (ρ ν) * (sval (σ ν) (r ≫ a.left) z J₂ * sval (σ' ν) r z J₁) = 0) → ∀ (g : GtPtF D₁.toPre F) (g' : GtPtF D₂.toPre F), Act D₁.toPre D₂.toPre b h g g' → ∀ (w : Frm D₂.toPre F j g'.b) (w' : Frm D₁.toPre F j' g.b), w.IsGen → w'.IsGen → ∀ (x : N → D₂.toPre.X → F) (x' : N → D₁.toPre.X → F), (∀ ν χ, MixedConv.IsCoefB j g' w χ (f ν χ) (x ν χ)) → (∀ ν χ, MixedConv.IsCoefB j' g w' χ (f' ν χ) (x' ν χ)) → ∀ α : D₁.toPre.X, SumF I F (fun p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} => ∑ ν, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (ρ ν)) * (x ν p.1.1 * x' ν p.1.2)) 0 := by
  intro hL R _ _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a b h hLin hCo F _ _ _ j j' N _ ρ σ σ' f f' hE hE' hrel
    g g' hg w w' hw hw' x x' hx hx' α
  choose u hu using hCo
  choose n hn using fun (ν : N) (α : D₁.toPre.X) (p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α}) =>
    GlobalTheory.T.exists_mixed_section_join_bundles R D₁.toPre D₂.toPre b j j' p.1.1 (h p.1.1) p.1.2 α p.2 (u p.1.1) (hu p.1.1).1.1 (f ν p.1.1) (f' ν p.1.2)
  let m : ∀ α, {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} →
      SecOver D₁.toPre.P.A.hom (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j')) :=
    fun α p => ∑ ν, ρ ν • (show SecOver D₁.toPre.P.A.hom _ from n ν α p)
  have hm : ∀ α p (Z : Scheme.{0}) (r : Z ⟶ D₁.toPre.P.A.left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J →
      sval (m α p) r z J = ∑ ν, constVal (r ≫ D₁.toPre.P.A.hom) z (ρ ν) *
        (sval (f ν p.1.1) (r ≫ b.left) z (rr J) * sval (f' ν p.1.2) r z (rl J) *
          (val (u p.1.1) r z J * val (MixedConv.cubB D₁.toPre (h p.1.1) p.1.2) r z (rl J)).val) :=
    fun α p Z r z J hJ =>
      (sval_sum' (π := D₁.toPre.P.A.hom) hJ _ _ _).trans (Finset.sum_congr rfl fun ν _ =>
        (sval_smul' (π := D₁.toPre.P.A.hom) hJ _ _ _).trans (congrArg _ (hn ν α p Z r z J hJ)))
  obtain ⟨τ, hτ, hv⟩ := GlobalTheory.T.exists_mixed_bundle_frame_from_part_frames R D₁.toPre D₂.toPre F b α j j' g _ hg.1 w w' hw hw'
  refine GlobalTheory.T.adicSum_sections_pullbacks_value_abelianPart R I hR D₁ F _ (JN D₁.toPre D₂.toPre) (jn_isLB D₁.toPre D₂.toPre) _ (mixφ D₁.toPre D₂.toPre b α)
    (MixedConv.mixε j j') _ (m α) (0 : SecOver D₁.toPre.P.A.hom _) (fun e => ?_) g.b τ hτ _ 0 fun z J hJ => ⟨fun p => ?_, ?_⟩
  · obtain ⟨S, hS⟩ := GlobalTheory.T.integral_relation_kills_mixed_section_sums_level R I D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a b h hLin.2.2.1 u (fun χ => (hu χ).2) j j' e N ρ σ σ' f f' (fun ν => hE ν e)
      (fun ν => hE' ν e) hrel m hm α
    exact ⟨S, fun Z r z J hJ => ⟨(hS Z r z J hJ).1,
      (sval_zero' (π := D₁.toPre.P.A.hom) hJ _).trans (hS Z r z J hJ).2.symm⟩⟩
  · obtain ⟨⟨χ, δ⟩, hp⟩ := p

    rw [hm _ _ _ _ z J hJ, CoefBasic.cst_eq, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have c₁ : constVal (g.b.left ≫ D₁.toPre.P.A.hom) z (ρ ν) =
        CoefBasic.cstH z (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (ρ ν))) := by
      refine Eq.trans ?_ (CoefBasic.cst_eq z _)
      rw [Over.w g.b]
      refine (constVal_specMap (jFK (R := R) F) _ z _).trans ?_
      exact (congrArg (fun q => constVal q z _) (Category.id_comp _).symm).trans (constVal_specMap (𝟙 _) _ z _)
    have e₁ := GlobalTheory.T.mixed_section_value_product_expansion_terms R D₁.toPre D₂.toPre F b h g g' hg j j' w w' χ δ (u χ) (hu χ).1 (f ν χ) (f' ν δ) _ _ (hx ν χ) (hx' ν δ) z J hJ
    have e₂ := hv z J hJ
    dsimp only at hp
    subst hp
    rw [c₁, e₁, e₂, CoefBasic.cst_eq]
    simp only [map_mul]
    ring
  · rw [CoefBasic.cst_eq, map_zero, zero_mul]
    exact sval_zero' (π := D₁.toPre.P.A.hom) hJ _

end GlobalTheory.Mum.Two.Mix
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem IsOpp.exists_isometry_extend {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (N : ℕ)
    (hN : 0 < N) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (t : Z →ₗ[𝓞 E] D.La)
    (ht : ∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) (hiso : ∀ z z' : Z, D.EF (t z) (t z') = 0) :
    ∃ g : D.La →ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧
      ∀ z : Z, g z = t z := by
  set q := h.symm.proj with hq
  have hr : ∀ a, a - (q a : D.La) ∈ perp D Z' := fun a => h.symm.sub_proj_mem a
  have hδ : ∀ z : Z, t z - (z : D.La) ∈ perp D Z' := fun z => by
    obtain ⟨e, he, hz⟩ := ht z
    rw [hz, add_sub_cancel_left]
    exact nsmul_mem he N
  choose c hc hu using fun a : D.La => h.2.2.1 (AddMonoidHom.mk' (fun z : Z => D.EF (t z - z) (a - q a))
    fun z z' => by simp only [map_add (f := _), map_sub, Submodule.coe_add, LinearMap.add_apply, LinearMap.sub_apply]; abel)
  simp only [AddMonoidHom.mk'_apply] at hc hu
  let α : D.La →ₗ[𝓞 E] Z' :=
    { toFun := c
      map_add' := fun a a' => (hu _ _ fun z => by
        simp only [Submodule.coe_add, map_add (f := _), hc, map_sub, LinearMap.sub_apply, map_add (f := _)]
        abel).symm
      map_smul' := fun x a => (hu _ _ fun z => by
        have key : ∀ u w : D.La, D.EF u (x • w) = D.EF (H.bar x • u) w := fun u w => by rw [D.adj, bar_bar]
        simp only [RingHom.id_apply, Submodule.coe_smul, map_smul, ← smul_sub]
        rw [key, key, ← Submodule.coe_smul, hc, Submodule.coe_smul, map_smul, smul_sub]).symm }
  have hα : ∀ a, α a = c a := fun _ => rfl
  let g : D.La →ₗ[𝓞 E] D.La := LinearMap.id + (t - Z.subtype) ∘ₗ q - Z'.subtype ∘ₗ α
  have hg : ∀ a, g a = a + (t (q a) - q a) - c a := fun _ => rfl
  refine ⟨g, fun a a' => ?_, fun a => ?_, fun z => ?_⟩
  · have hZ : ∀ (x y : Z), D.EF x y = 0 := fun x y => h.1 x.2 _ y.2
    have hZ' : ∀ (x y : Z'), D.EF x y = 0 := fun x y => h.2.1 x.2 _ y.2
    have f1 := hZ' (c a) (c a')
    have f2 : D.EF (t (q a) - q a) (c a') = 0 := hδ (q a) _ (c a').2
    have f3 : D.EF (c a) (t (q a') - q a') = 0 := by
      rw [ef_swap, hδ (q a') _ (c a).2, neg_zero]
    have f4 := hiso (q a) (q a')
    have f5 := hZ (q a) (q a')
    have f7 : D.EF a (c a') = D.EF (t (q a) - q a) (a' - q a') := by
      have := hr a _ (c a').2
      rw [← hc a' (q a)]
      simp only [map_sub, LinearMap.sub_apply] at this
      linear_combination this
    have f8 : D.EF (c a) a' = D.EF (a - q a) (t (q a') - q a') := by
      have := hr a' _ (c a).2
      have h2 := hc a (q a')
      rw [ef_swap D (c a) a', ef_swap D (a - q a)]
      simp only [map_sub, LinearMap.sub_apply] at this h2 ⊢
      linear_combination -this - h2
    rw [hg, hg]
    simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply] at f2 f3 f7 f8 ⊢
    linear_combination f1 - f2 - f3 + f4 - f5 - f7 - f8
  · obtain ⟨e, -, he⟩ := ht (q a)
    obtain ⟨e', he'⟩ := GlobalTheory.ModuliGenus.exists_eq_nsmul_of_dvd D hN (c a : D.La) fun b => by
      obtain ⟨e₁, -, he₁⟩ := ht (q b)
      have h1 : D.EF (c a) (b - q b) = 0 := by rw [ef_swap, hr b _ (c a).2, neg_zero]
      have h2 := hc a (q b)
      rw [he₁, add_sub_cancel_left, map_nsmul, LinearMap.smul_apply] at h2
      refine ⟨-D.EF e₁ (a - q a), ?_⟩
      have h3 : D.EF (c a) b = D.EF (c a) (q b) := by
        rw [map_sub] at h1; linear_combination h1
      rw [h3, ef_swap, h2, nsmul_eq_mul]
      ring
    refine ⟨e - e', ?_⟩
    rw [hg, he, he', smul_sub]
    abel
  · have hqz : q z = z := Subtype.ext (h.symm.proj_of_mem z.2)
    have hcz : c z = 0 := (hu z 0 fun z' => by simp [hqz]).symm
    rw [hg, hqz, hcz]
    simp

end GlobalTheory.LowFilt
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem _root_.GlobalTheory.T.injective_mod_of_surjective_mod_opposite : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∀ b ∈ Z', (∃ e, y b = n • e) → ∃ e ∈ Z', b = n • e := by
  first | exact @GlobalTheory.LowFilt.inj_mod_of_surj_mod | exact GlobalTheory.LowFilt.inj_mod_of_surj_mod | (intros; apply GlobalTheory.LowFilt.inj_mod_of_surj_mod <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.tateIso_latticePart_surjective_coisotropicKernel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F),
    ∃ y : ℕ → D.La →ₗ[𝓞 E] D₀.X, (∀ n, 0 < n → ∀ a, ∃ e, y n a = (I.ev n a).y + n • e) ∧
      ∀ n, 0 < n → Cois D (y n) n := by
  first | exact @GlobalTheory.LowFilt.tateIsoQ_y_cois | exact GlobalTheory.LowFilt.tateIsoQ_y_cois | (intros; apply GlobalTheory.LowFilt.tateIsoQ_y_cois <;> assumption)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp.LevelCmp

theorem lift_comp_pG {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A)
    (hab : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ b.left)
    {A₂ : PolAV (Sp (FractionRing R))} {D₂ : DegData R (maximalIdeal R)} (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (β : D₂.toPre.P.A ≅ D.toPre.P.A) (hβ : ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left)
    (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left) (hh' : h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left) :
    h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom b 0 := by
  classical
  haveI := GlobalTheory.TorsionTranslate.mono_fst (I := maximalIdeal R) e G
  have hs : (thick R (maximalIdeal R) e ≫ a.left) ≫ G.hom = 𝟙 (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))).left ≫ thick R (maximalIdeal R) e := by
    rw [Category.assoc, Over.w a]; simp
  let ae : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶ thickObj R (maximalIdeal R) e G :=
    Over.homMk (pullback.lift (thick R (maximalIdeal R) e ≫ a.left) (𝟙 (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))).left) hs) (pullback.lift_snd _ _ _)
  have hae : ae.left ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left := pullback.lift_fst _ _ _
  have heq : h = (GlobalTheory.MumCmp.Transl.tr ae).left :=
    (cancel_mono (fstG (maximalIdeal R) e G).left).1 (by rw [hh', GlobalTheory.MumCmp.Transl.tr_fst hae])
  have h₁ := GlobalTheory.TorusCoord.im_mul (U.gt e) (toUnit (thickObj R (maximalIdeal R) e G) ≫ ae) (𝟙 (thickObj R (maximalIdeal R) e G))
  have h₂ : GlobalTheory.TorusCoord.im (U.gt e) (toUnit (thickObj R (maximalIdeal R) e G) ≫ ae) = toUnit _ ≫ b := by
    ext
    have := hab e ae.left (Over.w ae) hae
    simp [GlobalTheory.TorusCoord.im] at this ⊢
    rw [this]
  have h₃ : GlobalTheory.TorusCoord.im (U.gt e) (𝟙 (thickObj R (maximalIdeal R) e G)) = (U₂.gt e).pG ≫ β.hom := by
    ext
    have := (hβ e).symm
    simp [GlobalTheory.TorusCoord.im] at this ⊢
    exact this
  have h₅ : GlobalTheory.TorusCoord.im (U.gt e) (GlobalTheory.MumCmp.Transl.tr ae) = (U₂.gt e).pG ≫ (β.hom * (toUnit D₂.toPre.P.A ≫ b)) := by
    rw [GlobalTheory.MumCmp.Transl.tr, h₁, h₂, h₃, comp_mul, comp_toUnit_assoc, mul_comm]
  rw [heq]
  exact congrArg Over.Hom.left h₅

end GlobalTheory.MumCmp.LevelCmp
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

theorem _root_.GlobalTheory.T.logDeriv_coordinate_sub_potentials_const : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → ∀ α : Q.X, ChartFree Y h ν m₀ V pb α → ∃ c : K, CoordEq Y h ν m₀ V pb α c := by
  first | exact @GlobalTheory.HeatConn.exists_coordEq | exact GlobalTheory.HeatConn.exists_coordEq | (intros; apply GlobalTheory.HeatConn.exists_coordEq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj


theorem _root_.GlobalTheory.T.exists_continuous_period_lattice_basis_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (g' : ℕ) (ρ : ℝ) (e' : ∀ u, (Fin g' → ℂ) → (Over.mk (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G)), GoodEmb c σ → 1 ≤ Dw.p + Dw.q → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ∀ s, (spMap (ψ u) ≫ x) s ∉ genBd Z) → 0 < ρ → ρ ≤ r → IsHolTo (Metric.ball (0 : ℂ) ρ ×ˢ Set.univ) (fun q : ℂ × (Fin g' → ℂ) => (show Sp ℂ ⟶ Z.t.G.left from (e' q.1 q.2).left)) → (∀ u ∈ Metric.ball (0 : ℂ) ρ, (∀ z w, e' u (z + w) = e' u z * e' u w) ∧ Function.Surjective (e' u) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (e' u z).left)) ∧ (∀ w, ∃! v : epsPt (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G, IsDerivAt0 (fun z => (e' u z).left) w v.left) ∧ (∀ v : epsPt (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' u 0).left → ∃! w, IsDerivAt0 (fun z => (e' u z).left) w v.left)) → ∃ (ρ₀ : ℝ) (m : ℕ) (lamE : ℂ → Fin m → Fin g' → ℂ), 0 < ρ₀ ∧ ρ₀ < ρ ∧ ContinuousOn lamE {s : ℂ | s.re < 0} ∧ (∀ s : ℂ, s.re < 0 → LinearIndependent ℝ (lamE s) ∧ Submodule.span ℝ (Set.range (lamE s)) = ⊤ ∧ ∀ z, e' ((ρ₀ : ℂ) * Complex.exp s) z = 1 ↔ ∃ n : Fin m → ℤ, z = ∑ j, n j • lamE s j) ∧ ∃ (C : ℝ) (k : ℕ), ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi → ‖lamE s‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.ShFam.BdArc.ArcLat.exists_continuous_latBasis_of_arc | exact GlobalTheory.ShFam.BdArc.ArcLat.exists_continuous_latBasis_of_arc | (intros; apply GlobalTheory.ShFam.BdArc.ArcLat.exists_continuous_latBasis_of_arc <;> assumption)
end
