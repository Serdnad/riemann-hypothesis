module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PicardGroup
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UTau0

theorem uw_even_val : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (f : D₀.P.A ⟶ D₀.P.A) [IsMonHom f]
    (uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ f) GlobalTheory.UTau0.w0ε)), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ (T : Over (Sp R)) (x : T ⟶ D₀.P.A) (z : T.left) (J : (T.left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D₀.P.L z J →
      val uw x⁻¹.left z J * val D₀.sym x.left z J * cubV D₀.cub z J (x ≫ f) (x ≫ f)⁻¹ x⁻¹ =
        val uw x.left z J * cubV D₀.cub z J x x⁻¹ (x ≫ f) := by
  intro R _ _ D₀ f _ uw hu h₀ T x z J hJ
  let gL := LB.mulGen D₀.P.L _ _ _ _
      (LB.mulGen D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw ((𝟙 D₀.P.A)⁻¹).left) D₀.sym)
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift f (lift f⁻¹ (𝟙 D₀.P.A)⁻¹)).left)
  let gR := LB.mulGen D₀.P.L _ _ _ _ uw
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift (𝟙 D₀.P.A) (lift (𝟙 D₀.P.A)⁻¹ f)).left)
  have ev : ∀ {T' : Over (Sp R)} (σ : T' ⟶ D₀.P.A) {z : T'.left} {J}, Good D₀.P.L z J →
      val gL σ.left z J = val uw (σ ≫ (𝟙 D₀.P.A)⁻¹).left z J * val D₀.sym σ.left z J *
          cubV D₀.cub z J (σ ≫ f) (σ ≫ f⁻¹) (σ ≫ (𝟙 D₀.P.A)⁻¹) ∧
        val gR σ.left z J = val uw σ.left z J *
          cubV D₀.cub z J (σ ≫ 𝟙 D₀.P.A) (σ ≫ (𝟙 D₀.P.A)⁻¹) (σ ≫ f) := fun σ z J hJ =>
    ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (val_pull hJ _ _ _) rfl)) (val_cub D₀.cub σ hJ _ _ _)),
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D₀.cub σ hJ _ _ _))⟩

  have pw : ∀ (V : Type) [CommGroup V] (k : (D₀.P.A.left ⟶ D₀.P.A.left) → V) (σ : D₀.P.A ⟶ D₀.P.A),
      ∏ i, k (σ.left ≫ w0φ D₀ f i) ^ w0ε i =
        k (σ * (σ ≫ f)).left * (k σ.left)⁻¹ * (k σ.left)⁻¹ * (k (σ ≫ f).left)⁻¹ *
          k (1 : D₀.P.A ⟶ D₀.P.A).left * k (1 : D₀.P.A ⟶ D₀.P.A).left := by
    intro V _ k σ
    have e₀ : σ.left ≫ (padd D₀.P.A (𝟙 _) f).left = (σ * (σ ≫ f)).left :=
      congrArg (fun q : D₀.P.A ⟶ D₀.P.A => q.left) ((MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id]))
    have e₃ : σ.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left = (1 : D₀.P.A ⟶ D₀.P.A).left := by
      rw [← Over.comp_left]; congr 1; simp [Hom.one_def]
    rw [Fin.prod_univ_four]
    show k (σ.left ≫ (padd D₀.P.A (𝟙 _) f).left) ^ (1 : ℤ) * k (σ.left ≫ 𝟙 _) ^ (-2 : ℤ) *
      k (σ.left ≫ f.left) ^ (-1 : ℤ) * k (σ.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left) ^ (2 : ℤ) = _
    rw [e₀, e₃, Category.comp_id]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Over.comp_left]
    abel
  have hL : val gL x.left z J = val gR x.left z J := by
    refine gen_unique' D₀.P.isLB (u := gL) (u' := gR) ?_ D₀.P.A.hom (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left
      (Over.w (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A)) (GlobalTheory.globalFns_holds _ _ D₀.P.isAb).2 ?_ ?_ ?_ T.left x.left z J hJ
    · intro V _ k
      have pw0 : ∏ i, k (w0φ D₀ f i) ^ w0ε i = _ :=
        (Finset.prod_congr rfl fun i _ => by rw [Over.id_left, Category.id_comp]).trans (pw V k (𝟙 D₀.P.A))
      have ps : ∏ i : Fin 2, k (![(ι[D₀.P.A]).left, 𝟙 D₀.P.A.left] i) ^ (![1, -1] : Fin 2 → ℤ) i =
          k (Over.Hom.left (𝟙 D₀.P.A)⁻¹) * (k (Over.Hom.left (𝟙 D₀.P.A)))⁻¹ := by
        have : (𝟙 D₀.P.A)⁻¹ = ι[D₀.P.A] := by simp [Hom.inv_def]
        rw [Fin.prod_univ_two, this]
        simp
      refine (DVR.prod_sum₂ (K := Fin 4) (K' := thK) (U := V) _ pw0 (prod_cub _ _ _ k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 2) (K' := thK) (U := V) _
          (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 2) (U := V) _ (pw V k _) ps) (prod_cub _ _ _ k)).symm)
      have a1 : 𝟙 D₀.P.A ≫ f = f := Category.id_comp f
      have a2 : (𝟙 D₀.P.A)⁻¹ ≫ f = f⁻¹ := by rw [GrpObj.inv_comp, Category.id_comp]
      have a3 : 𝟙 D₀.P.A * (𝟙 D₀.P.A)⁻¹ * f = f := by group
      have a4 : 𝟙 D₀.P.A * (𝟙 D₀.P.A)⁻¹ = 1 := by group
      have a5 : f * f⁻¹ * (𝟙 D₀.P.A)⁻¹ = (𝟙 D₀.P.A)⁻¹ := by group
      have a6 : f * f⁻¹ = 1 := by group
      have a7 : f * (𝟙 D₀.P.A)⁻¹ = (𝟙 D₀.P.A)⁻¹ * f := mul_comm _ _
      have a8 : f⁻¹ * (𝟙 D₀.P.A)⁻¹ = (𝟙 D₀.P.A)⁻¹ * f⁻¹ := mul_comm _ _
      rw [a1, a2, a3, a4, a5, a6, a7, a8]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · exact DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) D₀.sym_gen)
        (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)
    · exact DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)
    · intro y I hI
      have C : IsCub (cubV D₀.cub (T := 𝟙_ _) y I) := isCub_cubV D₀.cub hI
      have o : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left = eSec D₀.P.A := by simp [Hom.one_def, eSec]
      have u1 : val uw (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left y I = 1 := by
        have := val_corr hI h₀ (𝟙 _)
        rwa [val_pull hI, Category.id_comp, val_one, ← o] at this
      have s1 : val D₀.sym (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left y I = 1 := by
        have := val_corr hI D₀.sym_rig (𝟙 _)
        rwa [val_pull hI, Category.id_comp, val_one, ← o] at this
      have i1 : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) ≫ (𝟙 D₀.P.A)⁻¹ = 1 := by
        rw [GrpObj.comp_inv, Category.comp_id, inv_one]
      have f1 : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) ≫ f⁻¹ = 1 := by
        rw [GrpObj.comp_inv, MonObj.one_comp, inv_one]
      rw [(ev _ hI).1, (ev _ hI).2, i1, f1, MonObj.one_comp, Category.comp_id, u1, s1, C.face]; simp only [_root_.mul_one]
  have := (ev x hJ).1.symm.trans (hL.trans (ev x hJ).2)
  rwa [GrpObj.comp_inv, GrpObj.comp_inv, Category.comp_id] at this

end GlobalTheory.UTau0
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UTau0.SecondDiff

theorem prod_symmetricPullback_formalSum_eq {R : Type} [CommRing R] [IsDomain R] (D₀ : DegPre R) (f : D₀.P.A ⟶ D₀.P.A) {T : Over (Sp R)}
    (q : T ⟶ D₀.P.A) {U : Type} [CommGroup U] (h : (T.left ⟶ D₀.P.A.left) → U) :
    ∏ i, h (q.left ≫ GlobalTheory.UTau0.w0φ D₀ f i) ^ GlobalTheory.UTau0.w0ε i =
      h (q * (q ≫ f)).left * (h q.left ^ 2)⁻¹ * (h (q ≫ f).left)⁻¹ * h (1 : T ⟶ D₀.P.A).left ^ 2 := by
  have e₀ : q.left ≫ (padd D₀.P.A (𝟙 _) f).left = (q * (q ≫ f)).left := by
    rw [← Over.comp_left]
    exact congrArg (fun r : T ⟶ D₀.P.A => r.left)
      (show q ≫ padd D₀.P.A (𝟙 _) f = q * (q ≫ f) from (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id]))
  have e₃ : q.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left = (1 : T ⟶ D₀.P.A).left := by
    rw [← Over.comp_left]
    exact congrArg (fun r : T ⟶ D₀.P.A => r.left)
      (show q ≫ toUnit D₀.P.A ≫ η[D₀.P.A] = 1 by rw [Hom.one_def, ← Category.assoc, comp_toUnit])
  rw [Fin.prod_univ_four]
  show h (q.left ≫ (padd D₀.P.A (𝟙 _) f).left) ^ (1 : ℤ) * h (q.left ≫ 𝟙 _) ^ (-2 : ℤ) *
    h (q.left ≫ f.left) ^ (-1 : ℤ) * h (q.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left) ^ (2 : ℤ) = _
  rw [e₀, e₃, Category.comp_id, ← Over.comp_left]
  simp only [zpow_one, zpow_neg, zpow_ofNat, pow_one]

theorem uw_second_diff : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (f g : D₀.P.A ⟶ D₀.P.A) [IsMonHom f] [IsMonHom g],
    padd D₀.P.A f g = 𝟙 D₀.P.A →
    ∀ uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ f) GlobalTheory.UTau0.w0ε), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ u : LB.Gen (LB.LinComb D₀.P.L (rosatiφ D₀.P.A f g) rosatiε), u.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (zero2 D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ (T : Over (Sp R)) (x x' : T ⟶ D₀.P.A) (z : T.left) (J : (T.left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D₀.P.L z J →
      val uw (x * x').left z J * cubV D₀.cub z J (x' ≫ f) (x' ≫ g) x =
        val uw x.left z J * val uw x'.left z J * val u (lift x x').left z J *
          cubV D₀.cub z J (x ≫ f) (x' ≫ f) x * cubV D₀.cub z J (x ≫ f) (x' ≫ f) x' *
          cubV D₀.cub z J x x' ((x ≫ f) * (x' ≫ f)) := by
  intro R _ _ D₀ f g _ _ hfg uw huw hw0 u hu hu0 T x x' z J hJ
  let p₀ : D₀.P.A ⊗ D₀.P.A ⟶ D₀.P.A := fst _ _
  let p₁ : D₀.P.A ⊗ D₀.P.A ⟶ D₀.P.A := snd _ _
  have mf : ∀ {T : Over (Sp R)} (a b : T ⟶ D₀.P.A), (a * b) ≫ f = (a ≫ f) * (b ≫ f) :=
    fun a b => MonObj.mul_comp a b f
  have fg : ∀ {T : Over (Sp R)} (a : T ⟶ D₀.P.A), (a ≫ f) * (a ≫ g) = a := fun a =>
    (MonObj.comp_mul _ _ _).symm.trans ((congrArg (a ≫ ·) (show f * g = 𝟙 _ from hfg)).trans (Category.comp_id a))
  let gLw := LB.mulGen D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (p₀ * p₁).left)
    (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift (p₁ ≫ f) (lift (p₁ ≫ g) p₀)).left)
  let gRw := LB.mulGen D₀.P.L _ _ _ _
    (LB.mulGen D₀.P.L _ _ _ _ (LB.mulGen D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw p₀.left)
      (LB.pullGen D₀.P.L _ _ uw p₁.left)) (LB.pullGen D₀.P.L _ _ u (lift p₀ p₁).left))
    (LB.mulGen D₀.P.L _ _ _ _ (LB.mulGen D₀.P.L _ _ _ _
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift (p₀ ≫ f) (lift (p₁ ≫ f) p₀)).left)
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift (p₀ ≫ f) (lift (p₁ ≫ f) p₁)).left))
      (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (lift p₀ (lift p₁ ((p₀ ≫ f) * (p₁ ≫ f)))).left))
  have vq : ∀ {T' : Over (Sp R)} (σ : T' ⟶ D₀.P.A ⊗ D₀.P.A) {z : T'.left} {J}, Good D₀.P.L z J →
      ∀ {K : Type} [Fintype K] {φ : K → (D₀.P.A.left ⟶ D₀.P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb D₀.P.L φ ε))
        (q : D₀.P.A ⊗ D₀.P.A ⟶ D₀.P.A), val (LB.pullGen D₀.P.L _ _ t q.left) σ.left z J = val t (σ ≫ q).left z J :=
    fun σ z J hJ K _ φ ε t q => by rw [val_pull hJ, ← Over.comp_left]
  have evL : ∀ {T' : Over (Sp R)} (σ : T' ⟶ D₀.P.A ⊗ D₀.P.A) {z : T'.left} {J}, Good D₀.P.L z J →
      val gLw σ.left z J = val uw (σ ≫ (p₀ * p₁)).left z J *
        cubV D₀.cub z J (σ ≫ p₁ ≫ f) (σ ≫ p₁ ≫ g) (σ ≫ p₀) := fun σ z J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vq σ hJ _ _) (val_cub D₀.cub σ hJ _ _ _))
  have evR : ∀ {T' : Over (Sp R)} (σ : T' ⟶ D₀.P.A ⊗ D₀.P.A) {z : T'.left} {J}, Good D₀.P.L z J →
      val gRw σ.left z J = val uw (σ ≫ p₀).left z J * val uw (σ ≫ p₁).left z J *
          val u (lift (σ ≫ p₀) (σ ≫ p₁)).left z J *
        (cubV D₀.cub z J (σ ≫ p₀ ≫ f) (σ ≫ p₁ ≫ f) (σ ≫ p₀) * cubV D₀.cub z J (σ ≫ p₀ ≫ f) (σ ≫ p₁ ≫ f) (σ ≫ p₁) *
          cubV D₀.cub z J (σ ≫ p₀) (σ ≫ p₁) (σ ≫ ((p₀ ≫ f) * (p₁ ≫ f)))) := fun σ z J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vq σ hJ _ _) (vq σ hJ _ _)))
      (by rw [val_pull hJ, ← Over.comp_left, comp_lift])))
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (val_cub D₀.cub σ hJ _ _ _) (val_cub D₀.cub σ hJ _ _ _))) (val_cub D₀.cub σ hJ _ _ _))))

  let e : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A ⊗ D₀.P.A := lift 1 1
  have he : e.left ≫ (snd D₀.P.A D₀.P.A).left ≫ D₀.P.A.hom = 𝟙 _ := by rw [Over.w]; exact Over.w e
  have sj : Function.Surjective ((snd D₀.P.A D₀.P.A).left ≫ D₀.P.A.hom).appTop.hom :=
    surj_comp (surj_snd GlobalTheory.globalFns_holds D₀.P.isAb _) ((GlobalTheory.globalFns_holds _ _ D₀.P.isAb).2)
  let ρ : T ⟶ D₀.P.A ⊗ D₀.P.A := lift x x'
  have key : val gLw ρ.left z J = val gRw ρ.left z J := by
    refine gen_unique' D₀.P.isLB (fun V _ k => ?_) _ e.left he sj ?_ ?_ (fun y I hI => ?_) _ ρ.left z J hJ
    · refine Eq.trans (DVR.prod_sum₂ (K := (Fin 4 ⊕ Fin 4) ⊕ Fin 6) (K' := (thK ⊕ thK) ⊕ thK) (U := V) _
          (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := Fin 6) (U := V) _
            (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _ (prod_symmetricPullback_formalSum_eq D₀ f p₀ k) (prod_symmetricPullback_formalSum_eq D₀ f p₁ k))
            (prod_ros f g p₀ p₁ k))
          (DVR.prod_sum₂ (K := thK ⊕ thK) (K' := thK) (U := V) _
            (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (p₀ ≫ f) (p₁ ≫ f) p₀ k)
              (prod_cub (p₀ ≫ f) (p₁ ≫ f) p₁ k))
            (prod_cub p₀ p₁ ((p₀ ≫ f) * (p₁ ≫ f)) k)))
        (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 4) (K' := thK) (U := V) _ (prod_symmetricPullback_formalSum_eq D₀ f (p₀ * p₁) k)
          (prod_cub (p₁ ≫ f) (p₁ ≫ g) p₀ k)).symm)
      rw [mf, fg, mul_comm p₁ p₀, mul_comm (p₀ ≫ f) p₀, mul_comm (p₁ ≫ f) p₁, mul_comm ((p₀ ≫ f) * (p₁ ≫ f)) p₀,
        mul_comm ((p₀ ≫ f) * (p₁ ≫ f)) p₁, mul_comm (p₁ ≫ g) p₀]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      abel
    · exact DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ huw _) (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)
    · exact DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.pullGen_isGen _ _ _ _ huw _) (DVR.pullGen_isGen _ _ _ _ huw _)) (DVR.pullGen_isGen _ _ _ _ hu _))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)
          (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _)) (DVR.pullGen_isGen _ _ _ _ D₀.cub.isGen _))
    · have C : IsCub (cubV D₀.cub y I) := isCub_cubV D₀.cub hI
      have w1 : val uw (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left y I = 1 := by
        have := val_corr hI hw0 (𝟙 _)
        rw [val_pull hI, Category.id_comp, val_one] at this
        have e1 : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) = η[D₀.P.A] := by simp [Hom.one_def]
        rw [e1]; exact this
      have u1 : val u (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) 1).left y I = 1 := by
        have := val_corr hI hu0 (𝟙 _)
        rw [val_pull hI, Category.id_comp, val_one] at this
        have e2 : lift (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) 1 = lift η[D₀.P.A] η[D₀.P.A] := by simp [Hom.one_def]
        rw [e2]; exact this
      have a₀ : e ≫ p₀ = 1 := lift_fst _ _
      have a₁ : e ≫ p₁ = 1 := lift_snd _ _
      have af : e ≫ p₀ ≫ f = 1 := by rw [← Category.assoc, a₀, MonObj.one_comp]
      have bf : e ≫ p₁ ≫ f = 1 := by rw [← Category.assoc, a₁, MonObj.one_comp]
      have bg : e ≫ p₁ ≫ g = 1 := by rw [← Category.assoc, a₁, MonObj.one_comp]
      have ab : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁, _root_.mul_one])
      have ff : e ≫ ((p₀ ≫ f) * (p₁ ≫ f)) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [af, bf, _root_.mul_one])
      rw [evL e hI, evR e hI, ab, ff, af, bf, bg, a₀, a₁, w1, u1, C.face]
      simp
  rw [evL ρ hJ, evR ρ hJ] at key
  have r₀ : ρ ≫ p₀ = x := lift_fst _ _
  have r₁ : ρ ≫ p₁ = x' := lift_snd _ _
  have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
  have s₂ : ρ ≫ ((p₀ ≫ f) * (p₁ ≫ f)) = (x ≫ f) * (x' ≫ f) :=
    (MonObj.comp_mul _ _ _).trans (by rw [← Category.assoc, ← Category.assoc, r₀, r₁])
  rw [s₁, s₂, ← Category.assoc ρ p₁ f, ← Category.assoc ρ p₁ g, ← Category.assoc ρ p₀ f, r₀, r₁] at key
  rw [key]
  simp only [_root_.mul_assoc]

end GlobalTheory.UTau0.SecondDiff
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UTau0

namespace GenTr

theorem stalkMap_gm_comp {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (u : Γ(X, U)ˣ) :
    Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U u) = gm (f ≫ g) z U u := by
  by_cases h : g (f z) ∈ U
  · apply Units.ext
    rw [Units.coe_map, gm_val g (f z) U h, gm_val (f ≫ g) z U h]
    exact (Scheme.Hom.germ_stalkMap_apply f _ z h _).trans rfl
  · have h' : (f ≫ g) z ∉ U := h
    simp only [gm, dif_neg h, dif_neg h', MonoidHom.one_apply, map_one]

theorem val_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y') (g : Y' ⟶ Y) (q : Z ⟶ Y) (hq : r ≫ g = q) (z : Z)
    (J : (Z ⟶ X) → L.ι) :
    val t q z J = Units.map (r.stalkMap z).hom.toMonoidHom (val t g (r z) (fun ψ => J (r ≫ ψ))) := by
  subst hq
  rw [val_of t g (r z) _ (fun k => J ((r ≫ g) ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact (stalkMap_gm_comp r g z _ _).symm

theorem toUnit_TK_left (R : Type) [CommRing R] [IsDomain R] : (toUnit (TK R)).left = jK R := by
  have := Over.w (toUnit (TK R))
  simpa using this

theorem val_tau {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (a b : D.X) : val (D.tau a b) (𝟙 _) z J = val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.psi b) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ := by
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv]

end GenTr

open GenTr

theorem rlaws_transfer : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D₀.X] (onB : D₀.P.OAct O), (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) →
    ∀ (w0 : O) (uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ (onB.act w0)) GlobalTheory.UTau0.w0ε)), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)),
    GlobalTheory.UTau0.RLaws D₀ onB w0 uw ψ →
    ∃ h : ∀ y, (LB.pullGen D₀.P.L _ _ (ψ y) (jK R)).IsGen,
      letI : Module O ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).X :=
        ‹Module O D₀.X›
      ∃ oa : ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).OAct O,
        oa.onB = onB ∧
        ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).PsiEven ∧
        ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).TauBimult ∧
        TraceFormTwistIso ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R) oa w0 ∧
        ∀ y, PsiUnitOn ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R) y
          Set.univ := by
  intro R _ _ D₀ O _ _ _ onB hc w0 uw huw hnw ψ hR
  obtain ⟨hgen, h1, h2, h3, h4⟩ := hR
  have hL := D₀.P.isLB
  have htu := toUnit_TK_left R
  let Dn : DegPre R := { D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := fun y => DVR.pullGen_isGen _ _ _ _ (hgen y) _ }
  have Fψ : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ y,
      val (Dn.psi y) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (val (ψ y) (𝟙 _) ((jK R) z) (fun f => J (jK R ≫ f))) :=
    fun z J hJ y => (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ (by simp) _ _)
  have Frig : ∀ (z : (TK R).left) J, Good D₀.P.L z J →
      val Dn.rigK (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (rigV D₀ ((jK R) z) (fun f => J (jK R ≫ f))) :=
    fun z J hJ => (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ (by simp [htu]) _ _)
  have Ftau : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ a b : D₀.X,
      val (Dn.tau a b) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (tauV D₀ ψ ((jK R) z) (fun f => J (jK R ≫ f)) a b) := by
    intro z J hJ a b
    rw [val_tau Dn hJ, Fψ z J hJ, Fψ z J hJ, Fψ z J hJ, Frig z J hJ, tauV, map_mul, map_mul, map_mul, map_inv, map_inv,
      map_inv]
    rfl
  have Fx : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ {K : Type} [Fintype K] (φ : K → (D₀.P.A.left ⟶ D₀.P.A.left))
      (ε : K → ℤ) (t : LB.Gen (LB.LinComb D₀.P.L φ ε)) (y : D₀.X),
      val (LB.pullGen D₀.P.L _ _ t (Dn.xK y)) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (val t (D₀.c y).left ((jK R) z) (fun f => J (jK R ≫ f))) := by
    intro z J hJ K _ φ ε t y
    refine (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ ?_ _ _)
    rw [Category.id_comp]
    show _ = (toUnit (TK R) ≫ D₀.c y).left
    rw [Over.comp_left, htu]
  have F2 : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ {K : Type} [Fintype K]
      (φ : K → ((D₀.P.A ⊗ D₀.P.A).left ⟶ D₀.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D₀.P.L φ ε)) (y y' : D₀.X),
      val (LB.pullGen D₀.P.L _ _ t (Dn.pt2 y y')) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom
          (val t (lift (D₀.c y) (D₀.c y')).left ((jK R) z) (fun f => J (jK R ≫ f))) := by
    intro z J hJ K _ φ ε t y y'
    refine (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ ?_ _ _)
    rw [Category.id_comp, DegPre.pt2, ← htu, ← Over.comp_left, comp_lift]
  have Fcub : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ a a' b : D₀.X,
      val (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (Dn.pt3 a a' b)) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom
          (val D₀.cub.t (lift (D₀.c a) (lift (D₀.c a') (D₀.c b))).left ((jK R) z) (fun f => J (jK R ≫ f))) := by
    intro z J hJ a a' b
    refine (val_pull hJ _ _ _).trans (val_stalk _ _ (lift (D₀.c a) (lift (D₀.c a') (D₀.c b))).left _ ?_ _ _)
    rw [Category.id_comp, DegPre.pt3, ← htu, ← Over.comp_left, comp_lift, comp_lift]
  refine ⟨fun y => DVR.pullGen_isGen _ _ _ _ (hgen y) _, ⟨onB, hc, ?_⟩, rfl, ?_, ?_, ⟨uw, huw, hnw, ?_⟩, ?_⟩
  · intro a u hu hun y y'
    refine corr_of_val hL fun z J hJ => ?_
    rw [val_mul hJ, Ftau z J hJ, F2 z J hJ, Ftau z J hJ, ← map_mul]
    exact congrArg _ (h3 a u hu hun y y' _ _ fun f => hJ _)
  · intro χ
    refine corr_of_val hL fun z J hJ => ?_
    rw [val_mul hJ, Fψ z J hJ, Fx z J hJ, Fψ z J hJ, ← map_mul]
    exact congrArg _ (h2 χ _ _ fun f => hJ _)
  · intro a a' b
    refine corr_of_val hL fun z J hJ => ?_
    have key : val (Dn.tau (a + a') b) (𝟙 _) z J *
        val (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (Dn.pt3 a a' b)) (𝟙 _) z J =
          val (Dn.tau a b) (𝟙 _) z J * val (Dn.tau a' b) (𝟙 _) z J := by
      rw [Ftau z J hJ, Fcub z J hJ, Ftau z J hJ, Ftau z J hJ, ← map_mul, ← map_mul]
      exact congrArg _ (h1 a a' b _ _ fun f => hJ _)
    exact (val_mul hJ _ _ _).trans (key.trans (val_mul hJ _ _ _).symm)
  · intro y
    refine corr_of_val hL fun z J hJ => ?_
    have key : val (Dn.tau y (w0 • y)) (𝟙 _) z J * val (LB.pullGen D₀.P.L _ _ uw (Dn.xK y)) (𝟙 _) z J =
        val (Dn.psi y) (𝟙 _) z J * val Dn.rigK (𝟙 _) z J := by
      rw [Ftau z J hJ, Fx z J hJ, Fψ z J hJ, Frig z J hJ, ← map_mul, ← map_mul]
      exact congrArg _ (h4 y _ _ fun f => hJ _)
    exact (val_mul hJ _ _ _).trans (key.trans (val_mul hJ _ _ _).symm)
  · intro y j V _ _ hV h
    have hle : V ≤ LB.wchart D₀.P.L (fun _ : PUnit => (D₀.c y).left) j :=
      fun x hx => Set.mem_iInter.2 fun _ => hV hx
    refine ⟨(res hle ((ψ y).s j)).val, Units.isUnit _, ?_⟩
    have e := congrArg (fun q => q.hom ((ψ y).s j).val) ((jK R).naturality (homOfLE hle).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    refine e.trans ?_
    show _ = ((TK R).left.presheaf.map (homOfLE h).op).hom (((TK R).left.presheaf.map (homOfLE _).op).hom
      (((jK R).app _).hom ((ψ y).s j).val))
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

end GlobalTheory.UTau0
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

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatV

theorem fracIotaBasicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (t : SAB H (Sp R)) (c : R), c ≠ 0 → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left), x' ≫ t.G.hom = spMap φ → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∃ iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* (FractionRing Ω), ∀ r, iota (GlobalTheory.HeatV.resV R c r) = (algebraMap Ω (FractionRing Ω)) (φ r) := by
  intro E _ _ _ H R _ _ t c hc Ω _ _ φ x' hx hinj
  have e1 : ∀ y : Γ(Sp R, ⊤), (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom
      ((x'.appTop).hom ((t.G.hom.appTop).hom y)) = φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y) := by
    intro y
    have n := congrArg (fun k => k.hom y) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
    rw [← n, show Spec.map (CommRingCat.ofHom φ) = x' ≫ t.G.hom from hx.symm, Scheme.Hom.comp_appTop]
    rfl
  have e2 : ∀ y : Γ(Sp R, ⊤), ((η[t.G]).left.appTop).hom ((t.G.hom.appTop).hom y) = y := by
    intro y
    have w : (η[t.G]).left ≫ t.G.hom = 𝟙 (Sp R) := by simpa using Over.w η[t.G]
    have := congrArg (fun k => (Scheme.Hom.appTop k).hom y) w
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    simp
  have ht : ⊤ ≤ x' ⁻¹ᵁ (⊤ : t.G.left.Opens) := by simp
  have inj : ∀ r : R, φ r = 0 → r = 0 := by
    intro r hr
    set y := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r with hy
    have hv : valR x' ⊤ ((t.G.hom.appTop).hom y) = 0 := by
      unfold valR
      rw [dite_eq_left ht]
      have : x'.appLE ⊤ ⊤ ht = x'.appTop := Scheme.Hom.appLE_eq_app _
      rw [this, e1, hy]
      simpa using hr
    have h0 := hinj ⊤ _ ht hv
    have h1 := e2 y
    rw [h0, map_zero] at h1
    have : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y = r := by simp [hy]
    rw [← this, ← h1, map_zero]
  let s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c
  let gg : Γ(Sp R, ⊤) →+* FractionRing Ω :=
    (algebraMap Ω (FractionRing Ω)).comp (φ.comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom)
  have hu : IsUnit (gg s) := by
    rw [isUnit_iff_ne_zero]
    simp only [gg, s, RingHom.comp_apply]
    have hs : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) = c := by simp
    rw [hs]
    intro h0
    exact hc (inj c ((IsFractionRing.injective Ω (FractionRing Ω)) (by simpa using h0)))
  refine ⟨IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu, fun r => ?_⟩
  show IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu
    (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
  rw [IsLocalization.Away.lift, IsLocalization.lift_eq]
  simp [gg]

end GlobalTheory.HeatV
end
end
