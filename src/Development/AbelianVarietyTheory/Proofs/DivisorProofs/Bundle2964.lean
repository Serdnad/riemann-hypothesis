module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2849
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocGenOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CartesianLiftThreeCompProjection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle012

@[expose] public section

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp

variable {S : Scheme.{0}} (P₀ P₁ P₂ : PolAV S)

theorem prod_cmp (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) {T : Over S} (a b : T ⟶ P₀.A) {V : Type} [CommGroup V]
    (h : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → V) :
    ∏ k, h ((lift a b).left ≫ cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂ k) ^ cmpε k =
      (h (((a ≫ f₂) * (b ≫ g₂)).left ≫ coprod.inr) * (h ((a ≫ f₂).left ≫ coprod.inr))⁻¹ *
        (h ((b ≫ g₂).left ≫ coprod.inr))⁻¹ * h ((1 : T ⟶ P₂.A).left ≫ coprod.inr)) *
      (h (((a ≫ f₁) * (b ≫ g₁)).left ≫ coprod.inl) * (h ((a ≫ f₁).left ≫ coprod.inl))⁻¹ *
        (h ((b ≫ g₁).left ≫ coprod.inl))⁻¹ * h ((1 : T ⟶ P₁.A).left ≫ coprod.inl))⁻¹ := by
  have c₂ := prod_cube₂ (fst P₀.A P₀.A ≫ f₂) (snd P₀.A P₀.A ≫ g₂) (fun q => h ((lift a b).left ≫ q ≫ coprod.inr))
  have c₁ := prod_neg _ _ (prod_cube₂ (fst P₀.A P₀.A ≫ f₁) (snd P₀.A P₀.A ≫ g₁)
    (fun q => h ((lift a b).left ≫ q ≫ coprod.inl)))
  have e : ∀ {Q : Over S} (q : P₀.A ⊗ P₀.A ⟶ Q) (t : Q.left ⟶ P₁.A.left ⨿ P₂.A.left),
      (lift a b).left ≫ q.left ≫ t = (lift a b ≫ q).left ≫ t := fun q t => by rw [Over.comp_left, Category.assoc]
  rw [Fintype.prod_sum_type]
  refine congrArg₂ (· * ·) (c₂.trans ?_) (c₁.trans ?_)
  · simp only [e, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, MonObj.comp_one]
  · simp only [e, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, MonObj.comp_one]

end GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp

theorem add_snd : GlobalFnsSt → ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], ∀ (r₁ : LB.Gen (P₁.L.pull (eSec P₁.A))) (hr₁ : r₁.IsGen) (c₁ : CubicalStr P₁.A ⟨P₁.L, r₁, P₁.isLB, hr₁⟩) (r₂ : LB.Gen (P₂.L.pull (eSec P₂.A))) (hr₂ : r₂.IsGen) (c₂ : CubicalStr P₂.A ⟨P₂.L, r₂, P₂.isLB, hr₂⟩) (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u (r ≫ zero2 P₀.A) z J = 1) → ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → (join P₁.L P₂.L).ι), Good (join P₁.L P₂.L) z J → ∀ (x y y' : T ⟶ P₀.A), val u (lift x (y * y')).left z J * cubV c₁ z (rl J) (x ≫ f₁) (y ≫ g₁) (y' ≫ g₁) = cubV c₂ z (rr J) (x ≫ f₂) (y ≫ g₂) (y' ≫ g₂) * (val u (lift x y).left z J * val u (lift x y').left z J) := by
  intro hG S P₀ P₁ P₂ _ _ f₁ g₁ f₂ g₂ _ _ _ _ r₁ hr₁ c₁ r₂ hr₂ c₂ u hu hn T z J hJ x y y'
  let p₀ := x3 P₀.A 0
  let p₁ := x3 P₀.A 1
  let p₂ := x3 P₀.A 2
  have hL := join_isLB P₁.isLB P₂.isLB
  have pl := isPart_inl P₁.L P₂.L
  have pr := isPart_inr P₁.L P₂.L
  have vp : ∀ {T' : Over S} (σ : T' ⟶ G3 P₀.A) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J → ∀ a b : G3 P₀.A ⟶ P₀.A,
      val (LB.pullGen _ _ _ u (lift a b).left) σ.left z J = val u (lift (σ ≫ a) (σ ≫ b)).left z J :=
    fun σ z J hJ a b => by rw [val_pull hJ, ← Over.comp_left, comp_lift]
  let U₁ := LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ u (lift p₀ (p₁ * p₂)).left)
    (pl.gen (LB.pullGen P₁.L _ _ c₁.t (lift (p₀ ≫ f₁) (lift (p₁ ≫ g₁) (p₂ ≫ g₁))).left))
  let U₂ := LB.mulGen _ _ _ _ _ (pr.gen (LB.pullGen P₂.L _ _ c₂.t (lift (p₀ ≫ f₂) (lift (p₁ ≫ g₂) (p₂ ≫ g₂))).left))
    (LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ u (lift p₀ p₁).left) (LB.pullGen _ _ _ u (lift p₀ p₂).left))
  have hU₁ : U₁.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _)
    (pl.gen_isGen (DVR.pullGen_isGen _ _ _ _ c₁.isGen _))
  have hU₂ : U₂.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (pr.gen_isGen (DVR.pullGen_isGen _ _ _ _ c₂.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))
  have ev₁ : ∀ {T' : Over S} (σ : T' ⟶ G3 P₀.A) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J →
      val U₁ σ.left z J = val u (lift (σ ≫ p₀) (σ ≫ (p₁ * p₂))).left z J *
        cubV c₁ z (rl J) (σ ≫ p₀ ≫ f₁) (σ ≫ p₁ ≫ g₁) (σ ≫ p₂ ≫ g₁) := fun σ z J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _)
      ((pl.val_gen _ _ _ hJ).trans (val_cub c₁ σ (pl.good hJ) _ _ _)))
  have ev₂ : ∀ {T' : Over S} (σ : T' ⟶ G3 P₀.A) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J →
      val U₂ σ.left z J = cubV c₂ z (rr J) (σ ≫ p₀ ≫ f₂) (σ ≫ p₁ ≫ g₂) (σ ≫ p₂ ≫ g₂) *
        (val u (lift (σ ≫ p₀) (σ ≫ p₁)).left z J * val u (lift (σ ≫ p₀) (σ ≫ p₂)).left z J) := fun σ z J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((pr.val_gen _ _ _ hJ).trans (val_cub c₂ σ (pr.good hJ) _ _ _))
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))))
  let e : 𝟙_ (Over S) ⟶ G3 P₀.A := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have o₁ : e ≫ (p₁ * p₂) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂, _root_.mul_one])
  have sj : Function.Surjective ((snd P₀.A (P₀.A ⊗ P₀.A)).left ≫ (snd P₀.A P₀.A).left ≫ P₀.A.hom).appTop.hom :=
    surj_comp (surj_snd hG P₀.isAb _) (surj_comp (surj_snd hG P₀.isAb _) (hG _ _ P₀.isAb).2)
  have he : e.left ≫ (snd P₀.A (P₀.A ⊗ P₀.A)).left ≫ (snd P₀.A P₀.A).left ≫ P₀.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := gen_unique' hL (u := U₁) (u' := U₂) (fun V _ k => ?_) _ e.left he sj hU₁ hU₂ (fun w I hI => ?_)
  rotate_left
  · refine (prod_sum₂ (K := thK) (K' := KK ⊕ KK) (U := V) _
      (prod_cub (p₀ ≫ f₂) (p₁ ≫ g₂) (p₂ ≫ g₂) fun q => k (q ≫ coprod.inr))
      (prod_sum₂ (K := KK) (K' := KK) (U := V) _ (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₀ p₁ k)
        (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₀ p₂ k))).trans
      (Eq.trans ?_ (prod_sum₂ (K := KK) (K' := thK) (U := V) _ (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₀ (p₁ * p₂) k)
        (prod_cub (p₀ ≫ f₁) (p₁ ≫ g₁) (p₂ ≫ g₁) fun q => k (q ≫ coprod.inl))).symm)
    simp only [MonObj.mul_comp, ← _root_.mul_assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · rw [ev₁ e hI, ev₂ e hI]
    simp only [← Category.assoc, e₀, e₁, e₂, o₁, MonObj.one_comp]
    have C₁ := isCub_cubV c₁ (pl.good hI)
    have C₂ := isCub_cubV c₂ (pr.good hI)
    have v1 : val u (lift (1 : 𝟙_ (Over S) ⟶ P₀.A) 1).left w I = 1 := by
      have eL : lift (1 : 𝟙_ (Over S) ⟶ P₀.A) 1 = lift η[P₀.A] η[P₀.A] := by simp [Hom.one_def]
      rw [eL]
      exact (congrArg (fun q => val u q w I) (Category.id_comp _).symm).trans (hn _ (𝟙 _) w I hI)
    rw [v1, C₁.face, C₂.face]
    simp
  have kk := (ev₁ _ hJ).symm.trans ((key _ (lift x (lift y y')).left z J hJ).trans (ev₂ _ hJ))
  have r₀ : lift x (lift y y') ≫ p₀ = x := by simp [p₀, x3]
  have r₁ : lift x (lift y y') ≫ p₁ = y := by simp [p₁, x3]
  have r₂ : lift x (lift y y') ≫ p₂ = y' := by simp [p₂, x3]
  have s₁ : lift x (lift y y') ≫ (p₁ * p₂) = y * y' := (MonObj.comp_mul _ _ _).trans (by rw [r₁, r₂])
  rw [s₁] at kk
  simp only [← Category.assoc, r₀, r₁, r₂] at kk
  exact kk

end GlobalTheory.Mum.Two.WeilCmp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp
variable {S : Scheme.{0}}
theorem comp_psum_nrm (G : Over S) [GrpObj G] [IsCommMonObj G] {n : ℕ} {T T' : Over S} (g : T' ⟶ T) (x : Fin n → (T ⟶ G))
    (I : Finset (Fin n)) : g ≫ psum G x I = psum G (fun k => g ≫ x k) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil =>
    simp only [List.foldr_nil, pzero]
    rw [← Category.assoc, toUnit_unique (g ≫ toUnit T) (toUnit T')]
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [padd, padd, ← Category.assoc, comp_lift, ih]

theorem psum_one_nrm (G : Over S) [GrpObj G] [IsCommMonObj G] {n : ℕ} {T : Over S} (I : Finset (Fin n)) :
    psum G (fun _ => (1 : T ⟶ G)) I = 1 := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp only [List.foldr_nil, pzero]; rfl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    show (1 : T ⟶ G) * 1 = 1
    exact _root_.mul_one _

theorem zeroPair_comp_partialSum_eq_unit (P₀ P : PolAV S) (f g : P₀.A ⟶ P.A) [IsMonHom f] [IsMonHom g] (I : Finset (Fin 2)) :
    zero2 P₀.A ≫ (psum P.A ![fst P₀.A P₀.A ≫ f, snd P₀.A P₀.A ≫ g] I).left = η[P.A].left := by
  have e : lift η[P₀.A] η[P₀.A] ≫ psum P.A ![fst P₀.A P₀.A ≫ f, snd P₀.A P₀.A ≫ g] I = η[P.A] := by
    rw [comp_psum_nrm]
    have : (fun k => lift η[P₀.A] η[P₀.A] ≫ (![fst P₀.A P₀.A ≫ f, snd P₀.A P₀.A ≫ g] : Fin 2 → _) k) =
        fun _ => (1 : 𝟙_ (Over S) ⟶ P.A) := by
      funext k
      fin_cases k <;> simp [IsMonHom.one_hom, Hom.one_def]
    rw [this, psum_one_nrm, Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over S))) (𝟙 _), Category.id_comp]
  exact congrArg (fun q => q.left) e

theorem prod_zpow_nrm {α U : Type} [CommGroup U] (a : U) (e : α → ℤ) (s : Finset α) :
    ∏ i ∈ s, a ^ e i = a ^ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

theorem exists_gen_nrm (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left]
    (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂]
    (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)) (hu : u.IsGen) :
    ∃ u' : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J),
      Good (join P₁.L P₂.L) z J → val u' (r ≫ zero2 P₀.A) z J = 1 := by
  let π := (P₀.A ⊗ P₀.A).hom
  have z2 : zero2 P₀.A ≫ π = 𝟙 S := Over.w (lift η[P₀.A] η[P₀.A])
  have cst : ∀ k, zero2 P₀.A ≫ cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂ k =
      Sum.elim (fun _ => η[P₂.A].left ≫ coprod.inr) (fun _ => η[P₁.A].left ≫ coprod.inl) k := by
    rintro (I | I)
    · show zero2 P₀.A ≫ (psum P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] I.down).left ≫ coprod.inr = _
      rw [← Category.assoc, zeroPair_comp_partialSum_eq_unit]; rfl
    · show zero2 P₀.A ≫ (psum P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] I.down).left ≫ coprod.inl = _
      rw [← Category.assoc, zeroPair_comp_partialSum_eq_unit]; rfl
  have s₁ : ∑ I : ULift.{0} (Finset (Fin 2)), ((-1 : ℤ) ^ (2 - I.down.card)) = 0 := by decide
  have s₂ : ∑ I : ULift.{0} (Finset (Fin 2)), (-((-1 : ℤ) ^ (2 - I.down.card))) = 0 := by decide
  have hF : FormEq (Sum.elim (cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂) (fun k => (π ≫ zero2 P₀.A) ≫ cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂ k))
      (Sum.elim (cmpε) (fun k => -cmpε k)) (cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂) cmpε := by
    intro U _ h
    have one : ∏ k, h ((π ≫ zero2 P₀.A) ≫ cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂ k) ^ cmpε k = 1 := by
      simp only [Category.assoc, cst]
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, cmpε]
      rw [prod_zpow_nrm, prod_zpow_nrm, s₁, s₂, zpow_zero, zpow_zero, _root_.mul_one]
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [DVR.prod_neg _ _ one, inv_one, _root_.mul_one]
  obtain ⟨u', hu', hv⟩ := exists_gen (join_isLB P₁.isLB P₂.isLB) hF
    (LB.mulGen _ _ _ _ _ u (LB.invGen _ _ _ (LB.pullGen _ _ _ u (π ≫ zero2 P₀.A))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _)))
  refine ⟨u', hu', fun Z r z J hJ => ?_⟩
  rw [hv Z _ z J hJ, val_mul hJ, val_inv, val_pull hJ]
  have : (r ≫ zero2 P₀.A) ≫ π ≫ zero2 P₀.A = r ≫ zero2 P₀.A := by
    rw [Category.assoc, ← Category.assoc (zero2 P₀.A), z2]
    exact congrArg (r ≫ ·) (Category.id_comp _)
  rw [this, mul_inv_cancel]

end GlobalTheory.Mum.Two.WeilCmp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section

namespace GlobalTheory.HomMum

variable {S : Scheme.{0}}

theorem prod_alt_const {U : Type} [CommGroup U] (m : U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), m ^ ((-1 : ℤ) ^ (2 - I.down.card)) = 1 := by
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => m ^ ((-1 : ℤ) ^ (2 - I.card))) (fun I => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₄ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₄]
  simp

theorem lift_one_psum {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (I : Finset (Fin 2)) :
    lift (1 : T ⟶ G) (1 : T ⟶ G) ≫ psum G (x2 G) I = 1 := by
  rw [comp_psum]
  have e : (fun k => lift (1 : T ⟶ G) (1 : T ⟶ G) ≫ x2 G k) = fun _ => (1 : T ⟶ G) := by
    funext k
    fin_cases k <;> simp [x2]
  rw [e]
  unfold psum
  induction ((List.finRange 2).filter (· ∈ I)) with
  | nil => simp only [List.foldr_nil, pzero]; rfl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    show (1 : T ⟶ G) * 1 = 1
    exact _root_.mul_one _

variable {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]

theorem kappa_comp_mφ (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b] (k : MK) :
    (lift (1 : H₁ ⊗ H₁ ⟶ H₁) (1 : H₁ ⊗ H₁ ⟶ H₁)).left ≫ mφ H₁ H₂ a b k =
      Sum.elim (fun _ => (1 : H₁ ⊗ H₁ ⟶ H₂).left ≫ coprod.inr) (fun _ => (1 : H₁ ⊗ H₁ ⟶ H₁).left ≫ coprod.inl) k := by
  rcases k with I | I
  · simp only [mφ, Sum.elim_inl]
    rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, comp_lift, lift_fst_assoc,
      lift_snd_assoc, MonObj.one_comp, MonObj.one_comp, lift_one_psum]
  · simp only [mφ, Sum.elim_inr]
    rw [← Category.assoc, ← Over.comp_left, lift_one_psum]

theorem exists_isNrm : ∀ {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]
    {L₁ : LB H₁.left} {L₂ : LB H₂.left}, (join L₁ L₂).IsLB → ∀ (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b]
    (t : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε)), t.IsGen →
    ∃ u : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε), IsNrm u := by
  intro S H₁ H₂ _ _ _ _ L₁ L₂ hL a b _ _ t ht
  have p : ∀ (V : Type) [CommGroup V] (k : ((H₁ ⊗ H₁).left ⟶ H₁.left ⨿ H₂.left) → V),
      ∏ i : MK, k ((lift (1 : H₁ ⊗ H₁ ⟶ H₁) (1 : H₁ ⊗ H₁ ⟶ H₁)).left ≫ mφ H₁ H₂ a b i) ^ mε i = 1 := by
    intro V _ k
    rw [Fintype.prod_sum_type]
    simp only [kappa_comp_mφ, Sum.elim_inl, Sum.elim_inr, mε, zpow_neg, Finset.prod_inv_distrib]
    rw [prod_alt_const, prod_alt_const, inv_one, _root_.mul_one]
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := mφ H₁ H₂ a b) (ε' := mε)
    (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := MK) (K' := MK) (U := V) _
        (c := ∏ i, k (mφ H₁ H₂ a b i) ^ mε i) rfl (DVR.prod_neg _ _ (p V k))) ?_
      simp)
    (LB.mulGen _ _ _ _ _ t (LB.invGen _ _ _ (LB.pullGen _ _ _ t (lift (1 : H₁ ⊗ H₁ ⟶ H₁) (1 : H₁ ⊗ H₁ ⟶ H₁)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨u, hu, fun y J hJ => ?_⟩
  have e : (lift (1 : 𝟙_ (Over S) ⟶ H₁) (1 : 𝟙_ (Over S) ⟶ H₁)).left ≫ (lift (1 : H₁ ⊗ H₁ ⟶ H₁) (1 : H₁ ⊗ H₁ ⟶ H₁)).left =
      (lift (1 : 𝟙_ (Over S) ⟶ H₁) (1 : 𝟙_ (Over S) ⟶ H₁)).left := by
    rw [← Over.comp_left, comp_lift, MonObj.comp_one]
  rw [hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, e, mul_inv_cancel]

end GlobalTheory.HomMum
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.EndRosati

namespace GlobalTheory.HomMum

variable {S : Scheme.{0}}

theorem mφ_comp {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] (a b : H₁ ⟶ H₂)
    {T : Over S} (x y : T ⟶ H₁) (k : MK) :
    (lift x y).left ≫ mφ H₁ H₂ a b k =
      Sum.elim (fun I : ULift.{0} (Finset (Fin 2)) => (psum H₂ ![x ≫ a, y ≫ b] I.down).left ≫ coprod.inr)
        (fun I : ULift.{0} (Finset (Fin 2)) => (psum H₁ ![x, y] I.down).left ≫ coprod.inl) k := by
  rcases k with I | I
  · have e : lift x y ≫ lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b) ≫ psum H₂ (x2 H₂) I.down =
        psum H₂ ![x ≫ a, y ≫ b] I.down := by
      rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.comp_psum]
      congr 1
      funext i
      fin_cases i <;> simp [x2]
    show (lift x y).left ≫ (lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b)).left ≫ (psum H₂ (x2 H₂) I.down).left ≫ coprod.inr =
      (psum H₂ ![x ≫ a, y ≫ b] I.down).left ≫ coprod.inr
    rw [← e]
    simp only [Over.comp_left, Category.assoc]
  · have e : lift x y ≫ psum H₁ (x2 H₁) I.down = psum H₁ ![x, y] I.down := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.comp_psum]
      congr 1
      funext i
      fin_cases i <;> simp [x2]
    show (lift x y).left ≫ (psum H₁ (x2 H₁) I.down).left ≫ coprod.inl = (psum H₁ ![x, y] I.down).left ≫ coprod.inl
    rw [← e]
    simp only [Over.comp_left, Category.assoc]

theorem mφ_push {S' : Scheme.{0}} {j : S' ⟶ S} {E₁ E₂ : Over S'} [GrpObj E₁] [IsCommMonObj E₁] [GrpObj E₂]
    [IsCommMonObj E₂] {A₁ A₂ : Over S} [GrpObj A₁] [IsCommMonObj A₁] [GrpObj A₂] [IsCommMonObj A₂]
    (p₁ : (Over.map j).obj E₁ ⟶ A₁) (p₂ : (Over.map j).obj E₂ ⟶ A₂)
    (hm₁ : ∀ {T : Over S'} (x y : T ⟶ E₁), push p₁ (x * y) = push p₁ x * push p₁ y)
    (hm₂ : ∀ {T : Over S'} (x y : T ⟶ E₂), push p₂ (x * y) = push p₂ x * push p₂ y)
    {a' b' : E₁ ⟶ E₂} {a b : A₁ ⟶ A₂} (ha : push p₂ a' = p₁ ≫ a) (hb : push p₂ b' = p₁ ≫ b)
    {T : Over S'} (x y : T ⟶ E₁) (k : MK) :
    (lift (push p₁ x) (push p₁ y)).left ≫ mφ A₁ A₂ a b k =
      (lift x y).left ≫ mφ E₁ E₂ a' b' k ≫ coprod.map p₁.left p₂.left := by
  let ρ₁ : (T ⟶ E₁) →* ((Over.map j).obj T ⟶ A₁) :=
    MonoidHom.mk' (push p₁) fun x y => hm₁ x y
  let ρ₂ : (T ⟶ E₂) →* ((Over.map j).obj T ⟶ A₂) :=
    MonoidHom.mk' (push p₂) fun x y => hm₂ x y
  have pa : ∀ (z : T ⟶ E₁) {c' : E₁ ⟶ E₂} {c : A₁ ⟶ A₂}, push p₂ c' = p₁ ≫ c → push p₂ (z ≫ c') = push p₁ z ≫ c :=
    fun z c' c h => by
      simp only [push, Functor.map_comp, Category.assoc] at h ⊢
      rw [h]
  rw [← Category.assoc, mφ_comp, mφ_comp]
  rcases k with I | I
  · have e := ReciprocityTheory.ChartRestriction.G.Geo.Tor.psum_hom ρ₂ ![x ≫ a', y ≫ b'] I.down
    have e' : (fun i => ρ₂ ((![x ≫ a', y ≫ b'] : Fin 2 → (T ⟶ E₂)) i)) = ![push p₁ x ≫ a, push p₁ y ≫ b] := by
      funext i
      fin_cases i
      · exact pa x ha
      · exact pa y hb
    rw [e'] at e
    show (psum A₂ ![push p₁ x ≫ a, push p₁ y ≫ b] I.down).left ≫ coprod.inr =
      ((psum E₂ ![x ≫ a', y ≫ b'] I.down).left ≫ coprod.inr) ≫ coprod.map p₁.left p₂.left
    rw [← e, Category.assoc, coprod.inr_map, ← Category.assoc]
    rfl
  · have e := ReciprocityTheory.ChartRestriction.G.Geo.Tor.psum_hom ρ₁ ![x, y] I.down
    have e' : (fun i => ρ₁ ((![x, y] : Fin 2 → (T ⟶ E₁)) i)) = ![push p₁ x, push p₁ y] := by
      funext i
      fin_cases i <;> rfl
    rw [e'] at e
    show (psum A₁ ![push p₁ x, push p₁ y] I.down).left ≫ coprod.inl =
      ((psum E₁ ![x, y] I.down).left ≫ coprod.inl) ≫ coprod.map p₁.left p₂.left
    rw [← e, Category.assoc, coprod.inl_map, ← Category.assoc]
    rfl

end GlobalTheory.HomMum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.Desc

section
variable {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R)))

theorem noetherianSpace_prod_field (F : Type) [Field F] [Algebra (FractionRing R) F] :
    TopologicalSpace.NoetherianSpace (TFK (R := R) F ⊗ A.A).left := by
  have := A.isAb.proper
  let b : (TFK (R := R) F ⊗ A.A).left ⟶ Spec (CommRingCat.of F) := (fst (TFK (R := R) F) A.A).left
  have : IsProper b := inferInstanceAs (IsProper (pullback.fst _ _))
  have : IsLocallyNoetherian (TFK (R := R) F ⊗ A.A).left := LocallyOfFiniteType.isLocallyNoetherian b
  have : CompactSpace (TFK (R := R) F ⊗ A.A).left := QuasiCompact.compactSpace_of_compactSpace b
  have : IsNoetherian (TFK (R := R) F ⊗ A.A).left := {}
  infer_instance

theorem isPullback_baseEm_whiskerRight {F : Type} [Field F] [Algebra (FractionRing R) F]
    (em : Kb R →ₐ[FractionRing R] F) :
    IsPullback (baseEm em ▷ A.A).left (fst (TFK (R := R) F) A.A).left (fst (TFK (R := R) (Kb R)) A.A).left
      (baseEm em).left := by
  have h₁ : IsPullback (snd (TFK (R := R) (Kb R)) A.A).left (fst (TFK (R := R) (Kb R)) A.A).left
      A.A.hom (TFK (R := R) (Kb R)).hom := (IsPullback.of_hasPullback _ _).flip
  have h₂ : IsPullback (snd (TFK (R := R) F) A.A).left (fst (TFK (R := R) F) A.A).left
      A.A.hom (TFK (R := R) F).hom := (IsPullback.of_hasPullback _ _).flip
  refine IsPullback.of_right ?_ (congrArg (fun q => q.left) (whiskerRight_fst (baseEm em) A.A)) h₁
  have e₁ : (baseEm em ▷ A.A).left ≫ (snd (TFK (R := R) (Kb R)) A.A).left =
      (snd (TFK (R := R) F) A.A).left := congrArg (fun q => q.left) (whiskerRight_snd (baseEm em) A.A)
  have e₂ : (baseEm em).left ≫ (TFK (R := R) (Kb R)).hom = (TFK (R := R) F).hom := Over.w (baseEm em)
  rw [e₁, e₂]
  exact h₂

end

theorem isExtension_secExt : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), letI : Algebra (Kb R) F := em.toRingHom.toAlgebra; GlobalTheory.FieldBaseChange.IsExtension (secExt A em N) := by
  intro R _ _ A F _ _ em N
  letI : Algebra (Kb R) F := em.toRingHom.toAlgebra
  have := noetherianSpace_prod_field A (Kb R)
  exact GlobalTheory.FieldBaseChange.isExtension_pullOver (K := Kb R) (F := F) (isPullback_baseEm_whiskerRight A em) A.isLB _ _

end GlobalTheory.Mum.Desc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

def OrigVal {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {k : ℕ} {α : D.X} (b : D.SecB k α) (v : R) : Prop :=
  ∀ (z : Sp R) (J : (Sp R ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    sval b (unitW D.P.A) z J = stalkOf z v * (val D.rig (idW R) z J).val ^ k

end GlobalTheory.Mum
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

theorem _root_.GlobalTheory.T.weilComparisonGenerator_additive_second_variable : GlobalFnsSt → ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], ∀ (r₁ : LB.Gen (P₁.L.pull (eSec P₁.A))) (hr₁ : r₁.IsGen) (c₁ : CubicalStr P₁.A ⟨P₁.L, r₁, P₁.isLB, hr₁⟩) (r₂ : LB.Gen (P₂.L.pull (eSec P₂.A))) (hr₂ : r₂.IsGen) (c₂ : CubicalStr P₂.A ⟨P₂.L, r₂, P₂.isLB, hr₂⟩) (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u (r ≫ zero2 P₀.A) z J = 1) → ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → (join P₁.L P₂.L).ι), Good (join P₁.L P₂.L) z J → ∀ (x y y' : T ⟶ P₀.A), val u (lift x (y * y')).left z J * cubV c₁ z (rl J) (x ≫ f₁) (y ≫ g₁) (y' ≫ g₁) = cubV c₂ z (rr J) (x ≫ f₂) (y ≫ g₂) (y' ≫ g₂) * (val u (lift x y).left z J * val u (lift x y').left z J) := by
  first | exact @GlobalTheory.Mum.Two.WeilCmp.add_snd | exact GlobalTheory.Mum.Two.WeilCmp.add_snd | (intros; apply GlobalTheory.Mum.Two.WeilCmp.add_snd <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

theorem _root_.GlobalTheory.T.exists_weilComparisonGenerator_normalised_zeroSection : ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], ∀ (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)), u.IsGen → ∃ u' : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u' (r ≫ zero2 P₀.A) z J = 1 := by
  first | exact @GlobalTheory.Mum.Two.WeilCmp.exists_gen_nrm | exact GlobalTheory.Mum.Two.WeilCmp.exists_gen_nrm | (intros; apply GlobalTheory.Mum.Two.WeilCmp.exists_gen_nrm <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum


theorem _root_.GlobalTheory.T.exists_homMumfordGenerator_normalised_origin : ∀ {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] {L₁ : LB H₁.left} {L₂ : LB H₂.left}, (join L₁ L₂).IsLB → ∀ (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b] (t : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε)), t.IsGen → ∃ u : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε), IsNrm u := by
  first | exact @GlobalTheory.HomMum.exists_isNrm | exact GlobalTheory.HomMum.exists_isNrm | (intros; apply GlobalTheory.HomMum.exists_isNrm <;> assumption)

end
end
