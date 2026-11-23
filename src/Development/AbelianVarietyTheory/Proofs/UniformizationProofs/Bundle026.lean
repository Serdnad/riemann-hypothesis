module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FormallyUnramifiedMulN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.UT.OLinEnd

variable {R : Type} [CommRing R] [IsDomain R]

theorem prod_Oφ (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (D.Oφ p χ i) ^ Oε i =
      h (cP D T χ * p).left * (h (cP D T χ).left)⁻¹ * (h p.left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  rw [Fin.prod_univ_four, _root_.mul_comm (cP D T χ) p]
  show h (p * cP D _ χ).left ^ (1 : ℤ) * h (cP D _ χ).left ^ (-1 : ℤ) * h p.left ^ (-1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem prod_Oφ_inv (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type}
    [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (D.Oφ p χ i) ^ Oinvε i =
      (h (cP D T χ * p).left)⁻¹ * h (cP D T χ).left * h p.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four, _root_.mul_comm (cP D T χ) p]
  show h (p * cP D _ χ).left ^ (-1 : ℤ) * h (cP D _ χ).left ^ (1 : ℤ) * h p.left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem exists_u (hG : GlobalFnsSt) (D : DegPre R) {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O)
    (a : O) (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) (hu : u.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) (χ : D.X) :
    ∃ v : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) (star a • χ)) (D.Oφ (oa.onB.act a) χ)) (Sum.elim Oε Oinvε)),
      Normd v ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
        Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) (star a • χ)) (D.Oφ (oa.onB.act a) χ)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (prod_ros _ _ (cP D _ χ) (𝟙 D.P.A) h).trans (Eq.symm ?_)
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_Oφ D (𝟙 _) (star a • χ) h)
        (prod_Oφ_inv D (oa.onB.act a) χ h)).trans ?_
      rw [cf, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.pullGen D.P.L _ _ u (lift (cP D D.P.A χ) (𝟙 D.P.A)).left) (pullGen_isGen _ _ _ _ hu _)
  have key : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
      Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := fun T x Z r z J hJ => by
    rw [vv Z _ z J hJ, val_pull hJ, Category.assoc, ← Over.comp_left, comp_lift, comp_cP, Category.comp_id]
  refine ⟨v, ⟨hv, corr_of_val D.P.isLB fun y J hJ => ?_⟩, key⟩
  have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) hJ 1 1 (cP D _ χ)).2
  rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J (cP D _ χ) 1 = 1 := mul_eq_left.1 e.symm
  have k := key (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 _ (𝟙 _) y J hJ
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  rw [o] at k
  refine (val_pull hJ _ _ _).trans (k.trans (Eq.trans ?_ (val_one _).symm))
  rw [Category.id_comp]
  exact e'

theorem ros_unique (hG : GlobalFnsSt) (D : DegPre R) {f g : D.P.A ⟶ D.P.A}
    {u u' : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L))
    (u₀' : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u' (zero2 D.P.A)) (LB.oneGen D.P.L))
    (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ D.P.A).left) (z : Z) (J) (hJ : Good D.P.L z J) :
    val u' r z J = val u r z J := by
  have z2 : zero2 D.P.A ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D.P.A] η[D.P.A])
  exact gen_unique D.P.isLB _ (zero2 D.P.A) z2 (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2) hu' hu
    (fun y I hI => by
      have a₁ := val_corr hI u₀' (𝟙 _)
      have a₂ := val_corr hI u₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a₁ a₂
      exact a₁.trans a₂.symm) _ _ z J hJ

theorem main : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → ∀ a : O, ∃ E : EndU U.toUnifPre, E.aG = ιG.act a ∧ E.aA = ιA.act a ∧ E.aB = ιD.onB.act a ∧ (∀ χ, E.h χ = star a • χ) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (g g' : GtPtF D.toPre F), E.Act g g' ↔ GtAct ιD a g g' := by
  intro hL R _ _ _ I _ D A G _ _ _ U O _ _ _ ιD ιA ιG hO a
  have hG := hL.1.globalFns
  have := ιD.onB.hom a
  have := ιD.onB.hom (star a)
  have hr := ιD.onB.rosati (star a)
  rw [star_star] at hr
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hr
  choose v hv vv using exists_u hG D.toPre ιD a u hu u₀
  refine ⟨{ aG := ιG.act a, aA := ιA.act a, aB := ιD.onB.act a, homG := ιG.hom a, homA := ιA.hom a,
            homB := ιD.onB.hom a, h := DistribSMul.toAddMonoidHom D.toPre.X (star a), ext := hO.ext a,
            q_lin := fun e => hO.q_lin e a, i_lin := fun e => hO.i_lin e a, u := v, u_norm := hv,
            t_lin := fun e χ Z x z J hJ => ?_ }, rfl, rfl, rfl, fun _ => rfl, fun F _ _ g g' => ?_⟩
  · have e₁ := val_corr hJ (hL.2.2.2.1.tLin R I O D A G U.toUnifPre ιD ιA ιG hO e a u hu u₀ χ) x
    refine ((val_pull hJ _ _ _).symm.trans e₁.symm).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))
    exact (val_pull hJ _ _ _).trans (vv χ _ (U.gt e).pG Z x z J hJ).symm
  · have k : ∀ χ z J, Good D.toPre.P.L z J →
        val (v χ) g.b.left z J = val u (𝟙 _ ≫ (lift (cP D.toPre _ χ) g.b).left) z J := fun χ z J hJ =>
      (congrArg (fun q => val (v χ) q z J) (Category.id_comp g.b.left).symm).trans (vv χ _ g.b _ (𝟙 _) z J hJ)
    refine and_congr Iff.rfl ⟨fun H u' hu' u₀' χ => corr_of_val D.toPre.P.isLB fun z J hJ => ?_, fun H χ z J hJ => ?_⟩
    · refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) rfl ?_) (H χ z J hJ).symm)
      exact (val_pull hJ _ _ _).trans ((ros_unique hG D.toPre hu hu' u₀ u₀' _ _ z J hJ).trans (k χ z J hJ).symm)
    · refine (val_corr hJ (H u hu u₀ χ) (𝟙 _)).symm.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))
      exact (val_pull hJ _ _ _).trans (k χ z J hJ).symm

end GlobalTheory.UT.OLinEnd

end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionSeparable

theorem exists_intermediateField {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) [FormallyUnramified p] [LocallyOfFiniteType p]
    (a : Spec (CommRingCat.of Ω) ⟶ X)
    (ha : a ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ b : Spec (CommRingCat.of K) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ b = a := by
  first
  | (rename_i h_2 h_3 h_4 h_7 h_8; revert k Ω h_2 h_3 h_4 X p h_7 h_8 a ha; exact @_root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point)
  | exact @_root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point
  | exact _root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point
  | (apply _root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point ..)

theorem exists_intermediateField_of_pow_eq_one {V : Type} [CommRing V]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] [LocallyOfFiniteType G.hom]
    {N : ℕ} (hN : IsUnit (N : V)) {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (r : V →+* k)
    (f : V →+* Ω) (hf : (algebraMap k Ω).comp r = f)
    (x : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ G) (hx : x ^ N = 1) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ b : Spec (CommRingCat.of K) ⟶ G.left,
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ b = x.left := by
  have hN' : IsUnit (N : Γ(Spec (CommRingCat.of V), ⊤)) := by
    simpa using hN.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  have h₁ := formallyUnramified_mulN _ G N hN'
  have h₂ : LocallyOfFiniteType (mulN G N).left := by
    have : LocallyOfFiniteType ((mulN G N).left ≫ G.hom) := by rw [Over.w]; infer_instance
    exact locallyOfFiniteType_of_comp _ G.hom
  let T : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom r))
  let e : Spec (CommRingCat.of k) ⟶ G.left := (1 : T ⟶ G).left
  let j : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ T :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (by
      subst hf
      exact (Spec.map_comp _ _).symm)
  have hw : x.left ≫ (mulN G N).left = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ≫ e := by
    change (x ≫ mulN G N).left = (j ≫ (1 : T ⟶ G)).left
    rw [MulUnramified.comp_mulN, hx, comp_one]
  have : FormallyUnramified (pullback.snd (mulN G N).left e) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @FormallyUnramified)
      (IsPullback.of_hasPullback _ _) h₁
  obtain ⟨K, hK, hK', b, hb⟩ := exists_intermediateField (pullback.snd (mulN G N).left e)
    (pullback.lift x.left _ hw) (pullback.lift_snd _ _ _)
  exact ⟨K, hK, hK', b ≫ pullback.fst _ _, by rw [reassoc_of% hb, pullback.lift_fst]⟩

theorem epi_specMap {K L : Type} [Field K] [Field L] (σ : K →+* L) :
    Epi (Spec.map (CommRingCat.ofHom σ)) := by
  have : Flat (Spec.map (CommRingCat.ofHom σ)) := inferInstance
  have : Surjective (Spec.map (CommRingCat.ofHom σ)) :=
    ⟨fun u => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

end GlobalTheory.TorsionSeparable

namespace GlobalTheory

open TorsionSeparable IsLocalRing

theorem exists_finite_extension_torsion_lift : UnramExtSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (N : ℕ), IsUnit (N : V) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (f : V →+* Ω), IsLocalHom f → ∀ s : Finset (Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ G), (∀ x ∈ s, x ^ N = 1) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : Algebra V W) (f' : W →+* Ω), Module.Finite V W ∧ Function.Injective (algebraMap V W) ∧ IsLocalHom (algebraMap V W) ∧ IsLocalHom f' ∧ f'.comp (algebraMap V W) = f ∧ ∀ x ∈ s, ∃ y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, y ^ N = 1 ∧ Spec.map (CommRingCat.ofHom f') ≫ y.left = x.left := by
  intro hU V _ _ _ _ G _ _ _ N hN Ω _ _ f hf s hs
  let : Algebra (ResidueField V) Ω := (ResidueField.lift f).toAlgebra
  have hr : (algebraMap (ResidueField V) Ω).comp (residue V) = f := ResidueField.lift_comp_residue f
  choose K hK hK' b hb using fun x : s =>
    exists_intermediateField_of_pow_eq_one G hN (residue V) f hr x.1 (hs x.1 x.2)
  let L : IntermediateField (ResidueField V) Ω := ⨆ x, K x
  have : FiniteDimensional (ResidueField V) L := inferInstance
  have : Algebra.IsSeparable (ResidueField V) L := inferInstance
  obtain ⟨W, _, _, _, _, _, hfin, hinj, hloc, -, e, he⟩ := hU V L
  let σ : ResidueField W →+* Ω := (algebraMap L Ω).comp e.toRingHom
  have hcomp : (σ.comp (residue W)).comp (algebraMap V W) = f := by
    ext v
    change algebraMap L Ω (e (residue W (algebraMap V W v))) = f v
    rw [he, ← IsScalarTower.algebraMap_apply, ← hr]
    rfl
  have hσ : IsLocalHom (σ.comp (residue W)) := ⟨fun a ha => by
    by_contra hn
    exact ha.ne_zero (by rw [RingHom.comp_apply, (residue_eq_zero_iff a).2 hn, map_zero])⟩
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    σ.comp (residue W), hfin, hinj, hloc, hσ, hcomp, fun x hx => ?_⟩
  have := epi_specMap σ
  let c : Spec (CommRingCat.of (ResidueField W)) ⟶ G.left :=
    Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp
      (IntermediateField.inclusion (le_iSup K ⟨x, hx⟩)).toRingHom)) ≫ b ⟨x, hx⟩
  have hc : Spec.map (CommRingCat.ofHom σ) ≫ c = x.left := by
    rw [← hb ⟨x, hx⟩, ← Spec.map_comp_assoc]
    congr 2
    ext t
    simp [σ]
  have hp : Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom (residue W)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap V W)) = Spec.map (CommRingCat.ofHom f) := by
    rw [← hcomp, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  let T : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom (residue W)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap V W)))
  let x₀ : T ⟶ G := Over.homMk c (by
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom σ))]
    exact ((reassoc_of% hc) _).trans ((Over.w x).trans hp.symm))
  let j : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ T :=
    Over.homMk (Spec.map (CommRingCat.ofHom σ)) hp
  have hj : j ≫ x₀ = x := Over.OverMorphism.ext hc
  have : Epi j.left := epi_specMap σ
  have : Epi j := Over.epi_of_epi_left j
  have hx₀ : x₀ ^ N = 1 := by
    rw [← cancel_epi j, comp_pow, hj, hs x hx, comp_one]
  obtain ⟨y, ⟨hy, hy'⟩, -⟩ := existsUnique_torsion_lift W _ G
    (Spec.map (CommRingCat.ofHom (algebraMap V W))) N
    (by simpa using hN.map (algebraMap V W)) x₀ hx₀
  refine ⟨y, hy, ?_⟩
  rw [← hc, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hy']
  rfl

end GlobalTheory
end
