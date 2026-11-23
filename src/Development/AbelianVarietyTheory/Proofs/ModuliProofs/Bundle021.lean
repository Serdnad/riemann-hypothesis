module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle010
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace FinitePresFibreFlat

open TensorProduct IsLocalRing FiniteFibreFlat

section Algebra

theorem free_of_flat_reduction {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    [Module.FinitePresentation A M] (p : Ideal R) (hp : p.map (algebraMap R A) ≤ maximalIdeal A)
    [Module.Flat (A ⧸ p.map (algebraMap R A)) ((A ⧸ p.map (algebraMap R A)) ⊗[A] M)] :
    Module.Free A M := by
  set I := p.map (algebraMap R A) with hI
  have hrel : LocalFlat.RelationsLift I M :=
    LocalFlat.relationsLift_of_flat (C := A ⧸ I) Ideal.Quotient.mk_surjective Ideal.mk_ker
      (TensorProduct.mk A (A ⧸ I) M 1) (TensorProduct.mk_surjective A M (A ⧸ I)
        Ideal.Quotient.mk_surjective) (LinearMap.ker_tensorProductMk M)
  apply Module.free_of_maximalIdeal_rTensor_injective
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj, injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hrel (maximalIdeal A) (maximalIdeal A).subtype x (by rw [hx]; simp)
  let e := Submodule.comapSubtypeEquivOfLe hp
  have hy : I.subtype.lTensor M (e.toLinearMap.lTensor M y) = 0 := by
    rw [← hx, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
    rfl
  rw [map_eq_zero_iff _ (lTensor_map_injective p)] at hy
  have : y = 0 := (LinearEquiv.lTensor M e).injective (hy.trans (map_zero _).symm)
  rw [this, map_zero]

theorem flat_of_flat_fibres {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Module.FinitePresentation A B]
    [Module.Flat R B]
    (H : ∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C),
      (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) :
    Module.Flat A B := by
  refine Module.flat_of_isLocalized_maximal A B (fun P _ => Localization.AtPrime P ⊗[A] B)
    (fun P _ => TensorProduct.mk A (Localization.AtPrime P) B 1) fun P _ => ?_
  let A' := Localization.AtPrime P
  let p : Ideal R := (maximalIdeal A').comap (algebraMap R A')
  let I := p.map (algebraMap R A')
  have h1 : Module.Flat R (B ⊗[A] A') := Module.Flat.trans R B (B ⊗[A] A')
  have h2 : Module.Flat R (A' ⊗[A] B) :=
    Module.Flat.of_linearEquiv
      ((Algebra.TensorProduct.comm A A' B).restrictScalars R).toLinearEquiv
  have h3 : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A] B) := by
    let ψ : R →+* A' ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap R A')
    have hψ₁ : p ≤ RingHom.ker ψ := fun r hr =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
    have hψ₂ : p.primeCompl ≤ (IsUnit.submonoid (A' ⧸ I)).comap ψ := by
      intro r hr
      have : IsUnit (algebraMap R A' r) := by
        by_contra h
        exact hr h
      exact this.map (Ideal.Quotient.mk I)
    refine H p.ResidueField (A' ⧸ I) (algebraMap R _) (Ideal.ResidueField.lift p ψ hψ₁ hψ₂) ?_
    ext r
    exact (Ideal.ResidueField.lift_algebraMap p ψ hψ₁ hψ₂ r).symm
  have h4 : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A'] (A' ⊗[A] B)) :=
    Module.Flat.of_linearEquiv
      (AlgebraTensorModule.cancelBaseChange A A' (A' ⧸ I) (A' ⧸ I) B)
  have h5 : Module.Free A' (A' ⊗[A] B) :=
    free_of_flat_reduction p Ideal.map_comap_le
  have h6 : Module.Flat A' (A' ⊗[A] B) := Module.Flat.of_free
  exact Module.Flat.trans A A' (A' ⊗[A] B)

end Algebra

open FibreFlat

set_option backward.isDefEq.respectTransparency false in
theorem flat_of_flatOver_fields {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S)
    (hY : LocallyOfFinitePresentation g) (h0 : LocallyOfFinitePresentation (f ≫ g))
    (h1 : Flat (f ≫ g)) (h2 : IsFinite f)
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) :
    Flat f := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  · refine IsZariskiLocalAtTarget.of_openCover (S.affineCover.pullback₁ g) fun i => ?_
    let u := S.affineCover.f i
    have sq := IsPullback.of_hasPullback f (pullback.fst g u)
    have sq' := IsPullback.of_hasPullback g u
    refine this (pullback.snd f (pullback.fst g u)) (pullback.snd g u)
      inferInstance (MorphismProperty.of_isPullback (sq.paste_vert sq') h0)
      (MorphismProperty.of_isPullback (sq.paste_vert sq') h1) inferInstance
      (fun k _ t => flatOver_of_comp_base (u := u) ?_) ⟨_, rfl⟩
    rw [← pullback.condition]
    exact (H k _).target sq
  obtain ⟨R, rfl⟩ := hS
  wlog hA : ∃ A, Y = Spec A generalizing X Y
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    exact this (pullback.snd f (Y.affineCover.f i)) inferInstance (Y.affineCover.f i ≫ g)
      inferInstance (by rw [e]; infer_instance) (by rw [e]; infer_instance)
      (fun k _ t => (H k t).target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hA
  wlog hX : ∃ B, X = Spec B generalizing X
  · haveI hX' : IsAffine X := isAffine_of_isAffineHom f
    rw [← MorphismProperty.cancel_left_of_respectsIso @Flat X.isoSpec.inv]
    exact this (X.isoSpec.inv ≫ f) inferInstance (by rw [Category.assoc]; infer_instance)
      (by rw [Category.assoc]; infer_instance)
      (fun k _ t => (H k t).source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1 h0
  rw [Flat.SpecMap_iff] at h1 ⊢
  rw [IsFinite.SpecMap_iff] at h2
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hY h0
  letI : Algebra R A := g.hom.toAlgebra
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra R B := (g ≫ f).hom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Flat R B := h1
  haveI : Module.Finite A B := h2
  haveI : Algebra.FinitePresentation R A := hY
  haveI : Algebra.FinitePresentation R B := h0
  haveI : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R A B
  haveI : Module.FinitePresentation A B :=
    Module.FinitePresentation.of_finite_of_finitePresentation A B
  refine flat_of_flat_fibres (R := R) (A := A) (B := B) fun k C _ _ _ t h e => ?_
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)
  have := H k (Spec.map (CommRingCat.ofHom t)) _ _ _ (Spec.map (CommRingCat.ofHom h)) sq.flip
    (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      exact e)
  rw [Flat.SpecMap_iff] at this
  exact RingHom.flat_algebraMap_iff.mp this

end FinitePresFibreFlat

theorem flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres :
    ∀ (S : Scheme.{0}) (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFinitePresentation X.hom → LocallyOfFinitePresentation Y.hom → IsFinite f.left → (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S), Flat ((Over.pullback t).map f).left) → Flat f.left := by
  intro S X Y f h1 h0 h2 h3 H
  refine FinitePresFibreFlat.flat_of_flatOver_fields f.left Y.hom h2 (by rwa [Over.w])
    (by rwa [Over.w]) h3 fun k _ t => ?_
  exact FiniteFibreFlat.flatOver_descend
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
    (FibreFlat.flatOver_of_pullback f _ (H _ _))

end GlobalTheory
end

section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace GlobalTheory.TripleCompare

section Cech

variable {X Y Z : Scheme.{0}}

theorem gen_refine {A B : LB Y} (n : ℤ) (σ : B.ι → A.ι) (hle : ∀ i, B.U i ≤ A.U (σ i))
    (hg : ∀ i j, B.g i j = res (inf_le_inf (hle i) (hle j)) (A.g (σ i) (σ j)) ^ n)
    (h : ∃ t : LB.Gen A, t.IsGen) : ∃ t : LB.Gen B, t.IsGen := by
  obtain ⟨t, ht⟩ := h
  refine ⟨⟨fun i => res (hle i) (t.s (σ i)) ^ n⟩, fun i j => ?_⟩
  have e := congrArg (res (inf_le_inf (hle i) (hle j))) (ht (σ i) (σ j))
  rw [map_mul, DVR.res_res', DVR.res_res'] at e
  rw [hg, map_zpow, map_zpow, DVR.res_res', DVR.res_res', ← mul_zpow]
  exact congrArg (· ^ n) e

theorem div_g_res (M L : LB Y) (p q : M.ι × L.ι) {V : Y.Opens}
    (h : V ≤ (M.U p.1 ⊓ L.U p.2) ⊓ (M.U q.1 ⊓ L.U q.2)) (h₁ : V ≤ M.U p.1 ⊓ M.U q.1)
    (h₂ : V ≤ L.U p.2 ⊓ L.U q.2) :
    res h ((LB.div M L).g p q) = res h₁ (M.g p.1 q.1) * (res h₂ (L.g p.2 q.2))⁻¹ :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (DVR.res_res' _ _ _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (DVR.res_res' _ _ _))))

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem sum_g_res (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (j j' : K' ⊕ K → L.ι) {V : Y.Opens}
    (h : V ≤ LB.wchart L (Sum.elim φ' φ) j ⊓ LB.wchart L (Sum.elim φ' φ) j')
    (h₁ : V ≤ LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ' (j' ∘ Sum.inl))
    (h₂ : V ≤ LB.wchart L φ (j ∘ Sum.inr) ⊓ LB.wchart L φ (j' ∘ Sum.inr)) :
    res h ((LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)).g j j') =
      res h₁ ((LB.LinComb L φ' ε').g (j ∘ Sum.inl) (j' ∘ Sum.inl)) *
        (res h₂ ((LB.LinComb L φ ε).g (j ∘ Sum.inr) (j' ∘ Sum.inr)))⁻¹ := by
  rw [DVR.linComb_g_res, DVR.linComb_g_res, DVR.linComb_g_res, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Function.comp]

theorem wchart_sum (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j : K' ⊕ K → L.ι) :
    LB.wchart L (Sum.elim φ' φ) j =
      LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := by
  refine le_antisymm (fun y hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k),
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩) fun y hy => ?_
  refine Set.mem_iInter.2 fun k => ?_
  rcases k with k | k
  · exact Set.mem_iInter.1 hy.1 k
  · exact Set.mem_iInter.1 hy.2 k

theorem lbIso_iff_gen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    Geo.Tor.LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') ↔
      ∃ t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)), t.IsGen := by
  constructor
  · refine gen_refine (A := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε)) 1
      (fun j => (j ∘ Sum.inl, j ∘ Sum.inr)) (fun j => (wchart_sum φ φ' j).le) fun j j' => ?_
    have a := (wchart_sum φ φ' j).le
    have b := (wchart_sum φ φ' j').le
    refine (DVR.res_refl' _).symm.trans ((sum_g_res φ ε φ' ε' j j' le_rfl
      (inf_le_inf (a.trans inf_le_left) (b.trans inf_le_left))
      (inf_le_inf (a.trans inf_le_right) (b.trans inf_le_right))).trans (Eq.symm ?_))
    exact (zpow_one _).trans (div_g_res (LB.LinComb L φ' ε') (LB.LinComb L φ ε) _ _ _ _ _)
  · refine gen_refine (B := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε)) 1
      (fun p => Sum.elim p.1 p.2) (fun p => (wchart_sum φ φ' (Sum.elim p.1 p.2)).ge) fun p q => ?_
    refine (DVR.res_refl' _).symm.trans ((div_g_res (LB.LinComb L φ' ε') (LB.LinComb L φ ε) p q le_rfl
      (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_right inf_le_right)).trans (Eq.symm ?_))
    exact (zpow_one _).trans (sum_g_res φ ε φ' ε' (Sum.elim p.1 p.2) (Sum.elim q.1 q.2) _ _ _)

theorem wchart_id (L : LB X) (j : PUnit.{1} → L.ι) :
    LB.wchart L (fun _ : PUnit.{1} => 𝟙 X) j = L.U (j ⟨⟩) :=
  le_antisymm (fun _ hy => Set.mem_iInter.1 hy PUnit.unit) fun _ hy => Set.mem_iInter.2 fun _ => hy

theorem pull_id_g_res (L : LB X) (j j' : PUnit.{1} → L.ι) {V : X.Opens}
    (h : V ≤ LB.wchart L (fun _ : PUnit.{1} => 𝟙 X) j ⊓ LB.wchart L (fun _ : PUnit.{1} => 𝟙 X) j')
    (h' : V ≤ L.U (j ⟨⟩) ⊓ L.U (j' ⟨⟩)) :
    res h ((L.pull (𝟙 X)).g j j') = res h' (L.g (j ⟨⟩) (j' ⟨⟩)) := by
  rw [DVR.linComb_g_res, Fintype.prod_unique, zpow_one, DVR.tr_def L (ψ := 𝟙 X) h']
  exact DVR.pullU_of_eq_id _ rfl _ _ _ _ _

theorem lbIso_iff_pull_id (L M : LB X) :
    Geo.Tor.LBIso L M ↔ Geo.Tor.LBIso M (L.pull (𝟙 X)) := by
  constructor
  · refine gen_refine (A := LB.div M L) (B := LB.div (L.pull (𝟙 X)) M) (-1)
      (fun p => (p.2, p.1 ⟨⟩))
      (fun p => le_inf inf_le_right (inf_le_left.trans (wchart_id L p.1).le)) fun p q => ?_
    have a := (wchart_id L p.1).le
    have b := (wchart_id L q.1).le
    refine (DVR.res_refl' _).symm.trans ((div_g_res (L.pull (𝟙 X)) M p q le_rfl
      (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_right inf_le_right)).trans (Eq.symm ?_))
    refine (zpow_neg_one _).trans ((congrArg (·⁻¹) (div_g_res M L (p.2, p.1 ⟨⟩) (q.2, q.1 ⟨⟩) _
      (inf_le_inf inf_le_right inf_le_right)
      (inf_le_inf (inf_le_left.trans a) (inf_le_left.trans b)))).trans ?_)
    refine (mul_inv_rev _ _).trans (congrArg₂ (· * ·) ((inv_inv _).trans ?_) rfl)
    exact (pull_id_g_res L p.1 q.1 _ _).symm
  · refine gen_refine (B := LB.div M L) (A := LB.div (L.pull (𝟙 X)) M) (-1)
      (fun p => (fun _ => p.2, p.1))
      (fun p => le_inf (inf_le_right.trans (wchart_id L fun _ => p.2).ge) inf_le_left) fun p q => ?_
    have a := (wchart_id L fun _ => p.2).ge
    have b := (wchart_id L fun _ => q.2).ge
    refine (DVR.res_refl' _).symm.trans ((div_g_res M L p q le_rfl
      (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_right inf_le_right)).trans (Eq.symm ?_))
    refine (zpow_neg_one _).trans ((congrArg (·⁻¹) (div_g_res (L.pull (𝟙 X)) M (fun _ => p.2, p.1)
      (fun _ => q.2, q.1) _ (inf_le_inf (inf_le_right.trans a) (inf_le_right.trans b))
      (inf_le_inf inf_le_left inf_le_left))).trans ?_)
    refine (mul_inv_rev _ _).trans (congrArg₂ (· * ·) (inv_inv _) (congrArg (·⁻¹) ?_))
    exact pull_id_g_res L (fun _ => p.2) (fun _ => q.2) _ _

end Cech

section Clauses

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

end Clauses

section Triples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E}
  {S S' : Scheme.{0}}

end Triples

end GlobalTheory.TripleCompare
end
end
