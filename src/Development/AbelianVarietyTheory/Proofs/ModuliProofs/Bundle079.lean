module

public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsExtensionAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

namespace FieldDescentGen

variable {X₀ X : Scheme.{0}}

theorem pull_le (M : LB X₀) (φ : X ⟶ X₀) (j : PUnit → M.ι) : (M.pull φ).U j ≤ φ ⁻¹ᵁ M.U (j PUnit.unit) :=
  fun _ hy => mem_pull.1 hy

def secPull (M : LB X₀) (φ : X ⟶ X₀) (s : M.Sec) : (M.pull φ).Sec where
  f j := (φ.appLE _ _ (pull_le M φ j)).hom (s.f (j PUnit.unit))
  compat i j := by
    have h : (M.pull φ).U i ⊓ (M.pull φ).U j ≤ φ ⁻¹ᵁ (M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)) :=
      fun _ hy => ⟨pull_le M φ i hy.1, pull_le M φ j hy.2⟩
    have e := congrArg (φ.appLE _ _ h).hom (s.compat (i PUnit.unit) (j PUnit.unit))
    rw [map_mul] at e
    have g : ((M.pull φ).g i j : Γ(X, (M.pull φ).U i ⊓ (M.pull φ).U j)) =
        (φ.appLE _ _ h).hom (M.g (i PUnit.unit) (j PUnit.unit)) := by
      have gu : (M.pull φ).g i j = res h (pullU φ _ (M.g (i PUnit.unit) (j PUnit.unit))) :=
        (Fintype.prod_unique fun k : PUnit => (res h (pullU φ _ (M.g (i k) (j k)))) ^ (1 : ℤ)).trans (zpow_one _)
      exact congrArg Units.val gu
    rw [g]
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE] at e ⊢
    exact e

theorem exists_ratio {L : LB X} (hL : L.IsLB) (t : L.Gen) (ht : t.IsGen) (s : L.Sec) :
    ∃ u : Γ(X, ⊤), ∀ j, s.f j =
      (X.presheaf.map (homOfLE (le_top : L.U j ≤ ⊤)).op).hom u * (t.s j).val := by
  obtain ⟨u, hu⟩ := Out.TLinPf.glue L.U hL.cover (fun j => s.f j * ((t.s j)⁻¹).val) (fun i j => by
    have e : res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (t.s j)⁻¹ =
        L.g i j * res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (t.s i)⁻¹ := by
      rw [map_inv, map_inv, ht i j, mul_inv, mul_inv_cancel_left]
    have e' : (X.presheaf.map (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op).hom ((t.s j)⁻¹).val =
        (L.g i j).val * (X.presheaf.map (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op).hom ((t.s i)⁻¹).val :=
      congrArg Units.val e
    rw [map_mul, map_mul, s.compat i j, e']
    ring)
  exact ⟨u, fun j => by rw [hu j, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]⟩

theorem isUnit_of_surjective (φ : X ⟶ X₀) [Surjective φ] {U : X₀.Opens} {V : X.Opens} (h : V ≤ φ ⁻¹ᵁ U)
    (h' : φ ⁻¹ᵁ U ≤ V) (a : Γ(X₀, U)) (ha : IsUnit ((φ.appLE U V h).hom a)) : IsUnit a := by
  refine RingedSpace.isUnit_of_isUnit_germ X₀.toLocallyRingedSpace.toRingedSpace U a fun x hx => ?_
  obtain ⟨y, rfl⟩ := φ.surjective x
  have hy : y ∈ X.basicOpen ((φ.appLE U V h).hom a) := by
    rw [X.basicOpen_of_isUnit ha]; exact h' hx
  rw [Scheme.basicOpen_appLE] at hy
  exact (X₀.mem_basicOpen a _ hx).1 hy.2

def chartDiv (M N : LB X₀) (φ : X ⟶ X₀) :
    ChartPull ((LB.div N M).pull φ) (LB.div (N.pull φ) (M.pull φ)) (𝟙 X) where
  idx J := (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
  le J y hy := ⟨mem_pull.2 (mem_pull.1 hy).1, mem_pull.2 (mem_pull.1 hy).2⟩
  g y J J' hj hj' := by
    have a := mem_pull.1 hj
    have a' := mem_pull.1 hj'
    refine (gm_pull_g (LB.div N M) φ (𝟙 X) y J J' hj hj').trans
      ((gm_div M N (𝟙 X ≫ φ) y (J PUnit.unit) (J' PUnit.unit) ⟨a, a'⟩).trans (Eq.symm ?_))
    refine (gm_div (M.pull φ) (N.pull φ) (𝟙 X) y (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2)
      ⟨⟨mem_pull.2 a.1, mem_pull.2 a.2⟩, mem_pull.2 a'.1, mem_pull.2 a'.2⟩).trans ?_
    exact congrArg₂ (fun u v => u * v⁻¹)
      (gm_pull_g N φ (𝟙 X) y _ _ (mem_pull.2 a.1) (mem_pull.2 a'.1))
      (gm_pull_g M φ (𝟙 X) y _ _ (mem_pull.2 a.2) (mem_pull.2 a'.2))

theorem exists_gen {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K)
    (φ : X ⟶ X₀) [Smooth p₀] [IsProper p₀] [GeometricallyConnected p₀] (H : IsPullback φ p p₀ (spMap i))
    (M : LB X₀) (hM : M.IsLB) (t : (M.pull φ).Gen) (ht : t.IsGen) : ∃ t : M.Gen, t.IsGen := by
  have hb : Function.Bijective p.appTop.hom := GlobalTheory.bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected K X p
    (MorphismProperty.of_isPullback (P := @Smooth) H inferInstance)
    (MorphismProperty.of_isPullback (P := @IsProper) H inferInstance)
    (MorphismProperty.of_isPullback (P := @GeometricallyConnected) H inferInstance)
  have hF : IsField Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.trans
      (RingEquiv.ofBijective p.appTop.hom hb)).symm.toMulEquiv.isField (Field.toIsField K)
  have : Surjective φ := ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₀ K i).1 X₀ X p₀ p φ H).2.2.1
  have hP := LB.isLB_pull hM φ
  let ts : (M.pull φ).Sec := ⟨fun j => (t.s j).val, fun a b => congrArg Units.val (ht a b)⟩
  obtain ⟨n, c, s, hs⟩ := GlobalTheory.SectionsDescent.main K₀ K i X₀ X p₀ p φ M hM H ts
  choose u hu using fun a => exists_ratio hP t ht (secPull M φ (s a))
  have hne : ∃ a, u a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := hF.nontrivial
    refine one_ne_zero (Out.TLinPf.eq_local (M.pull φ).U hP.cover 1 0 fun j => ?_)
    have h0 : (t.s j).val = 0 := by
      refine (hs j (pull_le M φ j)).trans (Finset.sum_eq_zero fun a _ => ?_)
      have e : (φ.appLE _ _ (pull_le M φ j)).hom ((s a).f (j PUnit.unit)) = _ := hu a j
      rw [e, hcon a, map_zero, zero_mul, mul_zero]
    rw [map_one, map_zero, ← (t.s j).mul_inv, h0, zero_mul]
  obtain ⟨a, ha⟩ := hne
  obtain ⟨v, hv⟩ := hF.mul_inv_cancel ha
  have hua : IsUnit (u a) := IsUnit.of_mul_eq_one v hv
  have hunit : ∀ k, IsUnit ((s a).f k) := fun k =>
    isUnit_of_surjective φ (pull_le M φ fun _ => k) (fun _ hy => mem_pull.2 hy) _ (by
      have e : (φ.appLE _ _ (pull_le M φ fun _ => k)).hom ((s a).f k) = _ := hu a fun _ => k
      rw [e]
      exact (hua.map _).mul (Units.isUnit _))
  exact ⟨⟨fun k => (hunit k).unit⟩, fun k l => Units.ext ((s a).compat k l)⟩

end FieldDescentGen


open FieldDescentGen in
theorem lb_gen_iso_descend_field : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀), Smooth p₀ → IsProper p₀ → GeometricallyConnected p₀ → IsPullback φ p p₀ (spMap i) → (∀ M : LB X₀, M.IsLB → (∃ t : (M.pull φ).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen) ∧ ∀ M N : LB X₀, M.IsLB → N.IsLB → LBIso (M.pull φ) (N.pull φ) → LBIso M N := by
  intro K₀ K _ _ i X₀ X p₀ p φ h₁ h₂ h₃ H
  refine ⟨fun M hM ⟨t, ht⟩ => exists_gen i p₀ p φ H M hM t ht, fun M N hM hN ⟨w, hw⟩ => ?_⟩
  exact exists_gen i p₀ p φ H (LB.div N M) (LB.isLB_div hN hM) _
    (GtBaseChange.genPull_isGen (chartDiv M N φ) hw)

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FibreGrp

theorem hom_ext_of_fibres {S : Scheme.{0}} [IsReduced S] {Sg : Set S} (hSg : Dense Sg) {X Y : Over S}
    [Smooth X.hom] [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ p ∈ Sg, ∃ (U : Scheme.{0}) (j : U ⟶ S), p ∈ Set.range j ∧
      ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  have : IsReduced X.left := GlobalTheory.isReduced_of_smooth_of_isReduced X.hom
  choose U j hj hfg using h
  let incl : (∐ fun q : Sg => pullback X.hom (j q.1 q.2)) ⟶ X.left :=
    Sigma.desc fun q : Sg => pullback.fst X.hom (j q.1 q.2)
  have hincl : ∀ q : Sg, Sigma.ι (fun q : Sg => pullback X.hom (j q.1 q.2)) q ≫ incl =
      pullback.fst X.hom (j q.1 q.2) := fun q => Sigma.ι_desc _ q
  have hdense : Dense (X.hom ⁻¹' Sg) := hSg.preimage X.hom.isOpenMap
  have : IsDominant incl := by
    refine ⟨Dense.mono ?_ hdense⟩
    intro x hx
    have hx' : x ∈ Set.range (pullback.fst X.hom (j _ hx)) := by
      rw [Scheme.Pullback.range_fst]
      exact hj _ hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨Sigma.ι (fun q : Sg => pullback X.hom (j q.1 q.2)) ⟨_, hx⟩ y, ?_⟩
    rw [← Scheme.Hom.comp_apply, hincl]
    exact hy
  apply Over.OverMorphism.ext
  refine ext_of_isDominant_of_isSeparated Y.hom (by rw [Over.w f, Over.w g]) incl ?_
  refine Sigma.hom_ext _ _ fun q => ?_
  rw [← Category.assoc, hincl, ← Category.assoc, hincl]
  have key := hfg q.1 q.2 (Over.mk (pullback.snd X.hom (j q.1 q.2)))
    (Over.homMk (pullback.fst X.hom (j q.1 q.2)) (by simp only [Over.mk_hom]; exact pullback.condition))
  exact congrArg CommaMorphism.left key

private theorem smooth_tensor_hom {S : Scheme.{0}} (P Q : Over S) [Smooth P.hom] [Smooth Q.hom] :
    Smooth (P ⊗ Q).hom := by
  change Smooth (pullback.fst P.hom Q.hom ≫ P.hom)
  infer_instance

private theorem smooth_tensorUnit_hom (S : Scheme.{0}) : Smooth (𝟙_ (Over S)).hom := by
  change Smooth (𝟙 S)
  infer_instance

private theorem eq_of_points_lemma_3 {R : Type} [CommRing R] [IsReduced R] {Z : Over (Sp R)} [IsSeparated Z.hom]
    {m : Z ⊗ Z ⟶ Z} {i : Z ⟶ Z} {e : 𝟙_ (Over (Sp R)) ⟶ Z} {Sg : Set (Sp R)} (hSg : Dense Sg)
    (hfib : ∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (A : Over (Sp K)) (_ : GrpObj A) (φ : A.left ⟶ Z.left), p ∈ Set.range x ∧ IsCommMonObj A ∧ IsPullback φ A.hom Z.hom x ∧ (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) ∧ φ ≫ i.left = (ι[A]).left ≫ φ ∧ x ≫ e.left = (η[A]).left ≫ φ)
    {P : Over (Sp R)} [Smooth P.hom] {u v : P ⟶ Z}
    (H : ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp R) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
      (φ : A.left ⟶ Z.left), IsPullback φ A.hom Z.hom x →
      (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) →
      φ ≫ i.left = (ι[A]).left ≫ φ → x ≫ e.left = (η[A]).left ≫ φ →
      ∀ (T : Over (Sp K)) (t : Over.mk (T.hom ≫ x) ⟶ P), t ≫ u = t ≫ v) : u = v := by
  refine hom_ext_of_fibres hSg fun p hp => ?_
  obtain ⟨K, _, x, A, _, φ, hx, hc, pb, hm, hi, he⟩ := hfib p hp
  exact ⟨Sp K, x, hx, H K x A φ pb hm hi he⟩

end GlobalTheory.FibreGrp

namespace GlobalTheory

open GrpDense FibreGrp

theorem grpObj_of_dense_fibres :
    ∀ (R : Type) [CommRing R] [IsReduced R] (Z : Over (Sp R)) (m : Z ⊗ Z ⟶ Z) (i : Z ⟶ Z) (e : 𝟙_ (Over (Sp R)) ⟶ Z) (Sg : Set (Sp R)), Dense Sg → Smooth Z.hom → IsProper Z.hom → GeometricallyConnected Z.hom → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (A : Over (Sp K)) (_ : GrpObj A) (φ : A.left ⟶ Z.left), p ∈ Set.range x ∧ IsCommMonObj A ∧ IsPullback φ A.hom Z.hom x ∧ (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) ∧ φ ≫ i.left = (ι[A]).left ≫ φ ∧ x ≫ e.left = (η[A]).left ≫ φ) → ∃ _ : GrpObj Z, μ[Z] = m ∧ η[Z] = e ∧ ι[Z] = i ∧ IsAbelianScheme Z ∧ ∀ (S' : Scheme.{0}) (x : S' ⟶ Sp R) (A : Over S') [GrpObj A] (φ : A.left ⟶ Z.left), IsPullback φ A.hom Z.hom x → (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) → IsGrpPullback A Z x φ := by
  intro R _ _ Z m i e Sg hSg hsm hpr hgc hfib
  have : Smooth Z.hom := hsm
  have : IsProper Z.hom := hpr
  have : Smooth (𝟙_ (Over (Sp R))).hom := smooth_tensorUnit_hom (Sp R)
  have : Smooth (Z ⊗ Z).hom := smooth_tensor_hom Z Z
  have : Smooth (𝟙_ (Over (Sp R)) ⊗ Z).hom := smooth_tensor_hom _ _
  have : Smooth (Z ⊗ 𝟙_ (Over (Sp R))).hom := smooth_tensor_hom _ _
  have : Smooth ((Z ⊗ Z) ⊗ Z).hom := smooth_tensor_hom _ _
  have one_mul' : e ▷ Z ≫ m = (λ_ Z).hom := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨c, hc⟩ := GrpDense.pushPt_surjective pb T (t ≫ snd (𝟙_ (Over (Sp R))) Z)
    rw [← lift_comp_fst_snd t, toUnit_unique (t ≫ fst (𝟙_ (Over (Sp R))) Z) (toUnit _),
      lift_whiskerRight_assoc, lift_leftUnitor_hom, ← hc, GrpDense.pushPt_one pb.w he T,
      GrpDense.pushPt_mul pb.w hm, _root_.one_mul]
  have mul_one' : Z ◁ e ≫ m = (ρ_ Z).hom := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨c, hc⟩ := GrpDense.pushPt_surjective pb T (t ≫ fst Z (𝟙_ (Over (Sp R))))
    rw [← lift_comp_fst_snd t, toUnit_unique (t ≫ snd Z (𝟙_ (Over (Sp R)))) (toUnit _),
      lift_whiskerLeft_assoc, lift_rightUnitor_hom, ← hc, GrpDense.pushPt_one pb.w he T,
      GrpDense.pushPt_mul pb.w hm, _root_.mul_one]
  have mul_assoc' : m ▷ Z ≫ m = (α_ Z Z Z).hom ≫ Z ◁ m ≫ m := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨a, ha⟩ := GrpDense.pushPt_surjective pb T (t ≫ fst (Z ⊗ Z) Z ≫ fst Z Z)
    obtain ⟨b, hb⟩ := GrpDense.pushPt_surjective pb T (t ≫ fst (Z ⊗ Z) Z ≫ snd Z Z)
    obtain ⟨c, hc⟩ := GrpDense.pushPt_surjective pb T (t ≫ snd (Z ⊗ Z) Z)
    have ht : t = lift (lift (pushPt pb.w a) (pushPt pb.w b)) (pushPt pb.w c) := by
      rw [ha, hb, hc]
      simp only [← Category.assoc, lift_comp_fst_snd]
    rw [ht]
    simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc,
      GrpDense.pushPt_mul pb.w hm, _root_.mul_assoc]
  have left_inv' : lift i (𝟙 Z) ≫ m = toUnit Z ≫ e := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨c, rfl⟩ := GrpDense.pushPt_surjective pb T t
    rw [comp_lift_assoc, Category.comp_id, GrpDense.pushPt_inv pb.w hi, GrpDense.pushPt_mul pb.w hm,
      ← Category.assoc (pushPt pb.w c) (toUnit Z) e, toUnit_unique (pushPt pb.w c ≫ toUnit Z) (toUnit _),
      GrpDense.pushPt_one pb.w he T, _root_.inv_mul_cancel]
  have right_inv' : lift (𝟙 Z) i ≫ m = toUnit Z ≫ e := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨c, rfl⟩ := GrpDense.pushPt_surjective pb T t
    rw [comp_lift_assoc, Category.comp_id, GrpDense.pushPt_inv pb.w hi, GrpDense.pushPt_mul pb.w hm,
      ← Category.assoc (pushPt pb.w c) (toUnit Z) e, toUnit_unique (pushPt pb.w c ≫ toUnit Z) (toUnit _),
      GrpDense.pushPt_one pb.w he T, _root_.mul_inv_cancel]
  have comm' : (β_ Z Z).hom ≫ m = m := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨a, ha⟩ := GrpDense.pushPt_surjective pb T (t ≫ fst Z Z)
    obtain ⟨b, hb⟩ := GrpDense.pushPt_surjective pb T (t ≫ snd Z Z)
    have ht : t = lift (pushPt pb.w a) (pushPt pb.w b) := by rw [ha, hb, lift_comp_fst_snd]
    rw [ht, lift_braiding_hom_assoc, GrpDense.pushPt_mul pb.w hm, GrpDense.pushPt_mul pb.w hm, _root_.mul_comm]
  let G : GrpObj Z :=
    { one := e, mul := m, one_mul := one_mul', mul_one := mul_one', mul_assoc := mul_assoc',
      inv := i, left_inv := left_inv', right_inv := right_inv' }
  refine ⟨G, rfl, rfl, rfl, ?_, ?_⟩
  · exact { comm := ⟨comm'⟩, smooth := hsm, proper := hpr, geomConnected := hgc }
  · intro S' x A _ φ pb hm'
    refine ⟨pb, fun T a b a₀ b₀ ha hb => ?_⟩
    have ea : a₀ = pushPt pb.w a := Over.OverMorphism.ext ha
    have eb : b₀ = pushPt pb.w b := Over.OverMorphism.ext hb
    subst ea eb
    exact congrArg CommaMorphism.left (GrpDense.pushPt_mul pb.w hm' a b)

end GlobalTheory
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

private theorem surjective_comp_isIso_of_surjective {A B C : CommRingCat} (a : A ⟶ B) (b : B ⟶ C) [IsIso b]
    (ha : Function.Surjective a.hom) : Function.Surjective (a ≫ b).hom := by
  intro y
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso b).2 y
  obtain ⟨w, rfl⟩ := ha z
  exact ⟨w, rfl⟩

theorem surjective_appTop_pullback_snd_of_app {X S : Scheme.{0}} (f : X ⟶ S) (V : S.Opens)
    (h : ∀ U : S.Opens, Function.Surjective (f.app U).hom) :
    Function.Surjective (pullback.snd f V.ι).appTop.hom := by
  have hr : Function.Surjective (f ∣_ V).appTop.hom := by
    rw [morphismRestrict_appTop]
    exact @surjective_comp_isIso_of_surjective _ _ _ _ _ (Functor.map_isIso _ _) (h _)
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f V, Scheme.Hom.comp_appTop]
  exact @surjective_comp_isIso_of_surjective _ _ _ _ _
    (inferInstanceAs (IsIso ((pullbackRestrictIsoRestrict f V).hom.app ⊤))) hr

theorem exists_gen_of_local_of_section : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (σ : S ⟶ X) (N : LB X), N.IsLB →
    σ ≫ f = 𝟙 S → (∀ U : S.Opens, Function.Surjective (f.app U).hom) →
    (∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : (N.pull (f ⁻¹ᵁ U).ι).Gen, t.IsGen) →
    (∃ t : (N.pull σ).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro X S f σ N hN hσ hf hl hg
  obtain ⟨c, hc⟩ := hg
  have hp : ∀ V : S.Opens, Function.Surjective (pullback.snd f V.ι).appTop.hom :=
    fun V => surjective_appTop_pullback_snd_of_app f V hf
  have e : σ ≫ f ≫ σ = σ := by rw [← Category.assoc, hσ, Category.id_comp]
  have h0 : ∀ (U : Type) [CommGroup U] (h : (S ⟶ X) → U),
      ∏ k, h (σ ≫ (![𝟙 X, f ≫ σ] : Fin 2 → (X ⟶ X)) k) ^ (![1, -1] : Fin 2 → ℤ) k = 1 := by
    intro U _ h
    simp [Fin.prod_univ_two, e]
  have hloc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ t : LB.Gen (LB.LinComb N (fun k => (f ⁻¹ᵁ U).ι ≫ (![𝟙 X, f ≫ σ] : Fin 2 → (X ⟶ X)) k)
        (![1, -1] : Fin 2 → ℤ)), t.IsGen := by
    intro s
    obtain ⟨U, hsU, t, ht⟩ := hl s
    refine ⟨U, hsU, ?_⟩
    let c₁ := LB.pullGen N (fun _ : PUnit => σ) (fun _ => 1) c ((f ⁻¹ᵁ U).ι ≫ f)
    have hc₁ : c₁.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ c hc _
    let c₂ := LB.invGen N _ _ c₁
    have hc₂ : c₂.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen N _ _ c₁ hc₁
    let m := LB.mulGen N (fun _ : PUnit => (f ⁻¹ᵁ U).ι) (fun _ => 1) _ _ t c₂
    have hm : m.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ t c₂ ht hc₂
    obtain ⟨g, hg, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN
      (φ' := fun k => (f ⁻¹ᵁ U).ι ≫ (![𝟙 X, f ≫ σ] : Fin 2 → (X ⟶ X)) k) (ε' := (![1, -1] : Fin 2 → ℤ))
      (by intro V _ h; simp [Fintype.prod_sum_type, Fin.prod_univ_two]) m hm
    exact ⟨g, hg⟩
  obtain ⟨u, hu⟩ := exists_gen_of_local_on_base hN (K := Fin 2) ![𝟙 X, f ≫ σ] ![1, -1] f σ hσ hp h0 hloc
  let c₃ := LB.pullGen N (fun _ : PUnit => σ) (fun _ => 1) c f
  have hc₃ : c₃.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ c hc f
  let m₂ := LB.mulGen N _ _ _ _ u c₃
  have hm₂ : m₂.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ u c₃ hu hc₃
  obtain ⟨g, hg, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN (φ' := fun _ : PUnit => 𝟙 X) (ε' := fun _ => 1)
    (by intro V _ h; simp [Fintype.prod_sum_type, Fin.prod_univ_two]) m₂ hm₂
  exact BoxTheta.exists_gen_of_section N (𝟙 X) (𝟙 X) (Category.id_comp _) g hg

end GlobalTheory
end
end
