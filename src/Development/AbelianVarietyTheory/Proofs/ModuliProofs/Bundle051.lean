module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteSetOfHilbertFunctionsFibres
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAffineOpenOfFiniteOpensProj
public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfIdModEpsThickening
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle043
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.UnifEigenRank

theorem finrank_of_existsUnique {k V : Type} [Field k] [AddCommGroup V] [Module k V] (E : Submodule k V) {n : ℕ}
    (W : Fin n → V) (hW : ∀ i, W i ∈ E) (h : ∀ z ∈ E, ∃! c : Fin n → k, z = ∑ i, c i • W i) :
    Module.finrank k E = n := by
  let W' : Fin n → E := fun i => ⟨W i, hW i⟩
  have hc : ∀ c : Fin n → k, ((Fintype.linearCombination k W' c : E) : V) = ∑ i, c i • W i := fun c => by
    simp [Fintype.linearCombination_apply, W']
  have hb : Function.Bijective (Fintype.linearCombination k W') := by
    refine (Function.bijective_iff_existsUnique _).2 fun z => ?_
    refine (existsUnique_congr fun c => ?_).1 (h z z.2)
    rw [Subtype.ext_iff, hc, eq_comm]
  rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_fin_fun]

end GlobalTheory.UnifEigenRank


open GlobalTheory.UnifLieBasis in
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD isTan_iff isLieComb_iff isTan_scale) in
theorem GlobalTheory.UnifEigenRank.finrank_eigenspace_of_lieMult : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (O : Type) [CommRing O] (act : OAct O P₀.A) (F : O → Module.End ℂ (Fin P₀.g → ℂ)), (∀ a z, u.ex (F a z) = u.ex z ≫ act.act a) → ∀ (τ : O →+* ℂ) (n : ℕ), LieMult act (𝟙 _) τ n → Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = n := by
  intro P₀ u Hm χ hu O _ act F hF τ n hn
  have := act.hom
  let j : epsPt (𝟙 (Sp ℂ)) ≅ epsR ℂ := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp ℂ)) ⟶ P₀.A) ≃* (epsR ℂ ⟶ P₀.A) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl P₀.A)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have one : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ P₀.A).left = η[P₀.A].left := Category.id_comp _
  obtain ⟨v, hv, hb⟩ := LiePull.basis_transport e (P := IsLieEigen act (𝟙 _) τ)
    (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
    (R' := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
    (Q := fun w => IsTangent w ∧ ∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w)
    (fun w => and_congr (by rw [IsTangent, he, one]) (forall_congr' fun a => by
      rw [Over.OverMorphism.ext_iff, Over.comp_left, Over.comp_left, Over.comp_left, he]
      rfl))
    (fun c u v => by rw [he, he]; rfl) n hn
  have key : ∀ (z : Fin P₀.g → ℂ) (w : epsR ℂ ⟶ P₀.A), IsTangent w → u.IsDiff z w →
      ((∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w) ↔
        z ∈ ⨅ a, Module.End.eigenspace (F a) (τ a)) := by
    intro z w hw hd
    rw [Submodule.mem_iInf]
    refine forall_congr' fun a => ?_
    rw [Module.End.mem_eigenspace_iff]
    have h1 : u.IsDiff (F a z) (w ≫ act.act a) :=
      isDiff_comp u (act.act a) (LinearMap.toContinuousLinearMap (F a)) (hF a) hw hd
    have h2 := isDiff_smul u ((isTan_iff _).2 hw) hd (τ a)
    have t1 := isTangent_comp (act.act a) hw
    have t2 := (isTan_iff _).1 (isTan_scale (τ a) ((isTan_iff _).2 hw))
    constructor
    · intro h
      exact (hu.tan₁ _ t1).unique h1 (by rw [h]; exact h2)
    · intro h
      rw [h] at h1
      exact (hu.tan₂ _).unique ⟨t1, h1⟩ ⟨t2, h2⟩
  choose W hW using fun i => (hu.tan₁ (v i) (hv i).1).exists
  have ht : ∀ i, Chart.IsTan (R := ℂ) (G := P₀.A) (v i) := fun i => (isTan_iff _).2 (hv i).1
  have list_prod : ∀ {k : ℕ} (x : Fin k → Fin P₀.g → ℂ) (y : Fin k → (epsR ℂ ⟶ P₀.A)),
      (∀ i, Chart.IsTan (y i)) → (∀ i, u.IsDiff (x i) (y i)) →
      Chart.IsTan (List.ofFn y).prod ∧ u.IsDiff (∑ i, x i) (List.ofFn y).prod := by
    intro k
    induction k with
    | zero =>
      intro x y hy hx
      simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
      exact ⟨Chart.isTan_one, isDiff_zero u⟩
    | succ k ih =>
      intro x y hy hx
      obtain ⟨h1, h2⟩ := ih (fun i => x i.succ) (fun i => y i.succ) (fun i => hy _) (fun i => hx _)
      rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
      exact ⟨Chart.isTan_mul (hy 0) h1, isDiff_add u (hy 0) h1 (hx 0) h2⟩
  have hp : ∀ c : Fin n → ℂ, IsTangent (prodPts (R := ℂ) (G := P₀.A) c v) ∧
      u.IsDiff (∑ i, c i • W i) (prodPts (R := ℂ) (G := P₀.A) c v) := by
    intro c
    obtain ⟨a, b⟩ := list_prod (fun i => c i • W i) (fun i => Chart.spMap (scaleD (c i)) ≫ v i)
      (fun i => isTan_scale (c i) (ht i)) (fun i => isDiff_smul u (ht i) (hW i) (c i))
    exact ⟨(isTan_iff _).1 a, b⟩
  refine UnifEigenRank.finrank_of_existsUnique _ W (fun i => (key _ _ (hv i).1 (hW i)).1 (hv i).2) fun z hz => ?_
  obtain ⟨w, hw, hd⟩ := (hu.tan₂ z).exists
  refine (existsUnique_congr fun c => ?_).1 (hb w ⟨hw, (key _ _ hw hd).2 hz⟩)
  refine Iff.trans (isLieComb_iff c v w) ⟨fun h => ?_, fun h => ?_⟩
  · exact (hu.tan₁ _ hw).unique hd (by rw [h]; exact (hp c).2)
  · rw [h] at hd
    exact (hu.tan₂ _).unique ⟨hw, hd⟩ (hp c)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.sectionCoordinateVector_exists_locally : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X), ∃ v, SecCoord M th x v) ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (p : Sp R), ∃ f : R, f ∉ p.asIdeal ∧ ∃ v, SecCoord M th (spMap (algebraMap R (Localization.Away f)) ≫ x) v) ∧ ∀ p : X, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (v : I → R), IsOpenImmersion x ∧ p ∈ Set.range x ∧ SecCoord M th x v := by
  first | exact @GlobalTheory.ZM.LocalCoord.secCoord_local | exact GlobalTheory.ZM.LocalCoord.secCoord_local | (intros; apply GlobalTheory.ZM.LocalCoord.secCoord_local <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.finite_setOf_hilbertFunctions_fibres : ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → {φ : ℕ → ℕ | ∃ (K : Type) (_ : Field K) (x : R →+* K), φ = dimDeg (I.map (MvPolynomial.map x))}.Finite := by
  first | exact @GlobalTheory.finite_setOf_dimDeg_map | exact GlobalTheory.finite_setOf_dimDeg_map | (intros; apply GlobalTheory.finite_setOf_dimDeg_map <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.IsGaloisCover

theorem exists_algClosed_point (T : Scheme.{0}) (p : T) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (j : Sp K ⟶ T), p ∈ Set.range j := by
  let k := T.residueField p
  let K := AlgebraicClosure k
  let i : Spec (CommRingCat.of K) ⟶ Spec k := Spec.map (CommRingCat.ofHom (algebraMap k K))
  refine ⟨K, inferInstance, inferInstance, i ≫ T.fromSpecResidueField p, ?_⟩
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  refine ⟨z, ?_⟩
  have hz : (T.fromSpecResidueField p) (i z) ∈ Set.range (T.fromSpecResidueField p) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecResidueField] at hz
  rw [Scheme.Hom.comp_apply]
  exact Set.mem_singleton_iff.mp hz

variable {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)}

theorem exists_local_geom (h : IsGaloisCover Ga ρ π) {T : Scheme.{0}} (x x' : T ⟶ X) (hx : x ≫ π = x' ≫ π) (p : T) :
    ∃ (V : T.Opens) (a : Ga), p ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x' := by
  have := h.etale
  let D := pullback.diagonal π
  let m : Ga → (T ⟶ pullback π π) := fun a =>
    pullback.lift (x ≫ ρ a) x' (by rw [Category.assoc, h.inv a, hx])
  obtain ⟨K, _, _, j, z, hz⟩ := exists_algClosed_point T p
  obtain ⟨a, ha, -⟩ := h.fibre K (j ≫ x) (j ≫ x') (by simp only [Category.assoc, hx])
  have hm1 : m a ≫ pullback.fst π π = x ≫ ρ a := pullback.lift_fst _ _ _
  have hm2 : m a ≫ pullback.snd π π = x' := pullback.lift_snd _ _ _
  have hjm : j ≫ m a = j ≫ x' ≫ D := by
    apply pullback.hom_ext
    · rw [Category.assoc, hm1, Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      simpa only [Category.assoc] using ha
    · rw [Category.assoc, hm2, Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id]
  let V : T.Opens := (m a) ⁻¹ᵁ D.opensRange
  have hpV : p ∈ V := by
    show (m a) p ∈ Set.range D
    rw [← hz]
    refine ⟨x' (j z), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hjm]
  have hsub : Set.range (V.ι ≫ m a) ⊆ Set.range D := by
    rintro _ ⟨w, rfl⟩
    have hw : V.ι w ∈ (V : Set T) := by
      rw [← Scheme.Opens.range_ι V]
      exact ⟨w, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hw
  let l := IsOpenImmersion.lift D (V.ι ≫ m a) hsub
  have hl : l ≫ D = V.ι ≫ m a := IsOpenImmersion.lift_fac _ _ _
  refine ⟨V, a, hpV, ?_⟩
  have e1 : V.ι ≫ x ≫ ρ a = l := by
    have h1 : l ≫ D ≫ pullback.fst π π = l := by rw [pullback.diagonal_fst, Category.comp_id]
    rw [← h1, ← Category.assoc l, hl, Category.assoc, hm1]
  have e2 : V.ι ≫ x' = l := by
    have h2 : l ≫ D ≫ pullback.snd π π = l := by rw [pullback.diagonal_snd, Category.comp_id]
    rw [← h2, ← Category.assoc l, hl, Category.assoc, hm2]
  rw [e1, e2]

theorem existsUnique_desc (h : IsGaloisCover Ga ρ π) {Z : Scheme.{0}} (f : X ⟶ Z) (hf : ∀ a, ρ a ≫ f = f) :
    ∃! f' : Y ⟶ Z, π ≫ f' = f := by
  have := h.fin
  have := h.etale
  have := h.onto
  have key : ∀ {W : Scheme.{0}} (g₁ g₂ : W ⟶ X), g₁ ≫ π = g₂ ≫ π → g₁ ≫ f = g₂ ≫ f := by
    intro W g₁ g₂ hg
    apply Scheme.hom_ext_of_forall
    intro p
    obtain ⟨V, a, hp, hV⟩ := h.exists_local_geom g₁ g₂ hg p
    refine ⟨V, hp, ?_⟩
    calc V.ι ≫ g₁ ≫ f = V.ι ≫ g₁ ≫ ρ a ≫ f := by rw [hf]
      _ = (V.ι ≫ g₁ ≫ ρ a) ≫ f := by simp only [Category.assoc]
      _ = V.ι ≫ g₂ ≫ f := by rw [hV, Category.assoc]
  refine ⟨EffectiveEpi.desc π f key, EffectiveEpi.fac π f key, ?_⟩
  intro f' hf'
  apply (cancel_epi π).1
  rw [hf', EffectiveEpi.fac]

variable {X' Y' : Scheme.{0}} {π' : X' ⟶ Y'} {ρ' : Ga → (X' ⟶ X')} {u : X' ⟶ X} {v : Y' ⟶ Y}

private theorem existsUnique_act_of_isPullback_isGaloisCover (h : IsGaloisCover Ga ρ π) (hp : IsPullback u π' π v)
    (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a) (hπ : ∀ a, ρ' a ≫ π' = π') (K : Type) [Field K] [IsAlgClosed K]
    (y y' : Sp K ⟶ X') (hy : y ≫ π' = y' ≫ π') : ∃! a, y ≫ ρ' a = y' := by
  have hyu : (y ≫ u) ≫ π = (y' ≫ u) ≫ π := by
    simp only [Category.assoc, hp.w, reassoc_of% hy]
  obtain ⟨a, ha, hauniq⟩ := h.fibre K (y ≫ u) (y' ≫ u) hyu
  refine ⟨a, ?_, ?_⟩
  · apply hp.hom_ext
    · rw [Category.assoc, hu, ← Category.assoc, ha]
    · rw [Category.assoc, hπ, hy]
  · intro b hb
    apply hauniq
    rw [Category.assoc, ← hu, ← Category.assoc, hb]

theorem isPullback (h : IsGaloisCover Ga ρ π) (h' : IsGaloisCover Ga ρ' π') (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a)
    (w : u ≫ π = π' ≫ v) : IsPullback u π' π v := by
  have := h.fin
  have := h.etale
  have := h.onto
  have := h'.fin
  have := h'.etale
  let ρP : Ga → (pullback π v ⟶ pullback π v) := fun a =>
    pullback.map π v π v (ρ a) (𝟙 Y') (𝟙 Y) (by rw [Category.comp_id, h.inv]) (by rw [Category.comp_id, Category.id_comp])
  have huP : ∀ a, ρP a ≫ pullback.fst π v = pullback.fst π v ≫ ρ a := fun a => pullback.lift_fst _ _ _
  have hπP : ∀ a, ρP a ≫ pullback.snd π v = pullback.snd π v := fun a => by
    rw [← Category.comp_id (pullback.snd π v)]
    exact pullback.lift_snd _ _ _
  let φ : X' ⟶ pullback π v := pullback.lift u π' w
  have hφ1 : φ ≫ pullback.fst π v = u := pullback.lift_fst _ _ _
  have hφ2 : φ ≫ pullback.snd π v = π' := pullback.lift_snd _ _ _
  have hφeq : ∀ a, φ ≫ ρP a = ρ' a ≫ φ := fun a => by
    apply pullback.hom_ext
    · simp only [Category.assoc, huP, hφ1, reassoc_of% hφ1, hu]
    · simp only [Category.assoc, hπP, hφ2, h'.inv]
  have hmono : Mono φ := by
    constructor
    intro T g₁ g₂ hg
    have hg1 : g₁ ≫ u = g₂ ≫ u := by rw [← hφ1, reassoc_of% hg]
    have hg2 : g₁ ≫ π' = g₂ ≫ π' := by rw [← hφ2, reassoc_of% hg]
    apply Scheme.hom_ext_of_forall
    intro p
    obtain ⟨V, a, hp, hV⟩ := h'.exists_local_geom g₁ g₂ hg2 p
    refine ⟨V, hp, ?_⟩
    have e : V.ι ≫ g₁ ≫ u ≫ ρ a = V.ι ≫ g₁ ≫ u := by
      rw [← hu, hg1]
      simpa only [Category.assoc] using congrArg (· ≫ u) hV
    obtain ⟨K, _, _, j, -⟩ := exists_algClosed_point V.toScheme ⟨p, hp⟩
    have ha : (j ≫ V.ι ≫ g₁ ≫ u) ≫ ρ a = j ≫ V.ι ≫ g₁ ≫ u := by
      simp only [Category.assoc] at e ⊢
      rw [e]
    have h1 : (j ≫ V.ι ≫ g₁ ≫ u) ≫ ρ 1 = j ≫ V.ι ≫ g₁ ≫ u := by
      rw [h.one, Category.comp_id]
    have ha1 : a = 1 := (h.fibre K _ _ rfl).unique ha h1
    rw [← hV, ha1, h'.one, Category.comp_id]
  have hsurj : Surjective φ := by
    constructor
    intro q
    obtain ⟨y, hy⟩ := h'.onto.surj (pullback.snd π v q)
    obtain ⟨r, hr1, hr2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd π v)
      (g := pullback.snd π v) (φ y) q (by rw [← Scheme.Hom.comp_apply, hφ2, hy])
    obtain ⟨K, _, _, j, z, hz⟩ := exists_algClosed_point _ r
    obtain ⟨a, ha, -⟩ := existsUnique_act_of_isPullback_isGaloisCover h (IsPullback.of_hasPullback π v) huP hπP K
      (j ≫ pullback.fst _ _) (j ≫ pullback.snd _ _)
      (by simp only [Category.assoc, pullback.condition])
    refine ⟨ρ' a y, ?_⟩
    have hz' := congrArg (fun m : Sp K ⟶ _ => m z) ha
    simp only [Scheme.Hom.comp_apply, hz, hr1, hr2] at hz'
    rw [← Scheme.Hom.comp_apply, ← hφeq, Scheme.Hom.comp_apply]
    exact hz'
  have : Etale φ := by
    have : Etale (φ ≫ pullback.snd π v) := by rw [hφ2]; exact h'.etale
    exact Etale.of_comp (f := φ) (pullback.snd π v)
  have : QuasiCompact φ := by
    have : QuasiCompact (φ ≫ pullback.snd π v) := by rw [hφ2]; infer_instance
    exact MorphismProperty.of_postcomp (W := @QuasiCompact) (W' := @QuasiSeparated) φ
      (pullback.snd π v) inferInstance this
  have : IsIso φ := Flat.isIso_of_surjective_of_mono φ
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso φ) hφ1 hφ2

theorem of_isPullback (h : IsGaloisCover Ga ρ π) (hp : IsPullback u π' π v) (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a)
    (hπ : ∀ a, ρ' a ≫ π' = π') : IsGaloisCover Ga ρ' π' := by
  refine ⟨h.finite, ?_, ?_, hπ, ?_, ?_, ?_, existsUnique_act_of_isPullback_isGaloisCover h hp hu hπ⟩
  · apply hp.hom_ext
    · rw [hu 1, h.one, Category.id_comp, Category.comp_id]
    · rw [hπ 1, Category.id_comp]
  · intro a c
    apply hp.hom_ext
    · rw [hu, h.mul, Category.assoc, hu c, reassoc_of% (hu a)]
    · rw [hπ, Category.assoc, hπ c, hπ a]
  · exact MorphismProperty.of_isPullback hp h.fin
  · exact MorphismProperty.of_isPullback hp h.etale
  · exact MorphismProperty.of_isPullback hp h.onto

end GlobalTheory.ZM.IsGaloisCover

namespace GlobalTheory.ZM

theorem galoisCover_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → (∀ (Z : Scheme.{0}) (f : X ⟶ Z), (∀ a, ρ a ≫ f = f) → ∃! f' : Y ⟶ Z, π ≫ f' = f) ∧ (∀ (T : Scheme.{0}) (x x' : T ⟶ X), x ≫ π = x' ≫ π → ∀ p : T, ∃ (V : T.Opens) (a : Ga), p ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x') ∧ ∀ (X' Y' : Scheme.{0}) (π' : X' ⟶ Y') (ρ' : Ga → (X' ⟶ X')) (u : X' ⟶ X) (v : Y' ⟶ Y), (∀ a, ρ' a ≫ u = u ≫ ρ a) → u ≫ π = π' ≫ v → (IsGaloisCover Ga ρ' π' → IsPullback u π' π v) ∧ (IsPullback u π' π v → (∀ a, ρ' a ≫ π' = π') → IsGaloisCover Ga ρ' π') := by
  intro X Y π Ga _ ρ h
  refine ⟨fun Z f hf => h.existsUnique_desc f hf, fun T x x' hx p => h.exists_local_geom x x' hx p, ?_⟩
  intro X' Y' π' ρ' u v hu w
  exact ⟨fun h' => h.isPullback h' hu w, fun hp hπ => h.of_isPullback hp hu hπ⟩

end GlobalTheory.ZM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

def autOfRightAction {X : Scheme.{0}} {Ga : Type} [Group Ga] (ρ : Ga → (X ⟶ X)) (h1 : ρ 1 = 𝟙 X)
    (hm : ∀ a c, ρ (a * c) = ρ a ≫ ρ c) : Ga →* Aut X :=
  MonoidHom.mk' (fun a ↦
    Aut.of
      { hom := ρ a⁻¹
        inv := ρ a
        hom_inv_id := by rw [← hm, inv_mul_cancel, h1]
        inv_hom_id := by rw [← hm, mul_inv_cancel, h1] }) fun a c ↦
    Aut.ext (Iso.ext (show ρ (a * c)⁻¹ = ρ c⁻¹ ≫ ρ a⁻¹ by rw [mul_inv_rev, hm]))

theorem autOfRightAction_hom {X : Scheme.{0}} {Ga : Type} [Group Ga] (ρ : Ga → (X ⟶ X))
    (h1 : ρ 1 = 𝟙 X) (hm : ∀ a c, ρ (a * c) = ρ a ≫ ρ c) (a : Ga) :
    (autOfRightAction ρ h1 hm a).asIso.hom = ρ a⁻¹ := rfl


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.ZM.isSeparated_finiteType_of_isQProjOver {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver f) :
    IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f := by
  obtain ⟨N, i, hi, hqc, rfl⟩ := h
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  exact ⟨inferInstance, inferInstance, inferInstance⟩


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) → ∃ (Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K), π ≫ sY = s ∧ _root_.GlobalTheory.ZM.IsGaloisCover Ga ρ π ∧ IsSeparated sY ∧ LocallyOfFiniteType sY ∧ QuasiCompact sY := by
  intro K _ X s Ga _ _ ρ hq h1 hm hs hfree
  set τ := _root_.GlobalTheory.ZM.autOfRightAction ρ h1 hm with hτ
  have horbits : _root_.GlobalTheory.OrbitsInAffineOpens τ :=
    _root_.GlobalTheory.OrbitsInAffineOpens.of_isQProjOver hq τ
  have hτg : ∀ g : Ga, (τ g).asIso.hom = ρ g⁻¹ := fun _ ↦ rfl
  have hτs : ∀ g : Ga, (τ g).asIso.hom ≫ s = s := fun g ↦ hs g⁻¹
  have hfreeτ : _root_.GlobalTheory.IsFreeAction τ := by
    refine _root_.GlobalTheory.IsFreeAction.of_isAlgClosed.{0} (fun k _ _ x g hx ↦ ?_)
    exact inv_eq_one.mp (hfree k x g⁻¹ hx)
  obtain ⟨Y, π, hQ⟩ := (_root_.GlobalTheory.exists_isAffineQuotient_iff τ).mpr horbits
  let sY := hQ.desc s hτs
  have hπs : π ≫ sY = s := hQ.comp_desc s hτs
  obtain ⟨hsep, hlft, hqc⟩ := _root_.GlobalTheory.ZM.isSeparated_finiteType_of_isQProjOver hq
  refine ⟨Y, π, sY, hπs, ?_, ?_, ?_, ?_⟩
  · refine ⟨inferInstance, h1, hm, fun a ↦ ?_,
      hQ.isFinite_of_isFreeAction hfreeτ, hQ.etale_of_isFreeAction hfreeτ, hQ.surjective, ?_⟩
    · have := hQ.comp_eq a⁻¹
      rwa [hτg, inv_inv] at this
    · intro k _ _ y y' hyy
      obtain ⟨g, hg⟩ := (hQ.comp_eq_comp_iff y y').mp hyy
      refine ⟨g⁻¹, hg, fun b hb ↦ ?_⟩
      have key : y ≫ ρ (b * g) = y := by
        rw [hm, ← Category.assoc, hb, ← hg, hτg, Category.assoc, ← hm, inv_mul_cancel, h1, Category.comp_id]
      exact eq_inv_of_mul_eq_one_left (hfree k y _ key)
  · haveI : IsSeparated (π ≫ sY) := by
      rw [hπs]; exact hsep
    exact hQ.isSeparated sY
  · haveI : LocallyOfFiniteType (π ≫ sY) := by
      rw [hπs]; exact hlft
    haveI : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))
    exact hQ.locallyOfFiniteType sY
  · haveI : QuasiCompact (π ≫ sY) := by
      rw [hπs]; exact hqc
    exact hQ.quasiCompact sY

end GlobalTheory.ZM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.isIso_of_id_mod_eps_thickening : ∀ (K : Type) [Field K] (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (π' : Z' ⟶ Sp (DualNumber K)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  first | exact @GlobalTheory.isIso_of_id_mod_eps | exact GlobalTheory.isIso_of_id_mod_eps | (intros; apply GlobalTheory.isIso_of_id_mod_eps <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_desc_of_dense_preimmersion : ∀ (S X X' U U' Y : Scheme.{0}) [IsLocallyNoetherian X'] (π : X ⟶ X') (j : U ⟶ X) (j' : U' ⟶ X') (r : U ⟶ U') (s' : X' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) (f₀ : U' ⟶ Y), IsNormalScheme X' → IsReduced X → IsFinite π → Surjective π → Surjective r → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsSeparated p → LocallyOfFiniteType p → j ≫ π = r ≫ j' → j ≫ f = r ≫ f₀ → f ≫ p = π ≫ s' → f₀ ≫ p = j' ≫ s' → ∃ f' : X' ⟶ Y, j' ≫ f' = f₀ ∧ π ≫ f' = f := by
  first | exact @GlobalTheory.exists_desc_of_isFinite_of_densePart | exact GlobalTheory.exists_desc_of_isFinite_of_densePart | (intros; apply GlobalTheory.exists_desc_of_isFinite_of_densePart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.torsion_and_isMonHom_of_open_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ (k : ℕ) (x : Out.baseOver S ⟶ A) (x' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i), (∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) → (∀ i, x' i ^ k = 1) → x ^ k = 1) ∧ ∀ (f : A ⟶ A) (f' : ∀ i, G i ⟶ G i), (∀ i, (f' i).left ≫ ψ i = ψ i ≫ f.left) → (∀ i, IsMonHom (f' i)) → IsMonHom f := by
  first | exact @GlobalTheory.CoverGlue.tors_and_isMonHom_of_cover | exact GlobalTheory.CoverGlue.tors_and_isMonHom_of_cover | (intros; apply GlobalTheory.CoverGlue.tors_and_isMonHom_of_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_grpObj_of_local_group_laws_on_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (m n : A ⊗ A ⟶ A) (e : Out.baseOver S ⟶ A), iSup U = ⊤ → (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i (T : Over (U i).toScheme) (x y : T ⟶ G i) (x₀ y₀ : Over.mk (T.hom ≫ (U i).ι) ⟶ A), x₀.left = x.left ≫ ψ i → y₀.left = y.left ≫ ψ i → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ ψ i ∧ (lift x₀ y₀ ≫ n).left = (x⁻¹).left ≫ ψ i) → (∀ i, (1 : Out.baseOver (U i).toScheme ⟶ G i).left ≫ ψ i = (U i).ι ≫ e.left) → ∃ _ : GrpObj A, ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i) := by
  first | exact @GlobalTheory.CoverGlue.exists_grpObj_of_cover | exact GlobalTheory.CoverGlue.exists_grpObj_of_cover | (intros; apply GlobalTheory.CoverGlue.exists_grpObj_of_cover <;> assumption)
end
