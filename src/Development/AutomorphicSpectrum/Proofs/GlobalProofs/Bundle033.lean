module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle017
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle031
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle001
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.SignTiles

variable {V : Type} [AddCommGroup V] [Module ℚ V]

theorem tile_mono {P : Set V} {Q Q' : Set V → Prop} (hQ : ∀ A, Q A → Q' A) {C : Set V} (h : Tile P Q C) :
    Tile P Q' C := by
  induction h with
  | empty => exact .empty
  | cone s hli hP hQs => exact .cone s hli hP (hQ _ hQs)
  | union _ _ hAB ihA ihB => exact .union ihA ihB hAB

theorem tile_refine {P : Set V} {Q Q' : Set V → Prop}
    (hc : ∀ s : Finset V, LinearIndepOn ℚ id (s : Set V) → (s : Set V) ⊆ P → Q (coneOn s) → Tile P Q' (coneOn s))
    {C : Set V} (h : Tile P Q C) : Tile P Q' C := by
  induction h with
  | empty => exact .empty
  | cone s hli hP hQs => exact hc s hli hP hQs
  | union _ _ hAB ihA ihB => exact .union ihA ihB hAB

theorem tile_inside {P : Set V} {Q : Set V → Prop} {C : Set V} (h : Tile P Q C) :
    Tile P (fun A => Q A ∧ A ⊆ C) C := by
  induction h with
  | empty => exact .empty
  | cone s hli hP hQs => exact .cone s hli hP ⟨hQs, subset_rfl⟩
  | @union A B _ _ hAB ihA ihB =>
    exact .union (tile_mono (fun X hX => ⟨hX.1, hX.2.trans Set.subset_union_left⟩) ihA)
      (tile_mono (fun X hX => ⟨hX.1, hX.2.trans Set.subset_union_right⟩) ihB) hAB

theorem signConst_mono {l : V →ₗ[ℚ] ℚ} {A C : Set V} (h : SignConst l C) (hAC : A ⊆ C) : SignConst l A := by
  rcases h with h | h | h
  · exact Or.inl fun x hx => h x (hAC hx)
  · exact Or.inr (Or.inl fun x hx => h x (hAC hx))
  · exact Or.inr (Or.inr fun x hx => h x (hAC hx))

theorem sign_eq_of_signConst {l : V →ₗ[ℚ] ℚ} {A : Set V} (h : SignConst l A) {x y : V} (hx : x ∈ A) (hy : y ∈ A) :
    SignType.sign (l x) = SignType.sign (l y) := by
  rcases h with h | h | h
  · rw [h x hx, h y hy]
  · rw [sign_pos (h x hx), sign_pos (h y hy)]
  · rw [sign_neg (h x hx), sign_neg (h y hy)]

theorem tile_signs (P : ConvexCone ℚ V) (s : Finset V) (hli : LinearIndepOn ℚ id (s : Set V))
    (hP : (s : Set V) ⊆ (P : Set V)) (Λ : Set (V →ₗ[ℚ] ℚ)) (hΛ : Λ.Finite) :
    Tile (P : Set V) (fun A => A ⊆ coneOn s ∧ ∀ l ∈ Λ, SignConst l A) (coneOn s) := by
  classical
  obtain ⟨t, rfl⟩ := hΛ.exists_finset_coe
  refine Finset.induction_on t ?_ ?_
  · exact .cone s hli hP ⟨subset_rfl, fun l hl => by simp at hl⟩
  · intro l t _ ih
    refine tile_refine (fun u hu huP hQu => ?_) ih
    refine tile_mono (fun A hA => ⟨hA.2.trans hQu.1, fun l' hl' => ?_⟩)
      (tile_inside (GlobalTheory.T.simplicial_cone_tiles_sign P l u hu huP))
    rcases Finset.mem_insert.1 (Finset.mem_coe.1 hl') with rfl | h'
    · exact hA.1
    · exact signConst_mono (hQu.2 l' (Finset.mem_coe.2 h')) hA.2

theorem tile_inter {P E C : Set V} (h : Tile P (fun A => A ⊆ E ∨ Disjoint A E) C) :
    Tile P (fun _ => True) (C ∩ E) := by
  induction h with
  | empty =>
    rw [Set.empty_inter]
    exact .empty
  | cone s hli hP hQs =>
    rcases hQs with hs | hs
    · rw [Set.inter_eq_left.2 hs]
      exact .cone s hli hP trivial
    · rw [Set.disjoint_iff_inter_eq_empty.1 hs]
      exact .empty
  | union _ _ hAB ihA ihB =>
    rw [Set.union_inter_distrib_right]
    exact .union ihA ihB (hAB.mono Set.inter_subset_left Set.inter_subset_left)

theorem mem_coneOn_basis [DecidableEq V] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ V) (x : V) :
    x ∈ coneOn (Finset.univ.image b) ↔ ∀ i, 0 < b.repr x i := by
  classical
  constructor
  · rintro ⟨t, ht, rfl⟩ i
    rw [Finset.sum_image (fun a _ c _ hac => b.injective hac)]
    have hrep : b.repr (∑ j, t (b j) • b j) i = t (b i) := by

      simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_single i]
      · rw [Finsupp.single_apply, if_pos rfl]
      · intro j _ hji
        rw [Finsupp.single_apply, if_neg hji]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [hrep]
    exact ht _ (Finset.mem_image_of_mem b (Finset.mem_univ i))
  · intro hx
    have key : ∀ i, ∑ j, b.repr (b i) j * b.repr x j = b.repr x i := by
      intro i
      rw [Module.Basis.repr_self, Finset.sum_eq_single i]
      · rw [Finsupp.single_apply, if_pos rfl, one_mul]
      · intro j _ hji
        rw [Finsupp.single_apply, if_neg (Ne.symm hji), zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    refine ⟨fun v => ∑ j, b.repr v j * b.repr x j, ?_, ?_⟩
    · intro v hv
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      show 0 < ∑ j, b.repr (b i) j * b.repr x j
      rw [key]
      exact hx i
    · rw [Finset.sum_image (fun a _ c _ hac => b.injective hac)]
      conv_lhs => rw [← b.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      show b.repr x i • b i = (∑ j, b.repr (b i) j * b.repr x j) • b i
      rw [key]

theorem tile_of_signs : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] {κ : Type} [Fintype κ] (P : ConvexCone ℚ V)
    (b : Module.Basis κ ℚ V), (∀ i, b i ∈ P) → ∀ (Λ : Set (V →ₗ[ℚ] ℚ)), Λ.Finite → ∀ (E : Set V),
    (∀ x ∈ E, ∀ i, 0 < b.repr x i) →
    (∀ x y, (∀ i, 0 < b.repr x i) → (∀ i, 0 < b.repr y i) →
      (∀ l ∈ Λ, SignType.sign (l x) = SignType.sign (l y)) → x ∈ E → y ∈ E) →
    Tile (P : Set V) (fun _ => True) E := by
  classical
  intro V _ _ κ _ P b hb Λ hΛ E hE hdec
  have hcoe : ((Finset.univ.image b : Finset V) : Set V) = Set.range b := by
    simp [Set.image_univ]
  have hli : LinearIndepOn ℚ id ((Finset.univ.image b : Finset V) : Set V) := by
    rw [hcoe]
    exact (linearIndepOn_id_range_iff b.injective).2 b.linearIndependent
  have hP' : ((Finset.univ.image b : Finset V) : Set V) ⊆ (P : Set V) := by
    rw [hcoe]
    rintro v ⟨i, rfl⟩
    exact hb i
  have hT := tile_inter (tile_mono (Q' := fun A => A ⊆ E ∨ Disjoint A E) (fun A hA => ?_)
    (tile_signs P _ hli hP' Λ hΛ))
  · have hEs : coneOn (Finset.univ.image b) ∩ E = E :=
      Set.inter_eq_right.2 fun x hx => (mem_coneOn_basis b x).2 (hE x hx)
    rw [hEs] at hT
    exact hT
  · obtain ⟨hAs, hAl⟩ := hA
    by_cases hex : ∃ x ∈ A, x ∈ E
    · left
      obtain ⟨x, hxA, hxE⟩ := hex
      intro y hyA
      exact hdec x y ((mem_coneOn_basis b x).1 (hAs hxA)) ((mem_coneOn_basis b y).1 (hAs hyA))
        (fun l hl => sign_eq_of_signConst (hAl l hl) hxA hyA) hxE
    · right
      exact Set.disjoint_left.2 fun x hxA hxE => hex ⟨x, hxA, hxE⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.SignTiles
end
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.real_difference_cone_bound : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B R : ℕ) (cs : List (Fin r)) (β : ι → ℕ),
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re → ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
    ‖DLR cs (Fr a b s β) x‖ ≤ C * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ) - (cs.length : ℤ)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay.diff_bound | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay.diff_bound | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay.diff_bound <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

theorem dim_eq_of_mem_inf {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : X.Opens} {n m : ℕ}
    (hU : SmoothOfRelativeDimension n (U.ι ≫ f)) (hV : SmoothOfRelativeDimension m (V.ι ≫ f))
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V) : n = m := by
  have e₁ : SmoothOfRelativeDimension (0 + n) ((U ⊓ V).ι ≫ f) := by
    rw [← Scheme.homOfLE_ι _ (inf_le_left : U ⊓ V ≤ U), Category.assoc]; infer_instance
  have e₂ : SmoothOfRelativeDimension (0 + m) ((U ⊓ V).ι ≫ f) := by
    rw [← Scheme.homOfLE_ι _ (inf_le_right : U ⊓ V ≤ V), Category.assoc]; infer_instance
  simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨x, hxU, hxV⟩

theorem smoothOfRelativeDimension_iSup {X Y : Scheme.{0}} (f : X ⟶ Y) (D : ℕ) {ι : Type*}
    (U : ι → X.Opens) (hU : ∀ i, SmoothOfRelativeDimension D ((U i).ι ≫ f)) :
    SmoothOfRelativeDimension D ((⨆ i, U i).ι ≫ f) := by
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} D) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} D)
    (fun i => (⨆ i, U i).ι ⁻¹ᵁ U i) ?_ fun i => ?_
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 x.2
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  · let j := ((⨆ i, U i).ι ⁻¹ᵁ U i).ι ≫ (⨆ i, U i).ι
    have hr : Set.range j ⊆ Set.range (U i).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact y.2
    let k := IsOpenImmersion.lift (U i).ι j hr
    have hk : k ≫ (U i).ι = j := IsOpenImmersion.lift_fac _ _ _
    have : IsOpenImmersion (k ≫ (U i).ι) := by rw [hk]; infer_instance
    have : IsOpenImmersion k := IsOpenImmersion.of_comp k (U i).ι
    have e : ((⨆ i, U i).ι ⁻¹ᵁ U i).ι ≫ (⨆ i, U i).ι ≫ f = k ≫ (U i).ι ≫ f := by
      rw [← Category.assoc, ← Category.assoc, hk]
    rw [e]
    exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension.{0} D) (hU i) k

theorem exists_clopen_smoothOfRelativeDimension :
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ), Smooth s → ∃ W : ℕ → X.Opens, (∀ D, IsClosed (W D : Set X)) ∧ (∀ D, SmoothOfRelativeDimension D ((W D).ι ≫ s)) ∧ (⨆ D, W D) = ⊤ ∧ Pairwise fun D D' => W D ⊓ W D' = ⊥ := by
  intro X s hs
  let W : ℕ → X.Opens := fun D => ⨆ U : {U : X.Opens // SmoothOfRelativeDimension D (U.ι ≫ s)}, U.1
  have hsm : ∀ D, SmoothOfRelativeDimension D ((W D).ι ≫ s) := fun D =>
    smoothOfRelativeDimension_iSup s D _ fun U => U.2
  have hcov : (⨆ D, W D) = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨n, U, hx, hU⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim s x
    exact Opens.mem_iSup.2 ⟨n, Opens.mem_iSup.2 ⟨⟨U, hU⟩, hx⟩⟩
  have hdis : Pairwise fun D D' => W D ⊓ W D' = ⊥ := by
    intro D D' hne
    refine le_bot_iff.1 fun x hx => ?_
    obtain ⟨U, hU⟩ := Opens.mem_iSup.1 hx.1
    obtain ⟨V, hV⟩ := Opens.mem_iSup.1 hx.2
    exact (hne (dim_eq_of_mem_inf s U.2 V.2 hU hV)).elim
  refine ⟨W, fun D => ?_, hsm, hcov, hdis⟩
  have hc : (W D : Set X)ᶜ = ((⨆ D' : {D' // D' ≠ D}, W D'.1 : X.Opens) : Set X) := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ (⨆ D, W D) := hcov ▸ trivial
      obtain ⟨D', hD'⟩ := Opens.mem_iSup.1 hx'
      refine Opens.mem_iSup.2 ⟨⟨D', fun e => hx (e ▸ hD')⟩, hD'⟩
    · intro hx hxD
      obtain ⟨D', hD'⟩ := Opens.mem_iSup.1 hx
      have := hdis D'.2
      have hm : x ∈ W D'.1 ⊓ W D := ⟨hD', hxD⟩
      rw [this] at hm
      exact hm
  rw [← isOpen_compl_iff, hc]
  exact Opens.isOpen _

end GlobalTheory.CompanionTheory.Gaga
end
