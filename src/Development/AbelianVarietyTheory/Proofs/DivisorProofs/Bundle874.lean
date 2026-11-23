module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle843
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle844
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.WittVector.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle845
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfC
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.RingTheory.Bialgebra.Basic

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory

theorem morita_spread_stable_summand_lie : ∀ {C : Type} [CommRing C] (I : Ideal C) {H : Type u} [AddCommGroup H] [Module C H]
  (m : ℕ) [NeZero m] (E : Fin m → Fin m → Module.End C H),
  (∀ i j k l, E i j * E k l = if j = k then E i l else 0) → ∑ i, E i i = 1 →
  ∀ {A : Type} [CommRing A] (σ : A →+* Module.End C H), (∀ i j c, E i j * σ c = σ c * E i j) →
  ∀ {O : Type} [Ring O] (ρ : O →+* Module.End C H),
  (∀ (c : O) i j (N : Submodule C H), (∀ c', ∀ x ∈ N, σ c' x ∈ N) → ∀ x ∈ N, E 0 0 x = x → E 0 i (ρ c (E j 0 x)) ∈ N) →
  ∀ (e : Module.End C H), e * e = e → (∀ i j, E i j * e = e * E i j) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ i j, ∀ x ∈ F, E i j x ∈ F) → (∀ x ∈ F, e x ∈ F) →
  ∀ (a : ℕ) (χ : Fin a → A →+* C) (G₀ M₀ : Submodule C H), G₀ ⊓ M₀ = ⊥ → G₀ ⊔ M₀ = LinearMap.range (E 0 0 * e) →
    (∀ c, ∀ x ∈ G₀, σ c x ∈ G₀) → G₀ ⊔ I • LinearMap.range (E 0 0 * e) = F ⊓ LinearMap.range (E 0 0 * e) →
    (∀ d ∈ LinearMap.range (E 0 0 * e), ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G₀) ∧ d - ∑ i, w i ∈ G₀) →
  ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : O), ∀ x ∈ G, ρ c x ∈ G) ∧
    G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧
    ∀ d ∈ LinearMap.range e, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
  intro C _ I H _ _ m _ E hE hsum A _ σ hσ O _ ρ hρ e he heE F hIF hFE hFe a χ G₀ M₀ hGM hGM' hσG hGF hLie
  have mul_ap : ∀ (f g : Module.End C H) x, (f * g) x = f (g x) := fun _ _ _ => rfl
  have app : ∀ i j k l x, E i j (E k l x) = if j = k then E i l x else 0 := by
    intro i j k l x
    rw [← mul_ap, hE]; split_ifs <;> simp
  have eapp : ∀ i j x, E i j (e x) = e (E i j x) := by
    intro i j x; rw [← mul_ap, heE, mul_ap]
  have sigcomm : ∀ i j c x, σ c (E i j x) = E i j (σ c x) := by
    intro i j c x; rw [← mul_ap, ← hσ, mul_ap]
  have ee : ∀ x, e (e x) = e x := fun x => by rw [← mul_ap, he]
  have memRe : ∀ x, x ∈ LinearMap.range e ↔ e x = x := by
    intro x; constructor
    · rintro ⟨y, rfl⟩; exact ee y
    · intro h; exact ⟨x, h⟩
  have memR00 : ∀ x, x ∈ LinearMap.range (E 0 0 * e) ↔ E 0 0 x = x ∧ e x = x := by
    intro x; constructor
    · rintro ⟨y, rfl⟩
      simp only [mul_ap]
      refine ⟨?_, ?_⟩
      · rw [app]; simp
      · rw [← eapp, ee]
    · rintro ⟨h1, h2⟩; exact ⟨x, by rw [mul_ap, h2, h1]⟩
  have decomp : ∀ x, ∑ i, E i 0 (E 0 i x) = x := by
    intro x
    calc ∑ i, E i 0 (E 0 i x) = ∑ i, E i i x := by simp [app]
      _ = (∑ i, E i i) x := (LinearMap.sum_apply _ _ _).symm
      _ = x := by rw [hsum]; rfl
  have E0i_mem : ∀ i x, e x = x → E 0 i x ∈ LinearMap.range (E 0 0 * e) := by
    intro i x hx; rw [memR00]
    exact ⟨by rw [app]; simp, by rw [← eapp, hx]⟩
  have hG0R : ∀ x ∈ G₀, E 0 0 x = x ∧ e x = x := fun x hx =>
    (memR00 x).1 (by rw [← hGM']; exact Submodule.mem_sup_left hx)
  have hM0R : ∀ x ∈ M₀, E 0 0 x = x ∧ e x = x := fun x hx =>
    (memR00 x).1 (by rw [← hGM']; exact Submodule.mem_sup_right hx)
  have hG₀F : ∀ g ∈ G₀, g ∈ F := fun g hg => by
    have h : g ∈ G₀ ⊔ I • LinearMap.range (E 0 0 * e) := Submodule.mem_sup_left hg
    rw [hGF] at h; exact h.1
  have spread_in : ∀ (N : Submodule C H) k, ∀ g ∈ N, E k 0 g ∈ ⨆ i, N.map (E i 0) :=
    fun N k g hg => Submodule.mem_iSup_of_mem k (Submodule.mem_map_of_mem hg)
  have spread_all : ∀ (N P : Submodule C H), (∀ k, ∀ g ∈ N, E k 0 g ∈ P) →
      (⨆ i, N.map (E i 0)) ≤ P :=
    fun N P h => iSup_le fun k => Submodule.map_le_iff_le_comap.2 fun g hg => h k g hg
  have spread_key : ∀ N : Submodule C H, (∀ x ∈ N, E 0 0 x = x) → ∀ j,
      ∀ x ∈ ⨆ i, N.map (E i 0), E 0 j x ∈ N := by
    intro N hN j x hx
    have : (⨆ i, N.map (E i 0)) ≤ N.comap (E 0 j) := by
      refine spread_all N _ fun k g hg => ?_
      simp only [Submodule.mem_comap]
      rw [app]
      split_ifs with h
      · subst h; rw [hN g hg]; exact hg
      · exact N.zero_mem
    exact this hx
  have spread_e : ∀ (N : Submodule C H), (∀ x ∈ N, e x = x) →
      (⨆ i, N.map (E i 0)) ≤ LinearMap.range e := fun N hN =>
    spread_all N _ fun k g hg => (memRe _).2 (by rw [← eapp, hN g hg])
  refine ⟨⨆ i, G₀.map (E i 0), ⨆ i, M₀.map (E i 0), ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxG, hxM⟩
    have h0 : ∀ i, E 0 i x = 0 := fun i => by
      have : E 0 i x ∈ G₀ ⊓ M₀ :=
        ⟨spread_key G₀ (fun y hy => (hG0R y hy).1) i x hxG,
         spread_key M₀ (fun y hy => (hM0R y hy).1) i x hxM⟩
      rw [hGM] at this; exact (Submodule.mem_bot C).1 this
    rw [Submodule.mem_bot, ← decomp x]; simp [h0]
  · refine le_antisymm (sup_le (spread_e G₀ fun y hy => (hG0R y hy).2)
      (spread_e M₀ fun y hy => (hM0R y hy).2)) ?_
    intro x hx
    rw [memRe] at hx
    rw [← decomp x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : E 0 i x ∈ G₀ ⊔ M₀ := by rw [hGM']; exact E0i_mem i x hx
    obtain ⟨g, hg, n, hn, hgn⟩ := Submodule.mem_sup.1 h1
    rw [← hgn, map_add (f := _)]
    exact Submodule.add_mem_sup (spread_in G₀ i g hg) (spread_in M₀ i n hn)
  · intro c x hx
    have key : ∀ j, E 0 j (ρ c x) ∈ G₀ := by
      intro j
      have : (⨆ i, G₀.map (E i 0)) ≤ G₀.comap (E 0 j * ρ c) :=
        spread_all G₀ _ fun k g hg => hρ c j k G₀ hσG g hg (hG0R g hg).1
      exact this hx
    rw [← decomp (ρ c x)]
    exact Submodule.sum_mem _ fun j _ => spread_in G₀ j _ (key j)
  · apply le_antisymm
    · refine sup_le ?_ (inf_le_inf_right _ hIF)
      refine spread_all G₀ _ fun k g hg => ⟨hFE k 0 g (hG₀F g hg), ?_⟩
      exact (memRe _).2 (by rw [← eapp, (hG0R g hg).2])
    · rintro x ⟨hxF, hxe⟩
      replace hxe := (memRe x).1 hxe
      rw [← decomp x]
      refine Submodule.sum_mem _ fun i _ => ?_
      have h1 : E 0 i x ∈ F ⊓ LinearMap.range (E 0 0 * e) := ⟨hFE 0 i x hxF, E0i_mem i x hxe⟩
      rw [← hGF] at h1
      obtain ⟨g, hg, t, ht, hgt⟩ := Submodule.mem_sup.1 h1
      rw [← hgt, map_add (f := _)]
      refine Submodule.add_mem_sup (spread_in G₀ i g hg) ?_
      have : I • LinearMap.range (E 0 0 * e) ≤ (I • ⊤ ⊓ LinearMap.range e).comap (E i 0) := by
        rw [Submodule.smul_le]
        intro r hr n hn
        rw [Submodule.mem_comap, map_smul]
        refine ⟨Submodule.smul_mem_smul hr Submodule.mem_top, ?_⟩
        exact (memRe _).2 (by rw [map_smul, ← eapp, ((memR00 n).1 hn).2])
      exact this ht
  · intro d hd
    rw [memRe] at hd
    have hw : ∀ i, ∃ w : Fin a → H, (∀ j c, σ c (w j) - χ j c • w j ∈ G₀) ∧
        E 0 i d - ∑ j, w j ∈ G₀ := fun i => hLie _ (E0i_mem i d hd)
    choose w hw1 hw2 using hw
    refine ⟨fun j => ∑ i, E i 0 (w i j), ?_, ?_⟩
    · intro j c
      have : σ c (∑ i, E i 0 (w i j)) - χ j c • ∑ i, E i 0 (w i j) =
          ∑ i, E i 0 (σ c (w i j) - χ j c • w i j) := by

        simp only [map_sum, map_sub, map_smul, Finset.smul_sum, Finset.sum_sub_distrib, sigcomm]
      rw [this]; exact Submodule.sum_mem _ fun i _ => spread_in G₀ i _ (hw1 i j c)
    · have : d - ∑ j, ∑ i, E i 0 (w i j) = ∑ i, E i 0 (E 0 i d - ∑ j, w i j) := by
        conv_lhs => rw [← decomp d]
        rw [Finset.sum_comm]

        simp only [map_sub, map_sum, Finset.sum_sub_distrib]
      rw [this]; exact Submodule.sum_mem _ fun i _ => spread_in G₀ i _ (hw2 i)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.baseChange_iso_spreads_to_subring : ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ Z : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (q : Z ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFinitePresentation f₀] [QuasiCompact q] [QuasiSeparated q] [LocallyOfFinitePresentation q] (φ : X ⟶ Z), IsPullback π f f₀ (spMap R₀.subtype) → IsPullback φ f q (spMap R₀.subtype) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hle)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ ψ : X₁ ⟶ Z, j ≫ ψ = φ ∧ IsPullback ψ f₁ q (spMap (Subring.inclusion hle)) := by
  first | exact @GlobalTheory.iso_spreads_to_subring | exact GlobalTheory.iso_spreads_to_subring | (intros; apply GlobalTheory.iso_spreads_to_subring <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.identityComponents_smooth_groupScheme_mul_mem : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ w : (G ⊗ G).left, (fst G G).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (snd G G).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (μ[G]).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  first | exact @GlobalTheory.IdCompMul.mul_mem | exact GlobalTheory.IdCompMul.mul_mem | (intros; apply GlobalTheory.IdCompMul.mul_mem <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.mem_mul_preimage_of_mem_unitComponent : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : G.left), (η[G]).left (G.hom y) ∈ U → y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → y ∈ {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by
  first | exact @GlobalTheory.mem_unitComponent_mul_mem | exact GlobalTheory.mem_unitComponent_mul_mem | (intros; apply GlobalTheory.mem_unitComponent_mul_mem <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.stableUnderGeneralization_section_connectedComponentIn : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → StableUnderGeneralization {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  first | exact @GlobalTheory.stableUnderGeneralization_sectionComponents | exact GlobalTheory.stableUnderGeneralization_sectionComponents | (intros; apply GlobalTheory.stableUnderGeneralization_sectionComponents <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_affine_chart_preirreducible_fiber' : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (V : S.Opens) (W : X.Opens) (_ : W ≤ f ⁻¹ᵁ V), IsAffineOpen V ∧ IsAffineOpen W ∧ e s ∈ W ∧ ∀ (k : Type) [Field k] (p : Spec (CommRingCat.of k) ⟶ S), p (IsLocalRing.closedPoint k) = s → PreirreducibleSpace ↥(pullback (W.ι ≫ f) p) := by
  first | exact @GlobalTheory.exists_affine_chart_preirreducible_fiber | exact GlobalTheory.exists_affine_chart_preirreducible_fiber | (intros; apply GlobalTheory.exists_affine_chart_preirreducible_fiber <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.BallStein

variable {n : ℕ}

noncomputable def sqd (c : V n) (y : V n) : ℝ := ‖y - c‖ ^ 2

theorem contDiff_sqd (c : V n) : ContDiff ℝ ∞ (sqd c) :=
  (contDiff_norm_sq ℂ).comp (contDiff_id.sub contDiff_const)

theorem sqd_lt {c y : V n} {r : ℝ} (hy : y ∈ ball c r) : sqd c y < r ^ 2 := by
  have h1 : ‖y - c‖ < r := by simpa [dist_eq_norm] using hy
  have h0 : 0 ≤ ‖y - c‖ := norm_nonneg _
  unfold sqd
  nlinarith

theorem hasDerivAt_k (r t : ℝ) (ht : t < r ^ 2) :
    HasDerivAt (fun t : ℝ => (r ^ 2 - t)⁻¹) (((r ^ 2 - t) ^ 2)⁻¹) t := by
  have hne : r ^ 2 - t ≠ 0 := by linarith
  have := ((hasDerivAt_id t).const_sub (r ^ 2)).inv hne
  refine this.congr_deriv ?_
  simp only [id]
  ring

theorem hasDerivAt_k' (r t : ℝ) (ht : t < r ^ 2) :
    HasDerivAt (fun t : ℝ => ((r ^ 2 - t) ^ 2)⁻¹) (2 * (r ^ 2 - t) / ((r ^ 2 - t) ^ 2) ^ 2) t := by
  have hne : (r ^ 2 - t) ^ 2 ≠ 0 := by
    have : r ^ 2 - t ≠ 0 := by linarith
    positivity
  have h1 := (((hasDerivAt_id t).const_sub (r ^ 2)).pow 2).inv hne
  refine h1.congr_deriv ?_
  simp only [id, Pi.pow_apply]
  norm_num

theorem deriv_k (r t : ℝ) (ht : t < r ^ 2) :
    deriv (fun t : ℝ => (r ^ 2 - t)⁻¹) t = ((r ^ 2 - t) ^ 2)⁻¹ :=
  (hasDerivAt_k r t ht).deriv

theorem deriv_deriv_k (r t : ℝ) (ht : t < r ^ 2) :
    deriv (deriv (fun t : ℝ => (r ^ 2 - t)⁻¹)) t = 2 * (r ^ 2 - t) / ((r ^ 2 - t) ^ 2) ^ 2 := by
  have hev : deriv (fun t : ℝ => (r ^ 2 - t)⁻¹) =ᶠ[𝓝 t] fun t : ℝ => ((r ^ 2 - t) ^ 2)⁻¹ := by
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact deriv_k r u hu
  rw [hev.deriv_eq]
  exact (hasDerivAt_k' r t ht).deriv

theorem leviV_sqd_nonneg (c x : V n) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun y => ((sqd c y : ℝ) : ℂ)) x ξ).re := by
  let u : Fin n → V n → ℝ := fun j y => Complex.normSq (EuclideanSpace.proj j (y - c))
  have hfun : (fun y => ((sqd c y : ℝ) : ℂ)) = fun y => ((∑ j, u j y : ℝ) : ℂ) := by
    funext y
    congr 1
    simp only [sqd, u, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]
    rfl
  have hg : ∀ j : Fin n, ContDiffAt ℂ 2 (fun y : V n => EuclideanSpace.proj j (y - c)) x := fun j =>
    ((EuclideanSpace.proj j : V n →L[ℂ] ℂ).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hu : ∀ j, ContDiffAt ℝ 2 (u j) x := fun j => by
    have hu' : u j = fun y => ‖EuclideanSpace.proj j (y - c)‖ ^ 2 := by
      funext y; simp only [u, Complex.normSq_eq_norm_sq]
    rw [hu']
    exact (contDiff_norm_sq ℂ).contDiffAt.comp x ((hg j).restrict_scalars ℝ)
  rw [hfun, leviV_ofReal_sum hu, Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => ((logPshAt_normSq (hg j)).2 ξ).1

end GlobalTheory.BallStein

namespace GlobalTheory.BallStein

variable {n : ℕ}

noncomputable def exh (c : V n) (r : ℝ) (y : V n) : ℝ := (r ^ 2 - sqd c y)⁻¹

theorem contDiffOn_exh (c : V n) (r : ℝ) : ContDiffOn ℝ ∞ (exh c r) (ball c r) :=
  (contDiffOn_const.sub (contDiff_sqd c).contDiffOn).inv fun _ hy => (sub_pos.2 (sqd_lt hy)).ne'

theorem leviV_exh_nonneg {c y : V n} {r : ℝ} (hy : y ∈ ball c r) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun w => ((exh c r w : ℝ) : ℂ)) y ξ).re := by
  have hlt := sqd_lt hy
  have hp : 0 < r ^ 2 - sqd c y := sub_pos.2 hlt
  have hk : ContDiffAt ℝ 2 (fun t : ℝ => (r ^ 2 - t)⁻¹) (sqd c y) :=
    (contDiffAt_const.sub contDiffAt_id).inv hp.ne'
  have hc := leviChain n (fun t : ℝ => (r ^ 2 - t)⁻¹) (sqd c) y ξ
    (((contDiff_norm_sq ℂ).comp (contDiff_id.sub contDiff_const) : ContDiff ℝ 2 (sqd c)).contDiffAt) hk
  have he : (fun w => ((exh c r w : ℝ) : ℂ)) =
      fun w => (((fun t : ℝ => (r ^ 2 - t)⁻¹) (sqd c w) : ℝ) : ℂ) := rfl
  rw [he, hc, deriv_k r _ hlt, deriv_deriv_k r _ hlt]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  have h1 := leviV_sqd_nonneg c y ξ
  have h2 := Complex.normSq_nonneg (∑ j, wd n j (fun w => ((sqd c w : ℝ) : ℂ)) y * ξ j)
  refine add_nonneg (mul_nonneg (by positivity) h1) (mul_nonneg (by positivity) h2)

theorem isCompact_exh (c : V n) (r a : ℝ) : IsCompact {y | y ∈ ball c r ∧ exh c r y ≤ a} := by
  by_cases hr : r ≤ 0
  · have : {y | y ∈ ball c r ∧ exh c r y ≤ a} = ∅ := by
      ext y; simp [Metric.ball_eq_empty.2 hr]
    rw [this]; exact isCompact_empty
  push_neg at hr
  by_cases ha : a ≤ 0
  · have : {y | y ∈ ball c r ∧ exh c r y ≤ a} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro hy
      have hp : 0 < r ^ 2 - sqd c y := sub_pos.2 (sqd_lt hy)
      exact lt_of_le_of_lt ha (inv_pos.2 hp)
    rw [this]; exact isCompact_empty
  push_neg at ha
  have heq : {y | y ∈ ball c r ∧ exh c r y ≤ a} = {y | sqd c y ≤ r ^ 2 - a⁻¹} := by
    ext y
    simp only [Set.mem_setOf_eq, exh]
    constructor
    · rintro ⟨hy, hle⟩
      have hp : 0 < r ^ 2 - sqd c y := sub_pos.2 (sqd_lt hy)
      have := (inv_le_comm₀ hp ha).1 hle
      linarith
    · intro hle
      have hai : 0 < a⁻¹ := inv_pos.2 ha
      have hp : 0 < r ^ 2 - sqd c y := by linarith
      refine ⟨?_, (inv_le_comm₀ hp ha).2 (by linarith)⟩
      rw [mem_ball, dist_eq_norm]
      by_contra hcon
      push_neg at hcon
      have : r ^ 2 ≤ sqd c y := by unfold sqd; nlinarith
      linarith
  rw [heq]
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (contDiff_sqd c).continuous continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := c) (r := r)).subset fun y hy => ?_
  have hai : 0 < a⁻¹ := inv_pos.2 ha
  have h1 : sqd c y ≤ r ^ 2 := by simp only [Set.mem_setOf_eq] at hy; linarith
  rw [mem_closedBall, dist_eq_norm]
  unfold sqd at h1
  nlinarith [norm_nonneg (y - c)]

theorem ball_etaleStein : ∀ (n : ℕ) (c : V n) (r : ℝ), ∃ X : EtaleStein n (ball c r), X.z = Subtype.val := by
  intro n c r
  have hU : IsOpen (ball c r) := isOpen_ball
  refine ⟨{ z := Subtype.val
            isLocalHomeomorph := ReciprocityTheory.ChartRestriction.G.AR.Up.HE.val_lh hU
            e := fun x => exh c r x.1
            smooth_e := ReciprocityTheory.ChartRestriction.G.AR.Up.HE.smoothR_val (contDiffOn_exh c r)
            levi_e := fun x ξ => by
              rw [ReciprocityTheory.ChartRestriction.G.AR.Up.HE.levi_val hU]
              exact leviV_exh_nonneg x.2 ξ
            isCompact_le := fun a => by
              rw [Subtype.isCompact_iff]
              convert isCompact_exh c r a using 1
              ext y
              constructor
              · rintro ⟨x, hx, rfl⟩
                exact ⟨x.2, hx⟩
              · rintro ⟨hy, hy'⟩
                exact ⟨⟨y, hy⟩, hy', rfl⟩ }, rfl⟩

end GlobalTheory.BallStein
end

section

open Polynomial

theorem _root_.GlobalTheory.T.classGroup_dedekind_algClosed_divisible : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), (q : k) ≠ 0 → ∀ c : ClassGroup B, ∃ d : ClassGroup B, d ^ q = c := by
  first | (exact @GlobalTheory.PicDiv.classGroup_divisible) | (exact GlobalTheory.PicDiv.classGroup_divisible) | (intros; apply GlobalTheory.PicDiv.classGroup_divisible <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.exists_padicInt_charpoly_commute_frobeniusSemilinear : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N] [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N] (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N) (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N), Function.Injective F → (∀ x, u (F x) = F (u x)) → ∃ P : Polynomial ℤ_[p], P.Monic ∧ P.map ψ = u.charpoly := by
  first | exact @GlobalTheory.DieuCharpoly.exists_monic_map_eq_charpoly | exact GlobalTheory.DieuCharpoly.exists_monic_map_eq_charpoly | (intros; apply GlobalTheory.DieuCharpoly.exists_monic_map_eq_charpoly; all_goals assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_ringHom_padicAlgCl_ne_zero' : ∀ (B : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CharZero B], Finite (ResidueField B) → ∀ h : B, h ≠ 0 → ∃ (p : ℕ) (_ : Fact p.Prime) (χ : B →+* PadicAlgCl p), (∀ b, ‖χ b‖ ≤ 1) ∧ (∀ b ∈ maximalIdeal B, ‖χ b‖ < 1) ∧ χ h ≠ 0 := by
  first | exact @GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero | exact GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero | (intros; apply GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.wittVector_colength_range_eq_det_valuation : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N] [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N] (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N) (d : ℤ_[p]), LinearMap.det u = ψ d → (∀ e : ℕ, Module.length (WittVector p k) (N ⧸ LinearMap.range u) = e → ‖d‖ = (p : ℝ) ^ (-(e : ℤ))) ∧ (¬ Function.Injective u → d = 0) ∧ Function.Injective ψ := by
  first | exact @GlobalTheory.Dieu.ColenDet.colength_det | exact GlobalTheory.Dieu.ColenDet.colength_det | (intros; apply GlobalTheory.Dieu.ColenDet.colength_det <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.length_ge_finrank_of_semilinear_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N U : Type) [AddCommGroup N] [Module (WittVector p k) N] [AddCommGroup U] [Module k U] [Module.Finite k U] (e : (WittVector p k) ≃+* (WittVector p k)) (θ : N →+ U), Function.Surjective θ → (∀ (a : (WittVector p k)) n, θ (e a • n) = WittVector.constantCoeff a • θ n) → ∀ L : Submodule (WittVector p k) N, ((∀ n ∈ L, θ n = 0) → (Module.finrank k U : ℕ∞) ≤ Module.length (WittVector p k) (N ⧸ L)) ∧ ((∀ n, n ∈ L ↔ θ n = 0) → Module.length (WittVector p k) (N ⧸ L) = Module.finrank k U) := by
  first | exact @GlobalTheory.Dieu.length_ge_finrank_of_semilinear_surj | exact GlobalTheory.Dieu.length_ge_finrank_of_semilinear_surj | (intros; apply GlobalTheory.Dieu.length_ge_finrank_of_semilinear_surj <;> assumption)
end
