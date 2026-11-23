module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
theorem _root_.GlobalTheory.exists_grpObj_over_of_points : ∀ (S : Scheme.{0}) (X : Over S) (e : 𝟙_ _ ⟶ X) (m : X ⊗ X ⟶ X) (n : X ⟶ X), (∀ (T : Over S) (x : T ⟶ X), lift (toUnit T ≫ e) x ≫ m = x) → (∀ (T : Over S) (x : T ⟶ X), lift (x ≫ n) x ≫ m = toUnit T ≫ e) → (∀ (T : Over S) (x y : T ⟶ X), lift x y ≫ m = lift y x ≫ m) → (∀ (T : Over S) (x y z : T ⟶ X), lift (lift x y ≫ m) z ≫ m = lift x (lift y z ≫ m) ≫ m) → ∃ G : GrpObj X, η[X] = e ∧ μ[X] = m ∧ (GrpObj.inv : X ⟶ X) = n ∧ IsCommMonObj X := by
  intro S X e m n hl hinv hcomm hassoc
  have hr : ∀ (T : Over S) (x : T ⟶ X), lift x (toUnit T ≫ e) ≫ m = x := fun T x => by
    rw [hcomm, hl]
  let M : MonObj X :=
    { one := e
      mul := m
      one_mul := by
        have : e ▷ X = lift (toUnit _ ≫ e) (snd _ _) := by
          apply hom_ext
          · simp only [whiskerRight_fst, lift_fst]
            rw [toUnit_unique (fst _ _) (toUnit _)]
          · simp only [whiskerRight_snd, lift_snd]
        rw [this, hl, leftUnitor_hom]
      mul_one := by
        have : X ◁ e = lift (fst _ _) (toUnit _ ≫ e) := by
          apply hom_ext
          · simp only [whiskerLeft_fst, lift_fst]
          · simp only [whiskerLeft_snd, lift_snd]
            rw [toUnit_unique (snd _ _) (toUnit _)]
        rw [this, hr, rightUnitor_hom]
      mul_assoc := by
        have h1 : m ▷ X = lift (lift (fst _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _) ≫ m) (snd _ _) := by
          apply hom_ext
          · simp only [whiskerRight_fst, lift_fst]
            rw [← comp_lift, lift_fst_snd, Category.comp_id]
          · simp only [whiskerRight_snd, lift_snd]
        have h2 : (α_ X X X).hom ≫ X ◁ m =
            lift (fst _ _ ≫ fst _ _) (lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ m) := by
          apply hom_ext
          · simp only [Category.assoc, whiskerLeft_fst, associator_hom_fst, lift_fst]
          · simp only [Category.assoc, whiskerLeft_snd, lift_snd]
            have h3 : (α_ X X X).hom ≫ snd _ _ = lift (fst _ _ ≫ snd _ _) (snd _ _) := by
              apply hom_ext <;>
                simp only [lift_fst, lift_snd, Category.assoc, associator_hom_snd_fst,
                  associator_hom_snd_snd]
            rw [reassoc_of% h3]
        rw [h1, reassoc_of% h2, hassoc] }
  let G : GrpObj X :=
    { inv := n
      left_inv := by
        show lift n (𝟙 X) ≫ m = toUnit X ≫ e
        simpa using hinv X (𝟙 X)
      right_inv := by
        show lift (𝟙 X) n ≫ m = toUnit X ≫ e
        rw [hcomm]
        simpa using hinv X (𝟙 X) }
  refine ⟨G, rfl, rfl, rfl, ⟨?_⟩⟩
  have : (β_ X X).hom = lift (snd _ _) (fst _ _) := by
    apply hom_ext <;> simp only [braiding_hom_fst, braiding_hom_snd, lift_fst, lift_snd]
  rw [this]
  show lift (snd X X) (fst X X) ≫ m = m
  rw [hcomm, lift_fst_snd, Category.id_comp]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_periodPair_of_lattice_in_line :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (w : Fin g → ℂ), g = 1 → w ≠ 0 → DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∃ L : PeriodPair, ∀ z : ℂ, z ∈ L.lattice ↔ z • w ∈ Λ := by
  intro g Λ w hg hw hdisc hspan
  subst hg
  have hw0 : w 0 ≠ 0 := by
    intro h
    apply hw
    funext j
    fin_cases j
    simpa using h

  obtain ⟨e, he⟩ : ∃ e : ℂ ≃L[ℝ] (Fin 1 → ℂ), ∀ z, e z = z • w := by
    let φ : ℂ →ₗ[ℝ] (Fin 1 → ℂ) :=
      { toFun := fun z => z • w
        map_add' := fun a b => add_smul a b w
        map_smul' := fun r z => by
          simp only [RingHom.id_apply]
          exact smul_assoc r z w }
    have hinj : Function.Injective φ := fun a b h => smul_left_injective ℂ hw h
    have hsurj : Function.Surjective φ := by
      intro y
      refine ⟨y 0 / w 0, ?_⟩
      funext j
      fin_cases j
      simp [φ, hw0]
    exact ⟨(LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun z => rfl⟩

  have : DiscreteTopology Λ := hdisc
  have : IsZLattice ℝ Λ := ⟨hspan⟩
  set Λ' := ZLattice.comap ℝ Λ e.toLinearMap with hΛ'
  have hrank : Module.finrank ℤ Λ' = 2 := by
    rw [ZLattice.rank ℝ Λ', Complex.finrank_real_complex]
  set b := Module.finBasisOfFinrankEq ℤ Λ' hrank with hb
  set bR := b.ofZLatticeBasis ℝ Λ' with hbR
  refine ⟨⟨bR 0, bR 1, ?_⟩, fun z => ?_⟩
  · have hv : ![bR 0, bR 1] = ⇑bR := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact bR.linearIndependent
  · have hr : ({bR 0, bR 1} : Set ℂ) = Set.range bR := by
      ext x
      simp [Fin.exists_fin_two, eq_comm]
    rw [PeriodPair.lattice]
    dsimp only
    rw [hr, hbR, Module.Basis.ofZLatticeBasis_span, ← SetLike.mem_coe, hΛ', ZLattice.coe_comap]
    simp [he]

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

theorem eq_or_eq_neg_of_purelyImaginary_of_norm_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ξ ξ' : E) (τ : E →+* ℂ),
      cc ξ = -ξ → cc ξ' = -ξ' → ‖τ ξ‖ = ‖τ ξ'‖ → ξ' = ξ ∨ ξ' = -ξ := by
  intro E _ _ _ ξ ξ' τ h h' hn
  have key : ∀ x : E, cc x = -x → τ (x ^ 2) = -((‖τ x‖ ^ 2 : ℝ) : ℂ) := by
    intro x hx
    have h1 : τ (cc x) = (starRingEnd ℂ) (τ x) := IsCMField.complexEmbedding_complexConj E τ x
    rw [hx, map_neg] at h1
    have h2 := Complex.mul_conj' (τ x)
    rw [← h1] at h2
    rw [map_pow]
    push_cast
    linear_combination -h2
  have h3 : τ (ξ' ^ 2) = τ (ξ ^ 2) := by rw [key ξ h, key ξ' h', hn]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (τ.injective h3)

end GlobalTheory
end
