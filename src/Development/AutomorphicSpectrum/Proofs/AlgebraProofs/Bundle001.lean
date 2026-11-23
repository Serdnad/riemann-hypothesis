module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Filtration

@[expose] public section

section

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem mem_ideal_smul_top_iff_coord {O : Type} [CommRing O] {L : Type} [AddCommGroup L]
    [Module O L] (s : L →ₗ[O] (L →₀ O))
    (hs : Function.LeftInverse (Finsupp.linearCombination O (id : L → L)) s)
    (𝔠 : Ideal O) (x : L) :
    x ∈ 𝔠 • (⊤ : Submodule O L) ↔ ∀ i, s x i ∈ 𝔠 := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr n _ i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact 𝔠.mul_mem_right _ hr
    · intro a b ha hb i
      rw [map_add (f := _), Finsupp.add_apply]
      exact 𝔠.add_mem (ha i) (hb i)
  · intro h
    rw [← hs x, Finsupp.linearCombination_apply, Finsupp.sum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem ideal_inf_smul_top_of_projective : ∀ (O : Type) [CommRing O] (L : Type) [AddCommGroup L] [Module O L] [Module.Projective O L] (𝔞 𝔟 : Ideal O), (𝔞 ⊓ 𝔟) • (⊤ : Submodule O L) = 𝔞 • (⊤ : Submodule O L) ⊓ 𝔟 • (⊤ : Submodule O L) := by
  intro O _ L _ _ hP 𝔞 𝔟
  obtain ⟨s, hs⟩ := Module.projective_def.1 hP
  ext x
  rw [Submodule.mem_inf, GlobalTheory.CompanionTheory.Ar.Cmp.mem_ideal_smul_top_iff_coord s hs,
    GlobalTheory.CompanionTheory.Ar.Cmp.mem_ideal_smul_top_iff_coord s hs,
    GlobalTheory.CompanionTheory.Ar.Cmp.mem_ideal_smul_top_iff_coord s hs]
  simp only [Submodule.mem_inf, forall_and]

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.DualFlag

theorem abel_sum_rev : ∀ (n : ℕ) (b : Fin (n + 1) → ℝ) (e : Fin (n + 2) → ℝ), e 0 = 0 →
    (∑ i : Fin (n + 1), b i * (e i.rev.succ - e i.rev.castSucc)) =
      (∑ i : Fin n, (b i.castSucc - b i.succ) * (-e i.rev.succ.castSucc)) +
        b 0 * e (Fin.last (n + 1)) := by
  intro n
  induction n with
  | zero =>
    intro b e h0
    simp [h0]
  | succ n ih =>
    intro b e h0
    have h := ih (fun i => b i.succ) (fun i => e i.castSucc) (by simpa using h0)
    have hL := Fin.sum_univ_succ (fun i : Fin (n + 2) => b i * (e i.rev.succ - e i.rev.castSucc))
    have hR := Fin.sum_univ_succ
      (fun i : Fin (n + 1) => (b i.castSucc - b i.succ) * (-e i.rev.succ.castSucc))
    simp only [Fin.rev_succ, Fin.rev_zero, Fin.succ_last, Fin.castSucc_zero,
      Fin.succ_zero_eq_one, Fin.succ_castSucc] at h hL hR
    rw [hL, hR]
    linear_combination h

end GlobalTheory.CompanionTheory.DualFlag
end

section

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.AbelFlag

theorem abel_summation_flag : ∀ (n : ℕ) (a : Fin (n + 1) → ℝ) (d : Fin (n + 2) → ℝ), d 0 = 0 →
    -(∑ i : Fin (n + 1), a i * (d i.succ - d i.castSucc)) =
      (∑ i : Fin n, (a i.castSucc - a i.succ) * (-d i.succ.castSucc))
        + a (Fin.last n) * (-d (Fin.last (n + 1))) := by
  intro n
  induction n with
  | zero =>
    intro a d h
    simp [h]
  | succ n ih =>
    intro a d h
    have key := ih (fun i => a i.castSucc) (fun i => d i.castSucc) (by simpa using h)
    rw [Fin.sum_univ_castSucc (n := n + 1), Fin.sum_univ_castSucc (n := n)
      (f := fun i : Fin (n + 1) => (a i.castSucc - a i.succ) * (-d i.succ.castSucc))]
    simp only [Fin.succ_castSucc, Fin.succ_last] at key ⊢
    linear_combination key

end GlobalTheory.CompanionTheory.AbelFlag
end

section

namespace GlobalTheory.CompanionTheory.Telescope

theorem telescope_fin_positions (α : Type) (n : ℕ) (F : (Fin n → α) → ℝ) (a b : Fin n → α) :
    F a - F b = ∑ i : Fin n, (F (fun j => if j < i then b j else a j) - F (fun j => if j ≤ i then b j else a j)) := by
  classical
  set G : ℕ → ℝ := fun m => F (fun j => if (j : ℕ) < m then b j else a j) with hG
  have h0 : G 0 = F a := by simp [hG]
  have hn : G n = F b := by simp [hG]
  rw [← h0, ← hn, ← Finset.sum_range_sub' G n, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hG, Nat.lt_succ_iff, Fin.lt_def, Fin.le_def]

end GlobalTheory.CompanionTheory.Telescope
end

section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_basis_split_of_exact_of_fg_valuationRing :
    ∀ (V C A W B : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C]
      [IsFractionRing V C] [AddCommGroup A] [Module C A] [Module V A] [IsScalarTower V C A]
      [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [AddCommGroup B]
      [Module C B] [Module V B] [IsScalarTower V C B] (b : A →ₗ[C] W) (al : W →ₗ[C] B),
      Function.Injective b → Function.Exact b al → ∀ (T : Submodule V W), T.FG →
      ∃ (p q : ℕ) (w : Fin p → A) (t : Fin q → W), LinearIndependent C w ∧
        Submodule.span V (Set.range w) = T.comap (b.restrictScalars V) ∧
        LinearIndependent C (fun j => al (t j)) ∧
        Submodule.span V (Set.range fun j => al (t j)) = T.map (al.restrictScalars V) ∧
        LinearIndependent C (Sum.elim (fun i => b (w i)) t) ∧
        Submodule.span V (Set.range (Sum.elim (fun i => b (w i)) t)) = T := by
  intro V C A W B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b al hb hex T hT
  have : IsBezout V := ValuationRing.instIsBezout

  have hfree : ∀ (X : Type) [AddCommGroup X] [Module C X] [Module V X] [IsScalarTower V C X]
      (N : Submodule V X), N.FG → Module.Free V N := by
    intro X _ _ _ _ N hN
    have : Module.Finite V N := Module.Finite.iff_fg.mpr hN
    have : Module.Flat V N := by
      rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
      have h2 : ((a : V) • x : N) = 0 := ha
      have h3 : (a : V) • (x : X) = 0 := by
        have h4 := congrArg Subtype.val h2
        simpa using h4
      have h1 : (algebraMap V C (a : V)) • (x : X) = 0 := by
        rw [algebraMap_smul]; exact h3
      have ha0 : algebraMap V C (a : V) ≠ 0 := by
        intro h
        have h5 : (a : V) = 0 := (IsFractionRing.injective V C) (by rw [h, map_zero])
        exact nonZeroDivisors.coe_ne_zero a h5
      have hx0 : (x : X) = 0 := (smul_eq_zero.mp h1).resolve_left ha0
      exact Subtype.ext (by simp [hx0])
    exact Module.free_of_flat_of_isLocalRing

  have hL : ∀ (X : Type) [AddCommGroup X] [Module C X] [Module V X] [IsScalarTower V C X]
      (N : Submodule V X), N.FG → ∃ (n : ℕ) (v : Fin n → X),
        LinearIndependent C v ∧ Submodule.span V (Set.range v) = N := by
    intro X _ _ _ _ N hN
    have := hfree X N hN
    have : Module.Finite V N := Module.Finite.iff_fg.mpr hN
    let e := (Module.Free.chooseBasis V N).reindex
      (Fintype.equivFin (Module.Free.ChooseBasisIndex V N))
    refine ⟨Fintype.card (Module.Free.ChooseBasisIndex V N), fun i => (e i : X), ?_, ?_⟩
    · rw [← LinearIndependent.iff_fractionRing V C]
      exact e.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
    · have hr : Set.range (fun i => (e i : X)) = N.subtype '' Set.range e := by
        rw [← Set.range_comp]; rfl
      rw [hr, Submodule.span_image, e.span_eq, Submodule.map_subtype_top]

  obtain ⟨q, u, hu, hus⟩ := hL B (T.map (al.restrictScalars V)) (hT.map _)
  have hu_mem : ∀ j, u j ∈ T.map (al.restrictScalars V) := by
    intro j
    rw [← hus]
    exact Submodule.subset_span ⟨j, rfl⟩
  choose t ht hta using fun j => Submodule.mem_map.mp (hu_mem j)
  have hta' : ∀ j, al (t j) = u j := fun j => hta j
  have hal : (fun j => al (t j)) = u := funext hta'

  have : Module.Free V (T.map (al.restrictScalars V)) := hfree B _ (hT.map _)
  have : Module.Finite V (T.map (al.restrictScalars V)) := Module.Finite.iff_fg.mpr (hT.map _)
  have : Module.Finite V T := Module.Finite.iff_fg.mpr hT
  have : Module.FinitePresentation V (T.map (al.restrictScalars V)) :=
    Module.finitePresentation_of_projective V _
  have hker : (LinearMap.ker ((al.restrictScalars V).submoduleMap T)).FG :=
    Module.FinitePresentation.fg_ker _ (LinearMap.submoduleMap_surjective _ _)
  have hK : (T.comap (b.restrictScalars V)).FG := by
    apply Submodule.fg_of_fg_map_injective (b.restrictScalars V) hb
    have heq : (T.comap (b.restrictScalars V)).map (b.restrictScalars V)
        = (LinearMap.ker ((al.restrictScalars V).submoduleMap T)).map T.subtype := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨⟨b a, ha⟩, ?_, rfl⟩
        show ((al.restrictScalars V).submoduleMap T) ⟨b a, ha⟩ = 0
        apply Subtype.ext
        show al (b a) = 0
        exact (hex (b a)).mpr ⟨a, rfl⟩
      · rintro ⟨⟨y, hyT⟩, hy0, rfl⟩
        have hy0' : ((al.restrictScalars V).submoduleMap T) ⟨y, hyT⟩ = 0 := hy0
        have hy : al y = 0 := congrArg Subtype.val hy0'
        obtain ⟨a, rfl⟩ := (hex y).mp hy
        exact ⟨a, hyT, rfl⟩
    rw [heq]
    exact hker.map _
  obtain ⟨p, w, hw, hws⟩ := hL A (T.comap (b.restrictScalars V)) hK
  refine ⟨p, q, w, t, hw, hws, ?_, ?_, ?_, ?_⟩
  · rw [hal]; exact hu
  · rw [hal]; exact hus
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    have h1 : ∀ i, al (b (w i)) = 0 := fun i => (hex _).mpr ⟨w i, rfl⟩
    have h2 : ∑ j, g (Sum.inr j) • u j = 0 := by
      have h7 := congrArg al hg

      simpa [map_add (f := _), map_sum, map_smul, h1, hta'] using h7
    have h3 : ∀ j, g (Sum.inr j) = 0 :=
      Fintype.linearIndependent_iff.mp hu (fun j => g (Sum.inr j)) h2
    have h4 : ∑ i, g (Sum.inl i) • b (w i) = 0 := by
      simpa [h3] using hg
    have h5 : ∑ i, g (Sum.inl i) • w i = 0 := by
      apply hb

      simpa [map_sum, map_smul] using h4
    have h6 := Fintype.linearIndependent_iff.mp hw (fun i => g (Sum.inl i)) h5
    intro i
    cases i with
    | inl i => exact h6 i
    | inr j => exact h3 j
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      cases i with
      | inl i =>
        have hwi : w i ∈ T.comap (b.restrictScalars V) := by
          rw [← hws]; exact Submodule.subset_span ⟨i, rfl⟩
        exact hwi
      | inr j => exact ht j
    · intro x hx
      have hax : al x ∈ T.map (al.restrictScalars V) := Submodule.mem_map_of_mem hx
      rw [← hus, Submodule.mem_span_range_iff_exists_fun] at hax
      obtain ⟨c, hc⟩ := hax
      have hyal : al (x - ∑ j, c j • t j) = 0 := by

        rw [map_sub, map_sum]
        simp only [LinearMap.map_smul_of_tower, hta']
        rw [hc, sub_self]
      obtain ⟨a, ha⟩ := (hex _).mp hyal
      have haK : a ∈ T.comap (b.restrictScalars V) := by
        show b a ∈ T
        rw [ha]
        exact T.sub_mem hx (T.sum_mem fun j _ => T.smul_mem (c j) (ht j))
      rw [← hws] at haK
      have hx_eq : x = b a + ∑ j, c j • t j := by rw [ha]; abel
      rw [hx_eq, Set.Sum.elim_range, Submodule.span_union]
      apply Submodule.add_mem_sup
      · have hr : Set.range (fun i => b (w i)) = (b.restrictScalars V) '' Set.range w := by
          rw [← Set.range_comp]; rfl
        rw [hr, Submodule.span_image]
        exact Submodule.mem_map_of_mem haK
      · exact Submodule.sum_mem _ fun j _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.KrullGroupAlg

theorem coeff_mem_of_mem_map {R M : Type} [CommRing R] [AddCommGroup M] (I : Ideal R)
    (x : AddMonoidAlgebra R M) (hx : x ∈ Ideal.map (algebraMap R (AddMonoidAlgebra R M)) I)
    (φ : AddMonoidAlgebra R M →ₗ[R] R) : φ x ∈ I := by
  have hx' : x ∈ Submodule.span (AddMonoidAlgebra R M) (algebraMap R (AddMonoidAlgebra R M) '' I) := hx
  clear hx
  revert φ
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    intro φ
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
    exact I.mul_mem_right _ ha
  | zero =>
    intro φ
    rw [map_zero]
    exact I.zero_mem
  | add y z _ _ hy hz =>
    intro φ
    rw [map_add (f := _)]
    exact I.add_mem (hy φ) (hz φ)
  | smul r y _ hy =>
    intro φ
    have := hy (φ ∘ₗ LinearMap.mulLeft R r)
    simpa [smul_eq_mul] using this

theorem eq_zero_of_mem_map_pow : ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M] (x : AddMonoidAlgebra R M), (∀ n : ℕ, x ∈ Ideal.map (algebraMap R (AddMonoidAlgebra R M)) (IsLocalRing.maximalIdeal R ^ n)) → x = 0 := by
  intro R M _ _ _ _ x hx
  ext m
  have hm : (Finsupp.lapply m ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap) x ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal R ^ n :=
    Ideal.mem_iInf.2 fun n =>
      coeff_mem_of_mem_map _ x (hx n) (Finsupp.lapply m ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_bot] at hm
  simpa using hm

end GlobalTheory.CompanionTheory.KrullGroupAlg
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.FreeQuotProof

def HasAffineChart {P X : Scheme.{0}} (a b : P ⟶ X) (V : X.Opens) : Prop :=
  a ⁻¹ᵁ V = b ⁻¹ᵁ V ∧
    ∃ (Y : Scheme.{0}) (q : V.toScheme ⟶ Y) (a' : (b ⁻¹ᵁ V).toScheme ⟶ V.toScheme),
      IsAffine Y ∧ IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
        a' ≫ V.ι = (b ⁻¹ᵁ V).ι ≫ a ∧ IsPullback a' (b ∣_ V) q q

end GlobalTheory.CompanionTheory.FreeQuotProof
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.QuotientSide

theorem isSeparated_of_finite_surjective {S X Y : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S)
    (r : X ⟶ Y) (w : r ≫ g = f) [IsSeparated f] [IsFinite r] [Surjective r] : IsSeparated g := by
  subst w
  let m : pullback (r ≫ g) (r ≫ g) ⟶ pullback g g :=
    pullback.map _ _ _ _ r r (𝟙 S) (by simp) (by simp)
  have hm : IsFinite m :=
    MorphismProperty.pullbackMap (P := @IsFinite) (i₁ := r) (i₂ := r) inferInstance inferInstance
      rfl rfl
  have comm : pullback.diagonal (r ≫ g) ≫ m = r ≫ pullback.diagonal g := by
    have h₁ : m ≫ pullback.fst g g = pullback.fst (r ≫ g) (r ≫ g) ≫ r := pullback.lift_fst _ _ _
    have h₂ : m ≫ pullback.snd g g = pullback.snd (r ≫ g) (r ≫ g) ≫ r := pullback.lift_snd _ _ _
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, h₁, ← Category.assoc, pullback.diagonal_fst,
        pullback.diagonal_fst, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, Category.assoc, h₂, ← Category.assoc, pullback.diagonal_snd,
        pullback.diagonal_snd, Category.id_comp, Category.comp_id]
  have hrange : Set.range (pullback.diagonal g) =
      m '' Set.range (pullback.diagonal (r ≫ g)) := by
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, comm,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr r.surjective, Set.image_univ]
  have hclosed : IsClosed (Set.range (pullback.diagonal g)) := by
    rw [hrange]
    exact m.isClosedMap _ (pullback.diagonal (r ≫ g)).isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩

theorem isSeparated_target_of_finite_surjective :
    ∀ {S : Scheme.{0}} {X Y K : Over S} (q : X ⟶ Y) (p₁ p₂ : K ⟶ X), IsPullback p₁ p₂ q q →
      IsFinite p₂.left → IsSeparated X.hom → IsFinite q.left → Surjective q.left →
      IsSeparated Y.hom := by
  intro S X Y K q p₁ p₂ _ _ hX hq hs
  exact isSeparated_of_finite_surjective X.hom Y.hom q.left (Over.w q)

end GlobalTheory.CompanionTheory.QuotientSide
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fcIndep_det_ne_zero_of_rank {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (h : B.rank = n) :
    B.det ≠ 0 := by
  have hs : Function.Surjective B.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    simpa [← Matrix.finrank_range_mulVecLin] using h
  have hu : IsUnit B := Matrix.mulVec_surjective_iff_isUnit.mp hs
  exact ((Matrix.isUnit_iff_isUnit_det B).mp hu).ne_zero

theorem fcIndep : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ) (Φ : Matrix (Fin q ⊕ Fin p) (Fin q) ℂ), A * Φ = 0 → A.rank = p → Φ.rank = q → (Φᴴ * Φ).det ≠ 0 ∧ (fromRows Φᴴ A).det ≠ 0 ∧ ∀ N : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ, (fromRows N A).det * (Φᴴ * Φ).det = (fromRows Φᴴ A).det * (N * Φ).det := by
  intro p q A Φ h0 hA hΦ
  have h1 : (Φᴴ * Φ).det ≠ 0 := by
    apply fcIndep_det_ne_zero_of_rank
    open ComplexOrder in rw [Matrix.rank_conjTranspose_mul_self, hΦ]
  have h2 : (A * Aᴴ).det ≠ 0 := by
    apply fcIndep_det_ne_zero_of_rank
    open ComplexOrder in rw [Matrix.rank_self_mul_conjTranspose, hA]
  have key : ∀ N : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ,
      (fromRows N A).det * (fromCols Φ Aᴴ).det = (N * Φ).det * (A * Aᴴ).det := by
    intro N
    rw [← Matrix.det_mul, Matrix.fromRows_mul_fromCols, h0, Matrix.det_fromBlocks_zero₂₁]
  have h3 : (fromRows Φᴴ A).det * (fromCols Φ Aᴴ).det ≠ 0 := by
    rw [key]; exact mul_ne_zero h1 h2
  refine ⟨h1, left_ne_zero_of_mul h3, fun N => ?_⟩
  apply mul_right_cancel₀ (right_ne_zero_of_mul h3)
  have a := key N
  have b := key Φᴴ
  linear_combination (Φᴴ * Φ).det * a - (N * Φ).det * b

end GlobalTheory.CompanionTheory.Ar.Flat
end
