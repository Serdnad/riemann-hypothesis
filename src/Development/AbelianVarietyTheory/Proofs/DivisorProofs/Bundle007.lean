module

public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.LinearAlgebra.Basis.MulOpposite
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section

section

noncomputable section
open scoped TensorProduct
open Module

namespace GlobalTheory.LocAzumaya

variable {A Λ : Type*} [CommRing A] [Ring Λ] [Algebra A Λ] {ι : Type*} [Fintype ι] [DecidableEq ι]

def structMat (b : Basis ι A Λ) : Matrix (ι × ι) (ι × ι) A :=
  LinearMap.toMatrix (b.tensorProduct b.mulOpposite) b.end (AlgHom.mulLeftRight A Λ).toLinearMap

theorem stdBasis_repr_apply' (M : Matrix ι ι A) (k l : ι) :
    (Matrix.stdBasis A ι ι).repr M (k, l) = M k l := rfl

theorem repr_equiv_apply {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {κ : Type*} (b₁ : Basis κ A M) (b₂ : Basis κ A N) (x : M) :
    b₂.repr (b₁.equiv b₂ (Equiv.refl κ) x) = b₁.repr x := by
  simp [Basis.equiv]

theorem structMat_apply (b : Basis ι A Λ) (k l i j : ι) :
    structMat b (k, l) (i, j) = b.repr (b i * b l * b j) k := by
  rw [structMat, LinearMap.toMatrix_apply]
  simp [Basis.end_repr_apply, Basis.tensorProduct_apply, LinearMap.toMatrix_apply, stdBasis_repr_apply']

theorem bijective_iff_isUnit_det (b : Basis ι A Λ) :
    Function.Bijective (AlgHom.mulLeftRight A Λ) ↔ IsUnit (structMat b).det := by
  set c := b.tensorProduct b.mulOpposite
  set f := (AlgHom.mulLeftRight A Λ).toLinearMap
  haveI := Module.Free.of_basis c
  haveI := Module.Finite.of_basis c
  let e : Module.End A Λ ≃ₗ[A] Λ ⊗[A] Λᵐᵒᵖ := b.end.equiv c (Equiv.refl _)
  have hM : structMat b = LinearMap.toMatrix c c (e.toLinearMap ∘ₗ f) := by
    ext p q
    rw [structMat, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, repr_equiv_apply]
  rw [hM, LinearMap.det_toMatrix, ← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff]
  constructor
  · intro h; exact e.bijective.comp h
  · intro h
    have := e.symm.bijective.comp h
    simpa [Function.comp_def, f] using this

end GlobalTheory.LocAzumaya
end
end

section

open scoped Classical

namespace GlobalTheory

theorem finsum_ite_eq_of_equiv {A B : Type} (PA : A → Prop) (PB : B → Prop)
    (e : {a // PA a} ≃ {b // PB b}) (g : A → ℂ) (h : B → ℂ)
    (hgh : ∀ a, h (e a).1 = g a.1) :
    (∑ᶠ a, if PA a then g a else 0) = ∑ᶠ b, if PB b then h b else 0 := by
  have hA : (∑ᶠ a, if PA a then g a else 0) = ∑ᶠ a : {a // PA a}, g a.1 := by
    rw [finsum_subtype_eq_finsum_cond]
    exact finsum_congr fun a => (finsum_eq_if).symm
  have hB : (∑ᶠ b, if PB b then h b else 0) = ∑ᶠ b : {b // PB b}, h b.1 := by
    rw [finsum_subtype_eq_finsum_cond]
    exact finsum_congr fun b => (finsum_eq_if).symm
  rw [hA, hB, ← finsum_comp_equiv e]
  exact finsum_congr fun a => (hgh a).symm

end GlobalTheory
end

section

namespace GlobalTheory

theorem unfold_sum_conj_invariant : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ F : P → ℂ, (∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) → ∀ k ∈ KM, ∀ y : P, (∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * ((s k)⁻¹ * y * s k) * u (Quotient.out x))) = ∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * y * u (Quotient.out x)) := by
  intro P M N _ _ _ s π u hπs hu hker KP KM L hsK hπK hL F hF k hk y
  set c := s k with hc_def
  have hc : c ∈ KP := hsK k hk
  have hπu : ∀ X, π (u X) = 1 := fun X => (hker _).2 ⟨X, rfl⟩
  have hex : ∀ (d : P), ∀ X, ∃ Y, u Y = d * u X * d⁻¹ := by
    intro d X
    exact (hker _).1 (by simp [map_mul, map_inv, hπu])
  choose φ hφ using hex c
  choose ψ hψ using hex c⁻¹
  have h1 : ∀ X, φ (ψ X) = X := fun X => hu (by rw [hφ, hψ]; group)
  have h2 : ∀ X, ψ (φ X) = X := fun X => hu (by rw [hψ, hφ]; group)
  have hconj : ∀ z, c * z * c⁻¹ ∈ KP ↔ z ∈ KP := by
    intro z
    constructor
    · intro h
      have := KP.mul_mem (KP.mul_mem (KP.inv_mem hc) h) hc
      simpa [mul_assoc] using this
    · intro h
      exact KP.mul_mem (KP.mul_mem hc h) (KP.inv_mem hc)
  let eN : N ≃ N := ⟨φ, ψ, h2, h1⟩
  let e : N ⧸ L ≃ N ⧸ L := Quotient.congr eN (by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← hL, ← hL]
    simp only [eN, Equiv.coe_fn_mk, map_mul, map_inv, hφ]
    rw [← hconj]
    constructor <;> intro h <;> convert h using 1 <;> group)
  conv_rhs => rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro x
  set X := Quotient.out x with hX
  have hex' : e x = (QuotientGroup.mk (φ X) : N ⧸ L) := by
    conv_lhs => rw [← Quotient.out_eq x]
    rfl
  set Z := Quotient.out (e x) with hZ
  have hZL : Z⁻¹ * φ X ∈ L := by
    apply QuotientGroup.eq.mp
    rw [← hex']
    exact Quotient.out_eq _
  have hw : u (Z⁻¹ * φ X) ∈ KP := (hL _).2 hZL
  calc F ((u X)⁻¹ * (c⁻¹ * y * c) * u X) = F (c⁻¹ * ((u (φ X))⁻¹ * y * u (φ X)) * c) := by
        congr 1; rw [hφ]; group
    _ = F ((u (φ X))⁻¹ * y * u (φ X)) := hF c hc _
    _ = F ((u Z * u (Z⁻¹ * φ X))⁻¹ * y * (u Z * u (Z⁻¹ * φ X))) := by
        rw [← map_mul, mul_inv_cancel_left]
    _ = F ((u (Z⁻¹ * φ X))⁻¹ * ((u Z)⁻¹ * y * u Z) * u (Z⁻¹ * φ X)) := by
        congr 1; group
    _ = F ((u Z)⁻¹ * y * u Z) := hF _ hw _

end GlobalTheory
end

section

open Filter
open scoped Classical

namespace GlobalTheory.DoubleCosetEuler

theorem finsum_doubleCoset_trivial_eq_one (H : Type) [Group H] (TH KH : Subgroup H) (f : H → ℂ)
    (hf : ∀ x, f x = if ∃ t ∈ TH, ∃ k ∈ KH, x = t * k then 1 else 0) :
    ∑ᶠ q : DoubleCoset.Quotient (TH : Set H) (KH : Set H), f (Quotient.out q) = 1 := by
  have h1 : ∀ q : DoubleCoset.Quotient (TH : Set H) (KH : Set H), q ≠ DoubleCoset.mk TH KH 1 →
      f (Quotient.out q) = 0 := by
    intro q hq
    rw [hf, if_neg]
    rintro ⟨t, ht, k, hk, he⟩
    apply hq
    rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
    exact ⟨t⁻¹, inv_mem ht, k⁻¹, inv_mem hk, by rw [he]; group⟩
  rw [finsum_eq_single _ (DoubleCoset.mk TH KH 1) h1, hf, if_pos]
  obtain ⟨a, ha, b, hb, he⟩ := DoubleCoset.mk_out_eq_mul TH KH (1 : H)
  exact ⟨a, ha, b, hb, by rw [he, mul_one]⟩

theorem finsum_pi_prod_eq_prod_finsum (J : Type) [Fintype J] (α : J → Type) (f : ∀ j, α j → ℂ)
    (hf : ∀ j, (Function.support (f j)).Finite) :
    ∑ᶠ y : (∀ j, α j), ∏ j, f j (y j) = ∏ j, ∑ᶠ a, f j a := by
  have hR : ∀ j, ∑ᶠ a, f j a = ∑ a ∈ (hf j).toFinset, f j a := fun j =>
    finsum_eq_sum_of_support_subset _ (by simp)
  simp_rw [hR]
  rw [Finset.prod_univ_sum]
  apply finsum_eq_sum_of_support_subset
  intro y hy
  rw [Function.mem_support, Finset.prod_ne_zero_iff] at hy
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro j
  simpa using hy j (Finset.mem_univ j)

theorem eval_eq_ite_prod_of_finprod (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (TH KH : ∀ i, Subgroup (H i)) (s : G → ℂ) (s' : ∀ i, H i → ℂ) (S0 : Finset ι)
    (hcof : ∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hS0 : ∀ i ∉ S0, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0)
    (hprod : ∀ g, s g = ∏ᶠ i, s' i (p i g)) (g : G) :
    s g = if ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g = t * k then ∏ i ∈ S0, s' i (p i g) else 0 := by
  rw [hprod]
  have hfin : {i | p i g ∉ KH i}.Finite := Filter.eventually_cofinite.mp (hcof g)
  set B : Finset ι := S0 ∪ hfin.toFinset with hB
  have hone : ∀ i ∉ B, s' i (p i g) = 1 := by
    intro i hi
    simp only [B, Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hi
    rw [hS0 i hi.1, if_pos ⟨1, (TH i).one_mem, p i g, hi.2, (one_mul _).symm⟩]
  rw [finprod_eq_prod_of_mulSupport_subset (f := fun i => s' i (p i g)) (s := B) (fun i hi => by by_contra h; exact hi (hone i h))]
  split_ifs with hgood
  · symm
    apply Finset.prod_subset Finset.subset_union_left
    intro i _ hi
    rw [hS0 i hi, if_pos (hgood i hi)]
  · push_neg at hgood
    obtain ⟨i, hi, hbad⟩ := hgood
    apply Finset.prod_eq_zero (i := i)
    · refine Finset.mem_union_right _ ?_
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      intro hk
      exact hbad 1 (TH i).one_mem (p i g) hk (one_mul _).symm
    · rw [hS0 i hi, if_neg (by push_neg; exact hbad)]

theorem doubleCoset_mk_eq_of_local (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (T K : Subgroup G) (TH KH : ∀ i, Subgroup (H i)) (S0 : Finset ι)
    (hsurj : ∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i)
    (hcof : ∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) (hT : ∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i)
    (g g' : G) (hg : ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g = t * k)
    (hg' : ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g' = t * k)
    (h : ∀ i ∈ S0, DoubleCoset.mk (TH i) (KH i) (p i g) = DoubleCoset.mk (TH i) (KH i) (p i g')) :
    DoubleCoset.mk T K g = DoubleCoset.mk T K g' := by
  have hloc : ∀ i, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g' = t * p i g * k ∧
      (p i g ∈ KH i → p i g' ∈ KH i → t = 1) := by
    intro i
    by_cases hk : p i g ∈ KH i ∧ p i g' ∈ KH i
    · exact ⟨1, (TH i).one_mem, (p i g)⁻¹ * p i g', mul_mem (inv_mem hk.1) hk.2, by group,
        fun _ _ => rfl⟩
    · by_cases hi : i ∈ S0
      · obtain ⟨t, ht, k, hk', he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 (h i hi)
        exact ⟨t, ht, k, hk', he, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
      · obtain ⟨a, ha, b, hb, hab⟩ := hg i hi
        obtain ⟨a', ha', b', hb', hab'⟩ := hg' i hi
        refine ⟨a' * a⁻¹, mul_mem ha' (inv_mem ha), b⁻¹ * b', mul_mem (inv_mem hb) hb', ?_,
          fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
        rw [hab, hab']; group
  choose t ht k hk he h1 using hloc
  obtain ⟨x, hx⟩ := hsurj t (by
    filter_upwards [hcof g, hcof g'] with i hi hi'
    rw [h1 i hi hi']; exact (KH i).one_mem)
  rw [DoubleCoset.eq]
  refine ⟨x, (hT x).2 (fun i => by rw [hx]; exact ht i), g⁻¹ * x⁻¹ * g', (hK _).2 (fun i => ?_), by group⟩
  rw [map_mul, map_mul, map_inv, map_inv, hx, he i]
  convert hk i using 1
  group

theorem finsum_doubleCoset_eq_finprod_local : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (T K : Subgroup G) (TH KH : ∀ i, Subgroup (H i)) (s : G → ℂ) (s' : ∀ i, H i → ℂ), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) → (∀ i, ∀ t ∈ TH i, ∀ k ∈ KH i, ∀ x, s' i (t * x * k) = s' i x) → (∀ i, {q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)) | s' i (Quotient.out q) ≠ 0}.Finite) → (∀ᶠ i in cofinite, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0) → (∀ g, s g = ∏ᶠ i, s' i (p i g)) → ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K : Set G), s (Quotient.out q) = ∏ᶠ i, ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q) := by
  intro ι G _ H _ p T K TH KH s s' hsurj hcof hK hT hinv hfin hgood hprod
  have hS0fin := Filter.eventually_cofinite.mp hgood
  set S0 : Finset ι := hS0fin.toFinset with hS0def
  have hS0 : ∀ i ∉ S0, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0 := by
    intro i hi
    simpa [S0] using hi
  have hloc : ∀ i (x : H i), s' i (Quotient.out (DoubleCoset.mk (TH i) (KH i) x)) = s' i x := by
    intro i x
    obtain ⟨a, ha, b, hb, he⟩ := DoubleCoset.mk_out_eq_mul (TH i) (KH i) x
    rw [he, hinv i a ha b hb]
  have hR : ∏ᶠ i, ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q)
      = ∏ i : S0, ∑ᶠ q : DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1)), s' i.1 (Quotient.out q) := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := S0)]
    · exact (Finset.prod_coe_sort S0 (fun i => ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q))).symm
    · intro i hi
      by_contra h
      exact hi (finsum_doubleCoset_trivial_eq_one (H i) (TH i) (KH i) (s' i) (hS0 i h))
  rw [hR, ← finsum_pi_prod_eq_prod_finsum S0 (fun i : S0 => DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1)))
    (fun i q => s' i.1 (Quotient.out q)) (fun i => hfin i.1)]
  obtain ⟨A, hAdef⟩ : ∃ A : Set (DoubleCoset.Quotient (T : Set G) (K : Set G)),
      ∀ q, q ∈ A ↔ ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i (Quotient.out q) = t * k :=
    ⟨{q | ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i (Quotient.out q) = t * k}, fun q => Iff.rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : DoubleCoset.Quotient (T : Set G) (K : Set G) →
      ∀ i : S0, DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1)),
      ∀ q i, Φ q i = DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 (Quotient.out q)) :=
    ⟨fun q i => DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 (Quotient.out q)), fun _ _ => rfl⟩
  have hLHS : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G), s (Quotient.out q) =
      ∑ᶠ (_ : q ∈ A), ∏ i : S0, s' i.1 (Quotient.out (Φ q i)) := by
    intro q
    rw [finsum_eq_if, eval_eq_ite_prod_of_finprod ι G H p TH KH s s' S0 hcof hS0 hprod (Quotient.out q)]
    by_cases hq : ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i (Quotient.out q) = t * k
    · rw [if_pos hq, if_pos ((hAdef q).2 hq), ← Finset.prod_coe_sort S0]
      simp only [hΦ, hloc]
    · rw [if_neg hq, if_neg (fun h => hq ((hAdef q).1 h))]
  refine (finsum_congr hLHS).trans ?_
  refine (finsum_mem_eq_of_bijOn (t := Set.univ)
    (g := fun y : (∀ i : S0, DoubleCoset.Quotient (TH i.1 : Set (H i.1)) (KH i.1 : Set (H i.1))) =>
      ∏ j : S0, s' j.1 (Quotient.out (y j))) Φ ?_ (fun q _ => rfl)).trans (finsum_mem_univ _)
  refine ⟨fun q _ => Set.mem_univ _, ?_, ?_⟩
  · intro q hq q' hq' he
    rw [← DoubleCoset.out_eq' q, ← DoubleCoset.out_eq' q']
    refine doubleCoset_mk_eq_of_local ι G H p T K TH KH S0 hsurj hcof hK hT _ _ ((hAdef q).1 hq) ((hAdef q').1 hq') (fun i hi => ?_)
    have := congrFun he ⟨i, hi⟩
    rwa [hΦ, hΦ] at this
  · intro y _
    obtain ⟨g, hg⟩ := hsurj (fun i => if hi : i ∈ S0 then Quotient.out (y ⟨i, hi⟩) else 1) (by
      filter_upwards [S0.finite_toSet.compl_mem_cofinite] with i hi
      rw [dite_eq_right (by simpa using hi)]; exact (KH i).one_mem)
    obtain ⟨a, ha, b, hb, he⟩ := DoubleCoset.mk_out_eq_mul T K g
    refine ⟨DoubleCoset.mk T K g, ?_, ?_⟩
    · rw [hAdef]
      intro i hi
      refine ⟨p i a, (hT a).1 ha i, p i b, (hK b).1 hb i, ?_⟩
      rw [he, map_mul, map_mul, hg i, dite_eq_right hi, mul_one]
    · funext i
      rw [hΦ, he, map_mul, map_mul, hg i.1, dite_eq_left i.2]
      show DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 a * Quotient.out (y i) * p i.1 b) = y i
      have h1 : DoubleCoset.mk (TH i.1) (KH i.1) (p i.1 a * Quotient.out (y i) * p i.1 b) =
          DoubleCoset.mk (TH i.1) (KH i.1) (Quotient.out (y i)) :=
        (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨(p i.1 a)⁻¹, inv_mem ((hT a).1 ha i.1), (p i.1 b)⁻¹,
          inv_mem ((hK b).1 hb i.1), by group⟩
      rw [h1, DoubleCoset.out_eq']

end GlobalTheory.DoubleCosetEuler
end

section

open scoped Pointwise

namespace GlobalTheory

theorem finsum_comp_eq_finsum_natCard_fiber_mul {X Y : Type} (π : X → Y) (h : Y → ℂ)
    (hf : (∀ y, h y ≠ 0 → (π ⁻¹' {y}).Finite) ∨ (∀ y, h y ≠ 0 → Nat.card (π ⁻¹' {y}) = 0)) :
    ∑ᶠ x, h (π x) = ∑ᶠ y, (Nat.card (π ⁻¹' {y}) : ℂ) * h y := by
  classical
  by_cases hfin : (Function.support (h ∘ π)).Finite
  · set S := hfin.toFinset with hS
    have hmemS : ∀ x, x ∈ S ↔ h (π x) ≠ 0 := by
      intro x
      simp [hS]
    have hL : ∑ᶠ x, h (π x) = ∑ x ∈ S, h (π x) := by
      apply finsum_eq_sum_of_support_subset
      intro x hx
      exact (hmemS x).2 hx
    have hR : ∑ᶠ y, (Nat.card (π ⁻¹' {y}) : ℂ) * h y
        = ∑ y ∈ S.image π, (Nat.card (π ⁻¹' {y}) : ℂ) * h y := by
      apply finsum_eq_sum_of_support_subset
      intro y hy
      rw [Function.mem_support] at hy
      have h1 : h y ≠ 0 := right_ne_zero_of_mul hy
      have h2 : Nat.card (π ⁻¹' {y}) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hy
      obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.mp h2).1
      have hxy : π x = y := hx
      rw [Finset.coe_image]
      refine ⟨x, ?_, hxy⟩
      rw [Finset.mem_coe, hmemS, hxy]
      exact h1
    rw [hL, hR, ← Finset.sum_fiberwise_of_maps_to (g := π) (t := S.image π)
      (fun x hx => Finset.mem_image_of_mem π hx)]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hy
    have hne : h (π x₀) ≠ 0 := (hmemS x₀).1 hx₀
    have hfib : π ⁻¹' {π x₀} = ↑(S.filter (fun x => π x = π x₀)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_filter, Set.mem_ofPred_eq]
      constructor
      · intro hx
        refine ⟨?_, hx⟩
        rw [hmemS, hx]
        exact hne
      · exact fun hx => hx.2
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
      Finset.sum_const, nsmul_eq_mul, hfib, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  · rw [finsum_of_infinite_support (f := fun x => h (π x)) hfin]
    symm
    rcases hf with hf | hf
    · apply finsum_of_infinite_support
      intro hR
      apply hfin
      refine (hR.preimage' (f := π) ?_).subset ?_
      · intro y hy
        exact hf y (right_ne_zero_of_mul hy)
      · intro x hx
        simp only [Function.mem_support, Function.comp_apply] at hx
        simp only [Set.mem_preimage, Function.mem_support]
        have hfinx : Finite (π ⁻¹' {π x}) := (hf (π x) hx).to_subtype
        have hnx : Nonempty (π ⁻¹' {π x}) := ⟨⟨x, rfl⟩⟩
        have hc : Nat.card (π ⁻¹' {π x}) ≠ 0 := Nat.card_ne_zero.mpr ⟨hnx, hfinx⟩
        exact mul_ne_zero (by exact_mod_cast hc) hx
    · have hz : (fun y => (Nat.card (π ⁻¹' {y}) : ℂ) * h y) = fun _ => 0 := by
        funext y
        by_cases hy : h y = 0
        · simp [hy]
        · simp [hf y hy]
      rw [hz, finsum_zero]

end GlobalTheory
end

section

namespace GlobalTheory.TwoCocycle

theorem interchange {Γ D : Type} [CommGroup Γ] [AddCommGroup D] (c : Γ → Γ → D)
    (hs : ∀ x y, c x y = c y x)
    (hc : ∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) (a b x y : Γ) :
    c (a * b) (x * y) + c x y + c a b = c a x + c b y + c (a * x) (b * y) := by
  have h1 := hc a b (x * y)
  have h2 := hc b y x
  have h3 := hc a x (b * y)
  rw [mul_comm y x, hs y x, hs (b * y) x] at h2
  rw [mul_left_comm x b y] at h3
  linear_combination (norm := abel) h2 + h3 - h1

theorem sum_pow_mul (Γ D : Type) [CommGroup Γ] [AddCommGroup D] (c : Γ → Γ → D)
    (hs : ∀ x y, c x y = c y x)
    (hc : ∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) (n : ℕ) (x y : Γ) :
    ∑ i ∈ Finset.range n, c ((x * y) ^ i) (x * y) + n • c x y =
      ∑ i ∈ Finset.range n, c (x ^ i) x + ∑ i ∈ Finset.range n, c (y ^ i) y
        + c (x ^ n) (y ^ n) - c 1 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := interchange c hs hc (x ^ n) (y ^ n) x y
    rw [← mul_pow] at h
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, succ_nsmul,
      pow_succ x, pow_succ y]
    linear_combination (norm := abel) ih + h

end GlobalTheory.TwoCocycle
end

section

namespace GlobalTheory.TargetEquivalence

open Finset

theorem main {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → α → β → R) :
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by
  calc ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ a : α, ∑ c : α, ∑ b : β, ∑ e : β, f a b c e := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ b : β, ∑ e : β, f a b c e := Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ e : β, ∑ b : β, f a b c e := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e := by
        refine Finset.sum_congr rfl fun c _ => ?_
        exact Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
        exact Finset.sum_comm

theorem target : ∀ {R α β : Type} [inst : AddCommMonoid R] [inst_1 : Fintype α] [inst_2 : Fintype β] (f : α → β → α → β → R), ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e :=
  fun f => main f

end GlobalTheory.TargetEquivalence
end
