module

import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle009
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle010
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle011
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.LoweringWordWeightOrNMinus
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionRangeTrivial
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.MemWeightSpaceIffDiagonalEigen
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem charZero_fraction_field_of_setting {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  apply Formalism.MainNotions.G.GLWeightTheory.dvr_fraction_field_charZero <;> assumption

theorem cyclicSubmodule_isSubrepresentation {n : ℕ} {K V : Type} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (v : V) :
    IsSubrepresentation E (cyclicSubmodule E v) := by
  unfold IsSubrepresentation cyclicSubmodule
  intro a b x hx
  have hle : Submodule.span K {x | ∃ u ∈ Umon E, x = u v} ≤
      (Submodule.span K {x | ∃ u ∈ Umon E, x = u v}).comap (E a b) := by
    rw [Submodule.span_le]
    rintro y ⟨u, hu, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    apply Submodule.subset_span
    refine ⟨E a b * u, ?_, rfl⟩
    unfold Umon at hu ⊢
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu
  exact hle hx

theorem log_bound_monotone (p n : ℕ) {k l : ℕ} (h : k ≤ l) : deF p n k ≤ deF p n l := by
  unfold deF
  exact Nat.log_mono_right (by omega)

theorem pow_smul_mem_of_le' {O W : Type} [CommRing O] [AddCommGroup W] [Module O W] (M : Submodule O W) (c : O) {a b : ℕ}
    (hab : a ≤ b) {z : W} (h : c ^ a • z ∈ M) : c ^ b • z ∈ M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, mul_comm, mul_smul]
  exact M.smul_mem _ h

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem monomial_shift_cancel {σ : Type} (m : σ →₀ ℕ) (v : σ) (c : K) :
    (monomial (m - Finsupp.single v 1 + Finsupp.single v 1) (c * (m v : K)) : MvPolynomial σ K) =
      monomial m (c * (m v : K)) := by
  by_cases h : m v = 0
  · simp [h]
  · rw [tsub_add_cancel_of_le]
    rw [Finsupp.single_le_iff]
    omega

theorem diagonal_derivation_monomial (LL : Letters ι) (S : Set ι) (a : Fin n) (m : ι × Fin n →₀ ℕ) (c : K) :
    glDerivation K LL S a a (monomial m c) = monomial m (((wtS LL S m a : ℤ) : K) * c) := by
  rw [gl_derivation_monomial]
  simp only [monomial_shift_cancel]
  unfold wtS

  rw [Int.cast_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp [mul_comm]

theorem diagonal_derivation_coeff (LL : Letters ι) (S : Set ι) (a : Fin n) (F : MvPolynomial (ι × Fin n) K)
    (m : ι × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (glDerivation K LL S a a F) m = ((wtS LL S m a : ℤ) : K) * AddMonoidAlgebra.coeff F m := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial u b =>
    rw [diagonal_derivation_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      rfl
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add, mul_add]

theorem polynomial_mem_weightSpace_iff (LL : Letters ι) (S : Set ι) (mu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) K) :
    F ∈ weightSp (glOps K n LL S) mu ↔ ∀ a, glDerivation K LL S a a F = ((mu a : ℤ) : K) • F := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, sub_eq_zero, gl_operator_apply_derivation]
  rfl

theorem weight_vector_monomial_weight [CharZero K] (LL : Letters ι) (S : Set ι) (mu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) K)
    (hF : F ∈ weightSp (glOps K n LL S) mu) (m : ι × Fin n →₀ ℕ) (hm : m ∈ F.support) : wtS LL S m = mu := by
  funext a
  have h := congrArg (AddMonoidAlgebra.coeff · m) ((polynomial_mem_weightSpace_iff LL S mu F).1 hF a)
  rw [diagonal_derivation_coeff, MvPolynomial.coeff_smul, smul_eq_mul] at h
  have hc : AddMonoidAlgebra.coeff F m ≠ 0 := mem_support_iff.1 hm
  have h2 := mul_right_cancel₀ hc h
  exact_mod_cast h2

theorem monomial_mem_weightSpace (LL : Letters ι) (S : Set ι) (m : ι × Fin n →₀ ℕ) (c : K) :
    monomial m c ∈ weightSp (glOps K n LL S) (wtS LL S m) := by
  rw [polynomial_mem_weightSpace_iff]
  intro a
  rw [diagonal_derivation_monomial, smul_monomial, smul_eq_mul]

theorem polynomial_isGLRep (LL : Letters ι) (S : Set ι) : IsGLRep (glOps K n LL S) := by
  classical
  refine ⟨polynomial_gl_commutation LL S, ?_, ?_⟩
  · intro x
    haveI : ∀ m : x.support, FiniteDimensional K (Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i)) :=
      fun m => homogeneous_multidegree_findim _
    refine ⟨⨆ m : x.support, Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i), inferInstance, ?_, ?_⟩
    · have key : ∑ m ∈ x.support, monomial m (AddMonoidAlgebra.coeff x m) ∈
          ⨆ m : x.support, Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i) := by
        apply Submodule.sum_mem
        intro m hm
        apply Submodule.mem_iSup_of_mem (⟨m, hm⟩ : x.support)
        rw [Pol, mem_restrictSupport_iff]
        intro m' hm'
        have h1 := support_monomial_subset (Finset.mem_coe.1 hm')
        rw [Finset.mem_singleton] at h1
        subst h1
        intro i
        rfl
      convert key using 1
      exact x.as_sum
    · intro a b y hy
      refine Submodule.iSup_induction _ (motive := fun y => glOps K n LL S a b y ∈
        ⨆ m : x.support, Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i)) hy ?_ ?_ ?_
      · intro m z hz
        exact Submodule.mem_iSup_of_mem m (gl_operator_preserves_multidegree LL S _ a b z hz)
      · simp
      · intro z w hz hw
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hz hw
  · rw [eq_top_iff]
    intro F _
    have key : ∑ m ∈ F.support, monomial m (AddMonoidAlgebra.coeff F m) ∈ ⨆ mu : Fin n → ℤ, weightSp (glOps K n LL S) mu := by
      apply Submodule.sum_mem
      intro m _
      exact Submodule.mem_iSup_of_mem (wtS LL S m) (monomial_mem_weightSpace LL S m _)
    convert key using 1
    exact F.as_sum

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem v2rep_comp_mem [CharZero K] (E : GLOps n K V) (Z : Submodule K V) (hZ : ∀ a, ∀ x ∈ Z, E a a x ∈ Z)
    (s : Finset (Fin n → ℤ)) : ∀ g : (Fin n → ℤ) → V, (∀ ν ∈ s, g ν ∈ weightSp E ν) → ∑ ν ∈ s, g ν ∈ Z →
      ∀ ν ∈ s, g ν ∈ Z := by
  induction s using Finset.strongInduction with
  | H s ih =>
  intro g hg hsum μ hμ
  by_cases hs : ∃ ν ∈ s, ν ≠ μ
  · obtain ⟨ν, hν, hne⟩ := hs
    obtain ⟨a, ha⟩ : ∃ a, μ a ≠ ν a := by
      by_contra h
      push_neg at h
      exact hne (funext h).symm
    let g' : (Fin n → ℤ) → V := fun ρ => (((ρ a - ν a : ℤ) : K)) • g ρ
    have hZ' : (E a a - (ν a : K) • (1 : Module.End K V)) (∑ ρ ∈ s, g ρ) ∈ Z := by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact Z.sub_mem (hZ a _ hsum) (Z.smul_mem _ hsum)
    have heq : (E a a - (ν a : K) • (1 : Module.End K V)) (∑ ρ ∈ s, g ρ) = ∑ ρ ∈ s.erase ν, g' ρ := by

      rw [map_sum, ← Finset.sum_erase_add _ _ hν]
      have h0 : (E a a - (ν a : K) • (1 : Module.End K V)) (g ν) = 0 := by
        have := (v2rep_mem_weightSp E ν (g ν)).mp (hg ν hν) a
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, this, sub_self]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have := (v2rep_mem_weightSp E ρ (g ρ)).mp (hg ρ (Finset.mem_of_mem_erase hρ)) a
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, this, ← sub_smul]
      simp only [g', Int.cast_sub]
    have hg' : ∀ ρ ∈ s.erase ν, g' ρ ∈ weightSp E ρ := fun ρ hρ =>
      (weightSp E ρ).smul_mem _ (hg ρ (Finset.mem_of_mem_erase hρ))
    have hIH := ih (s.erase ν) (Finset.erase_ssubset hν) g' hg' (heq ▸ hZ') μ
      (Finset.mem_erase.mpr ⟨hne.symm, hμ⟩)
    have hc : (((μ a - ν a : ℤ)) : K) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr ha
    have := Z.smul_mem (((μ a - ν a : ℤ) : K))⁻¹ hIH
    simp only [g'] at this
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  · push_neg at hs
    have : ∑ ν ∈ s, g ν = g μ :=
      Finset.sum_eq_single_of_mem μ hμ (fun ν hν hne => absurd (hs ν hν) hne)
    rw [this] at hsum
    exact hsum

theorem v2rep_graded [CharZero K] (E : GLOps n K V) (Z : Submodule K V) (hZ : ∀ a, ∀ x ∈ Z, E a a x ∈ Z)
    (x : V) (hx : x ∈ Z) (hw : x ∈ ⨆ ν, weightSp E ν) : x ∈ ⨆ ν, weightSp E ν ⊓ Z := by
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hw
  have hsum : ∑ ν ∈ f.support, f ν ∈ Z := by simpa [Finsupp.sum] using hx
  have key := v2rep_comp_mem E Z hZ f.support f (fun ν _ => hf ν) hsum
  show ∑ ν ∈ f.support, f ν ∈ _
  exact Submodule.sum_mem _ fun ν hν => Submodule.mem_iSup_of_mem ν ⟨hf ν, key ν hν⟩

def weightHeight' (ν : Fin n → ℤ) : ℤ := -∑ a : Fin n, (a.val : ℤ) * ν a

theorem v2rep_ht_root (ν : Fin n → ℤ) (a b : Fin n) (h : a < b) : weightHeight' ν < weightHeight' (ν + rootW a b) := by
  have hab : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast h
  simp only [weightHeight', rootW, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  linarith

def heightOperator' (E : GLOps n K V) : Module.End K V := -∑ a : Fin n, ((a.val : ℤ) : K) • E a a

theorem v2rep_H_apply (E : GLOps n K V) (ν : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ν) :
    heightOperator' E x = ((weightHeight' ν : ℤ) : K) • x := by
  rw [v2rep_mem_weightSp] at hx
  have h1 : heightOperator' E x = -∑ a : Fin n, (((a.val : ℤ) : K) * (ν a : K)) • x := by
    simp only [heightOperator', LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      hx, smul_smul]
  rw [h1, ← Finset.sum_smul, ← neg_smul]
  congr 1
  simp only [weightHeight']
  push_cast
  rfl

theorem v2rep_exists_hwv [CharZero K] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Z : Submodule K V)
    [FiniteDimensional K Z] (hZ : IsStableUnderOperators E Z) (hw : Z ≤ ⨆ ν, weightSp E ν) (hne : Z ≠ ⊥) :
    ∃ mu v, v ∈ Z ∧ IsHWV E mu v := by
  have hHZ : ∀ x ∈ Z, heightOperator' E x ∈ Z := by
    intro x hx
    simp only [heightOperator', LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Z.neg_mem (Z.sum_mem fun a _ => Z.smul_mem _ (hZ a a x hx))
  let HZ : Module.End K Z := (heightOperator' E).restrict hHZ
  let S : Set ℤ := {h | ∃ ν v, v ∈ Z ∧ v ≠ 0 ∧ v ∈ weightSp E ν ∧ weightHeight' ν = h}
  have hSeig : ∀ h ∈ S, HZ.HasEigenvalue (h : K) := by
    rintro h ⟨ν, v, hvZ, hv0, hvw, rfl⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvZ⟩) ?_
    rw [Module.End.hasEigenvector_iff]
    refine ⟨Module.End.mem_eigenspace_iff.mpr (Subtype.ext ?_), fun h0 => hv0 (congrArg Subtype.val h0)⟩
    exact v2rep_H_apply E ν v hvw
  have hSfin : S.Finite :=
    ((Module.End.finite_hasEigenvalue HZ).preimage (Int.cast_injective (α := K)).injOn).subset
      fun h hh => hSeig h hh
  obtain ⟨x, hxZ, hx0⟩ := (Submodule.ne_bot_iff Z).mp hne
  have hgr := v2rep_graded E Z (fun a x hx => hZ a a x hx) x hxZ (hw hxZ)
  obtain ⟨ν0, hν0⟩ : ∃ ν, weightSp E ν ⊓ Z ≠ ⊥ := by
    by_contra hc
    push_neg at hc
    simp [hc] at hgr
    exact hx0 hgr
  obtain ⟨v0, hv0m, hv00⟩ := (Submodule.ne_bot_iff _).mp hν0
  have hSne : S.Nonempty := ⟨_, ν0, v0, hv0m.2, hv00, hv0m.1, rfl⟩
  have hTne : hSfin.toFinset.Nonempty := (Set.Finite.toFinset_nonempty hSfin).mpr hSne
  obtain ⟨ν, v, hvZ, hv0, hvw, hht⟩ := (hSfin.mem_toFinset).mp (hSfin.toFinset.max'_mem hTne)
  refine ⟨ν, v, hvZ, hv0, hvw, fun a b hab => ?_⟩
  by_contra hne'
  have hmem : weightHeight' (ν + rootW a b) ∈ S :=
    ⟨ν + rootW a b, E a b v, hZ a b v hvZ, hne', v2rep_shift E hR a b ν v hvw, rfl⟩
  have h1 := hSfin.toFinset.le_max' _ ((hSfin.mem_toFinset).mpr hmem)
  have h2 := v2rep_ht_root ν a b hab
  omega

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section
variable {n : ℕ} {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

def weightHeightRootWeights (nu : Fin n → ℤ) : ℤ := ∑ c : Fin n, ((c : ℕ) : ℤ) * nu c

theorem weight_height_root_weights_add_root (nu : Fin n → ℤ) (a b : Fin n) :
    weightHeightRootWeights (nu + rootW a b) = weightHeightRootWeights nu + (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) := by
  unfold weightHeightRootWeights rootW
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib]
  simp [Pi.single_apply]

theorem lowering_monomial_raises_height {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) {mu : Fin n → ℤ} {v : V}
    (hv : v ∈ weightSp E mu) {u : Module.End K V} (hu : u ∈ loweringWordMonoid E) :
    ∃ nu, u v ∈ weightSp E nu ∧ ((u v = v ∧ nu = mu) ∨ weightHeightRootWeights mu < weightHeightRootWeights nu) := by
  induction hu using Submonoid.closure_induction generalizing mu v with
  | mem x hx =>
    obtain ⟨a, b, hba, rfl⟩ := hx
    refine ⟨mu + rootW a b, hs a b mu v hv, Or.inr ?_⟩
    rw [weight_height_root_weights_add_root]
    have : (b : ℕ) < (a : ℕ) := hba
    omega
  | one => exact ⟨mu, by simpa using hv, Or.inl ⟨by simp, rfl⟩⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨nu2, h2, hc2⟩ := ihy hv
    obtain ⟨nu1, h1, hc1⟩ := ihx h2
    refine ⟨nu1, by simpa [Module.End.mul_apply] using h1, ?_⟩
    rcases hc2 with ⟨e2, rfl⟩ | lt2
    · rcases hc1 with ⟨e1, rfl⟩ | lt1
      · left; exact ⟨by rw [Module.End.mul_apply, e1, e2], rfl⟩
      · right; exact lt1
    · right
      rcases hc1 with ⟨_, rfl⟩ | lt1
      · exact lt2
      · exact lt2.trans lt1

theorem self_mem_cyclicSubmodule (E : GLOps n K V) (v : V) : v ∈ cyclicSubmodule E v := Submodule.subset_span ⟨1, (Umon E).one_mem, by simp⟩

theorem cyclic_highest_weightSpace_line [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) (v : V)
    (hv : IsHWV E mu v) (x : V) (hx : x ∈ cyclicSubmodule E v) (hxw : x ∈ weightSp E mu) : ∃ c : K, x = c • v := by
  classical
  have hs : OperatorsShiftWeightsByRoots E := gl_rep_shifts_weights hE

  set Hh : Module.End K V := ∑ c : Fin n, (((c : ℕ) : ℤ) : K) • E c c with hHh
  have hH : ∀ nu (w : V), w ∈ weightSp E nu → Hh w = ((weightHeightRootWeights nu : ℤ) : K) • w := by
    intro nu w hw
    rw [mem_weightSpace_iff_diag_eigen] at hw
    rw [hHh, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, hw, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    simp [weightHeightRootWeights]

  have hvY : v ∈ loweringWordSpan E v := Submodule.subset_span ⟨1, (loweringWordMonoid E).one_mem, by simp⟩
  have hcY : cyclicSubmodule E v ≤ loweringWordSpan E v := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, rfl⟩
    exact lowering_word_span_enveloping_stable hE hv hu v hvY
  set S : Submodule K V := Submodule.span K
    {y | ∃ nu, y ∈ weightSp E nu ∧ weightHeightRootWeights mu < weightHeightRootWeights nu} with hS
  have hYS : loweringWordSpan E v ≤ K ∙ v ⊔ S := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, rfl⟩
    obtain ⟨nu, hnu, hc⟩ := lowering_monomial_raises_height hs hv.2.1 hu
    rcases hc with ⟨he, -⟩ | hlt
    · rw [he]; exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨nu, hnu, hlt⟩)
  obtain ⟨y, hy, s, hsS, hys⟩ := Submodule.mem_sup.1 (hYS (hcY hx))
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  refine ⟨c, ?_⟩
  have hsx : s = x - c • v := by rw [← hys]; abel
  have hs1 : s ∈ Hh.eigenspace ((weightHeightRootWeights mu : ℤ) : K) := by
    rw [Module.End.mem_eigenspace_iff, hsx, map_sub, map_smul, hH mu x hxw, hH mu v hv.2.1, smul_sub,
      smul_comm]
  have hs2 : s ∈ ⨆ (l : K) (_ : l ≠ ((weightHeightRootWeights mu : ℤ) : K)), Hh.eigenspace l := by
    refine (Submodule.span_le.2 ?_) hsS
    rintro w ⟨nu, hnu, hlt⟩
    have hne : ((weightHeightRootWeights nu : ℤ) : K) ≠ ((weightHeightRootWeights mu : ℤ) : K) := by
      exact_mod_cast hlt.ne'
    refine Submodule.mem_iSup_of_mem ((weightHeightRootWeights nu : ℤ) : K) (Submodule.mem_iSup_of_mem hne ?_)
    rw [Module.End.mem_eigenspace_iff]
    exact hH nu w hnu
  have h0 : s = 0 :=
    (Submodule.disjoint_def.1 (Module.End.eigenspaces_iSupIndep Hh ((weightHeightRootWeights mu : ℤ) : K))) s hs1 hs2
  rw [← hys, h0, add_zero]

theorem equivariant_kills_cyclic_of_zero (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') (hT : IsEquivariantMap E E' T) (v : V)
    (h0 : T v = 0) : ∀ x ∈ cyclicSubmodule E v, T x = 0 := by
  intro x hx
  have hle : cyclicSubmodule E v ≤ LinearMap.ker T := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, rfl⟩
    obtain ⟨u', -, hu'⟩ := equivariant_intertwines_monoid E E' T hT hu
    show T (u v) = 0
    rw [hu' v, h0, map_zero]
  exact hle hx

theorem envelopingMonoid_restrict (E : GLOps n K V) (L : Submodule K V) (hL : IsSubrepresentation E L) {u : Module.End K V} (hu : u ∈ Umon E) :
    ∃ uL ∈ Umon (restrictRepresentation E L hL), ∀ y : L, ((uL y : L) : V) = u (y : V) := by
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact ⟨restrictRepresentation E L hL a b, Submonoid.subset_closure ⟨(a, b), rfl⟩, fun y => rfl⟩
  | one => exact ⟨1, (Umon _).one_mem, fun y => rfl⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨ux, hux, hx⟩ := ihx
    obtain ⟨uy, huy, hy⟩ := ihy
    refine ⟨ux * uy, (Umon _).mul_mem hux huy, fun z => ?_⟩
    simp only [Module.End.mul_apply, hx, hy]

theorem cyclicSubmodule_restrict_eq_top (E : GLOps n K V) (v : V) (hL : IsSubrepresentation E (cyclicSubmodule E v)) :
    cyclicSubmodule (restrictRepresentation E _ hL) (⟨v, self_mem_cyclicSubmodule E v⟩ : cyclicSubmodule E v) = ⊤ := by
  refine eq_top_iff.2 ?_
  rintro ⟨x, hx⟩ -
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    obtain ⟨uL, huL, hL'⟩ := envelopingMonoid_restrict E _ hL hu
    have heq : (⟨u v, Submodule.subset_span ⟨u, hu, rfl⟩⟩ : cyclicSubmodule E v) = uL ⟨v, self_mem_cyclicSubmodule E v⟩ :=
      Subtype.ext (hL' ⟨v, self_mem_cyclicSubmodule E v⟩).symm
    rw [heq]
    exact Submodule.subset_span ⟨uL, huL, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add y z hy hz ihy ihz =>
    have := Submodule.add_mem _ ihy ihz
    exact this
  | smul c y hy ihy =>
    have := Submodule.smul_mem _ c ihy
    exact this

theorem highest_vector_restrict (E : GLOps n K V) (L : Submodule K V) (hL : IsSubrepresentation E L) (mu : Fin n → ℤ) (v : V) (hvL : v ∈ L)
    (hv : IsHWV E mu v) : IsHWV (restrictRepresentation E L hL) mu ⟨v, hvL⟩ := by
  obtain ⟨h0, hw, hl⟩ := hv
  refine ⟨fun h => h0 (congrArg Subtype.val h), ?_, fun a b hab => Subtype.ext (hl a b hab)⟩
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at hw ⊢
  intro a
  apply Subtype.ext
  have := hw a
  simpa using this

end

end Formalism.MainNotions.G.GLWeightTheory
end
end
