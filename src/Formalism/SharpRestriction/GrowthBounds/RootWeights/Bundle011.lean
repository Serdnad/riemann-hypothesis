module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle003
public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.RingTheory.Derivation.Lie
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle005
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
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.OfAssociative

@[expose] public section

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem v2rep_mem_weightSp (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]

theorem v2rep_comm (E : GLOps n K V) (hR : SatisfiesGLRelations E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) + ((if b = c then E a d x else 0) - (if d = a then E c b x else 0)) := by
  have h := congrArg (fun f : Module.End K V => f x) (hR a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [sub_eq_iff_eq_add'] at h
  rw [h]
  congr 1
  split_ifs <;> simp

theorem v2rep_shift (E : GLOps n K V) (hR : SatisfiesGLRelations E) (a b : Fin n) (ν : Fin n → ℤ) (x : V)
    (hx : x ∈ weightSp E ν) : E a b x ∈ weightSp E (ν + rootW a b) := by
  rw [v2rep_mem_weightSp] at hx ⊢
  intro c
  rw [v2rep_comm E hR c c a b x, hx c, map_smul]
  by_cases hca : c = a <;> by_cases hcb : c = b
  · subst hca; subst hcb
    simp [rootW]
  · subst hca
    simp [rootW, hcb, Ne.symm hcb]
    module
  · subst hcb
    simp [rootW, hca]
    module
  · simp [rootW, hca, hcb, Ne.symm hcb]

def cyclicLevelSubmodule (E : GLOps n K V) (v : V) : ℕ → Submodule K V
  | 0 => Submodule.span K {v}
  | k + 1 => cyclicLevelSubmodule E v k ⊔ ⨆ ab : Fin n × Fin n, ⨆ (_ : ab.2 < ab.1), (cyclicLevelSubmodule E v k).map (E ab.1 ab.2)

theorem v2rep_Y_le (E : GLOps n K V) (v : V) (k : ℕ) : cyclicLevelSubmodule E v k ≤ cyclicLevelSubmodule E v (k + 1) := by
  exact le_sup_left

theorem v2rep_Y_low (E : GLOps n K V) (v : V) (k : ℕ) (a b : Fin n) (h : b < a) (x : V) (hx : x ∈ cyclicLevelSubmodule E v k) :
    E a b x ∈ cyclicLevelSubmodule E v (k + 1) := by
  show E a b x ∈ cyclicLevelSubmodule E v k ⊔ _
  refine Submodule.mem_sup_right ?_
  refine Submodule.mem_iSup_of_mem (a, b) ?_
  refine Submodule.mem_iSup_of_mem h ?_
  exact Submodule.mem_map_of_mem hx

theorem v2rep_Y_up (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) (k : ℕ) :
    ∀ c d : Fin n, c ≤ d → ∀ x ∈ cyclicLevelSubmodule E v k, E c d x ∈ cyclicLevelSubmodule E v k := by
  induction k with
  | zero =>
    intro c d hcd x hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    rcases hcd.lt_or_eq with hlt | heq
    · rw [hv.2.2 c d hlt]
      exact Submodule.zero_mem _
    · subst heq
      rw [(v2rep_mem_weightSp E mu v).1 hv.2.1 c]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  | succ k ih =>
    have hany : ∀ p q : Fin n, ∀ y ∈ cyclicLevelSubmodule E v k, E p q y ∈ cyclicLevelSubmodule E v (k + 1) := by
      intro p q y hy
      rcases lt_or_ge q p with hqp | hpq
      · exact v2rep_Y_low E v k p q hqp y hy
      · exact v2rep_Y_le E v k (ih p q hpq y hy)
    intro c d hcd
    suffices hs : cyclicLevelSubmodule E v (k + 1) ≤ (cyclicLevelSubmodule E v (k + 1)).comap (E c d) from fun x hx => hs hx
    refine sup_le (fun y hy => v2rep_Y_le E v k (ih c d hcd y hy)) ?_
    refine iSup_le fun ab => iSup_le fun hab => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_comap, Submodule.mem_comap, v2rep_comm E hR c d ab.1 ab.2 y]
    refine Submodule.add_mem _ (v2rep_Y_low E v k ab.1 ab.2 hab _ (ih c d hcd y hy)) ?_
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs
      · exact hany c ab.2 y hy
      · exact Submodule.zero_mem _
    · split_ifs
      · exact hany ab.1 d y hy
      · exact Submodule.zero_mem _

theorem v2rep_Y_all (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) (k : ℕ)
    (a b : Fin n) (y : V) (hy : y ∈ cyclicLevelSubmodule E v k) : E a b y ∈ cyclicLevelSubmodule E v (k + 1) := by
  rcases lt_or_ge b a with hba | hab
  · exact v2rep_Y_low E v k a b hba y hy
  · exact v2rep_Y_le E v k (v2rep_Y_up E hR mu v hv k a b hab y hy)

theorem v2rep_Umon_Y (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v)
    (u : Module.End K V) (hu : u ∈ Umon E) : ∀ k, ∀ x ∈ cyclicLevelSubmodule E v k, ∃ k', u x ∈ cyclicLevelSubmodule E v k' := by
  induction hu using Submonoid.closure_induction with
  | mem u hu =>
    obtain ⟨ab, rfl⟩ := hu
    intro k x hx
    exact ⟨k + 1, v2rep_Y_all E hR mu v hv k ab.1 ab.2 x hx⟩
  | one =>
    intro k x hx
    exact ⟨k, hx⟩
  | mul u₁ u₂ _ _ h₁ h₂ =>
    intro k x hx
    obtain ⟨k₂, hk₂⟩ := h₂ k x hx
    obtain ⟨k₁, hk₁⟩ := h₁ k₂ _ hk₂
    exact ⟨k₁, hk₁⟩

def dominantWeightSubmodule [NeZero n] (E : GLOps n K V) (mu : Fin n → ℤ) : Submodule K V :=
  ⨆ ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}, weightSp E ν

theorem v2rep_Good_low [NeZero n] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (a b : Fin n) (h : b < a) :
    dominantWeightSubmodule E mu ≤ (dominantWeightSubmodule E mu).comap (E a b) := by
  refine iSup₂_le fun ν hν => ?_
  intro x hx
  rw [Submodule.mem_comap]
  have hs := v2rep_shift E hR a b ν x hx
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at h
    exact absurd h (Fin.not_lt_zero b)
  have hbl : b ≠ lastIdx n := by
    intro hb
    have : (a : ℕ) ≤ n - 1 := Nat.le_sub_one_of_lt a.2
    have h2 : (b : ℕ) < a := h
    rw [hb] at h2
    simp [lastIdx] at h2
    omega
  refine (le_iSup₂ (f := fun ν (_ : ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}) =>
    weightSp E ν) (ν + rootW a b) ?_) hs
  obtain ⟨h1, h2⟩ := hν
  refine ⟨?_, ?_⟩
  · simp only [Pi.add_apply, rootW, Pi.sub_apply, Pi.single_apply, Ne.symm hbl, if_false, sub_zero]
    split_ifs <;> omega
  · simp only [Pi.add_apply, rootW, Pi.sub_apply, Pi.single_apply, Ne.symm ha0, if_false, zero_sub]
    split_ifs <;> omega

theorem v2rep_Y_Good [NeZero n] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v)
    (k : ℕ) : cyclicLevelSubmodule E v k ≤ dominantWeightSubmodule E mu := by
  induction k with
  | zero =>
    refine (Submodule.span_singleton_le_iff_mem _ _).2 ?_
    exact (le_iSup₂ (f := fun ν (_ : ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}) =>
      weightSp E ν) mu ⟨le_rfl, le_rfl⟩) hv.2.1
  | succ k ih =>
    refine sup_le ih (iSup_le fun ab => iSup_le fun hab => ?_)
    rw [Submodule.map_le_iff_le_comap]
    exact ih.trans (v2rep_Good_low E hR mu ab.1 ab.2 hab)

theorem highest_weight_module_bounds : HighestWeightModuleWeightBounds := by
  intro K V _ _ _ _ n _ E hR mu v hv u hu
  obtain ⟨k, hk⟩ := v2rep_Umon_Y E hR mu v hv u hu 0 v (Submodule.mem_span_singleton_self v)
  exact v2rep_Y_Good E hR mu v hv k hk

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

attribute [local instance 100] LieRing.ofAssociativeRing

theorem highest_weight_dominant_pair {n : ℕ} {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V}
    (hv : IsHWV E lam v) {a b : Fin n} (hab : a < b) : lam b ≤ lam a := by
  have hne : a ≠ b := ne_of_lt hab
  have hw := (mem_weightSpace_iff_diagonal_rep E lam v).1 hv.2.1
  have hhv : (E a a - E b b) v = ((lam a - lam b : ℤ) : K) • v := by
    rw [LinearMap.sub_apply, hw a, hw b, ← sub_smul]; push_cast; rfl
  by_cases h0 : E a a - E b b = 0
  · rw [h0, LinearMap.zero_apply] at hhv
    have := (smul_eq_zero.1 hhv.symm).resolve_right hv.1
    have h1 : lam a - lam b = 0 := by exact_mod_cast this
    omega
  have t : IsSl2Triple (E a a - E b b) (E a b) (E b a) := by
    refine ⟨h0, ?_, ?_, ?_⟩
    · rw [Ring.lie_def, hE.1 a b b a]; simp
    · rw [sub_lie, Ring.lie_def, Ring.lie_def, hE.1 a a a b, hE.1 b b a b]
      simp [hne, hne.symm, two_smul]
    · rw [sub_lie, Ring.lie_def, Ring.lie_def, hE.1 a a b a, hE.1 b b b a]
      simp [hne, hne.symm, two_smul]
      abel
  have P : t.HasPrimitiveVectorWith v (((lam a - lam b : ℤ) : K)) :=
    ⟨hv.1, hhv, hv.2.2 a b hab⟩
  obtain ⟨m, hm⟩ := P.exists_nat
  have : lam a - lam b = (m : ℤ) := by exact_mod_cast hm
  omega

theorem highest_weight_dominant_holds : HighestWeightDominant := by
  intro K V _ _ _ _ _ n E hE lam v hv a b hab
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · exact highest_weight_dominant_pair hE hv h

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem v2con_bracket {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b c d : Fin n) :
    ⁅letterPolarizationDerivation R LL S a b, letterPolarizationDerivation R LL S c d⁆ =
      (if b = c then letterPolarizationDerivation R LL S a d else 0) - (if d = a then letterPolarizationDerivation R LL S c b else 0) := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨l, e⟩
  rw [Derivation.commutator_apply, Derivation.sub_apply]
  have h1 : (if b = c then letterPolarizationDerivation R LL S a d else 0) (X (l, e)) =
      if b = c then letterPolarizationDerivation R LL S a d (X (l, e)) else 0 := by split_ifs <;> simp
  have h2 : (if d = a then letterPolarizationDerivation R LL S c b else 0) (X (l, e)) =
      if d = a then letterPolarizationDerivation R LL S c b (X (l, e)) else 0 := by split_ifs <;> simp
  rw [h1, h2]
  simp only [v2con_der_X]
  have k5 : (c = b) = (b = c) := propext eq_comm
  have k6 : (a = d) = (d = a) := propext eq_comm
  by_cases hS : l ∈ S
  · by_cases hv : LL.vec l = true
    · simp only [hS, hv, if_true]
      by_cases h3 : e = d <;> by_cases h4 : e = b <;> by_cases h5 : b = c <;> by_cases h6 : d = a <;>
        simp_all [v2con_der_X]
    · simp only [hS, hv, if_true]
      by_cases h3 : e = c <;> by_cases h4 : e = a <;> by_cases h5 : b = c <;> by_cases h6 : d = a <;>
        simp_all [v2con_der_X]
  · simp [hS]

theorem polynomial_operators_gl_relations : PolynomialOperatorsGLRelations := by
  intro R _ ι _ LL n S a b c d
  apply LinearMap.ext
  intro F
  have h := congrArg (fun D : Derivation R (MvPolynomial (ι × Fin n) R) (MvPolynomial (ι × Fin n) R) => D F)
    (v2con_bracket (R := R) LL S a b c d)
  simp only [Derivation.commutator_apply, Derivation.sub_apply] at h
  simp only [glOps, LinearMap.sub_apply, Module.End.mul_apply, v2con_glAct_eq]
  rw [h]
  congr 1
  · split_ifs <;> simp [v2con_glAct_eq]
  · split_ifs <;> simp [v2con_glAct_eq]

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section fwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι) (j : Fin n)
  (Pr : ℤ → Prop)

theorem propertySubmodule_dividedPower_stable (hT : TransvectionExpansion) (a b : Fin n) (hab : a ≠ b) (k : ℕ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : divPow R LL S a b k y ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical
  have key := laurent_coefficients_mem_property (LL := LL) (S := S) (j := j) (Pr := Pr) y
    ((Finset.range (y.totalDegree + k + 1)).image (fun i : ℕ => (i : ℤ)))
    (fun z => divPow R LL S a b z.toNat y) ?_ hy
  · have hk := key (k : ℤ) (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), rfl⟩)
    simpa using hk
  intro k1 _ φ
  refine ⟨Matrix.transvection a b (LaurentPolynomial.T 1), Matrix.transvection a b (-LaurentPolynomial.T 1),
    ?_, ?_⟩
  · rw [Matrix.transvection_mul_transvection_same (h := hab), neg_add_cancel, Matrix.transvection_zero]
  · rw [hT R (LaurentPolynomial k1) ι LL n S (LaurentPolynomial.C.comp φ) a b hab (LaurentPolynomial.T 1) y
      (y.totalDegree + k + 1) (by omega)]
    rw [Finset.sum_image (fun x _ z _ h => by exact_mod_cast h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [LaurentPolynomial.T_pow]


open Classical in
def weightEntryComponent (a : Fin n) (w : ℤ) (y : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ y.support.filter (fun m => wtS LL S m a = w), monomial m (y.coeff m)

private theorem laurent_T_unit_zpow_eq_T {k1 : Type} [CommRing k1] (z : ℤ) :
    (((⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by rw [← LaurentPolynomial.T_add]; simp,
      by rw [← LaurentPolynomial.T_add]; simp⟩ : (LaurentPolynomial k1)ˣ) ^ z :
        (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1) = LaurentPolynomial.T z := by
  induction z using Int.induction_on with
  | zero => simp
  | succ i ih => rw [zpow_add_one, Units.val_mul, ih, ← LaurentPolynomial.T_add]
  | pred i ih =>
    rw [zpow_sub_one, Units.val_mul, ih, Units.inv_mk, ← LaurentPolynomial.T_add]
    rfl

theorem propertySubmodule_weightEntryComponent (hTo : TorusActsThroughWeight) (a : Fin n) (w : ℤ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : weightEntryComponent LL S a w y ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical
  set K : Finset ℤ := y.support.image (fun m => wtS LL S m a) with hK
  by_cases hw : w ∈ K
  swap
  · have h0 : weightEntryComponent LL S a w y = 0 := by
      unfold weightEntryComponent
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [Finset.mem_filter] at hm
      exact absurd (Finset.mem_image.2 ⟨m, hm.1, hm.2⟩) hw
    rw [h0]
    exact Submodule.zero_mem _
  refine laurent_coefficients_mem_property (LL := LL) (S := S) (j := j) (Pr := Pr) y K (fun w => weightEntryComponent LL S a w y) ?_ hy w hw
  intro k1 _ φ
  let u : (LaurentPolynomial k1)ˣ := ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
    by rw [← LaurentPolynomial.T_add]; simp, by rw [← LaurentPolynomial.T_add]; simp⟩
  let D : Fin n → (LaurentPolynomial k1)ˣ := fun b => if b = a then u else 1
  refine ⟨Matrix.diagonal fun b => ((D b : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1),
    Matrix.diagonal fun b => (((D b)⁻¹ : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1), ?_, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal]
    simp
  ·
    have hmono : ∀ m : ι × Fin n →₀ ℕ, ∀ c : R,
        matrixSubst LL S (LaurentPolynomial.C.comp φ)
          (Matrix.diagonal fun b => ((D b : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1))
          (Matrix.diagonal fun b => (((D b)⁻¹ : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1))
          (monomial m c) = C (LaurentPolynomial.T (wtS LL S m a)) *
            monomial m (LaurentPolynomial.C (φ c)) := by
      intro m c
      rw [hTo R (LaurentPolynomial k1) ι LL n S (LaurentPolynomial.C.comp φ) D m c, C_mul_monomial]
      congr 1
      have hp : (∏ b, D b ^ (wtS LL S m b) : (LaurentPolynomial k1)ˣ) = u ^ (wtS LL S m a) := by
        rw [Finset.prod_eq_single a (fun b _ hb => by simp [D, hb]) (fun h => absurd (Finset.mem_univ a) h)]
        simp [D]
      rw [hp, laurent_T_unit_zpow_eq_T, mul_comm]
      rfl
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff y]

    rw [map_sum]
    simp_rw [hmono]
    unfold weightEntryComponent

    simp_rw [map_sum, MvPolynomial.map_monomial, Finset.mul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := y.support) (t := K) (g := fun m => wtS LL S m a)
      (fun m hm => Finset.mem_image.2 ⟨m, hm, rfl⟩)]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_filter] at hm
    rw [hm.2]
    rfl

theorem propertySubmodule_binomial_stable (hTo : TorusActsThroughWeight) (a : Fin n) (k : ℕ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : binomPol R LL S a k y ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical

  have hdec : binomPol R LL S a k y = ∑ w ∈ y.support.image (fun m => wtS LL S m a),
      (((Ring.choose w k : ℤ) : R)) • weightEntryComponent LL S a w y := by
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff y]

    rw [map_sum]
    unfold weightEntryComponent
    simp_rw [Finset.smul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := y.support) (t := y.support.image (fun m => wtS LL S m a))
      (g := fun m => wtS LL S m a) (fun m hm => Finset.mem_image.2 ⟨m, hm, rfl⟩)]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_filter] at hm
    have h1 : monomial m (y.coeff m) = (y.coeff m) • (MvPolynomial.basisMonomials (ι × Fin n) R) m := by
      rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [h1, map_smul, binomPol, Module.Basis.constr_basis, MvPolynomial.coe_basisMonomials,
      MvPolynomial.smul_monomial, MvPolynomial.smul_monomial, MvPolynomial.smul_monomial, hm.2]
    congr 1
    simp only [smul_eq_mul]
    ring
  rw [hdec]
  exact Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (propertySubmodule_weightEntryComponent LL S j Pr hTo a w y hy)

theorem weights_property_of_generic_translate (hT : TransvectionExpansion) (hTo : TorusActsThroughWeight) (hSp : GenericMonomialsSpecialise) (G : MvPolynomial (ι × Fin n) R)
    (hG : ∀ m ∈ (genericTranslate LL S G).support, Pr (wtS LL S m j)) :
    ∀ mu ∈ polWts LL S (polGenSub R LL S G), Pr (mu j) := by
  classical

  have hG0 : G ∈ weightEntryPropertySubmodule LL S j Pr := by
    intro k1 _ φ g0 g0inv h m hm
    exact hG m (hSp R ι LL n S k1 φ g0 g0inv h G hm)

  have hclos : ∀ u ∈ Submonoid.closure (polUZgens R LL S),
      ∀ x ∈ weightEntryPropertySubmodule LL S j Pr, u x ∈ weightEntryPropertySubmodule LL S j Pr := by
    intro u hu
    induction hu using Submonoid.closure_induction with
    | mem u hu =>
      rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
      · exact fun x hx => propertySubmodule_dividedPower_stable LL S j Pr hT a b hab k x hx
      · exact fun x hx => propertySubmodule_binomial_stable LL S j Pr hTo a k x hx
    | one => exact fun x hx => hx
    | mul u v _ _ hu hv => exact fun x hx => hu _ (hv x hx)
  have hsub : polGenSub R LL S G ≤ weightEntryPropertySubmodule LL S j Pr := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨u, hu, rfl⟩
    exact hclos u hu G hG0
  rintro mu ⟨x, hx, hx0, hxw⟩
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hx0
  rw [← MvPolynomial.mem_support_iff] at hm
  have h1 := hsub hx R (RingHom.id R) 1 1 (mul_one 1) m
  rw [matrixSubst_one, MvPolynomial.map_id] at h1
  rw [← hxw m hm]
  exact h1 hm

end fwd

end Formalism.MainNotions.G.GLWeightTheory
end
end
