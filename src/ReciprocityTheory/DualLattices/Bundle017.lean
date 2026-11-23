module

public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.Bundle002
public import ReciprocityTheory.DualLattices.Bundle011
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import ReciprocityTheory.DualLattices.Bundle014
public import ReciprocityTheory.DualLattices.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.DualLattices.ExistsFamilyValuationDetEqOne
public import ReciprocityTheory.DualLattices.IsUnitDetOfSpanEq
public import ReciprocityTheory.DualLattices.Bundle015
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import ReciprocityTheory.DualLattices.IsLocalOfIntegers

@[expose] public section

section

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem exists_basis_map_restrictToSubgroup (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∃ β : Matrix K K C, IsUnit β.det ∧
      AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j) := by
  obtain ⟨B, hB, hAB⟩ := AA.lat
  apply exists_matrix_span_eq hv
  · rw [hAB]
    exact (Submodule.fg_span (Set.finite_range _)).map _
  · rw [eq_top_iff]
    rintro φ -
    let F : N → C := fun x => if h : x ∈ K then φ ⟨x, h⟩ else 0
    have hBB : B *ᵥ (B⁻¹ *ᵥ F) = F := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]
    have hF : F = ∑ j, (B⁻¹ *ᵥ F) j • (fun x => B x j) := by
      calc F = B *ᵥ (B⁻¹ *ᵥ F) := hBB.symm
        _ = _ := by
          funext x
          simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hsm : ∀ (c : C) (g : N → C), resK (R := R) K (c • g) = c • resK (R := R) K g := by
      intro c g; funext k; simp [resK]
    have hφ : φ = resK (R := R) K F := by
      funext k; simp [resK, F]

    rw [hφ, hF, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [hsm]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨fun x => B x j, ?_, rfl⟩
    rw [hAB]
    exact Submodule.subset_span ⟨j, rfl⟩

theorem exists_coset_basis (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∃ f : K → N → C, (∀ j, f j ∈ AA.carrier) ∧ ∀ g ∈ AA.carrier,
      ∃! b : K → N → C, (∀ j, b j ∈ (AA.carrier.comap (pullQ (R := R) K)).map (pullQ K)) ∧
        g = ∑ j, b j * f j := by
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hf, hgood⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  refine ⟨f, hf, fun g hg => ?_⟩
  obtain ⟨b, hbA, hbinv, hgb⟩ := exists_coset_invariant_coefficients hv AA K β hβ hAK f hf hgood hg
  refine ⟨b, ⟨fun j => mem_map_comap_pullbackQuotient AA K (hbA j) (hbinv j), hgb⟩, ?_⟩
  rintro b' ⟨hb', hgb'⟩
  funext j x
  have hc := eq_zero_of_sum_mul_coset_eq_zero (v := v) K β hβ f hgood x (fun j => b' j x - b j x) (fun k => by
    have e1 := congrFun hgb (x + k)
    have e2 := congrFun hgb' (x + k)
    simp only [Finset.sum_apply, Pi.mul_apply] at e1 e2
    have h1 : ∀ j, b' j x - b j x = b' j (x + k) - b j (x + k) := fun j => by
      rw [apply_add_of_mem_map_pullbackQuotient K _ (hb' j) x k, hbinv j x k]
    simp only [h1, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e2, sub_self])
  exact sub_eq_zero.mp (congrFun hc j)

theorem mem_of_restrictToSubgroup_eq_zero (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∀ g ∈ AA.carrier, resK (R := R) K g = 0 →
      g ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) *
        AA.carrier := by
  intro g hg hres
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hf, hgood⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  obtain ⟨b, hbA, hbinv, hgb⟩ := exists_coset_invariant_coefficients hv AA K β hβ hAK f hf hgood hg
  have h0 : (fun j => b j 0) = 0 := eq_zero_of_sum_mul_coset_eq_zero (v := v) K β hβ f hgood 0 _ (fun k => by
    have e : g (k : N) = 0 := by simpa [resK] using congrFun hres k
    calc ∑ j, b j 0 * f j (0 + k) = ∑ j, b j (0 + k) * f j (0 + k) :=
          Finset.sum_congr rfl fun j _ => by rw [hbinv j 0 k]
      _ = g (0 + k) := by rw [hgb]; simp [Finset.sum_apply]
      _ = 0 := by rw [zero_add]; exact e)
  rw [hgb]
  exact Submodule.sum_mem _ fun j _ => Submodule.mul_mem_mul
    (mem_map_augmentationIdeal_comap_pullbackQuotient AA K (hbA j) (hbinv j) (by simpa using congrFun h0 j)) (hf j)

private theorem mem_augIdeal_iff {X : Type} [AddCommGroup X] (M : Submodule R (X → C)) (f : X → C) :
    f ∈ augIdeal M ↔ f ∈ M ∧ f 0 = 0 := by
  simp [augIdeal]

theorem mem_sup_of_restrictToSubgroup_mem_sq (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∀ g ∈ augIdeal AA.carrier, resK (R := R) K g ∈
        augIdeal (AA.carrier.map (resK (R := R) K)) * augIdeal (AA.carrier.map (resK (R := R) K)) →
      g ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) ⊔
        augIdeal AA.carrier * augIdeal AA.carrier := by
  intro g hgI hres
  have hIA : ∀ a, a ∈ augIdeal AA.carrier ↔ a ∈ AA.carrier ∧ a 0 = 0 := mem_augIdeal_iff _
  have hII : augIdeal AA.carrier * augIdeal AA.carrier ≤ AA.carrier :=
    Submodule.mul_le.mpr fun a ha b hb => AA.mul_mem a b ((hIA a).1 ha).1 ((hIA b).1 hb).1
  have hle : augIdeal (AA.carrier.map (resK (R := R) K)) * augIdeal (AA.carrier.map (resK (R := R) K)) ≤
      (augIdeal AA.carrier * augIdeal AA.carrier).map (resK (R := R) K) := by
    refine Submodule.mul_le.mpr fun p hp q hq => ?_
    obtain ⟨⟨a, ha, rfl⟩, hp0⟩ := (mem_augIdeal_iff _ _).1 hp
    obtain ⟨⟨b, hb, rfl⟩, hq0⟩ := (mem_augIdeal_iff _ _).1 hq
    refine ⟨a * b, Submodule.mul_mem_mul ((hIA a).2 ⟨ha, ?_⟩) ((hIA b).2 ⟨hb, ?_⟩), ?_⟩
    · simpa [resK] using hp0
    · simpa [resK] using hq0
    · funext k; simp [resK]
  obtain ⟨q, hq, hqg⟩ := hle hres
  have hgq : g - q ∈ AA.carrier := AA.carrier.sub_mem ((hIA g).1 hgI).1 (hII hq)
  have hker := mem_of_restrictToSubgroup_eq_zero hv AA K (g - q) hgq (by rw [map_sub, hqg, sub_self])
  have hmul : (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) * AA.carrier ≤
      (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) ⊔
        augIdeal AA.carrier * augIdeal AA.carrier := by
    refine Submodule.mul_le.mpr fun e he a ha => ?_
    obtain ⟨e', he', rfl⟩ := he
    obtain ⟨he'A, he'0⟩ := (mem_augIdeal_iff _ _).1 he'
    obtain ⟨r, hr⟩ := hopfOrder_exists_algebraMap_eq_of_mem AA ha 0
    have heI : pullQ (R := R) K e' ∈ augIdeal AA.carrier :=
      (hIA _).2 ⟨he'A, by simpa [pullQ] using he'0⟩
    have haI : a - r • (1 : N → C) ∈ augIdeal AA.carrier :=
      (hIA _).2 ⟨AA.carrier.sub_mem ha (AA.carrier.smul_mem r AA.one_mem),
        by simp [Algebra.smul_def, hr]⟩
    have hsplit : pullQ (R := R) K e' * a =
        pullQ (R := R) K e' * (a - r • (1 : N → C)) + r • pullQ (R := R) K e' := by
      rw [mul_sub, mul_smul_comm, mul_one, sub_add_cancel]
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mul_mem_mul heI haI))
      (Submodule.mem_sup_left (Submodule.smul_mem _ r ⟨e', he', rfl⟩))
  have hg : g = (g - q) + q := by abel
  rw [hg]
  exact Submodule.add_mem _ (hmul hker) (Submodule.mem_sup_right hq)

end ReciprocityTheory.PGsh.L2
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Defs

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

def btP (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O) : Matrix (Fin g) (Ix g) R :=
  ∑ i, H.ρL (e i) * H.Bt * (H.ρ (e i)).map (algebraMap ℤ_[p] R) +
    H.PL * H.Bt * H.P.map (algebraMap ℤ_[p] R)

def phiP (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O) : Matrix (Fin g ⊕ Fin g) (Ix g) R :=
  fromRows H.Ht (btP H e)

def qW (H : HodgeTateDatum p g v R O σ cp) (a b : O) : Submodule R (Fin g ⊕ Fin g → R) :=
  (lieDPart H b).comap (LinearMap.funLeft R R Sum.inl) ⊓
    (LinearMap.range (Matrix.mulVecLin (H.ρL a))).comap (LinearMap.funLeft R R Sum.inr)

abbrev xMod (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (w : Fin m) :=
  qW H (e w) (e (π w)) ⧸
    ((tPart H (e w)).map (Matrix.mulVecLin (phiP H e))).comap (qW H (e w) (e (π w))).subtype

end Defs

def WdetLenStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ cw cwb : NNReal,
      HasLen v R (htCoker H (e w) (e (π w))) cw →
      HasLen v R (htCoker H (e (π w)) (e w)) cwb →
      ∃ (d : ℕ) (X : NNReal),
        Nonempty (LinearMap.range (Matrix.mulVecLin (H.ρL (e w))) ≃ₗ[R] (Fin d → R)) ∧
        HasLen v R (xMod H e π w) X ∧ X * cw = v (algebraMap R C cp) ^ d * cwb

def WdetDegStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ (d : ℕ) (X : NNReal),
      Nonempty (LinearMap.range (Matrix.mulVecLin (H.ρL (e w))) ≃ₗ[R] (Fin d → R)) →
      HasLen v R (xMod H e π w) X → X ≤ v (algebraMap R C cp) ^ d

theorem cokernelLengthComparison_of (hW1 : WdetLenStatement) (hW2 : WdetDegStatement) : CokernelLengthComparisonStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb
  obtain ⟨d, X, hd, hX, hXe⟩ :=
    hW1 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb
  have hle := hW2 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw d X hd hX
  have hcp : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h5 := hS.cp_val
    rw [h0, zero_pow (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt).ne'] at h5
    exact hS.p_ne h5.symm
  have hpos : 0 < v (algebraMap R C cp) ^ d := pow_pos (pos_iff_ne_zero.mpr hcp) d
  have h6 : v (algebraMap R C cp) ^ d * cwb ≤ v (algebraMap R C cp) ^ d * cw := by
    rw [← hXe]
    exact mul_le_mul_of_nonneg_right hle zero_le
  exact le_of_mul_le_mul_left h6 hpos

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def PermutedCokernelLowerBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ (d : ℕ),
      Nonempty (LinearMap.range (Matrix.mulVecLin (H.ρL (e (π w)))) ≃ₗ[R] (Fin d → R)) →
      ∀ cw : NNReal, HasLen v R (htCoker H (e w) (e (π w))) cw →
        (v (algebraMap R C (p : R)) : ℝ) ^ ((d : ℝ) / (p - 1)) ≤ cw

def UnramifiedCokernelLowerBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) (V1 : NNReal),
    HasLen v R (cokE H.Ht U.εT U.εL i (U.cj i)) V1 →
    (v (algebraMap R C (p : R)) : ℝ) ^
      (((U.r i : ℝ) + U.r (U.cj i)) / (p - 1) - frobSum U i) ≤ V1

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace ATower

variable {p : ℕ} (Tw : ATower R₀ p)

lemma ξmul_surj (n : ℕ) : Function.Surjective (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) := by
  rintro ⟨k, hk⟩
  have hk' : k ∈ Ideal.span {Tw.ξ n} := by
    rw [← Tw.ker_eq n]
    simpa using hk
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hk'
  refine ⟨a, Subtype.ext ?_⟩
  show Tw.ξ n * a = k
  rw [← ha, mul_comm]

lemma exists_factor (n : ℕ) : ∃ g' : (Tw.π n).ker →ₗ[R₀] (Tw.R n : Type u),
    g' ∘ₗ ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) = (Tw.π n).1.toLinearMap := by
  have hle : LinearMap.ker (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) ≤
      LinearMap.ker (Tw.π n).1.toLinearMap := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    have h0 : Tw.ξ n * a = 0 := congrArg Subtype.val ha
    have hm : a ∈ Ideal.span {Tw.ξ n} := Tw.ann n a (by rw [mul_comm]; exact h0)
    rw [← Tw.ker_eq n, RingHom.mem_ker] at hm
    exact hm
  have hs := Tw.ξmul_surj n
  refine ⟨(LinearMap.ker _).liftQ _ hle ∘ₗ
    (LinearMap.quotKerEquivOfSurjective _ hs).symm.toLinearMap, ?_⟩
  refine LinearMap.ext fun a => ?_
  have h1 : (LinearMap.quotKerEquivOfSurjective _ hs).symm (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) a) =
      Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply]

end ATower

namespace BX

variable (B : BX R₀) {p : ℕ}

lemma nsmul_ker_zero (Tw : ATower R₀ p) (n : ℕ) (V : B.gg ⊗[R₀] (Tw.π n).ker) :
    (p ^ (n + 1)) • V = 0 := by
  have hc : ((p : (Tw.R' n : Type u))) ^ (n + 1) = 0 := by exact_mod_cast Tw.char n
  induction V using TensorProduct.induction_on with
  | zero => simp
  | tmul g k =>
    have hk : (p ^ (n + 1)) • k = 0 := by
      apply Subtype.ext
      simp [nsmul_eq_mul, hc]
    rw [← TensorProduct.tmul_smul, hk, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

lemma exists_lift (Tw : ATower R₀ p) (n : ℕ) (y : B.G (Tw.R n)) (hy : (p ^ (n + 1)) • y = 0) :
    ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)), B.map (Tw.π n) th = y ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) := by
  obtain ⟨th, hth⟩ := B.surj (Tw.π n) (Tw.sqZero n) y
  have h0 : B.map (Tw.π n) ((p ^ (n + 1)) • th) = 0 := by rw [map_nsmul, hth, hy]
  obtain ⟨v, hv⟩ := (B.tg_ker (Tw.π n) (Tw.sqZero n) _).1 h0
  obtain ⟨w, hw⟩ := LinearMap.lTensor_surjective B.gg (Tw.ξmul_surj n) v
  exact ⟨th, w, hth, by rw [← hv, ← hw]; rfl⟩

lemma lift_indep (Tw : ATower R₀ p) (n : ℕ) (th th' : B.G (Tw.R' n)) (w w' : B.gg ⊗[R₀] (Tw.R' n : Type u))
    (he : B.map (Tw.π n) th = B.map (Tw.π n) th')
    (hw : (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w))
    (hw' : (p ^ (n + 1)) • th' = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w')) :
    LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w = LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w' := by
  have hd : B.map (Tw.π n) (th - th') = 0 := by rw [map_sub, he, sub_self]
  obtain ⟨v0, hv0⟩ := (B.tg_ker (Tw.π n) (Tw.sqZero n) _).1 hd
  have hp : (p ^ (n + 1)) • th = (p ^ (n + 1)) • th' := by
    have h : (p ^ (n + 1)) • (th - th') = 0 := by
      rw [← hv0, ← map_nsmul, B.nsmul_ker_zero Tw n v0, map_zero]
    rwa [smul_sub, sub_eq_zero] at h
  rw [hw, hw'] at hp
  have hx := B.tg_inj (Tw.π n) (Tw.sqZero n) hp
  obtain ⟨g', hg'⟩ := Tw.exists_factor n
  rw [← hg', LinearMap.lTensor_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  exact congrArg (LinearMap.lTensor B.gg g') hx

end BX

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def ColengthCotangentValuation (p : ℕ) (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] : Prop :=
  ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) →
    ∀ AA : HopfOrder (C := C) R N,
    ∃ (n : ℕ) (g : Fin n → N → C) (δ : Fin n → R),
      (∀ i, g i ∈ augIdeal AA.carrier) ∧
      (∀ f ∈ augIdeal AA.carrier, ∃ r : Fin n → R,
        f - ∑ j, r j • g j ∈ sqIdeal (augIdeal AA.carrier)) ∧
      (∀ i, ∃ a : Fin n → R,
        δ i • g i - ∑ j, (if j < i then a j else 0) • g j ∈ sqIdeal (augIdeal AA.carrier)) ∧
      ∀ c, HasColen R v AA.carrier c →
        c ^ 2 = (∏ i, v (algebraMap R C (δ i))) ^ Fintype.card N

theorem colengthCotangentBound_of_claim (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal)
    (R : Type) [CommRing R] [Algebra R C] (hv : v.Integers R) (hcl : ColengthCotangentValuation p C v R)
    (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (hN : ∀ x : N, p • x = 0)
    (AA : HopfOrder (C := C) R N) (lenN lenOm : NNReal)
    (hlen : HasColen R v AA.carrier lenN) (hom : HasLen v R (OmAA AA.carrier) lenOm) :
    lenN ^ 2 ≤ lenOm ^ Fintype.card N := by
  obtain ⟨n, g, δ, hg, hgen, htri, hcol⟩ := hcl N hN AA
  let q := ((sqIdeal (augIdeal AA.carrier)).comap (augIdeal AA.carrier).subtype).mkQ
  have key : ∀ x z : augIdeal AA.carrier,
      ((x : N → C) - z) ∈ sqIdeal (augIdeal AA.carrier) → q x = q z := by
    intro x z h
    exact (Submodule.Quotient.eq _).mpr (by simpa [Submodule.mem_comap] using h)
  let y : Fin n → OmAA AA.carrier := fun i => q ⟨g i, hg i⟩
  have hy : Submodule.span R (Set.range y) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨r, hr⟩ := hgen f hf
    have e : q ⟨f, hf⟩ = ∑ j, r j • y j := by

      simp only [y, ← map_smul, ← map_sum]
      apply key
      simpa using hr
    show q ⟨f, hf⟩ ∈ _
    rw [e]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hrel : ∀ i, ∃ a : Fin n → R, δ i • y i = ∑ j, (if j < i then a j else 0) • y j := by
    intro i
    obtain ⟨a, ha⟩ := htri i
    refine ⟨a, ?_⟩

    simp only [y, ← map_smul, ← map_sum]
    apply key
    have e2 : (((∑ j, (if j < i then a j else 0) • (⟨g j, hg j⟩ : augIdeal AA.carrier) :
        augIdeal AA.carrier)) : N → C) = ∑ j, (if j < i then a j else 0) • g j := by
      rw [Submodule.coe_sum]
      rfl
    rw [e2]
    exact ha
  have hle := prod_le_of_gen hv hom y hy δ hrel
  rw [hcol lenN hlen]
  first
    | exact pow_le_pow_left₀ zero_le hle _
    | exact pow_le_pow_left zero_le hle _
    | gcongr

theorem colengthCotangentBoundStatement_of_claim (hcl : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → v (p : C) < 1 → ColengthCotangentValuation p C v R) : ColengthCotangentBoundStatement := by
  intro p _ C _ _ _ v R _ _ hv hp N _ _ _ hN AA lenN lenOm hlen hom
  exact colengthCotangentBound_of_claim p C v R hv (hcl p C v R hv hp) N hN AA lenN lenOm hlen hom

end ReciprocityTheory.PGsh.Up
end
end
