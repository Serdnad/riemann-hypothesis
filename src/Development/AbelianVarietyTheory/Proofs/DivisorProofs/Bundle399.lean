module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle342
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle004

@[expose] public section

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD.Loc

variable {k : Type} [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} {x : Fin (d + 1) → F}

theorem gen_mem (I : Finset (Fin (d + 1))) {i : Fin (d + 1)} (hi : i ∈ I) (j : Fin (d + 1)) :
    x j / x i ∈ rA k x I :=
  Algebra.subset_adjoin ⟨i, hi, j, rfl⟩

theorem rA_mono {I J : Finset (Fin (d + 1))} (h : I ⊆ J) : rA k x I ≤ rA k x J :=
  Algebra.adjoin_mono fun _ ⟨i, hi, j, e⟩ => ⟨i, h hi, j, e⟩

theorem prod_mem_single (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) :
    ∏ j ∈ I, x j / x i ∈ rA k x {i} :=
  Subalgebra.prod_mem _ fun j _ => gen_mem {i} (Finset.mem_singleton_self i) j

theorem gen_mul_prod_mem (hne : ∀ l, x l ≠ 0) (I : Finset (Fin (d + 1))) (i : Fin (d + 1))
    {i' : Fin (d + 1)} (hi' : i' ∈ I) (j : Fin (d + 1)) :
    x j / x i' * ∏ l ∈ I, x l / x i ∈ rA k x {i} := by
  rw [← Finset.mul_prod_erase I (fun l => x l / x i) hi', ← mul_assoc]
  have e : x j / x i' * (x i' / x i) = x j / x i := by
    field_simp [hne i', hne i]
  rw [e]
  exact Subalgebra.mul_mem _ (gen_mem {i} (Finset.mem_singleton_self i) j)
    (Subalgebra.prod_mem _ fun l _ => gen_mem {i} (Finset.mem_singleton_self i) l)

end GlobalTheory.PD.Loc


open GlobalTheory.PD.Loc in
theorem GlobalTheory.PD.rA_eq_loc : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F),
    IsPd k x → ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → ∀ y : F,
      y ∈ rA k x I ↔ ∃ N : ℕ, y * (∏ j ∈ I, x j / x i) ^ N ∈ rA k x {i} := by
  intro k _ F _ _ d x hx I i hi y
  set P := ∏ j ∈ I, x j / x i with hP
  have hPm : P ∈ rA k x {i} := prod_mem_single I i
  constructor
  · intro hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨i', hi', j, rfl⟩ := hz
      exact ⟨1, by rw [pow_one]; exact gen_mul_prod_mem hx.ne I i hi' j⟩
    | algebraMap r => exact ⟨0, by rw [pow_zero, mul_one]; exact Subalgebra.algebraMap_mem _ r⟩
    | add a b _ _ ha hb =>
      obtain ⟨N₁, h₁⟩ := ha
      obtain ⟨N₂, h₂⟩ := hb
      refine ⟨N₁ + N₂, ?_⟩
      have e : (a + b) * P ^ (N₁ + N₂) = (a * P ^ N₁) * P ^ N₂ + (b * P ^ N₂) * P ^ N₁ := by ring
      rw [e]
      exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ h₁ (Subalgebra.pow_mem _ hPm _))
        (Subalgebra.mul_mem _ h₂ (Subalgebra.pow_mem _ hPm _))
    | mul a b _ _ ha hb =>
      obtain ⟨N₁, h₁⟩ := ha
      obtain ⟨N₂, h₂⟩ := hb
      refine ⟨N₁ + N₂, ?_⟩
      have e : (a * b) * P ^ (N₁ + N₂) = (a * P ^ N₁) * (b * P ^ N₂) := by ring
      rw [e]
      exact Subalgebra.mul_mem _ h₁ h₂
  · rintro ⟨N, hN⟩
    have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (hx.ne j) (hx.ne i)
    have hPinv : P⁻¹ ∈ rA k x I := by
      rw [hP, ← Finset.prod_inv_distrib]
      exact Subalgebra.prod_mem _ fun j hj => by rw [inv_div]; exact gen_mem I hj i
    have e : y = (y * P ^ N) * P⁻¹ ^ N := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hP0, one_pow, mul_one]
    rw [e]
    exact Subalgebra.mul_mem _ (rA_mono (Finset.singleton_subset_iff.2 hi) hN) (Subalgebra.pow_mem _ hPinv _)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD

theorem IsFinCover.dlog_basis_and_vanish : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → (∃ b : Module.Basis (Fin d) K Ω[K⁄k], ∀ j, b j = (algebraMap F K (x j.succ / x 0))⁻¹ • D k K (algebraMap F K (x j.succ / x 0))) ∧ ∀ q, d < q → ∀ y ∈ ⋀[K]^q Ω[K⁄k], y = 0 := by
  intro k _ _ F K _ _ _ _ _ _ d x h
  obtain ⟨b, hb⟩ := h.exists_basis
  have hu : ∀ j : Fin d, (algebraMap F K (x j.succ / x 0))⁻¹ ≠ 0 := fun j =>
    inv_ne_zero ((map_ne_zero _).2 (div_ne_zero (h.pd.ne _) (h.pd.ne 0)))
  haveI : Module.Finite K Ω[K⁄k] := Module.Finite.of_basis b
  refine ⟨⟨b.unitsSMul (fun j => Units.mk0 _ (hu j)), fun j => ?_⟩, fun q hq y hy => ?_⟩
  · rw [Module.Basis.unitsSMul_apply, hb]
    rfl
  · rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨m, rfl⟩ := hz
      apply AlternatingMap.map_linearDependent
      intro hli
      have h1 := hli.fintype_card_le_finrank
      rw [Module.finrank_eq_card_basis b] at h1
      simp at h1
      omega
    | zero => rfl
    | add a c _ _ ha hc => rw [ha, hc, add_zero]
    | smul r a _ ha => rw [ha, smul_zero]

end GlobalTheory.PD
end

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD.KSpan

theorem alt_mem_of_span {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    {n : ℕ} (f : M [⋀^Fin n]→ₗ[K] N) (s : Set M) (hs : Submodule.span K s = ⊤) (T : Submodule K N)
    (hT : ∀ v : Fin n → M, (∀ i, v i ∈ s) → f v ∈ T) (v : Fin n → M) : f v ∈ T := by
  have key : ∀ j : ℕ, ∀ v : Fin n → M, (∀ i : Fin n, j ≤ i.val → v i ∈ s) → f v ∈ T := by
    intro j
    induction j with
    | zero => intro v hv; exact hT v fun i => hv i (Nat.zero_le _)
    | succ j ih =>
      intro v hv
      by_cases hj : j < n
      · have hmem : v ⟨j, hj⟩ ∈ Submodule.span K s := hs ▸ Submodule.mem_top
        have hall : ∀ x ∈ Submodule.span K s, f (Function.update v ⟨j, hj⟩ x) ∈ T := by
          intro x hx
          induction hx using Submodule.span_induction with
          | mem x hx =>
            apply ih
            intro i hi
            by_cases h : i = ⟨j, hj⟩
            · rw [h, Function.update_self]; exact hx
            · rw [Function.update_of_ne h]
              apply hv
              have : i.val ≠ j := fun h' => h (Fin.ext h')
              omega
          | zero => rw [AlternatingMap.map_update_zero]; exact T.zero_mem
          | add a b _ _ ha hb => rw [AlternatingMap.map_update_add]; exact T.add_mem ha hb
          | smul r a _ ha => rw [AlternatingMap.map_update_smul]; exact T.smul_mem r ha
        simpa using hall _ hmem
      · exact ih v fun i hi => hv i (by have := i.isLt; omega)
  exact key n v fun i hi => absurd i.isLt (by omega)

end GlobalTheory.PD.KSpan

namespace GlobalTheory.PD


open KSpan in
theorem omB_comap_span_eq_top : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → Submodule.span K ((omB k K B p).comap (e.restrictScalars k) : Set W) = ⊤ := by
  intro k K _ _ _ B _ p W _ _ _ _ e he hr
  have hD : Submodule.span K (D k K '' (B : Set K)) = ⊤ := by
    rw [eq_top_iff, ← span_range_derivation k K, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨b1, b2, hb2, rfl⟩ := IsFractionRing.div_surjective (A := B) y
    have h2 : algebraMap B K b2 ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb2
    set q := algebraMap B K b1 / algebraMap B K b2 with hqdef
    have e1 : algebraMap B K b1 = q * algebraMap B K b2 := by rw [hqdef, div_mul_cancel₀ _ h2]
    have hq : D k K q = (algebraMap B K b2)⁻¹ • (D k K (algebraMap B K b1) - q • D k K (algebraMap B K b2)) := by
      rw [e1, Derivation.leibniz, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ h2, one_smul]
    have m1 : D k K (algebraMap B K b1) ∈ Submodule.span K (D k K '' (B : Set K)) :=
      Submodule.subset_span ⟨(b1 : K), b1.2, rfl⟩
    have m2 : D k K (algebraMap B K b2) ∈ Submodule.span K (D k K '' (B : Set K)) :=
      Submodule.subset_span ⟨(b2 : K), b2.2, rfl⟩
    rw [SetLike.mem_coe, hq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ m1 (Submodule.smul_mem _ _ m2))
  have hS : (omB k K B p : Set (DR k K)) ⊆ ⋀[K]^p Ω[K⁄k] := by
    intro y hy
    change y ∈ Submodule.span k _ at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, -, v, -, rfl⟩ := hy
      exact Submodule.smul_mem _ b (ExteriorAlgebra.ιMulti_range K p ⟨_, rfl⟩)
    | zero => exact Submodule.zero_mem _
    | add a c _ _ ha hc => exact Submodule.add_mem _ ha hc
    | smul r a _ ha => rw [← algebraMap_smul K r a]; exact Submodule.smul_mem _ _ ha
  have hP : ⋀[K]^p Ω[K⁄k] ≤ Submodule.span K (omB k K B p : Set (DR k K)) := by
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    refine alt_mem_of_span (ExteriorAlgebra.ιMulti K p) _ hD _ ?_ v
    intro v hv
    choose b hb hbv using hv
    apply Submodule.subset_span
    apply Submodule.subset_span
    refine ⟨1, B.one_mem, b, hb, ?_⟩
    rw [one_smul]
    simp only [hbv]
  have hSC : (omB k K B p : Set (DR k K)) ⊆ e '' ((omB k K B p).comap (e.restrictScalars k) : Set W) := by
    intro y hy
    obtain ⟨w, rfl⟩ : y ∈ LinearMap.range e := hr ▸ hS hy
    exact ⟨w, hy, rfl⟩
  rw [eq_top_iff, ← Submodule.map_le_map_iff_of_injective he, ← LinearMap.range_eq_map, hr, Submodule.map_span]
  exact hP.trans (Submodule.span_mono hSC)

end GlobalTheory.PD
end
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD


open KaehlerDifferential in
theorem _root_.GlobalTheory.PD.rA_isFractionRing_isNoetherianRing : ∀ (k : Type) [Field k]
    (F : Type) [Field F] [Algebra k F] (d : ℕ)
    (x : Fin (d + 1) → F), _root_.GlobalTheory.PD.IsPd k x → ∀ I : Finset (Fin (d + 1)),
      I.Nonempty →
      IsFractionRing (_root_.GlobalTheory.PD.rA k x I) F ∧
        IsNoetherianRing (_root_.GlobalTheory.PD.rA k x I) := by
  intro k _ F _ _ d x hx I hI
  set S : Set F := {y | ∃ i ∈ I, ∃ j, y = x j / x i} with hS
  have hA : _root_.GlobalTheory.PD.rA k x I = Algebra.adjoin k S := rfl
  refine ⟨?_, ?_⟩
  · refine IsFractionRing.of_field _ F fun z => ?_
    obtain ⟨i, hi⟩ := hI
    have hle : IntermediateField.adjoin k (Set.range fun j : Fin d => x j.succ / x 0) ≤
        IntermediateField.adjoin k S := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, IntermediateField.mem_adjoin_iff_div]
      refine ⟨x j.succ / x i, Algebra.subset_adjoin ⟨i, hi, j.succ, rfl⟩,
        x 0 / x i, Algebra.subset_adjoin ⟨i, hi, 0, rfl⟩, ?_⟩
      have h0 := hx.ne 0
      have hi0 := hx.ne i
      field_simp
    have hz : z ∈ IntermediateField.adjoin k S := by
      apply hle
      rw [hx.gen]
      trivial
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    exact ⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩
  · have hfin : S.Finite :=
      (Set.finite_range fun q : Fin (d + 1) × Fin (d + 1) => x q.2 / x q.1).subset
        (by rintro _ ⟨i, -, j, rfl⟩; exact ⟨(i, j), rfl⟩)
    have hfg : (_root_.GlobalTheory.PD.rA k x I).FG := by
      rw [hA, ← hfin.coe_toFinset]
      exact Subalgebra.fg_adjoin_finset _
    haveI := (Subalgebra.fg_iff_finiteType _).mp hfg
    exact Algebra.FiniteType.isNoetherianRing k _

end GlobalTheory.PD
end

section

set_option autoImplicit false

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

section DualMono

variable {k : Type} [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} {x : Fin (d + 1) → F}

theorem rA_le_of_subset {I J : Finset (Fin (d + 1))} (h : I ⊆ J) : rA k x I ≤ rA k x J := by
  refine Algebra.adjoin_mono ?_
  rintro y ⟨i, hi, j, rfl⟩
  exact ⟨i, h hi, j, rfl⟩

theorem div_mem_rA_of_mem {J : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ J) (j : Fin (d + 1)) :
    x j / x i ∈ rA k x J :=
  Algebra.subset_adjoin ⟨i, hi, j, rfl⟩

theorem mem_omA_iff_mul {I : Finset (Fin (d + 1))} {y : F} :
    y ∈ omA k x I ↔ ∀ i ∈ I, (∏ j, x i / x j) * y ∈ rA k x I := by
  simp [omA, Submodule.mem_iInf]

theorem mul_mem_omA_of_mem_rA {J : Finset (Fin (d + 1))} {r y : F} (hr : r ∈ rA k x J) (hy : y ∈ omA k x J) :
    r * y ∈ omA k x J := by
  rw [mem_omA_iff_mul] at hy ⊢
  intro i hi
  rw [mul_left_comm]
  exact (rA k x J).mul_mem hr (hy i hi)

theorem omA_le_of_subset (hx : ∀ i, x i ≠ 0) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (h : I ⊆ J) :
    omA k x I ≤ omA k x J := by
  obtain ⟨i₀, hi₀⟩ := hI
  intro y hy
  rw [mem_omA_iff_mul] at hy ⊢
  intro i hi
  have e : (∏ j, x i / x j) = (x i / x i₀) ^ (d + 1) * ∏ j, x i₀ / x j := by
    have hc : (x i / x i₀) ^ (d + 1) = ∏ _j : Fin (d + 1), (x i / x i₀) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hc, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    field_simp [hx i₀, hx j]
  rw [e, mul_assoc]
  exact (rA k x J).mul_mem ((rA k x J).pow_mem (div_mem_rA_of_mem (h hi₀) i) _) (rA_le_of_subset h (hy i₀ hi₀))

variable {W W' : Type} [AddCommGroup W] [Module F W] [Module k W] [IsScalarTower k F W]
  [AddCommGroup W'] [Module F W'] [Module k W'] [IsScalarTower k F W']

end DualMono

end GlobalTheory.PD
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

variable (k K : Type) [Field k] [Field K] [Algebra k K]

theorem dDR_ιMulti_D (q : ℕ) (v : Fin q → K) :
    dDR k K (ExteriorAlgebra.ιMulti K q fun j => D k K (v j)) = 0 := by
  induction q with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply, ← map_one (algebraMap K (DR k K)), dDR_algebraMap,
      Derivation.map_one_eq_zero, map_zero]
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, dDR_mul]
    have ht : Matrix.vecTail (fun j => D k K (v j)) = fun j => D k K (v j.succ) := rfl
    rw [ht, ih (fun j => v j.succ), mul_zero, zero_add,
      show dDR k K (ExteriorAlgebra.ι K (D k K (v 0))) = 0 from dDR_D (v 0), zero_mul]

variable {k K}

theorem mem_deg_of_mem_omB (B : Subalgebra k K) (q : ℕ) (a : DR k K) (ha : a ∈ omB k K B q) :
    a ∈ ⋀[K]^q Ω[K⁄k] := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, -, v, -, rfl⟩ := hx
    exact Submodule.smul_mem _ c (ExteriorAlgebra.ιMulti_range K q ⟨_, rfl⟩)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul r x _ hx => exact Submodule.smul_of_tower_mem _ r hx

theorem mul_mem_omB (B : Subalgebra k K) (p q : ℕ) (a : DR k K) (ha : a ∈ omB k K B p)
    (b : DR k K) (hb : b ∈ omB k K B q) : a * b ∈ omB k K B (p + q) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc, v, hv, rfl⟩ := hx
      obtain ⟨c', hc', w, hw, rfl⟩ := hy
      have happ : Fin.append (fun j => D k K (v j)) (fun j => D k K (w j)) =
          fun j => D k K (Fin.append v w j) := by
        funext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
      refine Submodule.subset_span ⟨c * c', B.mul_mem hc hc', Fin.append v w, fun j => ?_, ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · rw [Fin.append_left]; exact hv i
        · rw [Fin.append_right]; exact hw i
      · rw [smul_mul_smul_comm, ExteriorAlgebra.ιMulti_mul_ιMulti, happ]
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem dDR_mem_omB (B : Subalgebra k K) (p : ℕ) (a : DR k K) (ha : a ∈ omB k K B p) :
    dDR k K a ∈ omB k K B (p + 1) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [dDR_smul, dDR_ιMulti_D, smul_zero, add_zero]
    refine Submodule.subset_span ⟨1, B.one_mem, Fin.cons c v, fun j => ?_, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) j
      · rw [Fin.cons_zero]; exact hc
      · rw [Fin.cons_succ]; exact hv i
    · rw [one_smul, ExteriorAlgebra.ιMulti_succ_apply]
      simp only [Matrix.vecTail, Function.comp_def, Fin.cons_succ, Fin.cons_zero]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem smul_mem_omB (B : Subalgebra k K) (p : ℕ) (c : K) (hc : c ∈ B) (a : DR k K)
    (ha : a ∈ omB k K B p) : c • a ∈ omB k K B p := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hx
    exact Submodule.subset_span ⟨c * b, B.mul_mem hc hb, v, hv, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_comm c r x]; exact Submodule.smul_mem _ r hx

theorem omB_mono (B B' : Subalgebra k K) (h : B ≤ B') (p : ℕ) : omB k K B p ≤ omB k K B' p := by
  refine Submodule.span_mono ?_
  rintro y ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩

theorem mem_omB_zero (B : Subalgebra k K) (y : DR k K) :
    y ∈ omB k K B 0 ↔ ∃ c ∈ B, y = algebraMap K (DR k K) c := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, v, -, rfl⟩ := hx
      exact ⟨b, hb, by rw [ExteriorAlgebra.ιMulti_zero_apply, Algebra.smul_def, mul_one]⟩
    | zero => exact ⟨0, B.zero_mem, (map_zero _).symm⟩
    | add x z _ _ hx hz =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hz
      exact ⟨c + c', B.add_mem hc hc', (map_add _ _ _).symm⟩
    | smul r x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨r • c, B.smul_mem hc r, by simp only [Algebra.algebraMap_eq_smul_one, smul_assoc]⟩
  · rintro ⟨c, hc, rfl⟩
    exact Submodule.subset_span ⟨c, hc, Fin.elim0, fun j => j.elim0, by
      rw [ExteriorAlgebra.ιMulti_zero_apply, Algebra.smul_def, mul_one]⟩

theorem omB_alg : ∀ (k K : Type) [Field k] [Field K] [Algebra k K], ∀ (B : Subalgebra k K) (p q : ℕ),
    (∀ a ∈ omB k K B p, ∀ b ∈ omB k K B q, a * b ∈ omB k K B (p + q)) ∧
    (∀ a ∈ omB k K B p, dDR k K a ∈ omB k K B (p + 1) ∧ sg k K a = (-1 : k) ^ p • a ∧
      a ∈ ⋀[K]^p Ω[K⁄k] ∧ ∀ c ∈ B, c • a ∈ omB k K B p) ∧
    (∀ B' : Subalgebra k K, B ≤ B' → omB k K B p ≤ omB k K B' p) ∧
    ∀ y : DR k K, y ∈ omB k K B 0 ↔ ∃ c ∈ B, y = algebraMap K (DR k K) c := by
  intro k K _ _ _ B p q
  refine ⟨fun a ha b hb => mul_mem_omB B p q a ha b hb, fun a ha => ?_,
    fun B' h => omB_mono B B' h p, mem_omB_zero B⟩
  have hdeg := mem_deg_of_mem_omB B p a ha
  refine ⟨dDR_mem_omB B p a ha, ?_, hdeg, fun c hc => smul_mem_omB B p c hc a ha⟩
  change sgn a = _
  rw [sgn_of_mem hdeg, Algebra.smul_def, map_pow, map_neg, map_one]

end GlobalTheory.PD
end
end

section

open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

theorem _root_.GlobalTheory.T.chernCurvature_form_self_eq_dual_norm : ∀ (n g : ℕ) (H : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (z : Fin n → ℂ), MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, mddbar H z ξ η = 0) → ∀ ξ v, form (H z) (curv H z ξ ξ *ᵥ v) v = form (H z)⁻¹ (mdel H z ξ *ᵥ v) (mdel H z ξ *ᵥ v) := by
  first | exact @GlobalTheory.CurvForm.form_curv_self_eq | exact GlobalTheory.CurvForm.form_curv_self_eq | (intros; apply GlobalTheory.CurvForm.form_curv_self_eq <;> assumption)
end
