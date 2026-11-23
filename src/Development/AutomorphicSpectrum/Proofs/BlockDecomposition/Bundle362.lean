module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle012
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle020
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle022
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle344
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.LamGap

theorem sum_lt_indicator (N m : ℕ) (h : m ≤ N) :
    (∑ i : Fin N, if (i : ℕ) < m then 1 else 0) = m := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < m then 1 else 0) N, Finset.sum_boole]
  have hf : (Finset.range N).filter (fun i => i < m) = Finset.range m := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hf, Finset.card_range, Nat.cast_id]

theorem sum_ge_indicator (N m : ℕ) (h : m ≤ N) :
    (∑ i : Fin N, if m ≤ (i : ℕ) then 1 else 0) = N - m := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if m ≤ i then 1 else 0) N, Finset.sum_boole]
  have hf : (Finset.range N).filter (fun i => m ≤ i) = Finset.Ico m N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf, Nat.card_Ico, Nat.cast_id]

theorem lamOf_sub {N : ℕ} (g : Fin (N - 1) → ℕ) (i i' : Fin N) (h : i < i') :
    (Zls.lamOf g i - Zls.lamOf g i').toNat
      = ∑ j : Fin (N - 1), if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 := by
  have hii : (i : ℕ) < (i' : ℕ) := h
  have key : Zls.lamOf g i - Zls.lamOf g i'
      = ((∑ j : Fin (N - 1), if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 : ℕ) : ℤ) := by
    simp only [Zls.lamOf]
    rw [← Finset.sum_sub_distrib, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp_all <;> omega
  rw [key, Int.toNat_natCast]

theorem gap_count (N : ℕ) (c j : ℕ) (hj : j + 1 ≤ N) :
    (∑ i : Fin N, ∑ i' : Fin N, if (i : ℕ) ≤ j ∧ j < (i' : ℕ) then c else 0)
      = c * ((j + 1) * (N - (j + 1))) := by
  calc (∑ i : Fin N, ∑ i' : Fin N, if (i : ℕ) ≤ j ∧ j < (i' : ℕ) then c else 0)
      = ∑ i : Fin N, ∑ i' : Fin N,
          c * ((if (i : ℕ) < j + 1 then 1 else 0) * (if j + 1 ≤ (i' : ℕ) then 1 else 0)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
        have a1 : ((i : ℕ) < j + 1) ↔ (i : ℕ) ≤ j := by omega
        have a2 : (j + 1 ≤ (i' : ℕ)) ↔ j < (i' : ℕ) := by omega
        simp only [a1, a2]
        split_ifs <;> simp_all
    _ = c * ((∑ i : Fin N, if (i : ℕ) < j + 1 then 1 else 0) *
          (∑ i' : Fin N, if j + 1 ≤ (i' : ℕ) then 1 else 0)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = c * ((j + 1) * (N - (j + 1))) := by
        rw [sum_lt_indicator N (j + 1) hj, sum_ge_indicator N (j + 1) hj]

theorem lamOf_antitone_gap_sum (N : ℕ) (g : Fin (N - 1) → ℕ) :
    Antitone (Zls.lamOf g) ∧
      (∑ i : Fin N, ∑ i' : Fin N,
          if i < i' then (Zls.lamOf g i - Zls.lamOf g i').toNat else 0)
        = ∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) := by
  refine ⟨fun a b hab => ?_, ?_⟩
  · simp only [Zls.lamOf]
    refine Finset.sum_le_sum fun j _ => ?_
    have hab' : (a : ℕ) ≤ (b : ℕ) := hab
    split_ifs <;> omega
  · have step : ∀ i i' : Fin N,
        (if i < i' then (Zls.lamOf g i - Zls.lamOf g i').toNat else 0)
          = ∑ j : Fin (N - 1), if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 := by
      intro i i'
      split_ifs with hlt
      · exact lamOf_sub g i i' hlt
      · symm
        refine Finset.sum_eq_zero fun j _ => ?_
        have hn : ¬ ((i : ℕ) < (i' : ℕ)) := hlt
        rw [if_neg]
        rintro ⟨h1, h2⟩
        omega
    calc (∑ i : Fin N, ∑ i' : Fin N,
            if i < i' then (Zls.lamOf g i - Zls.lamOf g i').toNat else 0)
        = ∑ i : Fin N, ∑ i' : Fin N, ∑ j : Fin (N - 1),
            if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => step i i'
      _ = ∑ i : Fin N, ∑ j : Fin (N - 1), ∑ i' : Fin N,
            if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ j : Fin (N - 1), ∑ i : Fin N, ∑ i' : Fin N,
            if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 :=
          Finset.sum_comm
      _ = ∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact gap_count N (g j) j (by have := j.isLt; omega)

end GlobalTheory.CompanionTheory.LamGap
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.LamOf

theorem lamOf_add_and_single :
    ∀ (N : ℕ), (∀ g g' : Fin (N - 1) → ℕ, Zls.lamOf (g + g') = Zls.lamOf g + Zls.lamOf g') ∧
      ∀ j : Fin (N - 1), Zls.lamOf (Pi.single j 1) = Zls.omegaVec N ((j : ℕ) + 1) := by
  intro N
  refine ⟨fun g g' => ?_, fun j => ?_⟩
  · funext i
    simp only [Zls.lamOf, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  · funext i
    simp only [Zls.lamOf, Zls.omegaVec]
    rw [Finset.sum_eq_single j]
    · by_cases h : (i : ℕ) ≤ (j : ℕ)
      · simp [h, Nat.lt_succ_of_le h]
      · have h' : ¬ (i : ℕ) < (j : ℕ) + 1 := fun h2 => h (Nat.le_of_lt_succ h2)
        simp [h, h']
    · intro l _ hl
      simp [Pi.single_apply, hl]
    · intro hj
      exact absurd (Finset.mem_univ j) hj

end GlobalTheory.CompanionTheory.LamOf
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.CongruenceCoef

theorem conj_mem_Km (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N m : ℕ) {p x : GL (Fin N) k}
    (hp : p ∈ KO k (Fin N)) (hx : x ∈ Zls.Km k N m) : p * x * p⁻¹ ∈ Zls.Km k N m := by
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, hb, rfl⟩ := hx
  refine ⟨a * b * a⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  exact (MonoidHom.normal_ker _).conj_mem b hb a

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ fixed π H ↔ ∀ h ∈ H, π h v = v := by
  constructor
  · intro hv h hh
    have := hv ⟨h, hh⟩
    simpa using this
  · intro hv h
    simpa using hv h h.2

theorem coef_const_translated_double_coset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), ∀ (m : ℕ) (v : V), v ∈ fixed π (Zls.Km k N m) → ∀ l : Module.Dual ℂ V, (∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l) → ∀ (p1 p2 : GL (Fin N) k), p1 ∈ KO k (Fin N) → p2 ∈ KO k (Fin N) → (π p2 v ∈ fixed π (Zls.Km k N m)) ∧ (∀ x ∈ Zls.Km k N m, (l ∘ₗ π p1) ∘ₗ π x = l ∘ₗ π p1) ∧ ∀ (D : GL (Fin N) k), ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m, l (π (p1 * x * D * y * p2) v) = (l ∘ₗ π p1) (π D (π p2 v)) := by
  intro k _ _ _ _ N V _ _ π m v hv l hl p1 p2 hp1 hp2
  have hv' := (mem_fixed_iff π _ v).1 hv
  have h1 : ∀ y ∈ Zls.Km k N m, π y (π p2 v) = π p2 v := by
    intro y hy
    have hc : p2⁻¹ * y * p2⁻¹⁻¹ ∈ Zls.Km k N m := conj_mem_Km k N m (inv_mem hp2) hy
    have e : y * p2 = p2 * (p2⁻¹ * y * p2⁻¹⁻¹) := by group
    have h := hv' _ hc
    calc π y (π p2 v) = π (y * p2) v := by rw [map_mul, Module.End.mul_apply]
      _ = π p2 (π (p2⁻¹ * y * p2⁻¹⁻¹) v) := by rw [e, map_mul, Module.End.mul_apply]
      _ = π p2 v := by rw [h]
  have h2 : ∀ x ∈ Zls.Km k N m, (l ∘ₗ π p1) ∘ₗ π x = l ∘ₗ π p1 := by
    intro x hx
    have hc : p1 * x * p1⁻¹ ∈ Zls.Km k N m := conj_mem_Km k N m hp1 hx
    have e : p1 * x = (p1 * x * p1⁻¹) * p1 := by group
    have h := hl _ hc
    ext w
    have hw := LinearMap.congr_fun h (π p1 w)
    simp only [LinearMap.comp_apply] at hw ⊢
    calc l (π p1 (π x w)) = l (π (p1 * x) w) := by rw [map_mul, Module.End.mul_apply]
      _ = l (π (p1 * x * p1⁻¹) (π p1 w)) := by rw [e, map_mul, Module.End.mul_apply]; simp
      _ = l (π p1 w) := hw
  refine ⟨(mem_fixed_iff π _ _).2 h1, h2, ?_⟩
  intro D x hx y hy
  have h3 := LinearMap.congr_fun (h2 x hx) (π D (π p2 v))
  simp only [LinearMap.comp_apply] at h3
  have e : π (p1 * x * D * y * p2) v = π p1 (π x (π D (π y (π p2 v)))) := by
    simp only [map_mul, Module.End.mul_apply]
  rw [e, h1 y hy, h3]
  simp only [LinearMap.comp_apply]

end GlobalTheory.CompanionTheory.CongruenceCoef
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.CongruenceSubgroups

theorem Km_antitone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N m m' : ℕ), m ≤ m' → Zls.Km k N m' ≤ Zls.Km k N m := by
  intro k _ _ _ _ N m m' h
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨g, ?_, rfl⟩
  have hle : Ideal.span {Zls.unif k ^ m'} ≤ Ideal.span {Zls.unif k ^ m} :=
    Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)
  have hg' : Matrix.GeneralLinearGroup.map (n := Fin N)
      (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m'})) g = 1 := hg
  have h2 := congrArg (Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.factor hle)) hg'
  rw [map_one] at h2
  show Matrix.GeneralLinearGroup.map (n := Fin N)
      (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m})) g = 1
  rw [← h2]
  ext i j
  simp [Matrix.GeneralLinearGroup.map]

end GlobalTheory.CompanionTheory.CongruenceSubgroups
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.UnifPow

theorem valuation_unifU_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : valuation k ((Zls.unifU k : kˣ) : k) < 1 := by
  have hle : valuation k ((Zls.unif k : 𝒪[k]) : k) ≤ 1 := (Zls.unif k).2
  refine lt_of_le_of_ne hle fun h1 => (Zls.irreducible_unif (k := k)).not_isUnit ?_
  exact ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one).2 h1

theorem tendsto_unifU_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k],
    Filter.Tendsto (fun n : ℕ => ((Zls.unifU k : kˣ) : k) ^ n) Filter.atTop (nhds 0) := by
  intro k _ _ _ _
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
  intro γ hγ
  have h := valuation_unifU_lt_one k
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

end GlobalTheory.CompanionTheory.UnifPow
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.Dblock.CartanCover

theorem sum_tel (A : ℕ → ℤ) (i n : ℕ) (h : i ≤ n) :
    ∑ j ∈ Finset.range n, (if i ≤ j then A j - A (j + 1) else 0) = A i - A n := by
  induction n, h using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero]
    · simp
    · intro j hj
      rw [if_neg]
      simpa using hj
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih, if_pos hn]
    ring

theorem exists_lamOf (N : ℕ) (hN : 1 ≤ N) (a : Fin N → ℤ) (ha : Antitone a) :
    ∃ g : Fin (N - 1) → ℕ, ∀ i, Zls.lamOf g i = a i - a ⟨N - 1, by omega⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  let A : ℕ → ℤ := fun j => a ⟨min j n, by omega⟩
  have hA : ∀ j, A (j + 1) ≤ A j := fun j => ha (by simp only [Fin.le_def]; omega)
  refine ⟨fun j => (A j - A (j + 1)).toNat, fun i => ?_⟩
  have h1 := sum_tel A i n (by omega)
  rw [Finset.sum_range] at h1
  have hi : A i = a i := by
    simp only [A]
    congr 1
    ext
    simp only
    omega
  have hn : A n = a ⟨n + 1 - 1, by omega⟩ := by
    simp only [A]
    congr 1
    ext
    simp
  rw [← hi, ← hn, ← h1]
  unfold Zls.lamOf
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · exact Int.toNat_of_nonneg (by linarith [hA j])
  · rfl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

noncomputable abbrev red (N m : ℕ) :
    GL (Fin N) 𝒪[k] →* GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) :=
  Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}))

noncomputable abbrev incl (N : ℕ) : GL (Fin N) 𝒪[k] →* GL (Fin N) k :=
  Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k)

theorem finite_red (N m : ℕ) : Finite (GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m})) := by
  haveI : IsFractionRing 𝒪[k] k := GlobalTheory.CompanionTheory.LocalFieldValuationRing.isFractionRing_integer k
  haveI : Finite (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) :=
    GlobalTheory.CompanionTheory.Congruence.finite_quotient_span_pow 𝒪[k] (Zls.unif k) m Zls.irreducible_unif
  infer_instance

theorem diag_eq (N : ℕ) (a : Fin N → ℤ) (g : Fin (N - 1) → ℕ) (c : ℤ)
    (hg : ∀ i, Zls.lamOf g i = a i - c) :
    (Matrix.diagonal (fun i => (algebraMap 𝒪[k] k (Zls.unif k)) ^ (a i)) : Matrix (Fin N) (Fin N) k) =
      ((Zls.diagPow k N (Zls.lamOf g) * Matrix.GeneralLinearGroup.scalar (Fin N) (Zls.unifU k ^ c) :
        GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := by
  have h1 : ((Zls.diagPow k N (Zls.lamOf g) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => ((Zls.unifU k ^ Zls.lamOf g i : kˣ) : k) := rfl
  have h2 : ((Matrix.GeneralLinearGroup.scalar (Fin N) (Zls.unifU k ^ c) : GL (Fin N) k) :
      Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun _ => ((Zls.unifU k ^ c : kˣ) : k) := rfl
  rw [Units.val_mul, h1, h2, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Units.val_mul, ← zpow_add, hg, sub_add_cancel, Units.val_zpow_eq_zpow_val]
  rfl

theorem cartan_cover : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N m : ℕ), 1 ≤ m → 1 ≤ N → ∃ s : Finset (GL (Fin N) k × GL (Fin N) k), (∀ p ∈ s, p.1 ∈ KO k (Fin N) ∧ p.2 ∈ KO k (Fin N)) ∧ ∀ h : GL (Fin N) k, ∃ p ∈ s, ∃ g : Fin (N - 1) → ℕ, ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, ∃ z ∈ Subgroup.center (GL (Fin N) k), h = p.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p.2 * z := by
  intro k _ _ _ _ N m _ hN
  classical
  haveI : IsFractionRing 𝒪[k] k := GlobalTheory.CompanionTheory.LocalFieldValuationRing.isFractionRing_integer k
  haveI := finite_red k N m

  have hsec : ∀ u : GL (Fin N) 𝒪[k], ∃ w : GL (Fin N) 𝒪[k], red k N m w = red k N m u := fun u => ⟨u, rfl⟩
  let σ : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) → GL (Fin N) 𝒪[k] := fun c =>
    if hc : ∃ w, red k N m w = c then hc.choose else 1
  have hσ : ∀ u, red k N m (σ (red k N m u)) = red k N m u := fun u => by
    have hc : ∃ w, red k N m w = red k N m u := hsec u
    simp only [σ, dif_pos hc]
    exact hc.choose_spec
  let f : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) × GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) →
      GL (Fin N) k × GL (Fin N) k := fun c => (incl k N (σ c.1), incl k N (σ c.2))
  refine ⟨(Set.finite_range f).toFinset, ?_, fun h => ?_⟩
  · intro p hp
    obtain ⟨c, rfl⟩ := (Set.Finite.mem_toFinset _).1 hp
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · have hh : IsUnit (h : Matrix (Fin N) (Fin N) k).det := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
    obtain ⟨u, v, a, hu, hv, ha, e⟩ := GlobalTheory.CompanionTheory.Dblock.CartanDVR.cartan_exists 𝒪[k] k N (Zls.unif k)
      Zls.irreducible_unif (h : Matrix (Fin N) (Fin N) k) hh
    obtain ⟨g, hg⟩ := exists_lamOf N hN a ha
    let U : GL (Fin N) 𝒪[k] := Matrix.nonsingInvUnit u hu
    let V : GL (Fin N) 𝒪[k] := Matrix.nonsingInvUnit v hv
    let z : GL (Fin N) k := Matrix.GeneralLinearGroup.scalar (Fin N) (Zls.unifU k ^ a ⟨N - 1, by omega⟩)
    have hz : z ∈ Subgroup.center (GL (Fin N) k) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    have hzc : ∀ w : GL (Fin N) k, z * w = w * z := fun w => ((Subgroup.mem_center_iff.1 hz) w).symm
    have hmat : h = incl k N U * (Zls.diagPow k N (Zls.lamOf g) * z) * incl k N V := by
      apply Units.ext
      rw [e, diag_eq k N a g _ hg]
      rfl
    let p₁ := σ (red k N m U)
    let p₂ := σ (red k N m V)
    have hx : p₁⁻¹ * U ∈ (red k N m).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
    have hy : V * p₂⁻¹ ∈ (red k N m).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel]
    refine ⟨f (red k N m U, red k N m V), (Set.Finite.mem_toFinset _).2 ⟨_, rfl⟩, g,
      incl k N (p₁⁻¹ * U), ⟨_, hx, rfl⟩, incl k N (V * p₂⁻¹), ⟨_, hy, rfl⟩, z, hz, ?_⟩
    simp only [f, map_mul, map_inv]
    rw [hmat]
    have hzV : ∀ w : GL (Fin N) k, w * z = z * w := fun w => (hzc w).symm
    change incl k N U * (Zls.diagPow k N (Zls.lamOf g) * z) * incl k N V =
      incl k N p₁ * ((incl k N p₁)⁻¹ * incl k N U) * Zls.diagPow k N (Zls.lamOf g) *
        (incl k N V * (incl k N p₂)⁻¹) * incl k N p₂ * z
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    rw [hzc (incl k N V), mul_inv_cancel_left]

end GlobalTheory.CompanionTheory.Dblock.CartanCover
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.CongruenceBasis

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_unif_lt_one : valuation k (algebraMap 𝒪[k] k (Zls.unif k)) < 1 := by
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 Zls.irreducible_unif.not_isUnit

theorem val_le_val_unif (x : k) (hx : valuation k x < 1) :
    valuation k x ≤ valuation k (algebraMap 𝒪[k] k (Zls.unif k)) := by
  let y : 𝒪[k] := ⟨x, hx.le⟩
  have hy : ¬ IsUnit y :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 hx
  have hmem : y ∈ IsLocalRing.maximalIdeal 𝒪[k] := hy
  rw [Zls.irreducible_unif.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hx' : x = algebraMap 𝒪[k] k c * algebraMap 𝒪[k] k (Zls.unif k) := by
    rw [← map_mul, hc]; rfl
  rw [hx', map_mul]
  exact mul_le_of_le_one_left' c.2

theorem val_sub_one_le_of_mem_Km {N m : ℕ} {g : GL (Fin N) k} (hg : g ∈ Zls.Km k N m) (i j : Fin N) :
    valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
      valuation k (algebraMap 𝒪[k] k (Zls.unif k) ^ m) := by
  obtain ⟨h, hker, rfl⟩ := Subgroup.mem_map.1 hg
  have h1 := congrArg (fun u : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) =>
    u.1 i j) (MonoidHom.mem_ker.1 hker)
  have h2 : (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}))
      ((h : Matrix (Fin N) (Fin N) 𝒪[k]) i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) = 0 := by
    rw [map_sub, sub_eq_zero]
    simpa [Matrix.one_apply, apply_ite] using h1
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h2
  obtain ⟨c, hc⟩ := h2
  have h3 : ((Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) h : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j =
      algebraMap 𝒪[k] k c * algebraMap 𝒪[k] k (Zls.unif k) ^ m := by
    rw [← map_pow, ← map_mul, hc, map_sub]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [h3, map_mul]
  exact mul_le_of_le_one_left' c.2

theorem exists_Km_subset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (U : Set (GL (Fin N) k)), IsOpen U →
    (1 : GL (Fin N) k) ∈ U → ∃ m : ℕ, 1 ≤ m ∧ (Zls.Km k N m : Set (GL (Fin N) k)) ⊆ U := by
  intro k _ _ _ _ N U hU h1
  have hne : algebraMap 𝒪[k] k (Zls.unif k) ≠ 0 :=
    (map_ne_zero_iff (algebraMap 𝒪[k] k) (IsFractionRing.injective 𝒪[k] k)).2
      Zls.irreducible_unif.ne_zero
  obtain ⟨m, hm, hsub⟩ := exists_congruence_subset k N (algebraMap 𝒪[k] k (Zls.unif k)) hne
    val_unif_lt_one val_le_val_unif U (hU.mem_nhds h1)
  exact ⟨m, hm, fun g hg => hsub fun i j => val_sub_one_le_of_mem_Km hg i j⟩

end GlobalTheory.CompanionTheory.CongruenceBasis
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

theorem _root_.GlobalTheory.T.dual_class_twist_neg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (s : ℂ), dualCl (x.nu s) = (dualCl x).nu (-s) := by
  first | exact @GlobalTheory.CompanionTheory.ZcDual.dualCl_nu | exact GlobalTheory.CompanionTheory.ZcDual.dualCl_nu | (intros; apply GlobalTheory.CompanionTheory.ZcDual.dualCl_nu <;> assumption)
end
