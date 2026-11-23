module

public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle087
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle004
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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
import Mathlib.NumberTheory.Padics.ProperSpace
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle027
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

section

open MeasureTheory
open scoped NNReal ENNReal

theorem _root_.GlobalTheory.T.haar_measure_semidirect_product_formula : ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] [MeasurableSpace Q] [BorelSpace Q] (N M : Subgroup Q) [N.Normal] [LocallyCompactSpace N] [LocallyCompactSpace M], IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) → (∀ x, x ∈ N → x ∈ M → x = 1) → ∀ (νN : Measure N) (νM : Measure M), νN.IsHaarMeasure → νN.IsMulRightInvariant → νM.IsHaarMeasure → νM.IsMulRightInvariant → ∀ δ : Q →* ℝ≥0, (∀ n ∈ N, δ n = 1) → (∀ m ∈ M, νN.map (fun n : N => MulAut.conjNormal m n) = (δ m)⁻¹ • νN) → ∀ q : Q, Measure.modularCharacterFun q = δ q := by
  first | exact @GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_semidirect | exact GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_semidirect | (intros; apply GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_semidirect <;> assumption)
end

section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem _root_.GlobalTheory.T.lintegral_power_line_scaling : ∀ s : ℝ, 1 / 2 < s → ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ a : ℝ, 0 < a → ∀ m : ℝ,
    ∫⁻ d : ℝ, ENNReal.ofReal ((a ^ 2 + (d - m) ^ 2) ^ (-s)) = C * ENNReal.ofReal (a ^ (1 - 2 * s)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_sq_add_sq_rpow_neg | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_sq_add_sq_rpow_neg | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_sq_add_sq_rpow_neg <;> assumption)
end

section

open ValuativeRel Matrix
open scoped Topology

namespace GlobalTheory.CompanionTheory.PrincipalCongruence

variable {k : Type*} [Field k] [ValuativeRel k]

theorem inv_congr {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n k)
    (hAB : A * B = 1) {t : k} (ht : valuation k t < 1)
    (hA : ∀ i j, valuation k (A i j - (1 : Matrix n n k) i j) ≤ valuation k t) :
    ∀ i j, valuation k (B i j - (1 : Matrix n n k) i j) ≤ valuation k t := by
  by_contra h
  push_neg at h
  obtain ⟨i₁, j₁, h₁⟩ := h
  haveI : Nonempty (n × n) := ⟨(i₁, j₁)⟩
  obtain ⟨⟨i₀, j₀⟩, hm⟩ := Finite.exists_max
    (fun p : n × n => valuation k (B p.1 p.2 - (1 : Matrix n n k) p.1 p.2))
  have hm' : ∀ l j, valuation k (B l j - (1 : Matrix n n k) l j) ≤
      valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) := fun l j => hm (l, j)
  have hM : valuation k t < valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) :=
    h₁.trans_le (hm' i₁ j₁)
  have hM0 : 0 < valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) :=
    lt_of_le_of_lt zero_le' hM
  have hmat : (A - 1) * (B - 1) = -(A - 1) - (B - 1) := by
    simp only [sub_mul, mul_sub, hAB, one_mul, mul_one]
    abel
  have key : B i₀ j₀ - (1 : Matrix n n k) i₀ j₀ = -(A i₀ j₀ - (1 : Matrix n n k) i₀ j₀) -
      ∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) * (B l j₀ - (1 : Matrix n n k) l j₀) := by
    have := congrFun (congrFun hmat i₀) j₀
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply] at this
    rw [this]
    ring
  have hsum : valuation k (∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) *
      (B l j₀ - (1 : Matrix n n k) l j₀)) ≤
      valuation k t * valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) := by
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hA i₀ l) (hm' l j₀)
  have hlt : valuation k t * valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) <
      valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) :=
    mul_lt_of_lt_one_left hM0 ht
  have hle := Valuation.map_sub (valuation k) (-(A i₀ j₀ - (1 : Matrix n n k) i₀ j₀))
    (∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) * (B l j₀ - (1 : Matrix n n k) l j₀))
  rw [← key, Valuation.map_neg] at hle
  rcases le_max_iff.mp hle with h | h
  · exact absurd ((h.trans (hA i₀ j₀))) (not_le.mpr hM)
  · exact absurd (h.trans hsum) (not_le.mpr hlt)

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def congSet (n : Type*) [DecidableEq n] (t : k) : Set (Matrix n n k) :=
  {A | ∀ i j, valuation k (A i j - (1 : Matrix n n k) i j) ≤ valuation k t}

theorem isOpen_congSet (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0) :
    IsOpen (congSet n t) := by
  have h : congSet n t = ⋂ i, ⋂ j, (fun A : Matrix n n k => A i j - (1 : Matrix n n k) i j) ⁻¹'
      GlobalTheory.SplitWeil.cball (Units.mk0 t ht) := by
    ext A
    simp [congSet, GlobalTheory.SplitWeil.cball]
  rw [h]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (GlobalTheory.SplitWeil.isOpen_cball _).preimage
    ((continuous_id.matrix_elem i j).sub continuous_const)

theorem isCompact_congSet (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0) :
    IsCompact (congSet n t) := by
  have h : congSet n t = Set.pi Set.univ fun i => Set.pi Set.univ fun j =>
      (fun x : k => x + (1 : Matrix n n k) i j) '' GlobalTheory.SplitWeil.cball (Units.mk0 t ht) := by
    ext A
    constructor
    · intro hA i _ j _
      exact ⟨A i j - (1 : Matrix n n k) i j, hA i j, by simp⟩
    · intro hA i j
      obtain ⟨x, hx, hxA⟩ := hA i (Set.mem_univ _) j (Set.mem_univ _)
      have hx' : A i j - (1 : Matrix n n k) i j = x := by
        rw [← hxA]
        simp
      rw [hx']
      exact hx
  rw [h]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    (GlobalTheory.SplitWeil.isCompact_cball _).image (continuous_id.add continuous_const)

def congGL (n : Type*) [Fintype n] [DecidableEq n] (t : k) : Set (GL n k) :=
  {g | (g : Matrix n n k) ∈ congSet n t}

theorem isOpen_congGL (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0) :
    IsOpen (congGL n t) :=
  (isOpen_congSet n ht).preimage Units.continuous_val

theorem isCompact_congGL (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0)
    (ht1 : valuation k t < 1) : IsCompact (congGL n t) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  have hc : IsCompact ((congSet n t ×ˢ (MulOpposite.op '' congSet n t)) ∩
      {p : Matrix n n k × (Matrix n n k)ᵐᵒᵖ |
        p.1 * p.2.unop = 1 ∧ p.2.unop * p.1 = 1}) := by
    refine ((isCompact_congSet n ht).prod
      ((isCompact_congSet n ht).image MulOpposite.continuous_op)).inter_right ?_
    have hu : Continuous fun p : Matrix n n k × (Matrix n n k)ᵐᵒᵖ => p.2.unop :=
      MulOpposite.continuous_unop.comp continuous_snd
    exact (isClosed_eq (continuous_fst.matrix_mul hu) continuous_const).inter
      (isClosed_eq (hu.matrix_mul continuous_fst) continuous_const)
  convert hc using 1
  ext ⟨A, B⟩
  constructor
  · rintro ⟨g, hg, hgp⟩
    simp only [Units.embedProduct_apply, Prod.mk.injEq] at hgp
    obtain ⟨rfl, rfl⟩ := hgp
    refine ⟨⟨hg, _, inv_congr (g : Matrix n n k) _ g.mul_inv ht1 hg, rfl⟩, ?_⟩
    exact ⟨g.mul_inv, g.inv_mul⟩
  · rintro ⟨⟨hA, -⟩, h₁, h₂⟩
    refine ⟨⟨A, B.unop, h₁, h₂⟩, hA, ?_⟩
    simp [Units.embedProduct_apply]

theorem isOpen_isCompact_principal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (t : k), t ≠ 0 → ValuativeRel.valuation k (t) < 1 →
    IsOpen {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
        ValuativeRel.valuation k (t)} ∧
    IsCompact {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
        ValuativeRel.valuation k (t)} :=
  fun _ _ _ _ _ N _ ht ht1 => ⟨isOpen_congGL (Fin N) ht, isCompact_congGL (Fin N) ht ht1⟩

end GlobalTheory.CompanionTheory.PrincipalCongruence
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PadicShift

theorem exists_period (p : ℕ) [Fact p.Prime] {N : Type} (f : ℤ_[p] → N)
    (hf : IsLocallyConstant f) :
    ∃ m : ℕ, ∀ x y : ℤ_[p], ((p : ℤ_[p]) ^ m) ∣ x - y → f x = f y := by
  obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric (s := (Set.univ : Set ℤ_[p]))
    (c := fun v : N => f ⁻¹' {v}) isCompact_univ (fun v => hf.isOpen_fiber v)
    (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ (inv_lt_one_of_one_lt₀ hp)
  refine ⟨m, fun x y hxy => ?_⟩
  obtain ⟨i, hi⟩ := h x (Set.mem_univ _)
  have hx : f x = i := hi (Metric.mem_ball_self hδ)
  have hy : f y = i := by
    apply hi
    rw [Metric.mem_ball, dist_comm, dist_eq_norm]
    have : x - y ∈ Ideal.span {(p : ℤ_[p]) ^ m} := Ideal.mem_span_singleton.2 hxy
    have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow (x - y) m).2 this
    refine lt_of_le_of_lt h2 (lt_of_eq_of_lt ?_ hm)
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hx, hy]

theorem sum_periodic {N : Type} [AddCommGroup N] (g : ℕ → N) (P : ℕ)
    (hg : ∀ i, g (i + P) = g i) (k : ℕ) :
    ∑ i ∈ Finset.range (k * P), g i = k • ∑ i ∈ Finset.range P, g i :=
  _root_.UpperTheory.Reformulated.B.Yra7.main g P hg k

theorem isLocallyConstant_toZModPow (p : ℕ) [Fact p.Prime] (M : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow (p := p) M) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨Metric.closedBall x ((p : ℝ) ^ (-(M : ℤ))),
    IsUltrametricDist.isOpen_closedBall _ (zpow_pos hp _).ne',
    Metric.mem_closedBall_self (zpow_pos hp _).le, fun y hy => ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at hy
  have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow (y - x) M).1 hy
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at h1
  exact h1

theorem val_toZModPow_dvd (p : ℕ) [Fact p.Prime] (M : ℕ) (z : ℤ_[p]) :
    ((p : ℤ_[p]) ^ M) ∣ z - (((PadicInt.toZModPow (p := p) M z).val : ℕ) : ℤ_[p]) := by
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
    ZMod.natCast_zmod_val, sub_self]

theorem exists_primitive (p : ℕ) [Fact p.Prime] {N : Type} [AddCommGroup N] (n : ℕ)
    (hN : ∀ x : N, p ^ n • x = 0) (f : ℤ_[p] → N) (hf : IsLocallyConstant f) :
    ∃ y : ℤ_[p] → N, IsLocallyConstant y ∧ ∀ z, y (z + 1) - y z = f z := by
  obtain ⟨m, hm⟩ := exists_period p f hf
  set M := n + m with hM
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let g : ℕ → N := fun i => f (i : ℤ_[p])
  have hper : ∀ i, g (i + p ^ m) = g i := by
    intro i
    apply hm
    refine ⟨1, ?_⟩
    push_cast
    ring
  have hsum : ∑ i ∈ Finset.range (p ^ M), g i = 0 := by
    rw [hM, pow_add, sum_periodic g (p ^ m) hper (p ^ n), hN]
  have hfg : ∀ z, f z = g (PadicInt.toZModPow (p := p) M z).val := by
    intro z
    apply hm
    exact (pow_dvd_pow _ (Nat.le_add_left m n)).trans (val_toZModPow_dvd p M z)
  refine ⟨fun z => ∑ i ∈ Finset.range (PadicInt.toZModPow (p := p) M z).val, g i,
    (isLocallyConstant_toZModPow p M).comp
      (fun a => ∑ i ∈ Finset.range a.val, g i), fun z => ?_⟩
  have hv : (PadicInt.toZModPow (p := p) M z).val < p ^ M := ZMod.val_lt _
  have hval : (PadicInt.toZModPow (p := p) M (z + 1)).val
      = ((PadicInt.toZModPow (p := p) M z).val + 1) % p ^ M := by
    rw [map_add (f := _), map_one, ← ZMod.val_natCast]
    push_cast
    rw [ZMod.natCast_zmod_val]
  simp only [hval]
  rw [hfg z]
  generalize (PadicInt.toZModPow (p := p) M z).val = v at hv
  rcases Nat.lt_or_ge (v + 1) (p ^ M) with h | h
  · rw [Nat.mod_eq_of_lt h, Finset.sum_range_succ, add_sub_cancel_left]
  · have hv1 : v + 1 = p ^ M := by omega
    rw [hv1, Nat.mod_self, Finset.sum_range_zero, zero_sub, neg_eq_iff_add_eq_zero,
      ← Finset.sum_range_succ, hv1]
    exact hsum

theorem eq_of_shift_invariant (p : ℕ) [Fact p.Prime] {N : Type} (f : ℤ_[p] → N)
    (hf : IsLocallyConstant f) (h : ∀ z, f (z + 1) = f z) (z : ℤ_[p]) : f z = f 0 := by
  have hnat : ∀ k : ℕ, f (k : ℤ_[p]) = f 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, h, ih]
  have hcl : IsClosed {x : ℤ_[p] | f x = f 0} := hf.isClosed_fiber (f 0)
  exact PadicInt.denseRange_natCast.induction_on z hcl hnat

end GlobalTheory.CompanionTheory.PadicShift
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TwistedUnit

theorem sub_sub_smul_eq_zero_of_smul_eq_zero {Λ N : Type} [CommRing Λ] [AddCommGroup N]
    [Module Λ N] [Module.Flat Λ N] (γ : N →ₗ[Λ] N) (c μ : Λ)
    (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (z : N) (hz : μ • z = 0) :
    γ z - z - c • z = 0 := by
  obtain ⟨k, a, y, hx, hf⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := Λ) (M := N)
    (f := fun _ : Fin 1 => μ) (x := fun _ : Fin 1 => z) (by simpa using hz)
  choose d hd using h
  have hz' : z = ∑ j, a 0 j • y j := hx 0
  have h0 : ∀ j, μ * a 0 j = 0 := fun j => by simpa using hf j
  have hlin : ∀ j, a 0 j • (γ (y j) - y j - c • y j) = 0 := by
    intro j
    rw [hd, smul_smul, mul_comm, h0, zero_smul]
  have hsum : γ z - z - c • z = ∑ j, a 0 j • (γ (y j) - y j - c • y j) := by
    conv_lhs => rw [hz']

    simp only [map_sum, map_smul, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => smul_comm _ _ _)
  rw [hsum]
  exact Finset.sum_eq_zero (fun j _ => hlin j)

theorem smul_eq_zero_of_fixed {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N]
    [Module.Flat Λ N] (γ : N →ₗ[Λ] N) (c w ξ μ : Λ) (hμ : μ = c * w * ξ) (hξ : IsNilpotent ξ)
    (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (x : N) (hx : γ x = x) : μ • x = 0 := by
  have hE := sub_sub_smul_eq_zero_of_smul_eq_zero γ c μ h
  have R : ∀ n : ℕ, ∀ x, (w * ξ) • (γ x - x) = 0 → ∃ u, μ • (x - ξ ^ n • u) = 0 := by
    intro n
    induction n with
    | zero => exact fun x _ => ⟨x, by simp⟩
    | succ n ih =>
      intro x hx
      obtain ⟨x', hx'⟩ := h x
      have h1 : μ • (x + (w * ξ) • x') = 0 := by
        have : μ • (x + (w * ξ) • x') = (w * ξ) • (γ x - x) := by
          subst hμ
          linear_combination (norm := module) -(w * ξ) • hx'
        rw [this, hx]
      have h2 := hE _ h1
      simp only [map_add (f := _), map_smul] at h2
      have hM : (w * ξ) • (γ x' - x') = 0 := by
        subst hμ
        linear_combination (norm := module) h2 - hx'
      obtain ⟨u, hu⟩ := ih x' hM
      refine ⟨-w • u, ?_⟩
      have : μ • (x - ξ ^ (n + 1) • (-w • u))
          = μ • (x + (w * ξ) • x') - (w * ξ) • (μ • (x' - ξ ^ n • u)) := by
        module
      rw [this, h1, hu]
      simp
  obtain ⟨n, hn⟩ := hξ
  obtain ⟨u, hu⟩ := R n x (by simp [hx])
  simpa [hn] using hu

theorem exists_mem_smul_top {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N]
    (γ : N →ₗ[Λ] N) (c μ : Λ) (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (𝔞 : Ideal Λ) (x : N)
    (hx : x ∈ 𝔞 • (⊤ : Submodule Λ N)) :
    ∃ x₁ ∈ 𝔞 • (⊤ : Submodule Λ N), γ x - x - c • x = μ • x₁ := by
  induction hx using Submodule.smul_induction_on' with
  | smul a ha n hn =>
    obtain ⟨n', hn'⟩ := h n
    refine ⟨a • n', Submodule.smul_mem_smul ha trivial, ?_⟩
    rw [map_smul]
    linear_combination (norm := module) a • hn'
  | add x hx y hy ihx ihy =>
    obtain ⟨x₁, hx₁, e₁⟩ := ihx
    obtain ⟨y₁, hy₁, e₂⟩ := ihy
    refine ⟨x₁ + y₁, Submodule.add_mem _ hx₁ hy₁, ?_⟩
    rw [map_add (f := _)]
    linear_combination (norm := module) e₁ + e₂

theorem exists_sub_eq_smul {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N]
    (γ : N →ₗ[Λ] N) (c w ξ μ : Λ) (hμ : μ = c * w * ξ) (hξ : IsNilpotent ξ)
    (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (𝔞 : Ideal Λ) (x : N)
    (hx : x ∈ 𝔞 • (⊤ : Submodule Λ N)) :
    ∃ y ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N), γ y - y = μ • x := by
  obtain ⟨n, hn⟩ := hξ
  have P : ∀ m k : ℕ, m + k = n → ∀ x ∈ 𝔞 • (⊤ : Submodule Λ N),
      ∃ y ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N), γ y - y = (μ * ξ ^ k) • x := by
    intro m
    induction m with
    | zero =>
      intro k hk x _
      have : ξ ^ k = 0 := by
        rw [show k = n by omega, hn]
      exact ⟨0, Submodule.zero_mem _, by simp [this]⟩
    | succ m ih =>
      intro k hk x hx
      obtain ⟨x₁, hx₁, e⟩ := exists_mem_smul_top γ c μ h 𝔞 x hx
      obtain ⟨y', hy', e'⟩ := ih (k + 1) (by omega) (w • x₁)
        (Submodule.smul_of_tower_mem _ w hx₁)
      have hξx : ξ • x ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N) := by
        rw [Submodule.mul_smul]
        exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ξ) hx
      refine ⟨(w * ξ ^ k) • (ξ • x) - y',
        Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ hξx) hy', ?_⟩
      simp only [map_sub, map_smul]
      subst hμ
      linear_combination (norm := module) (w * ξ ^ (k + 1)) • e - e'
  simpa using P n 0 rfl x hx

theorem twisted_bijective_up_to :
    ∀ {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N] [Module.Flat Λ N]
      (γ : N →ₗ[Λ] N) (c w ξ μ : Λ), μ = c * w * ξ → IsNilpotent ξ →
      (∀ x, ∃ x', γ x - x - c • x = μ • x') →
      (∀ x, γ x = x → μ • x = 0) ∧ ∀ (𝔞 : Ideal Λ), ∀ x ∈ 𝔞 • (⊤ : Submodule Λ N),
        ∃ y ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N), γ y - y = μ • x := by
  intro Λ N _ _ _ _ γ c w ξ μ hμ hξ h
  exact ⟨smul_eq_zero_of_fixed γ c w ξ μ hμ hξ h,
    fun 𝔞 x hx => exists_sub_eq_smul γ c w ξ μ hμ hξ h 𝔞 x hx⟩

end GlobalTheory.CompanionTheory.TwistedUnit
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre

theorem summable_comp_of_bounded_fibres :
    ∀ (A B : Type) (π : A → B) (k : ℕ), (∀ b, Finite {a // π a = b} ∧ Nat.card {a // π a = b} ≤ k) → ∀ (g : B → ℝ), (∀ b, 0 ≤ g b) → Summable g → Summable (fun a => g (π a)) ∧ ∑' a, g (π a) ≤ k * ∑' b, g b := by
  intro A B π k h g hg hs
  classical
  have hcard : ∀ (u : Finset A) (b : B), (u.filter (fun a => π a = b)).card ≤ k := by
    intro u b
    have hf : ({a | π a = b} : Set A).Finite := Set.finite_coe_iff.mp (h b).1
    calc (u.filter (fun a => π a = b)).card
        = ((u.filter (fun a => π a = b) : Finset A) : Set A).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ ({a | π a = b} : Set A).ncard := by
          apply Set.ncard_le_ncard _ hf
          intro a ha
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
          exact ha.2
      _ = Nat.card {a // π a = b} := (Nat.card_coe_set_eq _).symm
      _ ≤ k := (h b).2
  have hbound : ∀ u : Finset A, ∑ a ∈ u, g (π a) ≤ k * ∑' b, g b := by
    intro u
    rw [Finset.sum_comp]
    calc ∑ b ∈ u.image π, (u.filter (fun a => π a = b)).card • g b
        ≤ ∑ b ∈ u.image π, (k : ℝ) * g b := by
          apply Finset.sum_le_sum
          intro b _
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard u b) (hg b)
      _ = k * ∑ b ∈ u.image π, g b := by rw [Finset.mul_sum]
      _ ≤ k * ∑' b, g b :=
          mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun b _ => hg b)) (Nat.cast_nonneg k)
  have hsum : Summable (fun a => g (π a)) := summable_of_sum_le (fun a => hg (π a)) hbound
  exact ⟨hsum, hsum.tsum_le_of_sum_le hbound⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre
end
