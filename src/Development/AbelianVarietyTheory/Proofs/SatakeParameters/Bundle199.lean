module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle107
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle008
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.HermitianForms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle195
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementE
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FourthPowerTheta
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle014

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphAvg

section Abstract

variable {G : Type} [Group G]

open GlobalTheory.SphLabelOps

theorem finiteIndex_stab {K : Subgroup G} {g : G} {R : Finset G} (hR : Reps K g R) :
    (MulAction.stabilizer K (QuotientGroup.mk g : G ⧸ K)).FiniteIndex := by
  have hfin : (MulAction.orbit K (QuotientGroup.mk g : G ⧸ K)).Finite := by
    refine (R.finite_toSet.image (fun γ => (QuotientGroup.mk γ : G ⧸ K))).subset ?_
    rintro _ ⟨k, rfl⟩
    obtain ⟨γ, ⟨hγ, e⟩, -⟩ := hR.2 ((k : G) * g) ⟨k, k.2, 1, one_mem _, by simp⟩
    refine ⟨γ, hγ, ?_⟩
    show (QuotientGroup.mk γ : G ⧸ K) = (k : G) • (QuotientGroup.mk g : G ⧸ K)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    exact e
  refine ⟨?_⟩
  rw [MulAction.index_stabilizer]
  exact ((Set.ncard_pos hfin).2 ⟨_, MulAction.mem_orbit_self _⟩).ne'

theorem mem_of_stab {K : Subgroup G} {g : G} {n : K} (hn : n ∈ MulAction.stabilizer K (QuotientGroup.mk g : G ⧸ K)) :
    g⁻¹ * (n : G) * g ∈ K := by
  have h : ((n : G) • (QuotientGroup.mk g : G ⧸ K)) = QuotientGroup.mk g := hn
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at h
  have := inv_mem h
  convert this using 1
  group

theorem card_pos {K : Subgroup G} {g : G} {R : Finset G} (hR : Reps K g R) : 0 < R.card := by
  obtain ⟨γ, ⟨hγ, -⟩, -⟩ := hR.2 g ⟨1, one_mem _, 1, one_mem _, by simp⟩
  exact Finset.card_pos.2 ⟨γ, hγ⟩

theorem fixed_comb {K : Subgroup G} {ι : Type} (s : Finset ι) (g : ι → G) (R : ι → Finset G)
    (hR : ∀ i ∈ s, Reps K (g i) (R i)) (a : ι → ℂ) {M : Type} [AddCommGroup M] [Module ℂ M]
    (π : G →* Module.End ℂ M) (u : M) (hu : ∀ k ∈ K, π k u = u)
    (hw : ∀ k ∈ K, π k (∑ i ∈ s, a i • π (g i) u) = ∑ i ∈ s, a i • π (g i) u) :
    ∑ i ∈ s, a i • π (g i) u = ∑ i ∈ s, (a i / ((R i).card : ℂ)) • ∑ γ ∈ R i, π γ u := by
  classical
  have fix : ∀ x, ∀ l ∈ K, π (x * l) u = π x u := fun x l hl => by
    rw [map_mul, Module.End.mul_apply, hu l hl]
  let St : ι → Subgroup K := fun i => MulAction.stabilizer K (QuotientGroup.mk (g i) : G ⧸ K)
  have hSt : (⨅ i ∈ s, St i).FiniteIndex := Subgroup.finiteIndex_iInf' St fun i hi => finiteIndex_stab (hR i hi)
  let N : Subgroup K := (⨅ i ∈ s, St i).normalCore
  haveI : N.FiniteIndex := Subgroup.finiteIndex_normalCore _
  haveI : Fintype (K ⧸ N) := Fintype.ofFinite _
  have hN : ∀ i ∈ s, ∀ n ∈ N, ∀ x : G, π (x * (n : G) * g i) u = π (x * g i) u := by
    intro i hi n hn x
    have h1 : n ∈ St i := (iInf₂_le i hi : (⨅ i ∈ s, St i) ≤ St i) (Subgroup.normalCore_le _ hn)
    have := fix (x * g i) _ (mem_of_stab h1)
    rw [← this]
    congr 1
    group
  let T : ι → M := fun i => ∑ q : K ⧸ N, π ((q.out : G) * g i) u

  have hT : ∀ i ∈ s, ∀ k₁ ∈ K, ∑ q : K ⧸ N, π ((q.out : G) * k₁ * g i) u = T i := by
    intro i hi k₁ hk₁
    have e := Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk (⟨k₁, hk₁⟩ : K) : K ⧸ N))
      (fun q => π (((q * QuotientGroup.mk (⟨k₁, hk₁⟩ : K) : K ⧸ N).out : G) * g i) u)
      (fun q => π ((q.out : G) * g i) u) (fun q => rfl)
    refine Eq.trans ?_ e
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq : (q.out * ⟨k₁, hk₁⟩)⁻¹ * (q * QuotientGroup.mk (⟨k₁, hk₁⟩ : K) : K ⧸ N).out ∈ N := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    have := hN i hi _ hq ((q.out : G) * k₁)
    rw [← this]
    congr 2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev]
    group
  have hC : ∀ i ∈ s, ((R i).card : ℂ) • T i = (Fintype.card (K ⧸ N) : ℂ) • ∑ γ ∈ R i, π γ u := by
    intro i hi
    have e1 : ∑ γ ∈ R i, ∑ q : K ⧸ N, π ((q.out : G) * γ) u = ∑ γ ∈ R i, T i := by
      refine Finset.sum_congr rfl fun γ hγ => ?_
      obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := (hR i hi).1 γ hγ
      rw [← hT i hi k₁ h₁]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← fix ((q.out : G) * k₁ * g i) k₂ h₂]
      congr 1
      group
    have e2 : ∑ γ ∈ R i, ∑ q : K ⧸ N, π ((q.out : G) * γ) u = ∑ q : K ⧸ N, ∑ γ ∈ R i, π γ u := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun q _ => (hR i hi).sum_eq (hR i hi) q.out.2 (fun x => π x u) fix
    rw [e1, Finset.sum_const, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
      ← Nat.cast_smul_eq_nsmul ℂ] at e2
    exact e2
  have hQ : (Fintype.card (K ⧸ N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have main : (Fintype.card (K ⧸ N) : ℂ) • ∑ i ∈ s, a i • π (g i) u = ∑ i ∈ s, a i • T i := by
    have e : ∀ q : K ⧸ N, π (q.out : G) (∑ i ∈ s, a i • π (g i) u) = ∑ i ∈ s, a i • π ((q.out : G) * g i) u := by
      intro q

      simp only [map_sum, map_smul, map_mul, Module.End.mul_apply]
    calc (Fintype.card (K ⧸ N) : ℂ) • ∑ i ∈ s, a i • π (g i) u
        = ∑ q : K ⧸ N, π (q.out : G) (∑ i ∈ s, a i • π (g i) u) := by
          rw [Nat.cast_smul_eq_nsmul ℂ, ← Finset.card_univ, ← Finset.sum_const]
          exact Finset.sum_congr rfl fun q _ => (hw _ q.out.2).symm
      _ = ∑ i ∈ s, a i • T i := by
          simp only [e, T, Finset.smul_sum]
          exact Finset.sum_comm
  refine smul_right_injective M hQ ?_
  simp only
  rw [main, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [smul_comm, ← hC i hi, smul_smul, div_mul_cancel₀ _ (Nat.cast_ne_zero.2 (card_pos (hR i hi)).ne')]

end Abstract

end GlobalTheory.SphAvg

namespace GlobalTheory.SphAvg

open GlobalTheory.SphLabelOps GlobalTheory.IdemSupport

theorem fixed_comb_eq_opOf : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ e f, IsPrimeIdem P e f → ∀ a : GA D V →₀ ℂ, (∀ g ∈ a.support, SuppF V f g) → ∃ c : List ℤ →₀ ℂ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → (∀ k ∈ hyp V P, π k (a.sum fun g z => z • π g u) = a.sum fun g z => z • π g u) → (a.sum fun g z => z • π g u) = opOf π P c u := by
  classical
  intro D V P e f h a ha
  obtain ⟨K, hK⟩ := exists_hyp V P
  obtain ⟨-, ϖ, -, h1, h2⟩ := exists_real_unif D P
  have he := (GlobalTheory.HeckeDual.idem_of_isPrimeIdem h).1
  have hd : ∀ g, ∃ d, SuppF V f g → Reps K g (rep V P d) := by
    intro g
    by_cases hg : SuppF V f g
    · obtain ⟨d, hd, hD⟩ := exists_divAt V he (tie_of_isPrimeIdem h) h1 h2 g
      exact ⟨d, fun _ => reps_of_sphOp hK h h1 h2 hg hD (sphOp_rep (isLab_of_divAt h h1 h2 hd hg hD))⟩
    · exact ⟨[], fun h' => absurd h' hg⟩
  choose d hd using hd
  refine ⟨∑ g ∈ a.support, Finsupp.single (d g) (a g / ((rep V P (d g)).card : ℂ)), ?_⟩
  intro M _ _ π u hu hw
  have hu' : ∀ k ∈ K, π k u = u := fun k hk => hu k (by rw [hK]; exact hk)
  have hw' : ∀ k ∈ K, π k (∑ g ∈ a.support, a g • π (id g) u) = ∑ g ∈ a.support, a g • π (id g) u :=
    fun k hk => hw k (by rw [hK]; exact hk)
  rw [Finsupp.sum]
  refine (fixed_comb a.support id (fun g => rep V P (d g)) (fun g hg => hd g (ha g hg)) a π u hu' hw').trans ?_
  rw [opOf, ← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by rw [add_smul]), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finsupp.sum_single_index (by simp), LinearMap.smul_apply, LinearMap.sum_apply]

end GlobalTheory.SphAvg
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphLabelComm

section Abstract

variable {G : Type} [Group G]

theorem isDC_of_reps {K : Subgroup G} {x : G} {A : Finset G} (h : GlobalTheory.SphLabelOps.Reps K x A) :
    Formalism.IndefR.Bridge.IsDC K x A := by
  refine ⟨fun a ha => ?_, fun g hg => h.2 g ?_⟩
  · obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h.1 a ha
    exact ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, rfl⟩
  · obtain ⟨k₁, k₂, rfl⟩ := hg
    exact ⟨k₁, k₁.2, k₂, k₂.2, rfl⟩

theorem sum_comm_of_antiInv (K L : Subgroup G) (hKL : K ≤ L) (θ : G → G)
    (t1 : ∀ g ∈ L, θ g ∈ L) (t2 : ∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) (t3 : ∀ x ∈ L, θ (θ x) = x)
    (t4 : ∀ k ∈ K, θ k ∈ K) (t5 : ∀ g ∈ L, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b)
    {x y : G} (hx : x ∈ L) (hy : y ∈ L) {A B A' : Finset G}
    (hA : GlobalTheory.SphLabelOps.Reps K x A) (hB : GlobalTheory.SphLabelOps.Reps K y B) (hA' : GlobalTheory.SphLabelOps.Reps K x⁻¹ A')
    {M : Type} [AddCommGroup M] [Module ℂ M] (π : G →* Module.End ℂ M) (u : M) (hu : ∀ k ∈ K, π k u = u) :
    ∑ a ∈ A, π a (∑ b ∈ B, π b u) = ∑ b ∈ B, π b (∑ a ∈ A, π a u) := by
  have memL : ∀ {z : G} {R : Finset G}, GlobalTheory.SphLabelOps.Reps K z R → z ∈ L → ∀ a ∈ R, a ∈ L := by
    intro z R hR hz a ha
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hR.1 a ha
    exact mul_mem (mul_mem (hKL h₁) hz) (hKL h₂)
  have hθ : ∃ θ : G → G, (∀ g ∈ L, θ g ∈ L) ∧ (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧
      (∀ x ∈ L, θ (θ x) = x) ∧ (∀ k ∈ K ⊓ L, θ k ∈ K) ∧ ∀ g ∈ L, ∃ a ∈ K ⊓ L, ∃ b ∈ K ⊓ L, θ g = a * g * b := by
    refine ⟨θ, t1, t2, t3, fun k hk => t4 k hk.1, fun g hg => ?_⟩
    obtain ⟨a, ha, b, hb, e⟩ := t5 g hg
    exact ⟨a, ⟨ha, hKL ha⟩, b, ⟨hb, hKL hb⟩, e⟩
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have hF : ∀ (k : K) (h : G), (fun g => φ (π g u)) (h * k) = ((1 : K →* ℂˣ) k : ℂ) • (fun g => φ (π g u)) h := by
    intro k h
    simp [map_mul, Module.End.mul_apply, hu k k.2]
  have key := (GlobalTheory.DoubleCosetComm.dcOp_comm_and_card (W := ℂ) K L 1 x y A B A' (fun g => φ (π g u))
    (fun k hk => ⟨k, hk, 1, one_mem _, hKL hk, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun k _ => rfl) hθ (memL hA hx) (memL hB hy) (memL hA' (inv_mem hx)) (isDC_of_reps hA) (isDC_of_reps hB)
    (isDC_of_reps hA') hF).1
  have e := congrFun key 1
  simp only [Formalism.IndefR.Bridge.dcOp, one_mul, map_mul, Module.End.mul_apply] at e

  simp only [map_sub, map_sum, LinearMap.zero_apply]
  rw [sub_eq_zero]
  exact e

theorem comb_comm {ι M : Type} [AddCommGroup M] [Module ℂ M] (S : ι → Module.End ℂ M) (u : M)
    (h : ∀ i j, S i (S j u) = S j (S i u)) (c c' : ι →₀ ℂ) :
    (c.sum fun i z => z • S i) ((c'.sum fun i z => z • S i) u) =
      (c'.sum fun i z => z • S i) ((c.sum fun i z => z • S i) u) := by

  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [h i j, smul_comm]

end Abstract


open GlobalTheory.IdemSupport in
theorem label_ops_comm : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ c c', ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P c (opOf π P c' u) = opOf π P c' (opOf π P c u) := by
  intro D V P c c' M _ _ π u hu
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  obtain ⟨e, f, h⟩ := (supported_group_and_prime_idempotents V).2.1 P
  have h0 := (supported_group_and_prime_idempotents V).2.2.1 P e f h
  obtain ⟨L, hL⟩ := ((supported_group_and_prime_idempotents V).1 f h0.1 h0.2.1).1
  have memK : ∀ k, k ∈ K ↔ k ∈ KsphC V ∅ ∧ SuppF V f k := fun k => by
    rw [← SetLike.mem_coe, ← hK, GlobalTheory.SphLabelOps.hyp_eq h]
    rfl
  have hKL : K ≤ L := fun k hk => (hL k).2 ((memK k).1 hk).2
  obtain ⟨θ, t1, t2, t3, t4, t5⟩ : ∃ θ : GA D V → GA D V, (∀ g ∈ L, θ g ∈ L) ∧
      (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧ (∀ x ∈ L, θ (θ x) = x) ∧ (∀ k ∈ K, θ k ∈ K) ∧
      ∀ g ∈ L, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b := by
    rcases id h with ⟨hs, rfl⟩ | ⟨rfl, -⟩
    · obtain ⟨θ, s1, s2, s3, s4, s5⟩ := (GlobalTheory.SplitPlace.split_local V P e hs).1
      refine ⟨θ, fun g hg => (hL _).2 (s1 g ((hL g).1 hg)), fun x hx y hy => s2 x y ((hL x).1 hx) ((hL y).1 hy),
        fun x hx => s3 x ((hL x).1 hx), fun k hk => ?_, fun g hg => ?_⟩
      · have hk' := (memK k).1 hk
        exact (memK _).2 ⟨s4 k hk', s1 k hk'.2⟩
      · obtain ⟨a, ha, b, hb, eq⟩ := s5 g ((hL g).1 hg)
        exact ⟨a, (memK a).2 ha, b, (memK b).2 hb, eq⟩
    · refine ⟨fun g => g⁻¹, fun g hg => inv_mem hg, fun x _ y _ => mul_inv_rev x y, fun x _ => inv_inv x,
        fun k hk => inv_mem hk, fun g hg => ?_⟩
      obtain ⟨a, b, ha, ha', hb, hb', eq⟩ := (GlobalTheory.InertDoubleCoset.inert_double_cosets V P _ h
        (GlobalTheory.SphLabelOps.exists_real_unif D P) g ((hL g).1 hg)).1
      exact ⟨a, (memK a).2 ⟨ha, ha'⟩, b, (memK b).2 ⟨hb, hb'⟩, eq⟩
  have reps : ∀ d, IsLab V P d → ∃ x ∈ L, GlobalTheory.SphLabelOps.Reps K x (rep V P d) ∧
      ∃ A', GlobalTheory.SphLabelOps.Reps K x⁻¹ A' := by
    intro d hd
    have hR := GlobalTheory.SphLabelOps.sphOp_rep hd
    obtain ⟨e', f', ϖ, α, -, h', h1, h2, -, -, -, hα, hD, -⟩ := id hR
    obtain ⟨rfl, rfl⟩ := h0.2.2.2.1 e' f' h'
    have hαL : α ∈ L := (hL α).2 hα
    refine ⟨α, hαL, GlobalTheory.SphLabelOps.reps_of_sphOp hK h' h1 h2 hα hD hR, ?_⟩
    obtain ⟨R', hR', -⟩ := GlobalTheory.SphLabelOps.exists_dual hR
    have he := (GlobalTheory.HeckeDual.idem_of_isPrimeIdem h').1
    exact ⟨R', GlobalTheory.SphLabelOps.reps_of_sphOp hK h' h1 h2 ((hL _).1 (inv_mem hαL))
      (GlobalTheory.DivDual.divAt_inv_and_mul V _ _ d α he (GlobalTheory.SphLabelOps.unif_ne_zero h2) hD).1 hR'⟩
  have key : ∀ d d', (∑ γ ∈ rep V P d, π γ) ((∑ δ ∈ rep V P d', π δ) u) =
      (∑ δ ∈ rep V P d', π δ) ((∑ γ ∈ rep V P d, π γ) u) := by
    intro d d'
    by_cases hd : IsLab V P d
    swap
    · simp [Hk3.rep, dif_neg hd]
    by_cases hd' : IsLab V P d'
    swap
    · simp [Hk3.rep, dif_neg hd']
    obtain ⟨x, hx, rA, A', rA'⟩ := reps d hd
    obtain ⟨y, hy, rB, -⟩ := reps d' hd'
    simp only [LinearMap.sum_apply]
    exact sum_comm_of_antiInv K L hKL θ t1 t2 t3 t4 t5 hx hy rA rB rA' π u
      (fun k hk => hu k (by rw [hK]; exact hk))
  exact comb_comm (fun d => ∑ γ ∈ rep V P d, π γ) u key c c'

end GlobalTheory.SphLabelComm
end

section

namespace GlobalTheory.ElementarySymmetricInverse

theorem esymm_deg_zero (s : Multiset ℂ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

theorem esymm_cons_succ (x : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (x ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + x * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add (f := _), Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]

theorem esymm_top (s : Multiset ℂ) (k : ℕ) (hk : Multiset.card s = k) : s.esymm k = s.prod := by
  subst hk
  simp [Multiset.esymm]

theorem esymm_inv_mul_prod (s : Multiset ℂ) (hs : ∀ x ∈ s, x ≠ 0) :
    ∀ i j : ℕ, i + j = Multiset.card s →
      (s.map fun x => x⁻¹).esymm i * s.prod = s.esymm j := by
  induction s using Multiset.induction_on with
  | empty =>
    intro i j h
    have hi : i = 0 := by simp at h; exact h.1
    have hj : j = 0 := by simp at h; exact h.2
    subst hi hj
    simp [esymm_deg_zero]
  | cons x s ih =>
    intro i j h
    have hx : x ≠ 0 := hs x (Multiset.mem_cons_self x s)
    have ih' := ih (fun y hy => hs y (Multiset.mem_cons_of_mem hy))
    rcases i with _ | i
    · rw [esymm_deg_zero, one_mul, esymm_top _ j (by omega)]
    rcases j with _ | j
    · rw [esymm_deg_zero, esymm_top _ (i + 1) (by rw [Multiset.card_map]; omega),
        Multiset.prod_map_inv']
      exact inv_mul_cancel₀ (Multiset.prod_ne_zero (fun h0 => hs 0 h0 rfl))
    rw [Multiset.card_cons] at h
    rw [Multiset.map_cons, Multiset.prod_cons, esymm_cons_succ, esymm_cons_succ,
      ← ih' (i + 1) j (by omega), ← ih' i (j + 1) (by omega)]
    field_simp
    ring

theorem half_pow (q a : ℕ) :
    (((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) ^ a = (q : ℂ) ^ Nat.choose a 2 := by
  have h : ((q : ℝ) ^ (((a : ℝ) - 1) / 2)) ^ a = (q : ℝ) ^ Nat.choose a 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q), ← Real.rpow_natCast,
      Nat.cast_choose_two]
    congr 1
    ring
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h

theorem algSat_eq (a q : ℕ) (B : Multiset ℂˣ) :
    UpperTheory.V.Af.algSat a q B =
      B.map fun b : ℂˣ => (((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) * (b : ℂ) := by
  unfold UpperTheory.V.Af.algSat
  simp only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, Multiset.map_map,
    Function.comp_def]

theorem esymm_inv_algSat : ∀ {q : ℕ}, q ≠ (0 : ℕ) → ∀ {a : ℕ} {B : Multiset ℂˣ},
    Multiset.card B = a → ∀ {j : ℕ}, j ≤ a → GlobalTheory.LFun.satEig q a B a ≠ (0 : ℂ) →
    Multiset.esymm (Multiset.map (fun (x : ℂ) ↦ x⁻¹) (UpperTheory.V.Af.algSat a q B)) j =
      Multiset.esymm (UpperTheory.V.Af.algSat a q B) (a - j) *
        (((↑q : ℂ) ^ Nat.choose a (2 : ℕ))⁻¹ * (GlobalTheory.LFun.satEig q a B a)⁻¹) := by
  intro q hq a B hB j hj hne
  have hsat : GlobalTheory.LFun.satEig q a B a = (B.map fun b : ℂˣ => (b : ℂ)).prod := by
    unfold GlobalTheory.LFun.satEig
    rw [esymm_top _ a (by rw [Multiset.card_map, hB])]
    simp
  have hcard : Multiset.card (UpperTheory.V.Af.algSat a q B) = a := by
    rw [algSat_eq, Multiset.card_map, hB]
  have hprod : (UpperTheory.V.Af.algSat a q B).prod =
      (q : ℂ) ^ Nat.choose a 2 * GlobalTheory.LFun.satEig q a B a := by
    rw [hsat, ← half_pow, algSat_eq, Multiset.prod_map_mul,
      Multiset.map_const', Multiset.prod_replicate, hB]
  have hq' : (q : ℂ) ^ Nat.choose a 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hq)
  have hP : (UpperTheory.V.Af.algSat a q B).prod ≠ 0 := by
    rw [hprod]
    exact mul_ne_zero hq' hne
  have hall : ∀ x ∈ UpperTheory.V.Af.algSat a q B, x ≠ 0 := by
    rintro x hx rfl
    exact hP (Multiset.prod_eq_zero hx)
  rw [← esymm_inv_mul_prod _ hall j (a - j) (by omega), hprod]
  field_simp

end GlobalTheory.ElementarySymmetricInverse
end

section

noncomputable section

namespace GlobalTheory.Ggeo.KerComb

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

theorem comb_of_tied : Formalism.L2.KerInert.AlgTAll → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → ∀ u μ w, LevFree Y u μ w → ∀ i < D.R.m, ∀ c c', TaylorLogMetric.admitted D _ _ ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 ∧ TaylorLogMetric.IsComb D t.B.tor (t.B.eNat t.χ) (t.ent.lam w) ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 (TaylorLogMetric.pSer D (t.ent.lam w) ((t.O u μ).Th i c c')) := by
  intro hAlg D L hT Gi Gl K Y cX ex t hH u μ w hw i hi c c'
  have hEven : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add (D.R.t_odd.add_one.mul_left j)
  have hAdm : TaylorLogMetric.admitted D _ _ ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 :=
    ⟨hEven i, hEven (i + 1), ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩
  refine ⟨hAdm, ?_⟩
  have hTA : TransAlg D t.B.tor (t.B.eNat t.χ) :=
    transcendence_algebraic_eigen D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok (KS.Lat.delta_ne t.cc_ok t.δ_ok) (t.B.stdOK t.cc_ok t.δ_ok)
      (hAlg D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok)
  have hS : D.what₂.places.resChar w ∉ (t.O u μ).S := by
    obtain ⟨h1, h2, h3⟩ := hw
    rw [t.O_S u μ]
    intro hm
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, not_or] at h2 hm
    rcases hm with h | (h | h) | h
    exacts [h1 h, h2.1 h, h2.2 h, h3 h]
  have hA' := hAdm
  rw [t.O_lat u μ i c, t.O_lat u μ (i + 1) c'] at hA' ⊢
  rw [t.O_Th u μ i c c']
  exact first_kernel_law_reading D t.X u (D.chTw u μ) (t.rd u μ) t.seam t.amb t.cc t.δ (t.B.eNat t.χ) (t.O u μ).S i (hH u μ i hi) hTA c c' hA' _ (t.ent.lam w) hS

end GlobalTheory.Ggeo.KerComb
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.KerJ NumberField Classical

theorem _root_.GlobalTheory.T.trueWeight_consecutive_steps_partition : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (i : ℕ), i < D.R.m → ∃ n : D.what₂.Tau → ℕ, (∀ τ r, (lamTG M i τ).natW r + n τ = nuT D u i τ r) ∧ (∀ τ, (lamTG M i τ).detShift + C.sSharp i τ = n τ) ∧ (∀ τ r, (lamTG M (i + 1) τ).natW r = extNu (D.R.N (i + 1)) (fun τ r => (lamTG M i τ).natW r + n τ) τ r) ∧ ∀ τ, (lamTG M (i + 1) τ).detShift = -C.sDiv i τ := by
  first | exact @GlobalTheory.KerWtStep.trueWt_step | exact GlobalTheory.KerWtStep.trueWt_step | (intros; apply GlobalTheory.KerWtStep.trueWt_step <;> assumption)
end

section

namespace GlobalTheory.ThLoc

theorem locJets_all :
    Formalism.L2.Th1.GD.IntOpLoc ∧ Formalism.L2.Th1.GD.IntOpTwoLoc ∧
      (Formalism.L2.Th1.GD.EmbSep → Formalism.L2.Th1.GD.ShapeEigenLoc) :=
  ⟨LocJets.jetsOdd, LocJets.jetsTwo, LocJets.shape⟩

end GlobalTheory.ThLoc
end
