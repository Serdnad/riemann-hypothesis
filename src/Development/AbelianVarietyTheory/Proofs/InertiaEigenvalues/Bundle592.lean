module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle148
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle563
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle190
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle228
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle533
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumInnerProductFinsuppLocalCosetFamilies
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightTranslateOperatorMulLocalOperatorHasSum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle541
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import GroundTheory.AutomorphicForms.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle542
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle566
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle565
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDerivativeInducedTensorForms
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle507
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle567
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

noncomputable section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.Desc

variable {K : UQ} (B : InvAlg K) {ι : Type}

theorem eS_mul_eS_of_disjoint_inv [Fintype ι] {e : ι → B.A} (he : CompleteOrthogonalIdempotents e)
    {I J : Finset ι} (h : Disjoint I J) : eS B e I * eS B e J = 0 := by
  unfold eS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  exact he.ortho (fun hij => Finset.disjoint_left.1 h hi (hij ▸ hj))

theorem eS_mul_self_inv [Fintype ι] {e : ι → B.A} (he : CompleteOrthogonalIdempotents e) (I : Finset ι) :
    eS B e I * eS B e I = eS B e I := by
  unfold eS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i]
  · exact (he.idem i).eq
  · intro j _ hji; exact he.ortho (Ne.symm hji)
  · intro h; exact absurd hi h

theorem σ_eS_inv [Fintype ι] {e : ι → B.A} {S : Finset ι} (hP : IsPre B e S) (I : Finset ι) :
    B.σ (eS B e I) = eS B e I := by
  unfold eS

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨f, -, -, -, h1, h2⟩ := hP.2 i
  by_cases hi : i ∈ S
  · obtain ⟨h, hf⟩ := h1 hi; rw [h, hf]
  · obtain ⟨-, h⟩ := h2 hi; rw [h, map_add (f := _), B.σ_σ, add_comm]

theorem HH_sub_chi_mul_HH_negligible : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι]
    (e π : ι → B.A) (S : Finset ι) (a : K.O), B.LieReg → K.Small a → IsFrame B e π S → ∀ I ⊆ S, ∀ x : B.A,
    B.Plus x → Tendsto (fun k : ℕ => (((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 -
      chi B e I x * HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ))) atTop (𝓝 0) := by
  intro K B ι _ _ e π S a hL ha hF I hI x hx
  have hEE := eS_mul_self_inv B hF.1.1 I
  have hE'E := eS_mul_eS_of_disjoint_inv B hF.1.1 (Finset.sdiff_disjoint (s := I) (t := S))
  have hσE := σ_eS_inv B hF.1 I
  have hcov : ∀ i ∈ S, i ∈ I ∨ i ∈ S \ I := fun i hi => by
    by_cases h : i ∈ I
    · exact Or.inl h
    · exact Or.inr (Finset.mem_sdiff.2 ⟨hi, h⟩)
  set E := eS B e I with hEdef
  set E' := eS B e (S \ I) with hE'def
  obtain ⟨xi, hxi⟩ : ∃ xi : B.A, x * xi = 1 := ⟨_, hx.1.mul_val_inv⟩

  have hyu : IsUnit (x * E + (1 - E)) :=
    IsUnit.of_mul_eq_one (xi * E + (1 - E)) (by linear_combination (E * E) * hxi + (2 - x - xi) * hEE)
  have hx'u : IsUnit (x * (1 - E) + E) :=
    IsUnit.of_mul_eq_one (xi * (1 - E) + E) (by linear_combination (1 - E) ^ 2 * hxi + (2 - x - xi) * hEE)
  have hyP : B.Plus (x * E + (1 - E)) := ⟨hyu, by simp only [map_add (f := _), map_mul, map_sub, map_one, hx.2, hσE]⟩
  have hxy : (x * E + (1 - E)) * (x * (1 - E) + E) = x := by linear_combination (-(x - 1) ^ 2) * hEE
  have hchi : chi B e I x = K.eta (Algebra.norm K.E (x * E + (1 - E))) := rfl

  have haU : IsUnit (algebraMap K.O B.A a) := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A a]
    refine (IsUnit.mk0 _ fun h => ha.1 ?_).map _
    exact IsFractionRing.injective K.O K.E (h.trans (map_zero _).symm)

  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_lattice_idempotent_position_involution_stable K B ι e π S a hL.2 ha hF
  obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.alternatingDifference_term_window K B ι e π S a hL.2 ha hF I (S \ I) hI Finset.sdiff_subset hcov N
    (x * (1 - E) + E) (x * E + (1 - E)) hx'u hyu
  obtain ⟨L₁, hL₁⟩ := GlobalTheory.T.alternatingDifference_term_window K B ι e π S a hL.2 ha hF I (S \ I) hI Finset.sdiff_subset hcov N
    1 1 isUnit_one isUnit_one
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → Submodule K.O B.A → ℚ, ∀ k M, F k M =
      B.sgnLat M * term B π I (S \ I) ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k)) (x * E + (1 - E)) M :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → Submodule K.O B.A → ℚ, ∀ k M, G k M =
      B.sgnLat M * term B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 M := ⟨_, fun _ _ => rfl⟩
  have hsg : ∀ M, |B.sgnLat M| = 1 := fun M => by unfold InvAlg.sgnLat; exact abs_eta _
  have hFfin : ∀ k, (B.Lin ∩ Function.support (F k)).Finite := fun k =>
    (GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero K B ι e π S hL.2 hF I (S \ I) hI Finset.sdiff_subset _ _ ((hx'u.mul (haU.pow _))) hyu).subset
      fun M ⟨hM, h⟩ => ⟨hM, fun h0 => h (by rw [hFdef, h0, mul_zero])⟩
  have hGfin : ∀ k, (B.Lin ∩ Function.support (G k)).Finite := fun k =>
    (GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero K B ι e π S hL.2 hF I (S \ I) hI Finset.sdiff_subset _ _ (haU.pow _) isUnit_one).subset
      fun M ⟨hM, h⟩ => ⟨hM, fun h0 => h (by rw [hGdef, h0, mul_zero])⟩
  have hsub : ∀ k, ∑ᶠ M ∈ B.Lin, (F k M - G k M) = ∑ᶠ M ∈ B.Lin, F k M - ∑ᶠ M ∈ B.Lin, G k M := by
    intro k
    have hFG : (B.Lin ∩ Function.support (fun M => F k M - G k M)).Finite :=
      ((hFfin k).union (hGfin k)).subset fun M ⟨hM, h⟩ => by
        by_cases h1 : F k M = 0
        · exact Or.inr ⟨hM, fun h2 => h (show F k M - G k M = 0 by rw [h1, h2, sub_zero])⟩
        · exact Or.inl ⟨hM, h1⟩
    rw [eq_sub_iff_add_eq, ← finsum_mem_add_distrib' hFG (hGfin k)]
    simp only [sub_add_cancel]

  have key : ∀ k : ℕ, HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 -
      chi B e I x * HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 =
      K.eta (Algebra.norm K.E (x * E + (1 - E))) * ∑ᶠ M ∈ B.Lin, (F k M - G k M) := by
    intro k
    have hx_eq : x * algebraMap K.O B.A a ^ (2 * k) =
        (x * E + (1 - E)) * ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k)) := by
      rw [← mul_assoc, hxy]
    rw [hx_eq, GlobalTheory.T.signedInvolutionStableLatticeSum_mul_fixed_unit K B ι π I (S \ I) _ 1 _ hL hyP, hchi, mul_one, hsub, ← mul_sub]
    congr 1
    unfold HH
    congr 1
    · exact finsum_congr fun M => finsum_congr fun _ => (hFdef k M).symm
    · exact finsum_congr fun M => finsum_congr fun _ => (hGdef k M).symm

  have hcmp := GlobalTheory.T.tendsto_finsum_div_rho_pow_zero K B ι e π S a hL.2 ha hF I (S \ I) hcov N (max L₀ L₁)
    (2 * 2 ^ I.card * 2 ^ (S \ I).card) (fun k M => F k M - G k M) hN
    (by
      intro k M
      rw [hFdef, hGdef, ← mul_sub, abs_mul, hsg, one_mul]
      calc _ ≤ |term B π I (S \ I) ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k)) (x * E + (1 - E)) M| +
            |term B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 M| := abs_sub _ _
        _ ≤ 2 ^ I.card * 2 ^ (S \ I).card + 2 ^ I.card * 2 ^ (S \ I).card :=
            add_le_add (abs_term _ _ _ _ _ _ _) (abs_term _ _ _ _ _ _ _)
        _ = _ := by ring)
    (by
      intro k hk M _ p hp hf
      rw [hFdef, hGdef, ← mul_sub] at hf
      have hne := right_ne_zero_of_mul hf
      obtain ⟨h1a, h1b⟩ := hL₀ (max L₀ L₁) (le_max_left _ _) k hk M p hp
      obtain ⟨h2a, h2b⟩ := hL₁ (max L₀ L₁) (le_max_right _ _) k hk M p hp
      rw [one_mul] at h2a h2b
      rw [← hEdef, ← hE'def] at h1b h2b
      have hW : Win I (S \ I) (max L₀ L₁) k p := by
        by_cases h : term B π I (S \ I) ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k))
            (x * E + (1 - E)) M = 0
        · exact h2a fun h2 => hne (by rw [h, h2, sub_zero])
        · exact h1a h
      refine ⟨hW, fun hmid => hne ?_⟩
      have hEx : E * ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k)) = E * algebraMap K.O B.A a ^ (2 * k) := by
        linear_combination algebraMap K.O B.A a ^ (2 * k) * (1 - x) * hEE
      have hE'y : E' * (x * E + (1 - E)) = E' * 1 := by linear_combination (x - 1) * hE'E
      rw [h1b hW hmid, h2b hW hmid, hEx, hE'y, sub_self])
  have hfun : (fun k : ℕ => (((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 -
      chi B e I x * HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ))) = fun k : ℕ =>
      (K.eta (Algebra.norm K.E (x * E + (1 - E))) : ℝ) * (((∑ᶠ M ∈ B.Lin, (F k M - G k M) : ℚ) : ℝ) /
        (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) := by
    funext k
    rw [key k, Rat.cast_mul, mul_div_assoc]
  rw [hfun]
  simpa using hcmp.const_mul (K.eta (Algebra.norm K.E (x * E + (1 - E))) : ℝ)

end GlobalTheory.UnitLemma.Desc
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.Desc

theorem finsum_mem_finset_sum_comm {α β : Type} (s : Set α) (P : Finset β) (f : β → α → ℚ)
    (hf : ∀ p ∈ P, (s ∩ Function.support (f p)).Finite) :
    ∑ᶠ x ∈ s, ∑ p ∈ P, f p x = ∑ p ∈ P, ∑ᶠ x ∈ s, f p x := by
  classical
  have hU : (⋃ p ∈ (P : Set β), s ∩ Function.support (f p)).Finite :=
    Set.Finite.biUnion P.finite_toSet fun p hp => hf p (Finset.mem_coe.1 hp)
  have key : ∀ g : α → ℚ, (∀ x ∈ s, g x ≠ 0 → x ∈ ⋃ p ∈ (P : Set β), s ∩ Function.support (f p)) →
      ∑ᶠ x ∈ s, g x = ∑ x ∈ hU.toFinset, g x := by
    intro g hg
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext x
    simp only [Set.mem_inter_iff, Function.mem_support, Set.Finite.coe_toFinset]
    constructor
    · rintro ⟨hx, hgx⟩; exact ⟨hg x hx hgx, hgx⟩
    · rintro ⟨hx, hgx⟩
      obtain ⟨p, _, hxs, _⟩ := Set.mem_iUnion₂.1 hx
      exact ⟨hxs, hgx⟩
  rw [key]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => (key _ ?_).symm
    intro x hx h
    exact Set.mem_iUnion₂.2 ⟨p, Finset.mem_coe.2 hp, hx, h⟩
  · intro x hx h
    obtain ⟨p, hp, hpx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact Set.mem_iUnion₂.2 ⟨p, Finset.mem_coe.2 hp, hx, hpx⟩

theorem HH_eq_alternating_GG : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A)
    (S : Finset ι), B.LieReg → IsFrame B e π S → ∀ I ⊆ S, ∀ u : B.A, IsUnit u →
    HH B π I (S \ I) u 1 = ∑ J ∈ S.powerset, (-1 : ℚ) ^ (J ∩ I).card * B.GG ((∏ j ∈ J, π j) * u) := by
  intro K B ι _ _ e π S hL hF I hI u hu
  have hPlus : ∀ J ⊆ S, B.Plus (∏ j ∈ J, π j) := fun J hJ =>
    Finset.prod_induction _ B.Plus (fun a b ha hb => ⟨ha.1.mul hb.1, by rw [map_mul, ha.2, hb.2]⟩)
      ⟨isUnit_one, map_one _⟩ (fun j hj => (hF.2 j (hJ hj)).1)
  have heta1 : K.eta 1 = 1 := by
    have h := eta_mul (K := K) (x := 1) (y := 1) one_ne_zero one_ne_zero
    have h2 := eta_sq (K := K) 1
    rw [mul_one] at h
    rw [← h] at h2
    exact h2
  have heta : ∀ J : Finset ι, J ⊆ S → K.eta (Algebra.norm K.E (∏ j ∈ J, π j)) = (-1 : ℚ) ^ J.card := by
    intro J
    induction J using Finset.induction_on with
    | empty => intro _; simp [heta1]
    | insert a J ha ih =>
      intro hJ
      have haS : a ∈ S := hJ (Finset.mem_insert_self a J)
      have hJS : J ⊆ S := (Finset.subset_insert a J).trans hJ
      rw [Finset.prod_insert ha, map_mul,
        eta_mul ((hF.2 a haS).1.1.map (Algebra.norm K.E)).ne_zero
          ((hPlus J hJS).1.map (Algebra.norm K.E)).ne_zero,
        ih hJS, (hF.2 a haS).2.2, Finset.card_insert_of_notMem ha, pow_succ]
      ring
  have hterm0 : ∀ w s M, term B π ∅ ∅ w s M = indM B M w * indD B M s := by
    intro w s M; simp [term, dlt]
  have hHG : ∀ v, HH B π ∅ ∅ v 1 = B.GG v := by
    intro v
    unfold HH InvAlg.GG
    rw [finsum_mem_def, finsum_mem_def]
    refine finsum_congr fun M => ?_
    have hD : InDual B 1 M ↔ ∀ z ∈ M, Algebra.trace K.E B.A z ∈ (algebraMap K.O K.E).range := by
      simp only [InDual, one_mul]
    simp only [Set.indicator, Set.mem_setOf_eq, hterm0, indM, indD, ← hD]
    by_cases h1 : M ∈ B.Lin
    · by_cases h2 : v ∈ M
      · by_cases h3 : InDual B 1 M
        · rw [if_pos h1, if_pos h2, if_pos h3, if_pos ⟨h1, h2, hD.1 h3⟩]; ring
        · rw [if_pos h1, if_pos h2, if_neg h3, if_neg (fun h => h3 (hD.2 h.2.2))]; ring
      · rw [if_pos h1, if_neg h2, zero_mul, mul_zero]
        exact (if_neg (fun h => h2 h.2.1)).symm
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
  have hexp : HH B π I (S \ I) u 1 = ∑ p ∈ I.powerset ×ˢ (S \ I).powerset,
      (-1 : ℚ) ^ p.1.card * (-1 : ℚ) ^ p.2.card *
        HH B π ∅ ∅ ((∏ j ∈ p.1, π j) * u) ((∏ j ∈ p.2, π j) * 1) := by
    have h1 : ∀ M, B.sgnLat M * term B π I (S \ I) u 1 M = ∑ p ∈ I.powerset ×ˢ (S \ I).powerset,
        (-1 : ℚ) ^ p.1.card * (-1 : ℚ) ^ p.2.card *
          (B.sgnLat M * term B π ∅ ∅ ((∏ j ∈ p.1, π j) * u) ((∏ j ∈ p.2, π j) * 1) M) := by
      intro M
      rw [Finset.sum_product, term, dlt, dlt, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun J' _ => ?_
      rw [hterm0]; ring
    unfold HH
    simp_rw [h1]
    rw [finsum_mem_finset_sum_comm]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [mul_finsum_mem]
    · intro p hp
      rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
      refine (GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero K B ι e π S hL.2 hF ∅ ∅ (Finset.empty_subset _) (Finset.empty_subset _) _ _
        ((hPlus p.1 (hp.1.trans hI)).1.mul hu) ((hPlus p.2 (hp.2.trans Finset.sdiff_subset)).1.mul isUnit_one)).subset ?_
      rintro M ⟨hM, hne⟩
      refine ⟨hM, fun h => hne ?_⟩
      simp only [h, mul_zero]
  rw [hexp]
  have hstep : ∀ p ∈ I.powerset ×ˢ (S \ I).powerset,
      (-1 : ℚ) ^ p.1.card * (-1 : ℚ) ^ p.2.card *
        HH B π ∅ ∅ ((∏ j ∈ p.1, π j) * u) ((∏ j ∈ p.2, π j) * 1) =
      (-1 : ℚ) ^ ((p.1 ∪ p.2) ∩ I).card * B.GG ((∏ j ∈ p.1 ∪ p.2, π j) * u) := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    have hdisj : Disjoint p.1 p.2 := Finset.disjoint_left.2 fun x h1 h2 =>
      (Finset.mem_sdiff.1 (hp.2 h2)).2 (hp.1 h1)
    have hcap : (p.1 ∪ p.2) ∩ I = p.1 := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact h
        · exact absurd hx (Finset.mem_sdiff.1 (hp.2 h)).2
      · intro h; exact ⟨Or.inl h, hp.1 h⟩
    have hy := hPlus p.2 (hp.2.trans Finset.sdiff_subset)
    have hm := GlobalTheory.T.signedInvolutionStableLatticeSum_mul_fixed_unit K B ι π ∅ ∅ ((∏ j ∈ p.1, π j) * u) 1 (∏ j ∈ p.2, π j) hL hy
    have hsq := eta_sq (K := K) (Algebra.norm K.E (∏ j ∈ p.2, π j))
    have hm' : HH B π ∅ ∅ ((∏ j ∈ p.1, π j) * u) ((∏ j ∈ p.2, π j) * 1) =
        K.eta (Algebra.norm K.E (∏ j ∈ p.2, π j)) *
          HH B π ∅ ∅ ((∏ j ∈ p.2, π j) * ((∏ j ∈ p.1, π j) * u)) 1 := by
      rw [hm, ← mul_assoc, hsq, one_mul]
    rw [hm', heta p.2 (hp.2.trans Finset.sdiff_subset), hHG, hcap, Finset.prod_union hdisj]
    have h11 : ((-1 : ℚ) ^ p.2.card) * ((-1 : ℚ) ^ p.2.card) = 1 := by rw [← mul_pow]; norm_num
    calc (-1 : ℚ) ^ p.1.card * (-1) ^ p.2.card *
          ((-1) ^ p.2.card * B.GG ((∏ j ∈ p.2, π j) * ((∏ j ∈ p.1, π j) * u)))
        = (-1 : ℚ) ^ p.1.card * B.GG ((∏ j ∈ p.1, π j) * (∏ j ∈ p.2, π j) * u) *
          (((-1 : ℚ) ^ p.2.card) * ((-1 : ℚ) ^ p.2.card)) := by ring_nf
      _ = _ := by rw [h11, mul_one]
  rw [Finset.sum_congr rfl hstep]
  refine Finset.sum_nbij' (fun p => p.1 ∪ p.2) (fun J => (J ∩ I, J \ I)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    rw [Finset.mem_powerset]
    exact Finset.union_subset (hp.1.trans hI) (hp.2.trans Finset.sdiff_subset)
  · intro J hJ
    rw [Finset.mem_powerset] at hJ
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.sdiff_subset_sdiff hJ le_rfl⟩
  · intro p hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    have h2 : ∀ x ∈ p.2, x ∉ I := fun x hx => (Finset.mem_sdiff.1 (hp.2 hx)).2
    refine Prod.ext ?_ ?_
    · ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact h
        · exact absurd hx (h2 x h)
      · intro h; exact ⟨Or.inl h, hp.1 h⟩
    · ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact absurd (hp.1 h) hx
        · exact h
      · intro h; exact ⟨Or.inr h, h2 x h⟩
  · intro J _
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · intro p _
    rfl

end GlobalTheory.UnitLemma.Desc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

theorem _root_.GlobalTheory.T.hasSum_innerProduct_finsupp_localCosetFamilies : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LevProd R i → TransLaws R i → FinMult R i t → LevFix R i t → VecNe R i t → FinSum R i t → ∀ th, IsRaw R i t th → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∃ a : ℝ, 0 < a ∧ ∀ x y, HasSum (fun F : {F : ∀ v, Eu.LX R i v // {w | F w ≠ Eu.lx0 R i w}.Finite} => (a : ℂ) * ((∏ᶠ v, Eu.acoef R i t μ 𝓕 v (F.1 v)) * ⟪x, Eu.Bfam R i F.1 y⟫_ℂ)) ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ := by
  first | exact @GlobalTheory.RawLift.FamSum.hasSum_families | exact GlobalTheory.RawLift.FamSum.hasSum_families | (intros; apply GlobalTheory.RawLift.FamSum.hasSum_families <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

theorem _root_.GlobalTheory.T.rightTranslateOperator_mul_localOperator_hasSum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LocSmall R i t → TransLaws R i → LevFix R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g) → ∀ v, ∀ γ ∈ GfC (Wc D i), HasSum (fun x : Eu.LX R i v => Eu.acoef R i t μ 𝓕 v x • Eu.Bop R i (γ * Eu.rep x)) (Eu.Bop R i γ * Eu.Zop R i t μ 𝓕 v) := by
  first | exact @GlobalTheory.RawLift.Eu.bop_mul_zop_hasSum | exact GlobalTheory.RawLift.Eu.bop_mul_zop_hasSum | (intros; apply GlobalTheory.RawLift.Eu.bop_mul_zop_hasSum <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

theorem _root_.GlobalTheory.T.lastRowCongruenceDetWeight_measurable_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m N : ℕ) (x : ℝ),
    Measurable (GlobalTheory.ZUnf.wt (E := E) (m := m) N x) ∧
    (∀ γ ∈ mirU E (m + 1) m, ∀ g, GlobalTheory.ZUnf.wt N x (ratGL E (m + 1) γ * g) = GlobalTheory.ZUnf.wt N x g) ∧
    ∀ (k : ℕ) (y : UnipotentBlockColumnIndex (m + 1) k k → Ad E) (g : GA E (m + 1)), GlobalTheory.ZUnf.wt N x (blkU y * g) = GlobalTheory.ZUnf.wt N x g := by
  first | exact @GlobalTheory.ZUnfWt.wt_measurable_invariant | exact GlobalTheory.ZUnfWt.wt_measurable_invariant | (intros; apply GlobalTheory.ZUnfWt.wt_measurable_invariant; all_goals assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift


theorem _root_.GlobalTheory.T.exists_heckeRepresentatives_rightTranslate_identity : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m), TransLaws R i → ∀ (B : GfC (Wc D i) → ((R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H)), (∀ (γ : GfC (Wc D i)) x y, trPair R i (γ : GA D (Wc D i)) x y = ⟪x, B γ y⟫_ℂ) → (∀ v α, GlobalTheory.UpInj.cf (Wc D i) v α = α → ∃ C, GlobalTheory.UpInj.DCRep (GlobalTheory.UpInj.cf (Wc D i) v) (GlobalTheory.UpInj.KR R i) α C) ∧ (∀ v α C, GlobalTheory.UpInj.cf (Wc D i) v α = α → GlobalTheory.UpInj.DCRep (GlobalTheory.UpInj.cf (Wc D i) v) (GlobalTheory.UpInj.KR R i) α C → ∀ γ, ∑ δ ∈ C, B (γ * δ) = B γ * ∑ δ ∈ C, B δ) := by
  first | exact @GlobalTheory.UpInj.heckeReps | exact GlobalTheory.UpInj.heckeReps | (intros; apply GlobalTheory.UpInj.heckeReps <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.frobenius_equation_lift_Ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ) (d : ℕ → ↥(K0 K)), 1 ≤ M → (∀ i ∈ T, Lifts AI K (w i) (c i)) → (∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = ∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j) → ∃ y : Ainf l, y - WittVector.frobenius y = ∑ i ∈ T, w i * WittVector.teichmuller l AI.ε ^ m i ∧ io AI y - ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * oB P (d j : Om l) * tD P ^ j ∈ FilB P (M : ℤ) := by
  first | exact @GlobalTheory.ExpImage.Tail.tail | exact GlobalTheory.ExpImage.Tail.tail | (intros; apply GlobalTheory.ExpImage.Tail.tail <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

theorem _root_.GlobalTheory.T.X_nygaard_ext_comes_from_base_field : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)), z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X → ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, ((F l).E K s LL h).tie.jD T z = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) z') := by
  first | exact @GlobalTheory.NL.XNTransfer.main | exact GlobalTheory.NL.XNTransfer.main | (intros; apply GlobalTheory.NL.XNTransfer.main <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

theorem _root_.GlobalTheory.T.inv_Q_pow_nygaard_ext_comes_from_base_field : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (m : ℕ) (y' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)), y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m) → ∃ y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m), ((F l).E K s LL h).tie.jD T y = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') := by
  first | exact @GlobalTheory.NL.TransitionThirdCase.main | exact GlobalTheory.NL.TransitionThirdCase.main | (intros; apply GlobalTheory.NL.TransitionThirdCase.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

theorem _root_.GlobalTheory.T.lie_derivative_induced_tensor_forms : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (X : Lie E N) (φ : Sm E N), φ ∈ indForms h π → ∀ (k : Kinf E N) (g : GL (Fin N) (Af E)), (fun m => (lie E N X φ).1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g))) ∈ tensorForms π := by
  first | exact @GlobalTheory.LieTensor.lie_tensorForms | exact GlobalTheory.LieTensor.lie_tensorForms | (intros; apply GlobalTheory.LieTensor.lie_tensorForms <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.MemLoc

theorem tied_regular_and_onto :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
      (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 →
        (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) ∧
      (∀ u : P.R.B, ∃ x, x - P.φB x = u) ∧
      ∀ (K : FinExt l) (w : P.R.BdR), ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 :=
  GlobalTheory.T.bcris_regular_surjections_of_fontaine_theorem GlobalTheory.T.fontaineBcrisBasicTheorems_proof

end GlobalTheory.MemLoc
end
