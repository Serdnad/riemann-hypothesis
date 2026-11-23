module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle022
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle013
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle021
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle017

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_totPos_congr {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hne : 𝔭 ≠ ⊥) (a : 𝓞 F) (k : ℕ) :
    ∃ x : F, TotPos (algebraMap F K x) ∧ InP 𝔭 k (algebraMap F K ((a : F) + x)) := by
  have := h𝔭.isPrime
  have ht0 : Ideal.absNorm (𝔭 ^ k) ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact pow_ne_zero _ hne
  have htm : ((Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) ∈ 𝔭 ^ k := Ideal.absNorm_mem _
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ φ : K →+* ℂ, ‖φ (algebraMap F K (a : F))‖)
  have hz : ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) ∈ 𝔭 ^ k := by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ htm
  have hzF : (((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) : F) = ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : F) := by
    simp
  refine ⟨(((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) : F) - (a : F), ?_, ?_⟩
  · intro φ
    rw [hzF, map_sub, map_sub, map_natCast, map_natCast, Complex.sub_re, Complex.natCast_re]
    have h1 : (φ (algebraMap F K (a : F))).re ≤ ∑ ψ : K →+* ℂ, ‖ψ (algebraMap F K (a : F))‖ :=
      (Complex.re_le_norm _).trans (Finset.single_le_sum
        (f := fun ψ : K →+* ℂ => ‖ψ (algebraMap F K (a : F))‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ φ))
    have h2 : (N : ℝ) ≤ ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : ℝ) := by
      push_cast
      exact le_mul_of_one_le_right (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.2 ht0)
    linarith
  · rw [add_sub_cancel]
    exact inP_of_mem_pow hz

end Formalism.L2.SG.Pf.GluingBases
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

def LastUnit : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    cJof 𝔭 a < finrank K (orthK h U) →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueDataPre h U 𝔭 a π w c τ →
      ∀ j : Fin (finrank K (orthK h U)), (j : ℕ) + 1 = finrank K (orthK h U) →
      ∃ l : K, l ≠ 0 ∧ InP 𝔭 0 (algebraMap F K (c j) * (l * star l)) ∧
        InP 𝔭 0 (algebraMap F K (c j) * (l * star l))⁻¹

theorem lastRescale_of (hL : LastUnit) : LastRescale := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc π w c τ hg
  have hm : 0 < finrank K (orthK h U) := lt_of_le_of_lt (Nat.zero_le _) hc
  set j₀ : Fin (finrank K (orthK h U)) := ⟨finrank K (orthK h U) - 1, by omega⟩ with hj₀
  obtain ⟨l, hl0, hl1, hl2⟩ :=
    hL K F V hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc π w c τ hg j₀ (by simp [j₀]; omega)
  obtain ⟨hwW, hwo, hwn, hτ, hu, hcong, hτl, hunit⟩ := hg
  obtain ⟨μ, hμ⟩ := (hF (l * star l)).1 (by rw [star_mul', star_star, mul_comm])
  have hμ0 : μ ≠ 0 := by
    intro e; rw [e, map_zero] at hμ
    exact mul_ne_zero hl0 (star_ne_zero.2 hl0) hμ.symm
  let w' := Function.update w j₀ (l • w j₀)
  let c' := Function.update c j₀ (μ * c j₀)
  have hw'₀ : w' j₀ = l • w j₀ := Function.update_self _ _ _
  have hw'n : ∀ j, j ≠ j₀ → w' j = w j := fun j hj => Function.update_of_ne hj _ _
  have hc'₀ : c' j₀ = μ * c j₀ := Function.update_self _ _ _
  have hc'n : ∀ j, j ≠ j₀ → c' j = c j := fun j hj => Function.update_of_ne hj _ _
  have hτ₀ : ∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j₀ := by
    intro i hi e
    have := hτl i hi
    rw [e] at this
    simp [j₀] at this
    omega
  refine ⟨w', c', ⟨?_, ?_, ?_, hτ, hu, ?_, ?_⟩⟩
  · intro j
    by_cases hj : j = j₀
    · rw [hj, hw'₀]; exact Submodule.smul_mem _ _ (hwW j₀)
    · rw [hw'n j hj]; exact hwW j
  · intro j k hjk
    by_cases hj : j = j₀
    · have hk : k ≠ j₀ := fun e => hjk (hj.trans e.symm)
      rw [hj, hw'₀, hw'n k hk, form_smul_left, hwo _ _ (hj ▸ hjk), mul_zero]
    · by_cases hk : k = j₀
      · rw [hk, hw'₀, hw'n j hj, form_smul_right, hwo _ _ (hk ▸ hjk), mul_zero]
      · rw [hw'n j hj, hw'n k hk]; exact hwo j k hjk
  · intro j
    by_cases hj : j = j₀
    · rw [hj, hw'₀, hc'₀, form_smul_smul, (hwn j₀).1, map_mul, hμ]
      refine ⟨by ring, mul_ne_zero hμ0 (hwn j₀).2⟩
    · rw [hw'n j hj, hc'n j hj]; exact hwn j
  · intro i hi
    rw [hc'n _ (hτ₀ i hi)]; exact hcong i hi
  · intro j hnp
    by_cases hj : j = j₀
    · rw [hj, hc'₀]
      refine ⟨?_, ?_⟩
      · rw [map_mul, hμ, mul_comm]; exact hl1
      · rw [map_inv₀, map_mul, hμ, mul_comm]; exact hl2
    · rw [hc'n j hj]
      refine hunit j ?_ hnp
      have h1 := j.isLt
      have h2 : (j : ℕ) ≠ finrank K (orthK h U) - 1 := fun e => hj (Fin.ext e)
      omega

end Formalism.L2.SG.Pf.GluingBases
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G6 Formalism.L2.SG.Pf.OrthogonalProjections

theorem fibre_counting_holds : FibCount := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hcU M T hM hT 𝔭 h𝔭 hne
  have oUW : ∀ x ∈ U, ∀ y ∈ orthK h U, h x y = 0 := fun x hx y hy => h_UW hx hy
  have oWU : ∀ x ∈ orthK h U, ∀ y ∈ U, h x y = 0 := fun x hx y hy => h_WU hs hx hy
  have hO := projOnto_of summand_localization riesz_hermitian_holds
  have hgood : ∀ Λ, InFib h U 𝔭 M T Λ → Good hcU M T 𝔭 Λ := fun Λ hΛ =>
    { iU := projection_into_holds K F V hK hF h hs hnd U (orthK h U) hcU oUW M hM 𝔭 h𝔭 Λ hΛ.1 hΛ.2.1 hΛ.2.2.1
      iW := projection_into_holds K F V hK hF h hs hnd (orthK h U) U hcU.symm oWU T hT 𝔭 h𝔭 Λ hΛ.1 hΛ.2.1
        hΛ.2.2.2
      oU := hO K F V hK hF h hs hnd U (orthK h U) hcU oUW M hM 𝔭 h𝔭 Λ hΛ.1 hΛ.2.1 hΛ.2.2.1
      oW := hO K F V hK hF h hs hnd (orthK h U) U hcU.symm oWU T hT 𝔭 h𝔭 Λ hΛ.1 hΛ.2.1 hΛ.2.2.2
      cU := hΛ.2.2.1
      cW := hΛ.2.2.2 }
  obtain ⟨⟨⟨Λ₀, h0⟩⟩, -⟩ := Nat.card_ne_zero.mp hne
  exact card_eq hs h𝔭 hM hT hgood h0

end Formalism.L2.SG.Pf.Cnt
end
end

section

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem locF_subset_span {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) V) :
    (locF 𝔭 L : Set V) ⊆ Submodule.span K (L : Set V) := by
  intro x hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp L x).1 hx
  have ht0 : algebraMap F K (t : F) ≠ 0 := by
    rw [← jι_eq']; exact jι_ne_zero (ne_zero_of_notMem ht)
  have h1 : algebraMap F K (t : F) • x ∈ Submodule.span K (L : Set V) := by
    rw [← jι_eq', algebraMap_smul]; exact Submodule.subset_span htx
  exact (Submodule.smul_mem_iff _ ht0).1 h1

theorem le_span_of_locF {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {U : Submodule K V}
    {M : Submodule (𝓞 K) V} (hM : IsLatIn U M) {n : ℕ} {b : Fin n → V}
    (hb : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 M) :
    U ≤ Submodule.span K (Set.range b) := by
  rw [← hM.2, Submodule.span_le]
  intro x hx
  have h1 : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hb]; exact LocF.le_locF 𝔭 M hx
  have h2 := locF_subset_span hp _ h1
  rwa [Submodule.span_span_of_tower] at h2

theorem linearIndependent_orth {m : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (w : Fin m → V)
    (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0) (hwn : ∀ j, h (w j) (w j) ≠ 0) :
    LinearIndependent K w := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have h1 := congrArg (h (w k)) hg

  rw [map_sum, map_zero] at h1
  simp only [map_smul, smul_eq_mul] at h1
  rw [Finset.sum_eq_single k (fun j _ hj => by rw [hwo k j (Ne.symm hj), mul_zero])
    (by simp)] at h1
  exact (mul_eq_zero.1 h1).resolve_right (hwn k)

theorem family_top_holds : FamTop := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have hp := h𝔭.isPrime
  obtain ⟨hbU, hbL, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hw : ∀ j, w j ∈ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) :=
    fun j => Submodule.subset_span ⟨Sum.inr j, rfl⟩
  have hb : ∀ i, b i ∈ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) := by
    intro i
    have hg' : glueFam K 𝔭 b a π w τ (Sum.inl i) ∈
        Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) := Submodule.subset_span ⟨Sum.inl i, rfl⟩
    simp only [glueFam, Sum.elim_inl] at hg'
    by_cases hi : vF 𝔭 (a i) = 0
    · rwa [if_pos hi] at hg'
    · rw [if_neg hi] at hg'
      have h0 : (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) ≠ 0 := by
        apply pow_ne_zero; apply inv_ne_zero; rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
      have h1 := (Submodule.smul_mem_iff _ h0).1 hg'
      have h2 := Submodule.sub_mem _ h1 (hw (τ i))
      rwa [add_sub_cancel_right] at h2
  have hU : U ≤ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) :=
    le_trans (le_span_of_locF hp hM hbL) (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i))
  have hli : LinearIndependent K w := linearIndependent_orth h w hwo fun j => by
    rw [(hwn j).1]; exact (map_ne_zero _).2 (hwn j).2
  have hle : Submodule.span K (Set.range w) ≤ orthK h U :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hwW j)
  have hfr : finrank K (Submodule.span K (Set.range w)) = finrank K (orthK h U) := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hW : orthK h U ≤ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) :=
    le_trans (Submodule.eq_of_le_of_finrank_eq hle hfr).ge
      (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hw j))
  rw [eq_top_iff, ← hUc.sup_eq_top]
  exact sup_le hU hW

end Formalism.L2.SG.Pf.GluingBases
end
end

section

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

theorem family_gram_holds : FamGram := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have := h𝔭.isPrime
  obtain ⟨hbU, -, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hwn1 : ∀ j, h (w j) (w j) = algebraMap F K (c j) := fun j => (hwn j).1
  have hbw : ∀ i j, h (b i) (w j) = 0 := fun i j =>
    LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (hwW j) (b i)) (hbU i))
  have hwb : ∀ i j, h (w j) (b i) = 0 := fun i j => by
    rw [← hs.eq (b i) (w j), hbw]; simp
  have hcP : ∀ i, vF 𝔭 (a i) ≠ 0 → InP 𝔭 (vF 𝔭 (a i)) (algebraMap F K (c (τ i))) := by
    intro i hi
    have h1 : InP 𝔭 (vF 𝔭 (a i)) (algebraMap F K ((a i : F) + c (τ i))) :=
      (hcong i hi).mono (by omega)
    have h2 : InP 𝔭 (vF 𝔭 (a i)) (algebraMap F K ((a i : 𝓞 F) : F)) := inP_vF h𝔭 (ha0 i)
    have e : algebraMap F K (c (τ i)) =
        algebraMap F K ((a i : F) + c (τ i)) + -algebraMap F K ((a i : 𝓞 F) : F) := by
      rw [map_add (f := _)]; ring
    rw [e]; exact h1.add h2.neg
  have hcS : ∀ j, algebraMap F K (c j) ∈ SP K 𝔭 := by
    intro j
    by_cases hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j
    · obtain ⟨i, hi, rfl⟩ := hj
      exact (hcP i hi).mem_SP
    · push Not at hj
      exact (hunit j fun i hi => hj i hi).1
  have haS : ∀ i, algebraMap F K ((a i : 𝓞 F) : F) ∈ SP K 𝔭 := fun i => by
    rw [← jι_eq']; exact jK_mem_SP _
  have key_ii : ∀ i, h (b i + w (τ i)) (b i + w (τ i)) = algebraMap F K ((a i : F) + c (τ i)) := by
    intro i
    simp only [map_add (f := _), LinearMap.add_apply, hbw, hwb, hbn, hwn1]
    ring
  have key_ik : ∀ i k, i ≠ k → vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 →
      h (b i + w (τ i)) (b k + w (τ k)) = 0 := by
    intro i k hik hi hk
    have hτik : τ i ≠ τ k := fun e => hik (hτ i k hi hk e)
    simp only [map_add (f := _), LinearMap.add_apply, hbw, hwb, hbo i k hik, hwo _ _ hτik]
    ring
  suffices H : ∀ x y, h (glueFam K 𝔭 b a π w τ x) (glueFam K 𝔭 b a π w τ y) ∈ SP K 𝔭 by
    intro x y; rw [← mem_SP_iff_locF]; exact H x y
  rintro (i | j) (k | l)
  · simp only [glueFam, Sum.elim_inl]
    by_cases hik : i = k
    · subst hik
      by_cases hi : vF 𝔭 (a i) = 0
      · rw [if_pos hi, hbn]; exact haS i
      · rw [if_neg hi, form_smul_smul, key_ii i, star_inv_pow hF, ← pow_add, ← two_mul]
        exact mem_SP_of_inP hu (hcong i hi)
    · by_cases hi : vF 𝔭 (a i) = 0 <;> by_cases hk : vF 𝔭 (a k) = 0
      · rw [if_pos hi, if_pos hk, hbo i k hik]; exact (SP K 𝔭).zero_mem
      · rw [if_pos hi, if_neg hk, form_smul_right, map_add (f := _), hbo i k hik, hbw, add_zero, mul_zero]
        exact (SP K 𝔭).zero_mem
      · rw [if_neg hi, if_pos hk, form_smul_left, map_add (f := _), LinearMap.add_apply, hbo i k hik, hwb,
          add_zero, mul_zero]
        exact (SP K 𝔭).zero_mem
      · rw [if_neg hi, if_neg hk, form_smul_smul, key_ik i k hik hi hk, mul_zero]
        exact (SP K 𝔭).zero_mem
  · simp only [glueFam, Sum.elim_inl, Sum.elim_inr]
    by_cases hi : vF 𝔭 (a i) = 0
    · rw [if_pos hi, hbw]; exact (SP K 𝔭).zero_mem
    · rw [if_neg hi, form_smul_left, map_add (f := _), LinearMap.add_apply, hbw, zero_add, star_inv_pow hF]
      by_cases hj : τ i = l
      · subst hj; rw [hwn1]; exact mem_SP_of_inP hu (hcP i hi)
      · rw [hwo _ _ hj, mul_zero]; exact (SP K 𝔭).zero_mem
  · simp only [glueFam, Sum.elim_inl, Sum.elim_inr]
    by_cases hk : vF 𝔭 (a k) = 0
    · rw [if_pos hk, hwb]; exact (SP K 𝔭).zero_mem
    · rw [if_neg hk, form_smul_right, map_add (f := _), hwb, zero_add]
      by_cases hj : τ k = j
      · subst hj; rw [hwn1]; exact mem_SP_of_inP hu (hcP k hk)
      · rw [hwo _ _ (Ne.symm hj), mul_zero]; exact (SP K 𝔭).zero_mem
  · simp only [glueFam, Sum.elim_inr]
    by_cases hjl : j = l
    · subst hjl; rw [hwn1]; exact hcS j
    · rw [hwo _ _ hjl]; exact (SP K 𝔭).zero_mem

end Formalism.L2.SG.Pf.GluingBases
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

theorem unramAt_of_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (v : HeightOneSpectrum (𝓞 F)) : UnramAt (E := E) v := by
  intro P hP hP0 _
  classical
  haveI : Algebra.IsQuadraticExtension F E := ⟨hc.deg2⟩
  let c : Gal(E/F) := AlgEquiv.ofRingEquiv (f := starRingAut) (fun r => (hc.fixed (algebraMap F E r)).2 ⟨r, rfl⟩)
  haveI : P.LiesOver (P.under (𝓞 F)) := ⟨rfl⟩
  have hp0 : P.under (𝓞 F) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 F) hP0
  have hcard : Nat.card (P.inertia Gal(E/F)) = P.ramificationIdx (𝓞 F) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(E/F)) (P.under (𝓞 F)) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 F)) P Gal(E/F)]
  by_contra hne
  have hG : Nat.card Gal(E/F) = 2 := by
    first
      | (rw [IsGalois.card_aut_eq_finrank]; exact hc.deg2)
      | (rw [Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]; exact hc.deg2)
  haveI : Fact (Nat.card Gal(E/F)).Prime := ⟨by rw [hG]; exact Nat.prime_two⟩
  have htop : P.inertia Gal(E/F) = ⊤ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (P.inertia Gal(E/F)) with h | h
    · exfalso
      apply hne
      rw [← hcard, h]
      simp
    · exact h
  have hcI : c ∈ P.inertia Gal(E/F) := htop ▸ Subgroup.mem_top c
  obtain ⟨θ, t, ht, hθ⟩ := hc.cmUnram.2.2 P (hP.isMaximal hP0)
  apply hθ
  have h1 := hcI θ
  have e : c • θ = t := by
    apply RingOfIntegers.coe_injective
    rw [ht]
    rfl
  rw [e] at h1
  have : θ - t = -(t - θ) := by ring
  rw [this]
  exact P.neg_mem h1

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omega_standard_holds : OmVStd X ψ := by
  intro h1 h2
  refine ⟨?_, ?_, h1, h2⟩
  · unfold IsCMExt
    refine ⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, ?_⟩
    exact fun τ x => X.B.I.cm.cmUnram.2.1 τ x
  · unfold IsHermND
    have hH := X.B.I.J_herm
    unfold Formalism.UG.IsHerm at hH
    refine ⟨fun i j => ?_, X.B.I.J_det⟩
    have h3 := congrFun (congrFun hH i) j
    exact h3

theorem omega_lattice_holds : OmVLat X := ⟨X.B.I.L, Submodule.IsLattice.of_fg X.B.I.E X.B.I.L_fg, rfl⟩

theorem omega_unramified_holds : OmVUnram X := fun v => unramAt_of_cm X.B.I.cm v

end Formalism.L2.SG.Pf.NcX.OmVSt
end
end
