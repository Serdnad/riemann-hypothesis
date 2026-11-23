module

public import Formalism.MirabolicMackeyTheory.Bundle001
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

open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem onLocal_of (hMono : IdxMono) (hCut : IdxCutLe) (hTr : IdxTransport) (hInt : LatInter)
    (h3 : ThreeForms) (hPG : IdxPsiGood) (hGG : LemmaGG) : OnLocal := by
  unfold OnLocal
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hrange M Th ThK Th0 X₃ X₄ hM hTh hThK
    hThM hTh0fg hTh0 hMst hThst σ hσ hThσ hucut a E r ha hE hW hT0 hX3 hX4 hX34 ε hε d φ hφ
    hφr Mj Tj hMj hTj
  have hr : (lix w M (M ⊓ sc a⁻¹ Th) : ℝ) ≤ r :=
    (h3 K Z w M Th hM hTh hThM a E r ha hE).mp hW
  have hNl : IsLatIn ⊤ (M ⊓ sc a⁻¹ Th) := hInt K Z M Th hM hTh a⁻¹ (inv_ne_zero ha)

  have hNst : ∀ g : P, (M ⊓ sc a⁻¹ Th).map ((ρ g).restrictScalars (𝓞 K)) ≤ M ⊓ sc a⁻¹ Th := by
    intro g x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨hyM, hyT⟩ := Submodule.mem_inf.mp hy
    refine Submodule.mem_inf.mpr ⟨hMst g (Submodule.mem_map_of_mem hyM), ?_⟩
    unfold sc at hyT ⊢
    obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.mp hyT
    refine Submodule.mem_map.mpr ⟨(ρ g) t, hThst g (Submodule.mem_map_of_mem ht), ?_⟩
    simp
  have hcard : Nat.card U ≠ 0 := Nat.card_pos.ne'
  have hidx : 0 < U.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hG := hGG K Z w P ρ U ψ hMk M (M ⊓ sc a⁻¹ Th) hM hNl inf_le_left hMst hNst
  obtain ⟨hTl, hbound⟩ := hPG K Z w (eig ρ U ψ) V₀ M Th ThK Th0 hM hTh hThK hThM hTh0fg hTh0
    σ hσ hThσ (Nat.card U) hcard hucut a E r ha hE hr U.index hidx hG
  have hXl : IsLatIn (eig ρ U ψ ⊓ V₀) (cut (eig ρ U ψ ⊓ V₀) M) :=
    (hCut K Z w ⊤ (eig ρ U ψ ⊓ V₀) M M hM hM le_rfl le_top).1

  have hcutle : cut V₀ Th0 ≤ Th0.map (e.restrictScalars (𝓞 K)) := by
    intro x hx
    simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem] at hx
    obtain ⟨hx0, hxV⟩ := hx
    rw [← hrange] at hxV
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hxV
    refine Submodule.mem_map.mpr ⟨e y, hx0, ?_⟩
    show e (e y) = e y
    rw [← LinearMap.comp_apply, he]
  have h1 := hMono K Z w (eig ρ U ψ ⊓ V₀) (cut (eig ρ U ψ ⊓ V₀) M) X₃ X₄ hXl hX3 hX4 hX34
  have h2 := hMono K Z w (eig ρ U ψ ⊓ V₀) (cut (eig ρ U ψ ⊓ V₀) M) (cut V₀ Th0)
    (Th0.map (e.restrictScalars (𝓞 K))) hXl hTl hT0 hcutle
  have htr := hTr K Z w d φ hφ Mj Tj
  rw [hMj, hTj] at htr
  have hdim : finrank K (eig ρ U ψ ⊓ V₀ : Submodule K Z) = d := by
    rw [← hφr, LinearMap.finrank_range_of_inj hφ, Module.finrank_fin_fun]
  rw [hdim] at hbound
  rw [← htr]
  have h1' : (lix w (cut (eig ρ U ψ ⊓ V₀) M) X₄ : ℝ) ≤ lix w (cut (eig ρ U ψ ⊓ V₀) M) X₃ := by
    exact_mod_cast h1
  have h2' : (lix w (cut (eig ρ U ψ ⊓ V₀) M) (Th0.map (e.restrictScalars (𝓞 K))) : ℝ) ≤
      lix w (cut (eig ρ U ψ ⊓ V₀) M) (cut V₀ Th0) := by
    exact_mod_cast h2
  linarith

theorem mackey_product : MackeyProd := by
  unfold MackeyProd
  intro ι A _ _ _ P _ U ψ hψ
  unfold IsMackey
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.prod_eq_one fun v _ => (hψ v).1
  · intro u hu u' hu'
    dsimp only
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hu1 : ∀ v ∈ (Set.univ : Set ι), u v ∈ U v := hu
    have hu2 : ∀ v ∈ (Set.univ : Set ι), u' v ∈ U v := hu'
    exact (hψ v).2.1 _ (hu1 v (Set.mem_univ v)) _ (hu2 v (Set.mem_univ v))
  · intro h hh
    have hex : ∃ v0, h v0 ∉ U v0 := by
      by_contra hc
      push_neg at hc
      apply hh
      show ∀ v ∈ (Set.univ : Set ι), h v ∈ U v
      exact fun v _ => hc v
    obtain ⟨v0, hv0⟩ := hex
    obtain ⟨u0, hu0, hc, hne⟩ := (hψ v0).2.2 (h v0) hv0
    refine ⟨Pi.mulSingle v0 u0, ?_, ?_, ?_⟩
    · show ∀ v ∈ (Set.univ : Set ι), Pi.mulSingle v0 u0 v ∈ U v
      intro v _
      by_cases hv : v = v0
      · subst hv
        simpa using hu0
      · simp [Pi.mulSingle_eq_of_ne hv]
    · show ∀ v ∈ (Set.univ : Set ι), (h⁻¹ * Pi.mulSingle v0 u0 * h) v ∈ U v
      intro v _
      by_cases hv : v = v0
      · subst hv
        simpa using hc
      · simp [Pi.mulSingle_eq_of_ne hv]
    · show ∏ v, ψ v ((h⁻¹ * Pi.mulSingle v0 u0 * h) v) ≠ ∏ v, ψ v (Pi.mulSingle v0 u0 v)
      rw [Fintype.prod_eq_single v0 (fun v hv => by simp [Pi.mulSingle_eq_of_ne hv, (hψ v).1]),
        Fintype.prod_eq_single v0 (fun v hv => by simp [Pi.mulSingle_eq_of_ne hv, (hψ v).1])]
      simpa using hne

end Formalism.EigenvalueLevelCeiling
end

section

open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

theorem orthogonality_of_mackey : OrthOfMackey := by
  unfold OrthOfMackey
  intro K _ _ _ Z _ _ P _ _ ρ U _ ψ hM h hh z hz
  obtain ⟨_, hmul, hex⟩ := hM
  obtain ⟨u0, hu0, hc, hne⟩ := hex h hh
  set S := ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) (ρ h z) with hS
  have hz' : ∀ u ∈ U, ρ u z = ((ψ u : 𝓞 K) : K) • z := by
    intro u hu
    unfold eig at hz
    have h1 := (Submodule.mem_iInf _).mp hz ⟨u, hu⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at h1
    exact h1
  have hA : ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) (ρ u0 (ρ h z)) =
      ((ψ u0 : 𝓞 K) : K) • S := by
    rw [hS, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight (⟨u0, hu0⟩ : U)) _ _ (fun u => ?_)
    simp only [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul]
    congr 1
    have key : ψ ((u : P)⁻¹) = ψ u0 * ψ (((u : P) * u0)⁻¹) := by
      rw [← hmul u0 hu0 _ (U.inv_mem (U.mul_mem u.2 hu0))]
      congr 1
      group
    rw [key]
    norm_cast
  have hB : ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) (ρ u0 (ρ h z)) =
      ((ψ (h⁻¹ * u0 * h) : 𝓞 K) : K) • S := by
    have e1 : ρ u0 (ρ h z) = ((ψ (h⁻¹ * u0 * h) : 𝓞 K) : K) • ρ h z := by
      have e2 : ρ u0 (ρ h z) = ρ h (ρ (h⁻¹ * u0 * h) z) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [e2, hz' _ hc, map_smul]
    rw [hS, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [e1, map_smul, smul_smul, smul_smul, mul_comm]
  have h3 : (((ψ u0 : 𝓞 K) : K) - ((ψ (h⁻¹ * u0 * h) : 𝓞 K) : K)) • S = 0 := by
    rw [sub_smul, ← hA, ← hB, sub_self]
  rcases smul_eq_zero.mp h3 with h0 | h0
  · exact absurd (by exact_mod_cast (sub_eq_zero.mp h0).symm) hne
  · exact h0

end Formalism.EigenvalueLevelCeiling
end

section

namespace Formalism.EigenvalueLevelCeiling

theorem depth_cases : DepthCases := by
  unfold DepthCases
  intro e ec F
  refine ⟨fun a h1 h2 => by linarith, fun h1 h2 h3 => by linarith,
    fun s T β h1 h2 h3 h4 => by linarith, fun s T h1 h2 h3 => by linarith,
    fun T nn nnc g2 h1 h2 h3 => by linarith⟩

theorem budget_numeric : BudgetNum := by
  unfold BudgetNum
  intro dK δq D B hδ hD hB hq
  rw [div_le_iff₀ (mul_pos hδ hD)]
  have h1 : dK ≤ 3 * D * δq := (div_le_iff₀ hδ).mp hq
  have h2 : dK * B ≤ 3 * D * δq * B := mul_le_mul_of_nonneg_right h1 hB
  linarith

theorem share_numeric : ShareNum := by
  unfold ShareNum
  intro dK d0 d U δq ep y del hU hδ hdK hd0 hep hey hy hdel hdel' h1 h2 h3
  rw [div_le_iff₀ hδ]
  have k1 : 7 / 8 * dK ≤ U * d0 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 8 - ep) hdK]
  have k2 : 7 / 8 * U ≤ δq := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 8 - y) hU.le]
  have k3 : 3 / 4 * d0 ≤ d := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 4 - del) hd0]
  have hd : 0 ≤ d := by linarith
  have k4 : d * (7 / 8 * U) ≤ d * δq := mul_le_mul_of_nonneg_left k2 hd
  have k5 : 3 / 4 * d0 * U ≤ d * U := mul_le_mul_of_nonneg_right k3 hU.le
  nlinarith

end Formalism.EigenvalueLevelCeiling
end
