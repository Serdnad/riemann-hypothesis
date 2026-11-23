module

public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle011
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle004
public import GroundTheory.AutomorphicForms.Cartan
public import Development.DiscreteGroups.GlobalIrreducibility.LConvUnifB
public import GroundTheory.AutomorphicForms.JacquetAdmissible
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle002
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle007
public import Development.DiscreteGroups.GlobalIrreducibility.LConvKirStep
public import Development.DiscreteGroups.GlobalIrreducibility.LConvAltA
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

@[expose] public section

section

noncomputable section

namespace DiscreteGroups.sglob.LConvU

open GroundTheory.Automorphic GroundTheory.Automorphic.Cartan GroundTheory.Automorphic.Parabolic Matrix

section Hop

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) F) V}
  (hρ : GroundTheory.Automorphic.IsSmooth ρ) {r : ℕ}
  (hKc : IsCompact (GLnLocal.congruenceSubgroup F n r : Set (GL (Fin n) F)))
  (hKo : IsOpen (GLnLocal.congruenceSubgroup F n r : Set (GL (Fin n) F)))

include hρ hKc hKo

theorem hop_diagPow_mul (hr : 1 ≤ r) {μ ν : Fin n → ℤ} (hμ : IsDominant μ) (hν : IsDominant ν) :
    hop ρ hρ hKc hKo (diagPow F n μ) * hop ρ hρ hKc hKo (diagPow F n ν) =
      hop ρ hρ hKc hKo (diagPow F n (μ + ν)) := by
  rw [diagPow_add]
  refine hop_mul hρ hKc hKo fun w hw κ hκ => ?_
  obtain ⟨a, ha, b, hb, c, hc, h⟩ := dominant_conj hr hμ hν hκ
  have hbc : ρ (b * c) w = w := hw _ (mul_mem hb hc)
  rw [h, show a * (diagPow F n μ * diagPow F n ν) * b * c =
      a * ((diagPow F n μ * diagPow F n ν) * (b * c)) by group,
    map_mul, mul_apply_eq_comp, fixedProj_apply_act hρ hKc hKo ha, map_mul,
    mul_apply_eq_comp, hbc]

theorem hop_integral_mul {k : GL (Fin n) F} (hk : k ∈ GLnLocal.integralGL F n)
    (g : GL (Fin n) F) :
    hop ρ hρ hKc hKo k * hop ρ hρ hKc hKo g = hop ρ hρ hKc hKo (k * g) := by
  refine hop_mul hρ hKc hKo fun w _ κ hκ => ?_
  rw [show k * κ * g = (k * κ * k⁻¹) * (k * g) by group, map_mul, mul_apply_eq_comp,
    fixedProj_apply_act hρ hKc hKo (GLnLocal.conj_mem_congruenceSubgroup F n hk hκ)]

theorem hop_mul_integral (g : GL (Fin n) F) {k : GL (Fin n) F}
    (hk : k ∈ GLnLocal.integralGL F n) :
    hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo k = hop ρ hρ hKc hKo (g * k) := by
  refine hop_mul hρ hKc hKo fun w hw κ hκ => ?_
  rw [show g * κ * k = (g * k) * (k⁻¹ * κ * k⁻¹⁻¹) by group, map_mul, mul_apply_eq_comp,
    hw _ (GLnLocal.conj_mem_congruenceSubgroup F n (inv_mem hk) hκ)]

local notation "K0" => GLnLocal.integralGL F n
local notation "Kr" => GLnLocal.congruenceSubgroup F n r
local notation "W" => fixedVectors ρ Kr
local notation "T" => hop ρ hρ hKc hKo

theorem finrank_le_of_commBound (hr : 1 ≤ r) [ρ.IsIrreducible] [FiniteDimensional ℂ W]
    [Fintype (K0 ⧸ (Kr).subgroupOf K0)] {c : ℕ}
    (hc : ∀ a : Fin (n + 1) → Module.End ℂ W, (∀ i j, a i * a j = a j * a i) →
      2 * Fintype.card (K0 ⧸ (Kr).subgroupOf K0) ^ 2 *
          Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ W ^ 2 + c * Module.finrank ℂ W) :
    Module.finrank ℂ W ≤ c := by
  classical
  by_cases h0 : Module.finrank ℂ W = 0
  · rw [h0]; exact Nat.zero_le _
  have hpos : 0 < Module.finrank ℂ W := Nat.pos_of_ne_zero h0
  have : Nontrivial W := Module.finrank_pos_iff.1 hpos
  have hspan := span_hop_eq_top hρ hKc hKo
  let a : Fin (n + 1) → Module.End ℂ W := fun i => T (diagPow F n (gen n i))
  have hcomm : ∀ i j, a i * a j = a j * a i := fun i j => by
    simp only [a]
    rw [hop_diagPow_mul hρ hKc hKo hr (gen_dominant n i) (gen_dominant n j),
      hop_diagPow_mul hρ hKc hKo hr (gen_dominant n j) (gen_dominant n i), add_comm]
  let C := Algebra.adjoin ℂ (Set.range a)
  have hTC : ∀ μ, IsDominant μ → T (diagPow F n μ) ∈ C := by
    refine dom_induct (fun μ => T (diagPow F n μ) ∈ C) ?_ ?_ ?_
    · show T (diagPow F n 0) ∈ C
      rw [diagPow_zero, hop_one]
      exact C.one_mem
    · intro i
      exact Algebra.subset_adjoin ⟨i, rfl⟩
    · intro μ ν hμ hν h1 h2
      show T (diagPow F n (μ + ν)) ∈ C
      rw [← hop_diagPow_mul hρ hKc hKo hr hμ hν]
      exact C.mul_mem h1 h2
  let P : (K0 ⧸ (Kr).subgroupOf K0) → Module.End ℂ W :=
    fun q => T ((Quotient.out q : K0) : GL (Fin n) F)
  have hP : ∀ k (hk : k ∈ K0), P (QuotientGroup.mk ⟨k, hk⟩) = T k := by
    intro k hk
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((Kr).subgroupOf K0) (⟨k, hk⟩ : K0)
    show T ((Quotient.out (QuotientGroup.mk ⟨k, hk⟩ : K0 ⧸ (Kr).subgroupOf K0) : K0) :
      GL (Fin n) F) = T k
    rw [hh, Subgroup.coe_mul, ← hop_mul_integral hρ hKc hKo _ ((h : K0)).2,
      hop_of_mem hρ hKc hKo (Subgroup.mem_subgroupOf.1 h.2), mul_one]
  have hCfin : FiniteDimensional ℂ C :=
    Module.Finite.of_injective C.val.toLinearMap Subtype.val_injective
  let Φ : ((K0 ⧸ (Kr).subgroupOf K0) × (K0 ⧸ (Kr).subgroupOf K0) → C) →ₗ[ℂ] Module.End ℂ W :=
    ∑ p, (LinearMap.mulLeft ℂ (P p.1)) ∘ₗ (LinearMap.mulRight ℂ (P p.2)) ∘ₗ
      C.val.toLinearMap ∘ₗ LinearMap.proj p
  have hΦ : ∀ f, Φ f = ∑ p, P p.1 * (((f p : C) : Module.End ℂ W) * P p.2) := by
    intro f
    rw [LinearMap.sum_apply]
    rfl
  have hrange : Set.range T ⊆ LinearMap.range Φ := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨μ, hμ, k1, hk1, k2, hk2, hg⟩ := exists_eq_mul_diagPow_mul F n g
    refine ⟨Pi.single (QuotientGroup.mk ⟨k1, hk1⟩, QuotientGroup.mk ⟨k2, hk2⟩)
      ⟨_, hTC μ hμ⟩, ?_⟩
    rw [hΦ, Finset.sum_eq_single (QuotientGroup.mk ⟨k1, hk1⟩, QuotientGroup.mk ⟨k2, hk2⟩)]
    · rw [Pi.single_eq_same]
      show P (QuotientGroup.mk ⟨k1, hk1⟩) * (T (diagPow F n μ) * P (QuotientGroup.mk ⟨k2, hk2⟩)) = T g
      rw [hP, hP, hg, mul_assoc, hop_mul_integral hρ hKc hKo _ hk2,
        hop_integral_mul hρ hKc hKo hk1]
    · intro p _ hp
      rw [Pi.single_eq_of_ne hp]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  have htop : LinearMap.range Φ = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    exact hrange
  have hdim := LinearMap.finrank_range_le Φ
  rw [htop, finrank_top, Module.finrank_linearMap, Module.finrank_pi_fintype] at hdim
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul] at hdim
  have hcb := hc a hcomm
  have h2 : Module.finrank ℂ W * Module.finrank ℂ W ≤ c * Module.finrank ℂ W := by
    nlinarith [hdim, hcb]
  exact Nat.le_of_mul_le_mul_right h2 hpos

end Hop

end DiscreteGroups.sglob.LConvU

namespace DiscreteGroups.sglob.LConv

open GroundTheory.Automorphic GroundTheory.Automorphic.Parabolic DiscreteGroups.sglob.LConvU

theorem unifOfComm : UnifOfComm := by
  intro hCB k _ _ _ _ m K hK
  classical
  obtain ⟨r0, -, hr0⟩ := (GLnLocal.hasBasis_nhds_one k m).mem_iff.1 (hK.mem_nhds K.one_mem)
  obtain ⟨r, hr, hrr⟩ : ∃ r, 1 ≤ r ∧ r0 ≤ r := ⟨max r0 1, le_max_right _ _, le_max_left _ _⟩
  have hKrK : GLnLocal.congruenceSubgroup k m r ≤ K := fun x hx =>
    hr0 (GLnLocal.congruenceSubgroup_antitone k m hrr hx)
  have hKc := GLnLocal.isCompact_congruenceSubgroup k m r
  have hKo := GLnLocal.isOpen_congruenceSubgroup k m r
  have : CompactSpace (GLnLocal.integralGL k m) :=
    isCompact_iff_compactSpace.mp (GLnLocal.isCompact_integralGL k m)
  have hHo : IsOpen (((GLnLocal.congruenceSubgroup k m r).subgroupOf (GLnLocal.integralGL k m) :
      Subgroup (GLnLocal.integralGL k m)) : Set (GLnLocal.integralGL k m)) :=
    hKo.preimage continuous_subtype_val
  have : Finite (GLnLocal.integralGL k m ⧸
      (GLnLocal.congruenceSubgroup k m r).subgroupOf (GLnLocal.integralGL k m)) :=
    Subgroup.quotient_finite_of_isOpen _ hHo
  let _ : Fintype (GLnLocal.integralGL k m ⧸
      (GLnLocal.congruenceSubgroup k m r).subgroupOf (GLnLocal.integralGL k m)) :=
    Fintype.ofFinite _
  obtain ⟨c, hc⟩ := hCB (m + 1) (2 * Fintype.card (GLnLocal.integralGL k m ⧸
      (GLnLocal.congruenceSubgroup k m r).subgroupOf (GLnLocal.integralGL k m)) ^ 2)
  refine ⟨c, fun V _ _ ρ hρs hρi => ?_⟩
  have hρ : GroundTheory.Automorphic.IsSmooth ρ := fun v => hρs v
  have : ρ.IsIrreducible := hρi
  have hfin : FiniteDimensional ℂ (fixedVectors ρ (GLnLocal.congruenceSubgroup k m r)) :=
    (isAdmissible_of_isIrreducible hρ).2 _ hKc hKo
  have hle : GlobalTheory.PRep.fixed ρ K ≤ fixedVectors ρ (GLnLocal.congruenceSubgroup k m r) := by
    intro v hv κ hκ
    have := hv ⟨κ, hKrK hκ⟩
    simpa using this
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  exact (LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)).trans
    (finrank_le_of_commBound hρ hKc hKo hr (c := c) fun a ha => hc _ a ha)

end DiscreteGroups.sglob.LConv
end
end

section

open scoped InnerProductSpace

noncomputable section

namespace DiscreteGroups.sglob.LConv

open CompanionTheory.D.gk.admitted

theorem irred_of_scalar {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : G →* (H →L[ℂ] H)) (hπ : ∀ g x, ‖π g x‖ = ‖x‖)
    (hsc : ∀ T : H →L[ℂ] H, (∀ g, T * π g = π g * T) → ∃ c : ℂ, T = c • (1 : H →L[ℂ] H))
    (S : Submodule ℂ H) (hcl : IsClosed (S : Set H)) (hS : ∀ g, ∀ v ∈ S, π g v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  have : CompleteSpace S := hcl.completeSpace_coe
  have hcomm : ∀ g, S.starProjection * π g = π g * S.starProjection := by
    intro g
    ext z
    show S.starProjection (π g z) = π g (S.starProjection z)
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact hS g _ (S.starProjection_apply_mem z)
    · intro w hw
      rw [← map_sub, FinOfPIAux.inner_left π hπ]
      exact S.starProjection_inner_eq_zero z _ (hS _ _ hw)
  obtain ⟨c, hc⟩ := hsc _ hcomm
  have hP : ∀ z, S.starProjection z = c • z := fun z => by rw [hc]; rfl
  by_cases h0 : S = ⊥
  · exact Or.inl h0
  · right
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    have h1 : c • x = x := by rw [← hP, Submodule.starProjection_eq_self_iff.mpr hx]
    have hc1 : c = 1 := by
      have h2 : (c - 1) • x = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      rcases smul_eq_zero.mp h2 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hx0
    rw [eq_top_iff]
    intro z _
    have h3 := S.starProjection_apply_mem z
    rwa [hP, hc1, one_smul] at h3

theorem word_eq_mul_prod {R : Type*} [Ring R] (e : R) (he : e * e = e) (l : List R) :
    word e l = e * (l.map fun a => e * a * e).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [word_cons, ih, List.map_cons, List.prod_cons, ← mul_assoc, he]

theorem finiteOfAlt : FiniteOfAlt := by
  intro G _ H _ _ _ π hπ hsc e he d hd
  have h : ∀ g : Fin d → G, stdPoly e (fun i => π (g i)) = 0 := by
    intro g
    have h0 := congrArg (fun X => e * X) (hd g)
    simp only [mul_zero] at h0
    rw [← h0, stdPoly, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [word_eq_mul_prod e he, List.map_ofFn, mul_smul_comm, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    rfl
  obtain ⟨hfd, -⟩ := finite_rank_of_irreducible_unitary G H π hπ (irred_of_scalar π hπ hsc) e d h
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional _).mpr hfd
  refine ⟨s, fun x => ?_⟩
  rw [hs]
  exact LinearMap.mem_range_self (e : H →ₗ[ℂ] H) x

end DiscreteGroups.sglob.LConv

end
end

section

noncomputable section
open GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv

open DiscreteGroups.sglob.LConvKir in
theorem kirBump : KirBump := by
  intro k _ _ _ _ ψ hψc hψ m V _ _ ρ hsm v₀
  have key : ∀ j, j ≤ m → ∃ v : V, ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l →
      l v = l v₀ ∧ (l v₀ = 0 → ∀ g, InH j g → l (ρ g v) = 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨v₀, fun l _ => ⟨rfl, fun h0 g hg => by rw [InH_zero g hg, map_one, Module.End.one_apply]; exact h0⟩⟩
    | succ j ih =>
      intro hj
      obtain ⟨v, hv⟩ := ih (by omega)
      obtain ⟨v', hv'⟩ := step ψ hψc hψ ρ hsm j (by omega) v
      exact ⟨v', fun l hl => ⟨(hv' l hl).1.trans (hv l hl).1,
        fun h0 g hg => (hv' l hl).2 ((hv l hl).2 h0) g hg⟩⟩
  obtain ⟨v, hv⟩ := key m le_rfl
  exact ⟨v, fun l hl => ⟨(hv l hl).1, fun h0 g => (hv l hl).2 h0 _ (InH_corner g)⟩⟩

end DiscreteGroups.sglob.LConv
end
end

section

noncomputable section

open GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv

theorem alt_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G) (N : ℕ)
    (hN : UnifAdm G K N) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)) (e : H →L[ℂ] H) (hKe' : ∀ κ ∈ K, π κ * e = e) (hee : e * e = e)
    (Y Y' : Submodule ℂ (H →L[ℂ] H))
    (hYs : Y ≤ Submodule.span ℂ (Set.range fun h => π h * e)) (heY : e ∈ Y)
    (hY1 : ∀ h, ∀ y ∈ Y, π h * y ∈ Y) (hYE : ∀ y ∈ Y, e * y ∈ Y)
    (hSm : ∀ y ∈ Y, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u * y = y)
    (hY'Y : Y' ≤ Y) (hY'G : ∀ h, ∀ y ∈ Y', π h * y ∈ Y') (hY'E : ∀ y ∈ Y', e * y ∈ Y') (heY' : e ∉ Y')
    (hmax : ∀ Z : Submodule ℂ (H →L[ℂ] H), Z ≤ Y → (∀ h, ∀ z ∈ Z, π h * z ∈ Z) → e ∉ Z → Y' ≤ Z → Z ≤ Y')
    (d : ℕ) (hd : N ^ 2 < d) (g : Fin d → G) :
    (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun i => e * π (g (σ i)) * e).prod) * e ∈ Y' := by
  let ρY : Representation ℂ G Y :=
    { toFun := fun h => (LinearMap.mulLeft ℂ (π h)).restrict (fun y hy => hY1 h y hy)
      map_one' := by
        refine LinearMap.ext fun y => Subtype.ext ?_
        show π 1 * (y : H →L[ℂ] H) = y
        rw [map_one, one_mul]
      map_mul' := by
        intro a b
        refine LinearMap.ext fun y => Subtype.ext ?_
        show π (a * b) * (y : H →L[ℂ] H) = π a * (π b * y)
        rw [map_mul, mul_assoc] }
  have hρY : ∀ h (y : Y), ((ρY h y : Y) : H →L[ℂ] H) = π h * y := fun h y => rfl
  let Y'' : Submodule ℂ Y := Y'.comap Y.subtype
  have hρY'' : ∀ h, Y'' ≤ Y''.comap (ρY h) := fun h y hy => hY'G h y hy
  let ρQ : Representation ℂ G (Y ⧸ Y'') :=
    { toFun := fun h => Y''.mapQ Y'' (ρY h) (hρY'' h)
      map_one' := by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        show Submodule.Quotient.mk (ρY 1 y) = Submodule.Quotient.mk y
        rw [map_one]; rfl
      map_mul' := by
        intro a b
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        show Submodule.Quotient.mk (ρY (a * b) y) = Submodule.Quotient.mk (ρY a (ρY b y))
        rw [map_mul]; rfl }
  have hρQ : ∀ h (y : Y), ρQ h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (ρY h y) := fun h y => rfl
  have hsm : IsSmooth ρQ := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Y'' q
    obtain ⟨U, hUo, hU⟩ := hSm y y.2
    exact alt_isOpen_fix ρQ _ U hUo fun v hv => by
      rw [hρQ]; congr 1; exact Subtype.ext (hU v hv)
  have hmk0 : ∀ y : Y, (Submodule.Quotient.mk y : Y ⧸ Y'') = 0 ↔ (y : H →L[ℂ] H) ∈ Y' :=
    fun y => Submodule.Quotient.mk_eq_zero Y''
  have hirr : ρQ.IsIrreducible := by
    unfold Representation.IsIrreducible
    rw [isSimpleOrder_iff]
    refine ⟨⟨⊥, ⊤, fun hbt => heY' ?_⟩, fun a => ?_⟩
    · have h1 : (Submodule.Quotient.mk (⟨e, heY⟩ : Y) : Y ⧸ Y'') ∈ (⊥ : Subrepresentation ρQ).toSubmodule := by
        rw [hbt]; exact Submodule.mem_top
      exact (hmk0 _).mp ((Submodule.mem_bot ℂ).mp h1)
    · let Z : Submodule ℂ (H →L[ℂ] H) := (a.toSubmodule.comap Y''.mkQ).map Y.subtype
      have hZY : Z ≤ Y := by rintro _ ⟨y, _, rfl⟩; exact y.2
      have hZG : ∀ h, ∀ x ∈ Z, π h * x ∈ Z := by
        rintro h _ ⟨y, hy, rfl⟩
        exact ⟨ρY h y, a.apply_mem_toSubmodule h hy, rfl⟩
      have hY'Z : Y' ≤ Z := by
        intro x hx
        refine ⟨⟨x, hY'Y hx⟩, ?_, rfl⟩
        show Submodule.Quotient.mk _ ∈ a.toSubmodule
        rw [(hmk0 _).mpr hx]
        exact a.toSubmodule.zero_mem
      by_cases heZ : e ∈ Z
      · right
        apply Subrepresentation.toSubmodule_injective
        show a.toSubmodule = ⊤
        refine eq_top_iff.mpr fun q _ => ?_
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Y'' q
        have hYZ : Y ≤ Z := hYs.trans (Submodule.span_le.mpr (by rintro _ ⟨h, rfl⟩; exact hZG h e heZ))
        obtain ⟨y', hy', hyy⟩ := hYZ y.2
        rw [← Subtype.ext hyy]
        exact hy'
      · left
        apply Subrepresentation.toSubmodule_injective
        show a.toSubmodule = ⊥
        refine eq_bot_iff.mpr fun q hq => ?_
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Y'' q
        have := hmax Z hZY hZG heZ hY'Z ⟨y, hq, rfl⟩
        exact (Submodule.mem_bot ℂ).mpr ((hmk0 y).mpr this)
  obtain ⟨hfd, hfr⟩ := hN (Y ⧸ Y'') ρQ hsm hirr
  let f : G → (H →L[ℂ] H) := fun h => e * π h * e
  have hfY : ∀ a, ∀ y ∈ Y, f a * y ∈ Y := fun a y hy => by
    show e * π a * e * y ∈ Y
    rw [mul_assoc, mul_assoc]; exact hYE _ (hY1 a _ (hYE y hy))
  let TY : G → Module.End ℂ Y := fun a => (LinearMap.mulLeft ℂ (f a)).restrict (fun y hy => hfY a y hy)
  have hTY'' : ∀ a, Y'' ≤ Y''.comap (TY a) := fun a y hy => by
    show e * π a * e * (y : H →L[ℂ] H) ∈ Y'
    rw [mul_assoc, mul_assoc]; exact hY'E _ (hY'G a _ (hY'E _ hy))
  let T : G → Module.End ℂ (Y ⧸ Y'') := fun a => Y''.mapQ Y'' (TY a) (hTY'' a)
  have hfixmk : ∀ y : Y, e * (y : H →L[ℂ] H) = y → Submodule.Quotient.mk y ∈ fixed ρQ K := by
    intro y hy
    show ∀ κ : K, _
    intro κ
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [hρQ]; congr 1; apply Subtype.ext
    rw [hρY, ← hy, ← mul_assoc, hKe' κ κ.2]
  have hTW : ∀ a q, T a q ∈ fixed ρQ K := by
    intro a q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Y'' q
    exact hfixmk (TY a y) (by show e * (e * π a * e * (y : H →L[ℂ] H)) = e * π a * e * y; simp only [← mul_assoc, hee])
  have := hfd
  let t : G → Module.End ℂ (fixed ρQ K) := fun a => (T a).restrict (fun q _ => hTW a q)
  have hdim : Module.finrank ℂ (Module.End ℂ (fixed ρQ K)) < d := by
    rw [Module.finrank_linearMap, ← sq]
    exact lt_of_le_of_lt (Nat.pow_le_pow_left hfr 2) hd
  have h0 := alt_std_eq_zero hdim fun i => t (g i)
  have key : ∀ (l : List G) (w : fixed ρQ K), (((l.map t).prod w : fixed ρQ K) : Y ⧸ Y'') = (l.map T).prod w := by
    intro l w
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      exact congrArg (T a) ih
  have key2 : ∀ (l : List G) (y : Y),
      (l.map T).prod (Submodule.Quotient.mk y) = Submodule.Quotient.mk ((l.map TY).prod y) := by
    intro l y
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]; rfl
  have key3 : ∀ (l : List G) (y : Y), (((l.map TY).prod y : Y) : H →L[ℂ] H) = (l.map f).prod * y := by
    intro l y
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.map_cons, List.prod_cons, mul_assoc, ← ih]
      rfl
  let e' : Y := ⟨e, heY⟩
  have he'W : Submodule.Quotient.mk e' ∈ fixed ρQ K := hfixmk e' hee
  have h1 := congrArg (fun X : Module.End ℂ (fixed ρQ K) => ((X ⟨_, he'W⟩ : fixed ρQ K) : Y ⧸ Y'')) h0
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    LinearMap.zero_apply, ZeroMemClass.coe_zero] at h1
  have hsum : ∀ σ : Equiv.Perm (Fin d), (((List.ofFn fun i => t (g (σ i))).prod ⟨_, he'W⟩ : fixed ρQ K) : Y ⧸ Y'')
      = Y''.mkQ (((List.ofFn fun i => g (σ i)).map TY).prod e') := by
    intro σ
    rw [show (List.ofFn fun i => t (g (σ i))) = (List.ofFn fun i => g (σ i)).map t by rw [List.map_ofFn]; rfl,
      key, key2]
    rfl
  have h1' : Y''.mkQ (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((List.ofFn fun i => g (σ i)).map TY).prod e') = 0 := by

    rw [map_sum]
    refine (Finset.sum_congr rfl fun σ _ => ?_).trans h1
    rw [map_smul, hsum]
  have h2 := (Submodule.Quotient.mk_eq_zero Y'').mp h1'
  have h3 : ((∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((List.ofFn fun i => g (σ i)).map TY).prod e' : Y) : H →L[ℂ] H) =
      (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun i => e * π (g (σ i)) * e).prod) * e := by
    rw [Submodule.coe_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Submodule.coe_smul, key3, smul_mul_assoc,
      show (List.ofFn fun i => e * π (g (σ i)) * e) = (List.ofFn fun i => g (σ i)).map f by rw [List.map_ofFn]; rfl]
  rw [← h3]
  exact h2

end DiscreteGroups.sglob.LConv
end
end
