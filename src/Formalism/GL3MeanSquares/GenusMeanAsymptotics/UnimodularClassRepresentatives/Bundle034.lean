module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle023
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AdjoinIntegralOfNonempty
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsVecOfHermRep
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle033
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NeZeroOfNotMem
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle008
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle016
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle032
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle031
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle026
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InLZeroIff

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

private theorem isFullLattice_adjoin (S : VecSplit h h') {Λ' : Submodule (𝓞 K) V'}
    (hΛ' : Submodule.IsFullLattice K Λ') : Submodule.IsFullLattice K (S.adjoin Λ') := by
  refine { toIsLattice := (S.isLattice_adjoin_iff Λ').2 hΛ'.toIsLattice, span_eq_top := ?_ }
  rw [eq_top_iff]
  intro v _
  obtain ⟨c, a, rfl⟩ := S.cover v
  refine add_mem (Submodule.smul_mem _ c (Submodule.subset_span (S.x₀_mem_adjoin Λ'))) ?_
  have hle : Submodule.map S.ι (Submodule.span K (Λ' : Set V')) ≤
      Submodule.span K (S.adjoin Λ' : Set V) := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨b, hb, rfl⟩
    exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hb)
  have ha : a ∈ Submodule.span K (Λ' : Set V') := by
    rw [hΛ'.span_eq_top]
    exact Submodule.mem_top
  exact hle (Submodule.mem_map_of_mem ha)

theorem fibLoc_eq_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {Λ' : Submodule (𝓞 K) V'}
    (hΛ' : Submodule.IsFullLattice K Λ') (hΛi : Formalism.HermitianLatticesTheory.IsIntegralLat h' Λ') {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvL : vd h L 𝔭 = 0) (hvn : vF 𝔭 n = 0) (hvΛ : vd h' Λ' 𝔭 = 0) : fibLoc S L 𝔭 Λ' = 1 := by
  classical
  rw [LocalizedFibreSets.fibLoc_eq_card]
  haveI := hL
  haveI hN := isFullLattice_adjoin S hΛ'
  have hmk : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n) = algebraMap F K (n : F) := rfl
  have hn1 : h S.x₀ S.x₀ ∈ (1 : Submodule (𝓞 K) K) := by
    rw [hn, ← hmk]
    exact Submodule.mem_one.2 ⟨_, rfl⟩
  have hNi : Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin Λ') := LocalizedFibreSets.isIntegralLat_adjoin hs S hn1 hΛi
  obtain ⟨P, hP, hPc⟩ := LocalizedFibreSets.exists_max_over (K := K) h𝔭
  have hne : algebraMap F K (n : F) ≠ 0 := by
    rw [← hn]
    exact S.hx₀
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (by simp)
  have hnP : n ∉ 𝔭 := LocalizedFibreSets.notMem_of_vF_zero h𝔭 hn0 hvn
  have hmP : algebraMap (𝓞 F) (𝓞 K) n ∉ P := by
    intro hm
    apply hnP
    rw [← hPc]
    exact hm
  have hvN : vd h (S.adjoin Λ') 𝔭 = 0 := by
    rw [← hPc, ← isUnimodularAt_iff_vd hK hF hs hd hN hNi hP]
    refine LocalizedFibreSets.unimod_adjoin hs S ?_ ?_ ?_
    · show ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, s • h S.x₀ S.x₀ ∈ (1 : Submodule (𝓞 K) K)
      exact ⟨1, Submonoid.one_mem _, by simpa using hn1⟩
    · show ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, s • (h S.x₀ S.x₀)⁻¹ ∈ (1 : Submodule (𝓞 K) K)
      refine ⟨algebraMap (𝓞 F) (𝓞 K) n, Submonoid.subset_closure ⟨hmP, ?_⟩, ?_⟩
      · intro t ht
        have hst : star (algebraMap F K (n : F)) = algebraMap F K (n : F) := (hF _).2 ⟨_, rfl⟩
        rw [hmk, hst, ← hmk] at ht
        rw [FaithfulSMul.algebraMap_injective (𝓞 K) K ht]
        exact hmP
      · rw [Algebra.smul_def, hmk, hn, mul_inv_cancel₀ hne]
        exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [isUnimodularAt_iff_vd hK hF (S.isSymm hs) (S.isTotPosDef hd) hΛ' hΛi hP, hPc]
      exact hvΛ
  rw [LocalizedFibreSets.fibSet_eq_singleton hK hF hs hd S inferInstance hLi inferInstance hNi h𝔭 hvL hvN]
  simp

theorem card_fibG_eq_prod (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {Λ' : Submodule (𝓞 K) V'}
    (hΛ' : Submodule.IsFullLattice K Λ') :
    (Nat.card (fibG S L Λ') : ℝ) = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (fibLoc S L 𝔭.1 Λ' : ℝ) := by
  classical
  by_cases hne : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (LocalizedFibreSets.fibSet S L 𝔭.1 Λ').Nonempty
  · haveI := hL
    haveI hN := isFullLattice_adjoin S hΛ'
    have hNi := LocalizedFibreSets.adjoin_integral_of_nonempty hK hF S hLi hne
    obtain ⟨t, ht⟩ : ∃ t : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
        ∀ 𝔭 ∉ t, vd h L 𝔭.1 = 0 ∧ vd h (S.adjoin Λ') 𝔭.1 = 0 := by
      have hfin := (finite_vd_ne_zero hK hF hs hd hL hLi).union (finite_vd_ne_zero hK hF hs hd hN hNi)
      refine ⟨hfin.toFinset, fun 𝔭 h𝔭 => ?_⟩
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h𝔭
      exact h𝔭
    have ht1 : ∀ 𝔭 ∉ t, LocalizedFibreSets.fibSet S L 𝔭.1 Λ' = {locF 𝔭.1 (S.adjoin Λ')} := fun 𝔭 h𝔭 =>
      LocalizedFibreSets.fibSet_eq_singleton hK hF hs hd S inferInstance hLi inferInstance hNi
        𝔭.2 (ht 𝔭 h𝔭).1 (ht 𝔭 h𝔭).2
    rw [LocalizedFibreSets.card_fibG_eq_card_pi hK hF S hL hΛ' t ht1, Nat.card_pi, Nat.cast_prod,
      tprod_eq_prod (s := t) (fun 𝔭 h𝔭 => by rw [LocalizedFibreSets.fibLoc_eq_card, ht1 𝔭 h𝔭]; simp)]
    rw [← Finset.prod_coe_sort t]
    exact Finset.prod_congr rfl fun 𝔭 _ => by rw [LocalizedFibreSets.fibLoc_eq_card]
  · push Not at hne
    obtain ⟨𝔭, h𝔭⟩ := hne
    have hE : fibG S L Λ' = ∅ := Set.eq_empty_of_forall_notMem fun Λ hΛ => by
      have h1 := LocalizedFibreSets.locF_mem_fibSet hK hF S hΛ 𝔭.2
      rw [h𝔭] at h1
      exact h1
    rw [hE, tprod_of_exists_eq_zero ⟨𝔭, by rw [LocalizedFibreSets.fibLoc_eq_card, h𝔭]; simp⟩]
    simp

end Formalism.HermitianLattices.Ext.L3
end
end

section

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def IsE (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (e : ℕ) : Prop :=
  ∀ x : V, (∀ y ∈ A, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) →
    ∀ t ∈ 𝔭 ^ e, algebraMap (𝓞 F) (𝓞 K) t • x ∈ A

theorem gramK_det_ne_zero {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) :
    (gramK h b).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv
  have h1 := form_repr h b (b.equivFun.symm v) (b.equivFun.symm v)
  rw [LinearEquiv.apply_symm_apply, hv0, dotProduct_zero] at h1
  have h2 := hd _ h1
  rw [← b.equivFun.apply_symm_apply v, h2, map_zero]

theorem exists_E (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V)
    {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {e : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) {π₀ : 𝓞 F} (hπ : π₀ ∈ 𝔭) :
    ∃ E : Matrix κ κ K, Ent (SP K 𝔭) E ∧ gramK h b * E = jK (ι π₀) ^ e • (1 : Matrix κ κ K) := by
  have hdet : IsUnit (gramK h b).det := isUnit_iff_ne_zero.2 (gramK_det_ne_zero hd b)
  refine ⟨jK (ι π₀) ^ e • (gramK h b)⁻¹, ?_, by rw [Matrix.mul_smul, Matrix.mul_nonsing_inv _ hdet]⟩
  intro i j
  have h1 : ∀ y ∈ locF 𝔭 (spanO b), h y (b.equivFun.symm fun i => (gramK h b)⁻¹ i j) ∈
      locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro y hy
    rw [form_repr h b, LinearEquiv.apply_symm_apply]
    have h2 : (gramK h b *ᵥ fun i => (gramK h b)⁻¹ i j) = Pi.single j 1 := by
      funext l
      have : (gramK h b *ᵥ fun i => (gramK h b)⁻¹ i j) l = (gramK h b * (gramK h b)⁻¹) l j := rfl
      rw [this, Matrix.mul_nonsing_inv _ hdet, Matrix.one_apply, Pi.single_apply]
    rw [h2, dotProduct_single_one, ← mem_SP_iff_locF]
    exact InP.conj hF ((mem_locF_iff_repr b y).1 hy j)
  have h3 := (mem_locF_iff_repr b _).1 (he _ h1 (π₀ ^ e) (Ideal.pow_mem_pow hπ e)) i
  rw [← algebraMap_smul K, map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, map_pow,
    map_pow] at h3
  exact h3

theorem gramK_eq_map {h : V →ₗ⋆[K] V →ₗ[K] K} {b : Basis κ K V} {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) : gramK h b = H.map jK := by
  ext i j
  exact (hH i j).symm

theorem map_form (H Y : Matrix κ κ (𝓞 K)) :
    (Y.map jK)ᴴ * H.map jK * Y.map jK = (Yᴴ * H * Y).map jK := by
  rw [Matrix.map_mul, Matrix.map_mul, conjTranspose_map jK (fun _ => rfl)]

theorem exists_Z {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {π₀ s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π₀ s₀)
    {H Y : Matrix κ κ (𝓞 K)} {k : ℕ} (hY : ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k) :
    ∃ Z : Matrix κ κ K, Ent (SP K 𝔭) Z ∧
      (Y.map jK)ᴴ * H.map jK * Y.map jK = H.map jK + jK (ι π₀) ^ k • Z := by
  choose Z hZ hZ' using fun i j => (mem_noncompactPart_iff hu k _).1 (inP_jK (hY i j))
  refine ⟨Matrix.of Z, hZ, ?_⟩
  rw [map_form]
  ext i j
  have := hZ' i j
  rw [Matrix.sub_apply, map_sub] at this
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul,
    ← this]
  ring

theorem ent_map {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (Y : Matrix κ κ (𝓞 K)) : Ent (SP K 𝔭) (Y.map jK) :=
  fun _ _ => jK_mem_SP _

theorem equivFun_sum_smul (b : Basis κ K V) (c : κ → 𝓞 K) :
    b.equivFun (∑ l, c l • b l) = fun l => jK (c l) := by
  have : ∑ l, c l • b l = ∑ l, jK (c l) • b l :=
    Finset.sum_congr rfl fun l _ => (algebraMap_smul K _ _).symm
  rw [this, ← Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

theorem exists_isom_matrix (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e k : ℕ}
    (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) (hk : e + 1 ≤ k) (Y : Matrix κ κ (𝓞 K))
    (hY : ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k) :
    ∃ g ∈ autSub h (locF 𝔭 (spanO b)), ∀ i, g (b i) - ∑ l, Y l i • b l ∈
      (extP K 𝔭 ^ (k - e) • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by
  have := h𝔭.isPrime
  obtain ⟨π₀, s₀, hu⟩ := exists_isUnif0 h𝔭
  obtain ⟨E, hE, hHE⟩ := exists_E hF hd b he hu.mem
  obtain ⟨Z, hZ, hXZ⟩ := exists_Z hu hY
  have hg := gramK_eq_map hH
  rw [hg] at hHE
  have hHh : (H.map jK)ᴴ = H.map jK := by rw [← hg]; exact gramK_conjTranspose hs b
  obtain ⟨G, G', D, hG, hG', hD, hGG, hU, hGX⟩ := exists_unitary_near (isLocUnif hK hF h𝔭 hu) hHh
    (ent_map H) hE hHE hk (ent_map Y) hZ hXZ
  refine ⟨equivOfMatrix b G G' hGG, ⟨equivOfMatrix_mem_isom h b G G' hGG (by rw [hg]; exact hU),
    gmap_equivOfMatrix b G G' hGG hG hG'⟩, fun i => ?_⟩
  rw [mem_smul_locF_iff_repr]
  intro l
  have hb1 : b.equivFun (b i) = Pi.single i 1 := by
    funext j
    rw [Basis.equivFun_self, Pi.single_apply]
    simp only [eq_comm]
  rw [map_sub, equivFun_equivOfMatrix, equivFun_sum_smul, hb1, mulVec_single_one, Pi.sub_apply]
  show InP 𝔭 (k - e) (G l i - jK (Y l i))
  rw [hGX, mem_noncompactPart_iff hu]
  refine ⟨D l i, hD l i, ?_⟩
  simp

theorem form_col (H Y : Matrix κ κ (𝓞 K)) (i j : κ) :
    (Yᴴ * H * Y) i j = star (fun l => Y l i) ⬝ᵥ (H *ᵥ fun l => Y l j) := by
  have := form_mulVec Y H (Pi.single i 1) (Pi.single j 1)
  rw [form_single, mulVec_single_one, mulVec_single_one] at this
  exact this.symm

end Formalism.HermitianLattices.Ext.L3.HU
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_isom_congr (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {x y : V} (hxL : x ∈ (locF 𝔭 A₀))
    (hyL : y ∈ (locF 𝔭 A₀)) (hx : h x x = algebraMap F K (n : F)) (hy : h y y = algebraMap F K (n : F))
    {j : ℕ} (hj : 4 * vF 𝔭 n + eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ j)
    (hxy : y - x ∈ ((extP K 𝔭) ^ j • (locF 𝔭 A₀) : Submodule (𝓞 K) V)) :
    ∃ g ∈ autSub h (locF 𝔭 A₀),
      (∀ z ∈ (locF 𝔭 A₀), g z - z ∈ ((extP K 𝔭) ^ (j - 2 * vF 𝔭 n) • (locF 𝔭 A₀) : Submodule (𝓞 K) V)) ∧
      g x = y := by
  classical
  have hp : 𝔭.IsPrime := h𝔭.isPrime
  have han : ∀ z, h z z = 0 → z = 0 := by
    intro z hz
    by_contra hz0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have hpos := hd z hz0 φ
    rw [hz, map_zero, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  set v := vF 𝔭 n with hvdef
  have hv : n ∉ 𝔭 ^ (v + 1) := localValuationFiltration.notMem_pow_vF h𝔭 hn
  have hx0 : WCA.InL 𝔭 A₀ 0 x := (WCA.inL_zero_iff hp).2 hxL
  have hJ : 1 ≤ j - 2 * v := by omega
  have hw : WCA.InL 𝔭 A₀ (v + (v + (j - 2 * v))) (y - x) := by
    have e : v + (v + (j - 2 * v)) = j := by omega
    rw [e]
    exact WCA.InL.of_mem h𝔭 hxy
  have hnMap : algebraMap F K (n : F) = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n) :=
    (IsScalarTower.algebraMap_apply (𝓞 F) F K n).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K n)
  obtain ⟨g, hgI, hgJ, hgS, hgxy⟩ :
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h,
        (∀ z, WCA.InL 𝔭 A₀ 0 z → WCA.InL 𝔭 A₀ (j - 2 * v) (g z - z)) ∧
        (∀ z, WCA.InL 𝔭 A₀ 0 z → WCA.InL 𝔭 A₀ 0 (g.symm z)) ∧ g x = y :=
    _root_.Formalism.HermitianLattices.Ext.L3.WCC.core
      (K := K) (F := F) (V := V) (A := A₀) (x := x) (y := y)
      (v := v) (J := j - 2 * v) hK hF hs han hA₀i h𝔭 hn hv hx0
      (hx.trans hnMap) (hy.trans hnMap) hJ hw
  have hL : ∀ z, z ∈ locF 𝔭 A₀ → g z ∈ locF 𝔭 A₀ := by
    intro z hz
    have hz0 : WCA.InL 𝔭 A₀ 0 z := (WCA.inL_zero_iff hp).2 hz
    have h1 : WCA.InL 𝔭 A₀ 0 (g z - z) := (hgJ z hz0).mono (Nat.zero_le _)
    have h2 := h1.add hp hz0
    rw [sub_add_cancel] at h2
    exact (WCA.inL_zero_iff hp).1 h2
  have hLs : ∀ z, z ∈ locF 𝔭 A₀ → g.symm z ∈ locF 𝔭 A₀ := fun z hz =>
    (WCA.inL_zero_iff hp).1 (hgS z ((WCA.inL_zero_iff hp).2 hz))
  refine ⟨g, ?_, fun z hz => (hgJ z ((WCA.inL_zero_iff hp).2 hz)).mem hp, hgxy⟩
  show g ∈ Formalism.ThetaLiftIndependence.autL h (locF 𝔭 A₀)
  refine ⟨hgI, le_antisymm ?_ ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hL z hz
  · intro z hz
    exact Submodule.mem_map.2 ⟨g.symm z, hLs z hz, by simp⟩

end Formalism.HermitianLattices.Ext.L3
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace RankOne

open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem trace_pos {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) :
    ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
  intro x hx
  have hsum := trace_eq_sum_embeddings ℂ (K := ℚ) (x := h x x)
  have hre : ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re := by
    have := congrArg Complex.re hsum
    simpa [Complex.re_sum] using this
  have hne : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re :=
    Finset.sum_pos (fun σ _ => hd x hx σ.toRingHom) Finset.univ_nonempty
  exact_mod_cast hre ▸ hpos

theorem exists_model [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) (h1 : finrank K V = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) :
    ∃ (h' : K →ₗ⋆[K] K →ₗ[K] K) (A : Submodule (𝓞 K) K), h' 1 1 ≠ 0 ∧ Submodule.IsFullLattice K A ∧
      (∃ s, IsClassReps h' A s) ∧ mass h' A = mass h L := by
  let b := Module.finBasisOfFinrankEq K V h1
  let φ : V ≃ₗ[K] K := b.equivFun.trans (LinearEquiv.funUnique (Fin 1) K K)
  let h' : K →ₗ⋆[K] K →ₗ[K] K := (h.comp φ.symm.toLinearMap).compl₂ φ.symm.toLinearMap
  have hh' : ∀ x y, h' (φ x) (φ y) = h x y := by
    intro x y
    simp [h']
  have htr := trace_pos hd
  obtain ⟨hex, -, -⟩ := Formalism.HermitianLatticesTheory.massBasic K V h hs htr L hL
  obtain ⟨hex', hm⟩ := mass_mapE φ hh' hex
  refine ⟨h', mapE φ L, ?_, isFullLattice_mapE φ hL, hex', hm⟩
  have h0 : φ.symm 1 ≠ 0 := by simp
  intro hz
  have := htr _ h0
  have hz' : h (φ.symm 1) (φ.symm 1) = 0 := by simpa [h'] using hz
  rw [hz', map_zero] at this
  exact lt_irrefl _ this

end RankOne

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_massConst_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    ∃ c : ℝ, 0 < c ∧ MassConst K F 1 c := by
  obtain ⟨h₀, hh⟩ : ∃ h₀ : K →ₗ⋆[K] K →ₗ[K] K, ∀ x y, h₀ x y = star x * y :=
    ⟨LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star x * y)
      (fun x y z => by simp [add_mul]) (fun a x y => by simp [smul_eq_mul, mul_assoc, starRingEnd_apply])
      (fun x y z => by simp [mul_add]) (fun a x y => by simp [smul_eq_mul, mul_left_comm]),
      fun _ _ => rfl⟩
  have hs₀ : h₀.IsSymm := by
    first
      | (intro x y; simp [hh, starRingEnd_apply, mul_comm])
      | (constructor; intro x y; simp [hh, starRingEnd_apply, mul_comm])
  have hd₀ : IsTotPosDef h₀ := by
    intro x hx φ
    have hx' : φ x ≠ 0 := (map_ne_zero φ).mpr hx
    have : φ (h₀ x x) = ((Complex.normSq (φ x) : ℝ) : ℂ) := by
      rw [hh, map_mul, hK.2.1 φ x, Complex.normSq_eq_conj_mul_self]
    rw [this, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hx'
  have hn₀ : h₀ 1 1 ≠ 0 := by simp [hh]
  set L₀ : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(1 : K)}
  have hL₀ : Submodule.IsFullLattice K L₀ :=
    { toIsLattice := Submodule.IsLattice.of_fg K (Submodule.fg_span_singleton _)
      span_eq_top := RankOne.span_eq_top_of_ne_zero (Submodule.subset_span rfl) one_ne_zero }
  obtain ⟨hex₀, -, hpos₀⟩ := Formalism.HermitianLatticesTheory.massBasic K K h₀ hs₀
    (RankOne.trace_pos hd₀) L₀ hL₀
  refine ⟨Formalism.HermitianLatticesTheory.mass h₀ L₀, hpos₀, ?_⟩
  intro V _ _ _ _ _ h L hs hd h1 hL hLi
  obtain ⟨h', A, hn', hA, -, hm⟩ := RankOne.exists_model hs hd h1 hL
  have hlam : lamG F h L = 1 := by
    unfold lamG
    exact (tprod_congr fun p => localFactor_rank_one hK hF hs hd hL hLi h1 p.2).trans tprod_one
  rw [hlam, mul_one, ← hm]
  exact RankOne.mass_eq_of_lattices hn₀ hn' hL₀ hA hex₀

end Formalism.HermitianLattices.Ext.L3
end
end
