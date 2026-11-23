module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle034
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle016
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityEleventh
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOfNormRepCountNeZero
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle011
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle019
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNotMemOfSol
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InLZeroIff

@[expose] public section

section

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem exists_arch {S : Subring K} {ϖ : K} (hS : IsLocUnif S ϖ) {α : Type*} [Fintype α] (f : α → K) :
    ∃ l : ℕ, ∀ a, ϖ ^ l * f a ∈ S := by
  classical
  choose l hl using fun a => hS.arch (f a)
  refine ⟨∑ a, l a, fun a => ?_⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), add_comm, pow_add, mul_assoc]
  exact S.mul_mem (pow_mem hS _) (hl a)

theorem exists_isE (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ e, IsE h (locF 𝔭 (spanO b)) 𝔭 e := by
  classical
  have : 𝔭.IsPrime := h𝔭.isPrime
  let f := algebraMap (𝓞 F) (𝓞 K)
  let g := algebraMap (𝓞 K) K
  let a := (gramK h b)⁻¹
  have hdet : IsUnit (gramK h b).det := isUnit_iff_ne_zero.2 (gramK_det_ne_zero hd b)
  -- Clear the denominators of all entries of the inverse Gram matrix at once.
  obtain ⟨n, hn, ha⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image (fun p : κ × κ => a p.1 p.2))
  have hentry (i j : κ) : ∃ z : 𝓞 K, g z = (n : K) * a i j := by
    have hi := ha (a i j) (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    exact ⟨⟨n • a i j, hi⟩, by simp [g, zsmul_eq_mul]⟩
  have hnspan : Ideal.span {(n : 𝓞 F)} ≠ 0 := by
    simpa using (Int.cast_ne_zero.mpr hn : (n : 𝓞 F) ≠ 0)
  have hpunit : ¬ IsUnit 𝔭 := fun hunit => h𝔭.ne_top (Ideal.isUnit_iff.mp hunit)
  -- Factor out the power of 𝔭 in the denominator ideal.
  obtain ⟨J, hJ, hJp⟩ :=
    (FiniteMultiplicity.of_not_isUnit hpunit hnspan).exists_eq_pow_mul_and_not_dvd
  rw [Ideal.dvd_iff_le] at hJp
  obtain ⟨u, huJ, hu⟩ := IsConcreteLE.not_le_iff_exists.mp hJp
  generalize multiplicity 𝔭 (Ideal.span {(n : 𝓞 F)}) = l at hJ
  refine ⟨l, fun x hx t ht => ?_⟩
  have htu : t * u ∈ Ideal.span {(n : 𝓞 F)} := by
    rw [hJ]
    exact Ideal.mul_mem_mul ht huJ
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp htu
  let v := gramK h b *ᵥ b.equivFun x
  have hv : ∀ j, v j ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro j
    have h1 := hx (b j) (le_locF 𝔭 _ (Submodule.subset_span ⟨j, rfl⟩))
    rw [form_repr h b] at h1
    have hb1 : b.equivFun (b j) = Pi.single j 1 := by
      funext j'
      rw [Basis.equivFun_self, Pi.single_apply]
      simp only [eq_comm]
    have hb2 : star (Pi.single j (1 : K) : κ → K) = Pi.single j 1 := by
      funext l
      by_cases hl : l = j
      · subst hl; simp
      · simp [hl]
    rwa [hb1, hb2, single_one_dotProduct] at h1
  have hx' : b.equivFun x = a *ᵥ v := by
    change b.equivFun x = (gramK h b)⁻¹ *ᵥ (gramK h b *ᵥ b.equivFun x)
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, one_mulVec]
  change f t • x ∈ locF 𝔭 (spanO b)
  rw [← b.sum_equivFun x, hx', Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨s, hs, hsj⟩ := (mem_locF 𝔭 _ _).mp (hv j)
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp hsj
  obtain ⟨z, hz⟩ := hentry i j
  refine (mem_locF 𝔭 _ _).mpr ⟨u * s, fun hm => (h𝔭.isPrime.mem_or_mem hm).elim hu hs, ?_⟩
  have hprod : g (f (u * s)) * g (f t) * (a i j * v j) = g (f w * z * y) := by
    have hw' : g (f w) * (n : K) = g (f t) * g (f u) := by
      simpa [map_mul, f, g] using congrArg (fun r => g (f r)) hw
    have hy' : g y = g (f s) * v j := hy
    calc
      _ = (g (f t) * g (f u)) * (a i j * (g (f s) * v j)) := by
        simp only [map_mul]
        ring
      _ = _ := by
        rw [map_mul, map_mul, hz, hy', ← hw']
        ring
  change f (u * s) • f t • (a i j * v j) • b i ∈ spanO b
  rw [← algebraMap_smul K (f (u * s)), ← algebraMap_smul K (f t), smul_smul, smul_smul]
  change (g (f (u * s)) * g (f t) * (a i j * v j)) • b i ∈ spanO b
  rw [hprod, show g (f w * z * y) • b i = (f w * z * y) • b i from algebraMap_smul K _ _]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem isE_eA (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    IsE h (locF 𝔭 (spanO b)) 𝔭 (eA h (locF 𝔭 (spanO b)) 𝔭) :=
  Nat.sInf_mem (s := {e | IsE h (locF 𝔭 (spanO b)) 𝔭 e}) (exists_isE hK hF hd b h𝔭)

end Formalism.HermitianLattices.Ext.L3.HU
end
end

section

open NumberField Module Matrix Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd

open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans traceDeterminantCongruences reductionMapsOfForms localValuationFiltration hermitianFormColumns vectorCountBounds

theorem limUnder_of_step {u : ℕ → ℕ} {q e k₀ : ℕ} (hq : 0 < q)
    (h : ∀ k, k₀ ≤ k → u (k + 1) = q ^ e * u k) {k : ℕ} (hk : k₀ ≤ k) :
    limUnder atTop (fun k : ℕ => (u k : ℝ) / (q : ℝ) ^ (k * e)) = (u k : ℝ) / (q : ℝ) ^ (k * e) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hstep : ∀ j, k₀ ≤ j → (u (j + 1) : ℝ) / (q : ℝ) ^ ((j + 1) * e) =
      (u j : ℝ) / (q : ℝ) ^ (j * e) := by
    intro j hj
    rw [h j hj, Nat.cast_mul, Nat.cast_pow, div_eq_div_iff (pow_ne_zero _ hq') (pow_ne_zero _ hq'),
      add_mul, one_mul, pow_add]
    ring
  have hconst : ∀ j, k₀ ≤ j → (u j : ℝ) / (q : ℝ) ^ (j * e) = (u k₀ : ℝ) / (q : ℝ) ^ (k₀ * e) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih => rw [hstep j hj, ih]
  have ht : Tendsto (fun k : ℕ => (u k : ℝ) / (q : ℝ) ^ (k * e)) atTop
      (𝓝 ((u k : ℝ) / (q : ℝ) ^ (k * e))) := by
    rw [hconst k hk]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k₀] with j hj
    exact (hconst j hj).symm
  exact ht.limUnder_eq

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem nkCount_succ_fine (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} {v : ℕ} (hn : n ∉ 𝔭 ^ (v + 1)) {k : ℕ}
    (hk : vd h L 𝔭 + v + 1 ≤ k) :
    nkCount h L 𝔭 (k + 1) n = Ideal.absNorm 𝔭 ^ (2 * finrank K V - 1) * nkCount h L 𝔭 k n := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [nkCount_eq h h𝔭 b hb hH, nkCount_eq h h𝔭 b hb hH]
  change nkM 𝔭 (k + 1) H n = _ * nkM 𝔭 k H n
  rw [hv] at hk
  have key := nkM_succ hK h𝔭 hHh hD (notMem_pow_vF h𝔭 hD0) hn hk
  rw [Fintype.card_fin] at key
  have hN := absNorm_pos h𝔭
  rcases Nat.eq_zero_or_pos (finrank K V) with h0 | hpos
  · have e0 : 2 * finrank K V = 0 := by omega
    have e1 : 2 * finrank K V - 1 = 0 := by omega
    rw [e0, pow_zero, one_mul] at key
    rw [e1, pow_zero, one_mul]
    have h2 := two_le_absNorm h𝔭
    have hB : nkM 𝔭 k H n ≤ 1 :=
      (card_sub_le hK h𝔭 k _).trans (by rw [Fintype.card_fin, e0, mul_zero, pow_zero])
    have hAN : 2 * nkM 𝔭 (k + 1) H n ≤ nkM 𝔭 (k + 1) H n * Ideal.absNorm 𝔭 := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ h2
    have hA0 : nkM 𝔭 (k + 1) H n = 0 := by
      rw [key] at hAN
      omega
    rw [hA0, zero_mul] at key
    omega
  · have e : 2 * finrank K V = (2 * finrank K V - 1) + 1 := by omega
    rw [e, pow_succ] at key
    apply Nat.eq_of_mul_eq_mul_right hN
    rw [key]
    ring

theorem alphaN_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} {v : ℕ} (hn : n ∉ 𝔭 ^ (v + 1)) {k : ℕ}
    (hk : vd h L 𝔭 + v + 1 ≤ k) :
    alphaN h L 𝔭 n =
      (nkCount h L 𝔭 k n : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) := by
  unfold alphaN
  exact limUnder_of_step (absNorm_pos h𝔭)
    (fun j hj => nkCount_succ_fine hK hF hs hd hL hLi h𝔭 hn hj) hk

theorem nkCount_congr (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n n' : 𝓞 F} {k : ℕ} (hc : n - n' ∈ 𝔭 ^ k) :
    nkCount h L 𝔭 k n = nkCount h L 𝔭 k n' := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [nkCount_eq h h𝔭 b hb hH, nkCount_eq h h𝔭 b hb hH]
  have e : Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι n) = Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι n') := by
    rw [Ideal.Quotient.eq, ← map_sub]
    exact (mem_pow_iff 𝔭 k _).mpr hc
  rw [e]

theorem akCount_succ_fine (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 2 * vd h L 𝔭 + 1 ≤ k) :
    akCount h L 𝔭 (k + 1) = Ideal.absNorm 𝔭 ^ (finrank K V ^ 2) * akCount h L 𝔭 k := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [akCount_eq h h𝔭 b hb hH, akCount_eq h h𝔭 b hb hH]
  rw [hv] at hk
  have key := akM_succ hK h𝔭 hHh hD (notMem_pow_vF h𝔭 hD0) hk
  rw [Fintype.card_fin, ← sq] at key
  exact key

theorem alphaL_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 2 * vd h L 𝔭 + 1 ≤ k) :
    alphaL h L 𝔭 = (akCount h L 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) := by
  unfold alphaL
  exact limUnder_of_step (absNorm_pos h𝔭)
    (fun j hj => akCount_succ_fine hK hF hs hd hL hLi h𝔭 (le_trans hk hj)) le_rfl

theorem akCount_pos (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : 0 < akCount h L 𝔭 k := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [akCount_eq h h𝔭 b hb hH]
  haveI := finite_quot (K := K) h𝔭 k
  haveI : Nonempty {X : Matrix (Fin (finrank K V)) (Fin (finrank K V)) (𝓞 K ⧸ extP K 𝔭 ^ k) //
      Xᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X = H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))} :=
    ⟨⟨1, by rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]⟩⟩
  exact Nat.card_pos

theorem nkCount_le_nat (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (n : 𝓞 F) :
    nkCount h L 𝔭 k n ≤ 2 * Ideal.absNorm 𝔭 ^ (2 * vd h L 𝔭 + 1) *
      Ideal.absNorm 𝔭 ^ (k * (2 * finrank K V - 1)) := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [nkCount_eq h h𝔭 b hb hH, hv]
  have key := nkM_le hK h𝔭 hHh hD (notMem_pow_vF h𝔭 hD0) (by rw [Fintype.card_fin]; exact hm) k n
  rw [Fintype.card_fin] at key
  exact key

end Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Cell

open LocalSpans idealPowerSpanBounds localizedQuotients WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

variable {𝔭 : Ideal (𝓞 F)}

theorem symm0 {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {x y : V} (hxy : h x y = 0) : h y x = 0 := by
  have e : starRingEnd K (h x y) = h y x := by
    first
    | exact hs.eq x y
    | exact hs x y
  rw [hxy, map_zero] at e
  exact e.symm

theorem form_smul_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (μ ν : K) (x y : V) :
    h (μ • x) (ν • y) = star μ * ν * h x y := by
  simp only [LinearMap.map_smulₛₗ₂, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply]
  ring

theorem exists_normalise (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (han : ∀ x, h x x = 0 → x = 0) {e : V} (he : e ≠ 0) :
    ∃ μ : K, ∃ a : 𝓞 F, h (μ • e) (μ • e) = κ (ι a) ∧ a ∉ 𝔭 ^ 2 := by
  have hd0 : h e e ≠ 0 := fun h0 => he (han e h0)
  have hds : star (h e e) = h e e := by
    have e' : starRingEnd K (h e e) = h e e := by
      first
      | exact hs.eq e e
      | exact hs e e
    rwa [starRingEnd_apply] at e'
  obtain ⟨μ, -, hμs, a, ha, ha2⟩ := exists_scale_fixed hF h𝔭 hd0 hds
  exact ⟨μ, a, by rw [form_smul_smul, hμs, ha], ha2⟩

theorem exists_pair (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {z e : V} {c a : 𝓞 F} (hze : h z e = 0)
    (hz : h z z = κ (ι c)) (he : h e e = κ (ι a)) (hc2 : c ∉ 𝔭 ^ 2) (ha2 : a ∉ 𝔭 ^ 2) (hcp : c ∈ 𝔭)
    (hap : a ∈ 𝔭) :
    ∃ u w : V, ∃ b₁ b₂ : 𝓞 F, h u u = κ (ι b₁) ∧ h w w = κ (ι b₂) ∧ b₁ ∉ 𝔭 ∧ b₂ ∉ 𝔭 ^ 2 ∧
      h w u = 0 ∧ ∀ v, h z v = 0 → h e v = 0 → h u v = 0 ∧ h w v = 0 := by
  have hez := symm0 hs hze
  obtain ⟨α, ν, hν, hW2, hW3⟩ := exists_alpha hK hF h𝔭 hcp hc2 hap ha2
  have hν' : star (κ α) * κ α = κ (ι ν) := by rw [← hν, map_mul]; rfl
  set W := c * ν + a with hW
  have hW0 : W ≠ 0 := fun h0 => hW3 (h0 ▸ zero_mem _)
  have hc0 : c ≠ 0 := fun h0 => hc2 (h0 ▸ zero_mem _)
  have ha0 : a ≠ 0 := fun h0 => ha2 (h0 ▸ zero_mem _)
  obtain ⟨μ₁, -, hμ₁s, b₁, hb₁, hb₁'⟩ := exists_scale (K := K) (r := 1) (k := 0) hF h𝔭
    (by simpa using hW2) (by simpa using hW3)
  obtain ⟨μ₂, -, hμ₂s, b₂, hb₂, hb₂'⟩ := exists_scale_int (K := K) hF h𝔭
    (mul_ne_zero (mul_ne_zero hc0 ha0) hW0)
  have hsι : ∀ t : 𝓞 F, star (κ (ι t)) = κ (ι t) := star_ι hF
  refine ⟨μ₁ • (κ α • z + e), μ₂ • ((-κ (ι a)) • z + (star (κ α) * κ (ι c)) • e), b₁, b₂,
    ?_, ?_, by simpa using hb₁', hb₂', ?_, fun v hzv hev => ⟨?_, ?_⟩⟩
  · rw [form_smul_smul, hμ₁s, ← hb₁]
    congr 1
    simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, hW, map_mul]
    linear_combination κ (ι c) * hν'
  · rw [form_smul_smul, hμ₂s, ← hb₂]
    congr 1
    simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, hW, map_mul, star_neg, star_star, hsι]
    linear_combination (κ (ι c) * κ (ι c) * κ (ι a)) * hν'
  · rw [form_smul_smul]
    simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, star_neg, star_mul', star_star, hsι]
    ring
  · simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, hzv, hev, mul_zero, add_zero]
  · simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, hzv, hev, mul_zero, add_zero]

theorem κι_inj {a b : 𝓞 F} (hab : κ (ι a) = κ (ι b)) : a = b := by
  have e : ∀ c : 𝓞 F, κ (ι c) = algebraMap F K (c : F) := fun c => rfl
  rw [e, e] at hab
  exact RingOfIntegers.ext ((algebraMap F K).injective hab)

variable [FiniteDimensional K V]

theorem exists_family (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (han : ∀ x, h x x = 0 → x = 0) {x₀ : V} {n : 𝓞 F}
    (hx : h x₀ x₀ = κ (ι n)) (hn : n ∉ 𝔭) :
    ∀ r : ℕ, r + 1 ≤ finrank K V → ∃ (y : Fin r → V) (a : Fin r → 𝓞 F) (z : V) (c : 𝓞 F),
      (∀ i j, i ≠ j → h (y i) (y j) = 0) ∧ (∀ i, h z (y i) = 0) ∧
      (∀ i, h (y i) (y i) = κ (ι (a i))) ∧ h z z = κ (ι c) ∧ (∏ i, a i) ∉ 𝔭 ∧ c ∉ 𝔭 ^ 2 ∧
      (z = x₀ ∨ ∃ i, y i = x₀) := by
  have hp := h𝔭.isPrime
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨fun i => i.elim0, fun i => i.elim0, x₀, n, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, hx, ?_, fun hm => hn (Ideal.pow_le_self two_ne_zero hm), Or.inl rfl⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    exact fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  | succ r ih =>
    intro hr
    obtain ⟨y, a, z, c, ho, hzy, hny, hnz, hprod, hc2, hx₀⟩ := ih (by omega)
    obtain ⟨e₀, he₀, hoe⟩ := GramDeterminantPositive.exists_ortho_ne_zero h (Fin.cons z y : Fin (r + 1) → V)
      (by omega)
    obtain ⟨μ, ae, hne, hae2⟩ := exists_normalise hF h𝔭 hs han he₀
    have hze : h z (μ • e₀) = 0 := by
      have := hoe 0
      rw [Fin.cons_zero] at this
      rw [map_smul, this, smul_zero]
    have hye : ∀ i, h (y i) (μ • e₀) = 0 := fun i => by
      have := hoe i.succ
      rw [Fin.cons_succ] at this
      rw [map_smul, this, smul_zero]
    set e := μ • e₀ with he
    have key : ∃ u w : V, ∃ b₁ b₂ : 𝓞 F, h u u = κ (ι b₁) ∧ h w w = κ (ι b₂) ∧ b₁ ∉ 𝔭 ∧
        b₂ ∉ 𝔭 ^ 2 ∧ h w u = 0 ∧ (∀ i, h u (y i) = 0 ∧ h w (y i) = 0) ∧
        (u = x₀ ∨ ∃ i, y i = x₀) := by
      by_cases hcp : c ∈ 𝔭
      · have hx₀' : ∃ i, y i = x₀ := by
          rcases hx₀ with rfl | h1
          · exact absurd hcp (by rw [κι_inj (hnz.symm.trans hx)]; exact hn)
          · exact h1
        by_cases hap : ae ∈ 𝔭
        · obtain ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5, h6⟩ :=
            exists_pair hK hF h𝔭 hs hze hnz hne hc2 hae2 hcp hap
          exact ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5,
            fun i => h6 _ (hzy i) (symm0 hs (hye i)), Or.inr hx₀'⟩
        · exact ⟨e, z, ae, c, hne, hnz, hap, hc2, hze,
            fun i => ⟨symm0 hs (hye i), hzy i⟩, Or.inr hx₀'⟩
      · exact ⟨z, e, c, ae, hnz, hne, hcp, hae2, symm0 hs hze,
          fun i => ⟨hzy i, symm0 hs (hye i)⟩, hx₀⟩
    obtain ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5, h6, h7⟩ := key
    refine ⟨Fin.cons u y, Fin.cons b₁ a, w, b₂, ?_, ?_, ?_, h2, ?_, h4, Or.inr ?_⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact (h6 j).1
      · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact symm0 hs (h6 i).1
      · intro hij
        rw [Fin.cons_succ, Fin.cons_succ]
        exact ho i j fun hh => hij (by rw [hh])
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Fin.cons_zero]; exact h5
      · rw [Fin.cons_succ]; exact (h6 i).2
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Fin.cons_zero, Fin.cons_zero]; exact h1
      · rw [Fin.cons_succ, Fin.cons_succ]; exact hny i
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact fun hm => (hp.mem_or_mem hm).elim h3 hprod
    · rcases h7 with rfl | ⟨i, hi⟩
      · exact ⟨0, by rw [Fin.cons_zero]⟩
      · exact ⟨i.succ, by rw [Fin.cons_succ]; exact hi⟩

end Formalism.HermitianLattices.Ext.L3.Cell
end
end
