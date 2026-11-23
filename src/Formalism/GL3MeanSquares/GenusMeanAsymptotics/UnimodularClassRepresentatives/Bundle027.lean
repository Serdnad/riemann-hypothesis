module

import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnitaryDensityFieldBis
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle019
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle011
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle005
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle013
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle004
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapConjO
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormDiscrIdealOfLe
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle016
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulDvdUnif
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InLZeroIff
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.StarAlgebraMap
import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal
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

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem absNorm_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) :
    Ideal.absNorm (extP K 𝔭) = Ideal.absNorm 𝔭 ^ 2 := by
  induction 𝔭 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp [extP]
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.mp hx]
    simp only [extP]
    simp only [Ideal.map_top, Ideal.absNorm_top, one_pow]
  | h₃ a p ha hp ih =>
    have hpm : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hq := idealPowerSpanBounds.absNorm_extP_eq_sq hK hF hpm
    simp only [extP] at ih hq ⊢
    rw [Ideal.map_mul, map_mul, map_mul, ih, hq, mul_pow]

theorem map_comap_eq_of_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P := by
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  rw [conjIdeal_eq_comap] at hc
  exact SplitPrimeIdeals.map_comap_of_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP hc hθ

theorem extP_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  apply Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.extP_split <;> assumption

theorem alphaStd_one (𝔭 : Ideal (𝓞 F)) :
    alphaStd K 𝔭 1 = 1 - etaF K F 𝔭 * (Ideal.absNorm 𝔭 : ℝ)⁻¹ := by
  simp [alphaStd]

theorem normRepCount_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {j : ℕ} (hj : 1 ≤ j) :
    (normRepCount K (extP K 𝔭 ^ j) 1 1 : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ j * alphaStd K 𝔭 1 := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have h1 : (1 : 𝓞 K) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hd := localDensity K hK P hP 1 j le_rfl hj 1 (map_one _) h1
  rw [alphaStd_one, etaF_comap hK hF hP]
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · rw [map_comap_eq_of_inert hK hF hP hc, hd.1 hc, if_pos hc, ← absNorm_comap_inert hK hF hP hc]
    push_cast
    rw [Real.sqrt_sq (Nat.cast_nonneg _)]
    simp
  · rw [extP_split hK hF hP hc, hd.2 hc, if_neg hc, absNorm_comap_split hK hF hP hc]
    simp

end Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallB

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] in
theorem exists_det_span (b : Basis (Fin (finrank K V)) K V) {x : Fin (finrank K V) → V}
    (hx : ∀ i, x i ∈ Submodule.span (𝓞 K) (Set.range b)) :
    ∃ d : 𝓞 K, algebraMap (𝓞 K) K d = b.det x := by
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 (hx j)
  have hrepr : ∀ j i, b.repr (x j) i = algebraMap (𝓞 K) K (c j i) := by
    intro j i
    rw [← hc j]

    simp [← algebraMap_smul K, map_sum, Finsupp.single_apply]
  refine ⟨(Matrix.of fun i j => c j i).det, ?_⟩
  rw [RingHom.map_det, Basis.det_apply]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply, hrepr]

theorem discrIdeal_span {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis (Fin (finrank K V)) K V) {g₀ : 𝓞 K}
    (hg : algebraMap (𝓞 K) K g₀ = gdet h b) :
    discrIdeal h (Submodule.span (𝓞 K) (Set.range b)) = Ideal.span {g₀} := by
  apply le_antisymm
  · refine discrIdeal_le b ?_
    intro x hx z hz
    obtain ⟨d, hd⟩ := exists_det_span b hx
    have hz' : z = conjO K d * g₀ * d := by
      apply IsFractionRing.injective (𝓞 K) K
      have e1 : algebraMap (𝓞 K) K (conjO K d) = star (algebraMap (𝓞 K) K d) := by
        first | rfl | simp [conjO]
      rw [hz, map_mul, map_mul, e1, hd, hg]
    rw [hz', Ideal.mem_span_singleton]
    exact ⟨conjO K d * d, by ring⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    refine mem_discrIdeal b (fun i => Submodule.subset_span (Set.mem_range_self i)) ?_
    rw [Basis.det_self, hg]
    simp

omit [StarRing K] in
theorem absNorm_span_singleton_eq [_root_.NumberField.IsTotallyComplex K] (g₀ : 𝓞 K) :
    (Ideal.absNorm (Ideal.span {g₀}) : ℝ) =
      (∏ w : InfinitePlace K, w (algebraMap (𝓞 K) K g₀)) ^ 2 := by
  have hm : ∀ w : InfinitePlace K, w.mult = 2 := by
    intro w
    have hw : ¬ w.IsReal := by
      rw [InfinitePlace.not_isReal_iff_isComplex]
      exact IsTotallyComplex.isComplex w
    simp [InfinitePlace.mult, hw]
  have hp := InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 K) K g₀)
  simp only [hm] at hp
  rw [Ideal.absNorm_span_singleton, ← Finset.prod_pow, hp, Nat.cast_natAbs]
  have h3 := Algebra.coe_norm_int g₀
  rw [← h3]
  norm_cast

theorem normD_mul_relIndex (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (b : Basis (Fin (finrank K V)) K V)
    (hb : ∀ i, b i ∈ L)
    (hidx : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
    normD h L * ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) =
      ∏ w : InfinitePlace K, w (gdet h b) := by
  haveI : IsTotallyComplex K := hK.1
  have hint : ∀ i j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = h (b i) (b j) := fun i j =>
    Submodule.mem_one.1 (hLi _ (hb i) _ (hb j))
  choose c hc using hint
  have hg : algebraMap (𝓞 K) K (Matrix.of fun i j => c i j).det = gdet h b := by
    rw [RingHom.map_det]
    unfold gdet
    congr 1
    ext i j
    simp [hc]
  have hle : Submodule.span (𝓞 K) (Set.range b) ≤ L :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i)
  obtain ⟨n, hn⟩ : ∃ n, (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup = n :=
    ⟨_, rfl⟩
  rw [hn] at hidx ⊢
  have hN := absNorm_discrIdeal_of_le hK hLi b n (Submodule.span (𝓞 K) (Set.range b)) hle hn hidx
  rw [discrIdeal_span b hg] at hN
  have hS := absNorm_span_singleton_eq (Matrix.of fun i j => c i j).det
  rw [hg] at hS
  have hprod : (0 : ℝ) ≤ ∏ w : InfinitePlace K, w (gdet h b) :=
    Finset.prod_nonneg (fun w _ => w.1.nonneg _)
  have key : ((n : ℝ) * Real.sqrt (Ideal.absNorm (discrIdeal h L) : ℝ)) ^ 2 =
      (∏ w : InfinitePlace K, w (gdet h b)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← hS, hN]
    push_cast
    ring
  unfold normD
  rw [← Real.sqrt_sq hprod, ← key, Real.sqrt_sq (by positivity)]
  ring

end Formalism.HermitianLattices.Ext.L3.BallB
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem ι_pow_smul (π : 𝓞 F) (r : ℕ) (w : V) :
    ι (π ^ r) • w = algebraMap F K (π : F) ^ r • w := by
  rw [← algebraMap_smul K (ι (π ^ r)) w]
  congr 1
  rw [map_pow, map_pow]
  rfl

theorem exists_pow_smul_mem {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsFullLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭) (w : V) :
    ∃ n : ℕ, algebraMap F K (π : F) ^ n • w ∈ locF 𝔭 A₀ := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hnw⟩ := Formalism.HermitianLatticesTheory.traceReal_mult A₀ hA₀ w
  have hc : ((n : ℤ) : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := exists_mul_dvd h𝔭 hc
  obtain ⟨v, hv⟩ := hdvd (π ^ r) (Ideal.pow_mem_pow hπ r)
  refine ⟨r, (LocalSpans.mem_locF 𝔭 _ _).2 ⟨u, hu, ?_⟩⟩
  have : ι u • (algebraMap F K (π : F) ^ r • w) = ι v • (n • w) := by
    rw [← LocF.algebraMap_intCast_smul (K := K) (F := F) n w, smul_smul, ← map_mul, mul_comm v, ← hv, map_mul,
      mul_smul, ι_pow_smul]
  rw [this]
  exact A₀.smul_mem _ hnw

theorem exists_smul_le {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    (hB₀ : Submodule.IsFullLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ r : ℕ, extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀ := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hA₀ hB₀
  have hc : ((n : ℤ) : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := exists_mul_dvd h𝔭 hc
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  obtain ⟨v, hv⟩ := hdvd (π ^ r) (Ideal.pow_mem_pow hπ r)
  refine ⟨r, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hx
  obtain ⟨t, ht, hty⟩ := (LocalSpans.mem_locF 𝔭 A₀ y).1 hy
  refine (LocalSpans.mem_locF 𝔭 _ _).2 ⟨u * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hu ht, ?_⟩
  have : ι (u * t) • (algebraMap F K (π : F) ^ r • y) = ι v • (n • (ι t • y)) := by
    rw [← LocF.algebraMap_intCast_smul (K := K) (F := F) n, ← ι_pow_smul, smul_smul, smul_smul, smul_smul,
      ← map_mul, ← map_mul, ← map_mul]
    congr 2
    linear_combination t * hv
  rw [this]
  exact B₀.smul_mem _ (hnx _ hty)

theorem eq_zero_of_forall_mem {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {v : V} (hv : ∀ j : ℕ, v ∈ extP K 𝔭 ^ j • locF 𝔭 A₀) :
    v = 0 := by
  have := h𝔭.isPrime
  have h0 : v ∈ locF 𝔭 A₀ := by simpa [pow_zero_smul] using hv 0
  obtain ⟨t, ht, htv⟩ := (LocalSpans.mem_locF 𝔭 A₀ v).1 h0
  have h1 : ∀ j : ℕ, ι t • v ∈ extP K 𝔭 ^ j • A₀ := fun j =>
    localizedQuotients.mem_smul_of_mem_smul_locF h𝔭 A₀ j htv (Submodule.smul_mem _ _ (hv j))
  have : Module.Finite (𝓞 K) ↥A₀ := Module.Finite.iff_fg.2 hA₀.fg
  have h2 : (⟨ι t • v, htv⟩ : ↥A₀) ∈ (⨅ i : ℕ, extP K 𝔭 ^ i • ⊤ : Submodule (𝓞 K) ↥A₀) := by
    rw [Submodule.mem_iInf]
    intro j
    rw [Submodule.mem_smul_top_iff]
    exact h1 j
  obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff (extP K 𝔭) _).1 h2
  have hr' : (r : 𝓞 K) • (ι t • v) = ι t • v := congrArg Subtype.val hr
  have hr1 : (r : 𝓞 K) ≠ 1 := by
    intro e
    have h3 : (1 : 𝓞 K) ∈ extP K 𝔭 ^ 1 := by rw [pow_one, ← e]; exact r.2
    have h4 : (1 : 𝓞 F) ∈ 𝔭 ^ 1 := (idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 1 1).1 (by simpa using h3)
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h4))
  have h5 : (algebraMap (𝓞 K) K ((r : 𝓞 K) - 1) * algebraMap F K (t : F)) • v = 0 := by
    rw [mul_smul, ← MeanB.algebraMap_comp, algebraMap_smul, algebraMap_smul, sub_smul, hr', one_smul,
      sub_self]
  rcases smul_eq_zero.1 h5 with h6 | h6
  · rcases mul_eq_zero.1 h6 with h7 | h7
    · exact absurd (sub_eq_zero.1 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).1 h7)) hr1
    · exact absurd h7 (notMem_ne_zero ht)
  · exact h6

theorem unif_pow_mem_pK_zero {𝔭 : Ideal (𝓞 F)} {π : 𝓞 F} (hπ : π ∈ 𝔭) (k : ℕ) :
    algebraMap F K (π : F) ^ k ∈ pK K 𝔭 0 := by
  refine ⟨1, Submonoid.one_mem _, ?_⟩
  rw [one_smul]
  refine ⟨ι (π ^ k), by simp, ?_⟩
  show algebraMap (𝓞 K) K (ι (π ^ k)) = _
  rw [map_pow, map_pow]
  rfl

theorem mem_of_add_mem {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsFullLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {D : V →ₗ[K] V}
    (hD : D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀)) (j : ℕ) {w : V}
    (hw : w + D w ∈ extP K 𝔭 ^ j • locF 𝔭 A₀) : w ∈ extP K 𝔭 ^ j • locF 𝔭 A₀ := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have hπ0 := unif_ne_zero (K := K) hπ'
  set p : K := algebraMap F K (π : F) with hp
  have key : ∀ w : V, w + D w ∈ locF 𝔭 A₀ → w ∈ locF 𝔭 A₀ := by
    intro w hw
    obtain ⟨n, hn⟩ := exists_pow_smul_mem hA₀ h𝔭 hπ w
    induction n with
    | zero => simpa using hn
    | succ n ih =>
      apply ih
      have h1 : D (p ^ (n + 1) • w) ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀ := by
        rw [pow_one]; exact hD _ hn
      have h2 : p ^ (n + 1) • (w + D w) ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀ :=
        (mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨p ^ n • (w + D w),
          smul_mem_locF h𝔭 A₀ (unif_pow_mem_pK_zero hπ n) hw, by rw [smul_smul, pow_one, pow_succ']⟩
      have h3 : p ^ (n + 1) • w ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀ := by
        have := sub_mem h2 h1
        rwa [map_smul, smul_add, add_sub_cancel_right] at this
      obtain ⟨y, hy, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 h3
      have : p ^ n • w = y := by
        apply smul_right_injective V hπ0
        show p • p ^ n • w = p • y
        rw [smul_smul, ← pow_succ', e, pow_one]
      rwa [this]
  obtain ⟨y, hy, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hw
  refine (mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨(p ^ j)⁻¹ • w, key _ ?_, ?_⟩
  · rw [map_smul, ← smul_add, e, smul_smul, inv_mul_cancel₀ (pow_ne_zero j hπ0), one_smul]
    exact hy
  · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero j hπ0), one_smul]

theorem exists_equiv_of_mem_endL {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsFullLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {D : V →ₗ[K] V}
    (hD : D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀)) :
    ∃ X : V ≃ₗ[K] V, (∀ x, X x = x + D x) ∧ X ∈ glSub (locF 𝔭 A₀) := by
  have hinj : Function.Injective (LinearMap.id + D : V →ₗ[K] V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw' : w + D w = 0 := hw
    exact eq_zero_of_forall_mem hA₀.toIsLattice h𝔭 fun j =>
      mem_of_add_mem hA₀ h𝔭 hD j (by rw [hw']; exact zero_mem _)
  refine ⟨LinearEquiv.ofInjectiveEndo _ hinj, fun x => ?_, ?_⟩
  · rw [LinearEquiv.coe_ofInjectiveEndo]; rfl
  · have hX : ∀ x, LinearEquiv.ofInjectiveEndo _ hinj x = x + D x := fun x => by
      rw [LinearEquiv.coe_ofInjectiveEndo]; rfl
    rw [mem_glSub]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      show LinearEquiv.ofInjectiveEndo _ hinj x ∈ _
      rw [hX]
      exact add_mem hx (Submodule.smul_le_right (hD x hx))
    · intro y hy
      refine ⟨(LinearEquiv.ofInjectiveEndo _ hinj).symm y, ?_, LinearEquiv.apply_symm_apply _ y⟩
      have h1 := hX ((LinearEquiv.ofInjectiveEndo _ hinj).symm y)
      rw [LinearEquiv.apply_symm_apply] at h1
      have := mem_of_add_mem hA₀ h𝔭 hD 0 (w := (LinearEquiv.ofInjectiveEndo _ hinj).symm y)
        (by rw [← h1, pow_zero_smul]; exact hy)
      rwa [pow_zero_smul] at this

theorem mem_glSub_of_sub_mem {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsFullLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {X : V ≃ₗ[K] V}
    (hX : ∀ x ∈ locF 𝔭 A₀, X x - x ∈ extP K 𝔭 • locF 𝔭 A₀) : X ∈ glSub (locF 𝔭 A₀) := by
  obtain ⟨Y, hY, hY'⟩ := exists_equiv_of_mem_endL hA₀ h𝔭
    (D := (X : V →ₗ[K] V) - LinearMap.id) (fun x hx => hX x hx)
  have : X = Y := by
    ext x
    rw [hY]
    simp
  rwa [this]

end Formalism.HermitianLattices.Ext.L3.D2
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Cell

open LocalSpans idealPowerSpanBounds localizedQuotients WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

theorem congrP_iff_inI {k : ℕ} {a b : K} : CongrP 𝔭 k a b ↔ InI 𝔭 k (a - b) := Iff.rfl

theorem inI_int (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {z : 𝓞 K} : InI 𝔭 k (κ z) ↔ z ∈ extP K 𝔭 ^ k := by
  simpa only [congrP_iff_inI, map_zero, sub_zero, Ideal.Quotient.eq_zero_iff_mem] using
    integralBasisSpans.congrP_int h𝔭 k z 0

theorem inI_ι (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {n : 𝓞 F} : InI 𝔭 k (κ (ι n)) ↔ n ∈ 𝔭 ^ k :=
  (inI_int (z := ι n) h𝔭).trans (mem_pow_iff (K := K) 𝔭 k n)

theorem InI.of_mul (hp : 𝔭.IsPrime) {k : ℕ} {t : 𝓞 F} (ht : t ∉ 𝔭) {a : K}
    (h : InI 𝔭 k (κ (ι t) * a)) : InI 𝔭 k a := by
  obtain ⟨u, hu, z, hz, e⟩ := h
  exact ⟨u * t, fun h => (hp.mem_or_mem h).elim hu ht, z, hz, by rw [e, map_mul, map_mul, mul_assoc]⟩

theorem InI.zero (hp : 𝔭.IsPrime) (k : ℕ) : InI (K := K) 𝔭 k 0 :=
  ⟨1, fun h => hp.ne_top ((Ideal.eq_top_iff_one 𝔭).2 h), 0, zero_mem _, by simp⟩

theorem exists_frac (hF : IsFixF K F) {D : K} (hD : star D = D) (h0 : InI 𝔭 0 D) :
    ∃ t δ : 𝓞 F, t ∉ 𝔭 ∧ κ (ι δ) = κ (ι t) * D := by
  obtain ⟨t, ht, z, -, e⟩ := h0
  obtain ⟨δ, hδ⟩ := (conjO_eq_iff_mem_range hF z).1 (by
    apply RingOfIntegers.coe_injective
    show star (κ z) = κ z
    rw [e, star_mul', hD, star_ι hF])
  exact ⟨t, δ, ht, by rw [hδ, e]⟩

theorem InI.divK (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {D : K} (hD : star D = D) (h0 : InI 𝔭 0 D)
    {v : ℕ} (hv : ¬ InI 𝔭 (v + 1) D) {k : ℕ} {a : K} (ha : InI 𝔭 (v + k) a) :
    InI 𝔭 k (D⁻¹ * a) := by
  obtain ⟨t, δ, ht, e⟩ := exists_frac hF hD h0
  have hδv : δ ∉ 𝔭 ^ (v + 1) := fun h =>
    hv (InI.of_mul h𝔭.isPrime ht (by rw [← e]; exact (inI_ι h𝔭).2 h))
  have hδ0 : δ ≠ 0 := fun h => hδv (h ▸ zero_mem _)
  have h1 := InI.div h𝔭 hδ0 hδv ha
  have h2 := InI.mul h𝔭.isPrime (InI.int h𝔭.isPrime (ι t)) h1
  rw [zero_add] at h2
  have ht0 := κι_ne_zero (K := K) (ne_zero_of_notMem ht)
  have hδ0' := κι_ne_zero (K := K) hδ0
  have hD0 : D ≠ 0 := by
    rintro rfl
    rw [mul_zero] at e
    exact hδ0' e
  have : D⁻¹ * a = κ (ι t) * ((κ (ι δ))⁻¹ * a) := by
    rw [e]
    field_simp
  rw [this]
  exact h2

end Formalism.HermitianLattices.Ext.L3.Cell
end
end
