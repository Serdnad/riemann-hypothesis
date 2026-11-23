module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle153
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle249
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle137
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle092
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle094
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle140
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle138
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle143
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankGeOfGenericFreeRowsFirst
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankLeRootExchange
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle141
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle067
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.qExpansionAllCoeffs_range_of_monic_root : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (N n : ℕ) (h : ℍ → ℂ) (s : Fin n → ℍ → ℂ), 0 < N → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → (∀ τ : ℍ, h ((N : ℝ) +ᵥ τ) = h τ) → (∀ j, QAll (· ∈ ε.range) N (s j)) → (∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0) → QAll (· ∈ ε.range) N h := by
  first | exact @GlobalTheory.FN.qAll_range_of_monic_root | exact GlobalTheory.FN.qAll_range_of_monic_root | (intros; apply GlobalTheory.FN.qAll_range_of_monic_root <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

theorem conjEx_hasQ_zero (N : ℕ) : HasQ N (fun _ => (0 : ℂ)) (fun _ => 0) := fun _ => by
  simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)

theorem conjEx_conv_coeff (a b : ℕ → ℂ) (n : ℕ) :
    conv a b n = PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b) := by
  simp [conv, PowerSeries.coeff_mul]

theorem conjEx_conv_map (g : ℂ ≃+* ℂ) (a b : ℕ → ℂ) :
    (fun n => g (conv a b n)) = conv (fun n => g (a n)) (fun n => g (b n)) := by
  funext n; simp [conv, map_sum, map_mul]

theorem conjEx_conv_cancel (a b d : ℕ → ℂ) (hd : d ≠ 0) (h : conv a d = conv b d) : a = b := by
  have hmk : PowerSeries.mk d ≠ 0 := by
    intro h0; apply hd; funext n
    have := congrArg (PowerSeries.coeff n) h0
    simpa using this
  have hm : PowerSeries.mk a * PowerSeries.mk d = PowerSeries.mk b * PowerSeries.mk d := by
    ext n
    have := congrFun h n
    rwa [conjEx_conv_coeff, conjEx_conv_coeff] at this
  have := mul_right_cancel₀ hmk hm
  funext n
  have := congrArg (PowerSeries.coeff n) this
  simpa using this

theorem conj_exists : ∀ (g : ℂ ≃+* ℂ) (N n : ℕ) (f D D' A A' : ℍ → ℂ) (s s' : Fin n → ℍ → ℂ), 0 < N → (∃ a, HasQ N f a) → QConj g N D D' → QConj g N A A' → (∀ j, QConj g N (s j) (s' j)) → D ≠ 0 → (∀ τ, f τ * D τ = A τ) → (∀ τ, f τ ^ n + ∑ j, s j τ * f τ ^ (j : ℕ) = 0) → ∃ f' : ℍ → ℂ, QConj g N f f' ∧ ∀ τ, f' τ * D' τ = A' τ := by
  intro g N n f D D' A A' s s' hN ⟨a, ha⟩ ⟨d, hd, hd'⟩ ⟨e, he, he'⟩ hs hD hfA hpol
  obtain ⟨uc, uf⟩ := GlobalTheory.QFam.hasQ_unique_both
  have hz := conjEx_hasQ_zero N
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hD (uf N D (fun _ => 0) _ hd hz)
  have hgd0 : (fun n => g (d n)) ≠ 0 := by
    intro h0; apply hd0; funext k
    have := congrFun h0 k
    simpa using this
  have hD' : D' ≠ 0 := by
    rintro rfl
    exact hgd0 (uc N (fun _ => 0) _ _ hN hd' hz)
  obtain ⟨_, hadd, _, hmul, hpow, hsumprod⟩ := GlobalTheory.QFam.qConj_ring g N hN
  have hA : QConj g N A A' := ⟨e, he, he'⟩
  have hDD : QConj g N D D' := ⟨d, hd, hd'⟩
  have hP : QConj g N (fun τ => A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j))
      (fun τ => A' τ ^ n + ∑ j, s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j)) := by
    refine hadd _ _ _ _ (hpow _ _ n hA) ?_
    refine (hsumprod (Fin n) Finset.univ (fun j τ => s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j))
      (fun j τ => s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j)) ?_).1
    intro j _
    exact hmul _ _ _ _ (hmul _ _ _ _ (hs j) (hpow _ _ _ hA)) (hpow _ _ _ hDD)
  have hP0 : (fun τ => A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j)) = fun _ => 0 := by
    funext τ
    have hx : A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j) =
        D τ ^ n * (f τ ^ n + ∑ j, s j τ * f τ ^ (j : ℕ)) := by
      rw [mul_add, Finset.mul_sum, ← hfA τ, mul_pow]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro j _
        rw [mul_pow, show D τ ^ n = D τ ^ (j : ℕ) * D τ ^ (n - j) by
          rw [← pow_add, Nat.add_sub_cancel' j.2.le]]
        ring
    rw [hx, hpol τ, mul_zero]
  have hP'0 : ∀ τ, A' τ ^ n + ∑ j, s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j) = 0 := by
    obtain ⟨c, hc, hc'⟩ := hP
    rw [hP0] at hc
    have hc0 : c = fun _ => 0 := uc N _ _ _ hN hc hz
    subst hc0
    simp only [map_zero] at hc'
    have := uf N _ _ _ hc' hz
    exact fun τ => congrFun this τ
  obtain ⟨h, b, hb, hAh⟩ := GlobalTheory.T.exists_hasQ_quotient_of_integral N n A' D' s' hN ⟨_, he'⟩ ⟨_, hd'⟩
    (fun j => by obtain ⟨c, _, hc'⟩ := hs j; exact ⟨_, hc'⟩) hD' hP'0
  have hfD : HasQ N A (conv a d) := by
    have := GlobalTheory.QFam.hasQ_mul_conv N f D a d hN ha hd
    have hAe : (fun τ => f τ * D τ) = A := funext hfA
    rwa [hAe] at this
  have he1 : e = conv a d := uc N A _ _ hN he hfD
  have hhD : HasQ N A' (conv b fun n => g (d n)) := by
    have := GlobalTheory.QFam.hasQ_mul_conv N h D' b _ hN hb hd'
    have hAe : (fun τ => h τ * D' τ) = A' := funext fun τ => (hAh τ).symm
    rwa [hAe] at this
  have he2 : (fun n => g (e n)) = conv b fun n => g (d n) := uc N A' _ _ hN he' hhD
  rw [he1, conjEx_conv_map] at he2
  have hba : b = fun n => g (a n) := (conjEx_conv_cancel _ _ _ hgd0 he2).symm
  refine ⟨h, ⟨a, ha, hba ▸ hb⟩, fun τ => (hAh τ).symm⟩

end GlobalTheory.FN
end
end

section

noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.TowerFix

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem exists_eq_of_isIntegral_div (h : IsClo p Ω) (T : Tower p Ω) {n : ℕ} (hn : 1 ≤ n)
    (ι : On p n →ₐ[O0 p] Ω) (hι : IsEmb T n ι) (wb wc : On p n) (hc : ι wc ≠ 0) {x : Ω}
    (hx : IsIntegral (O0 p) x) (hxe : x = ι wb / ι wc) : ∃ w : On p n, ι w = x := by
  have hinj : Function.Injective ι := GlobalTheory.T.tower_embedding_injective p Ω h T n hn ι hι
  obtain ⟨hdom, hdvr, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p n hn
  let K := FractionRing (On p n)
  let φ : K →+* Ω := IsFractionRing.lift (g := ι.toRingHom) hinj
  have hφ : ∀ w : On p n, φ (algebraMap (On p n) K w) = ι w := fun w =>
    IsFractionRing.lift_algebraMap _ _
  let φa : K →ₐ[O0 p] Ω :=
    { φ with
      commutes' := fun r => by
        have : algebraMap (O0 p) K r = algebraMap (On p n) K (algebraMap (O0 p) (On p n) r) :=
          IsScalarTower.algebraMap_apply _ _ _ r
        show φ (algebraMap (O0 p) K r) = _
        rw [this, hφ, AlgHom.commutes] }
  have hwc0 : wc ≠ 0 := fun h0 => hc (by rw [h0, map_zero])
  let z : K := algebraMap (On p n) K wb / algebraMap (On p n) K wc
  have hz : φa z = x := by
    show φ z = x
    simp only [z, map_div₀, hφ, hxe]
  have hzi : IsIntegral (O0 p) z := by
    rw [← isIntegral_algHom_iff φa φa.toRingHom.injective, hz]; exact hx
  have hzi' : IsIntegral (On p n) z := hzi.tower_top
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 hzi'
  refine ⟨w, ?_⟩
  rw [← hφ, hw]
  exact hz

end GlobalTheory.K5.TowerFix

theorem GlobalTheory.K5.mem_towerAlg_of_fixed :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
      ∀ (T : Tower p Ω) (x : (integralClosure (O0 p) Ω)),
        (∀ g ∈ ⨅ n, Gn T n, g (x : Ω) = x) → x ∈ towerAlg T := by
  intro p _ Ω _ _ h T x hx
  haveI := h.clo
  haveI := h.alg
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo h
  rw [GlobalTheory.T.mem_towerUnionAdjoinIntegralClosure_iff p Ω T x]
  set B := Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq)
  obtain ⟨b, hb, c, hc, hc0, hbc⟩ := GlobalTheory.mem_adjoin_div_of_fixed (O0 p) Ω h.inj
    (Set.range T.ζ ∪ Set.range T.qq) (x : Ω) (fun g hg => hx g (by
      rw [Subgroup.mem_iInf]
      intro n
      exact ⟨hg _ (Or.inl ⟨n, rfl⟩), hg _ (Or.inr ⟨n, rfl⟩)⟩))
  obtain ⟨m, hm⟩ := GlobalTheory.K5.Level.exists_mem_bn T hb
  obtain ⟨k, hk⟩ := GlobalTheory.K5.Level.exists_mem_bn T hc
  set N := max m k + 1
  have hN : 1 ≤ N := Nat.le_add_left 1 _
  have hbN : b ∈ GlobalTheory.K5.Level.Bn T N :=
    GlobalTheory.K5.Level.bn_mono T (le_trans (le_max_left m k) (Nat.le_succ _)) hm
  have hcN : c ∈ GlobalTheory.K5.Level.Bn T N :=
    GlobalTheory.K5.Level.bn_mono T (le_trans (le_max_right m k) (Nat.le_succ _)) hk
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T N
  obtain ⟨wb, hwb⟩ := GlobalTheory.K5.Level.bn_le_range T N ι hι hbN
  obtain ⟨wc, hwc⟩ := GlobalTheory.K5.Level.bn_le_range T N ι hι hcN
  obtain ⟨w, hw⟩ := GlobalTheory.K5.TowerFix.exists_eq_of_isIntegral_div h T hN ι hι wb wc
    (by rw [show ι wc = c from hwc]; exact hc0) x.2
    (by rw [hbc, show ι wb = b from hwb, show ι wc = c from hwc])
  rw [← hw]
  exact GlobalTheory.K5.Level.bn_le_B T N (GlobalTheory.K5.Level.range_le_bn T N ι hι w)
end
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.algebraicTowerKhat_padic_smul_torsionFree : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → ∀ (c : ℤ_[l]) (x : X.Khat l), c ≠ 0 → c • x = 0 → x = 0 := by
  first | exact @GlobalTheory.KZ.H3.khat_torsionFree | exact GlobalTheory.KZ.H3.khat_torsionFree | (intros; apply GlobalTheory.KZ.H3.khat_torsionFree <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

noncomputable section

namespace GlobalTheory.GeoFix.Divide

theorem divide_ev : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p),
    (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp p (e t)) → ∀ (v : ℕ) (o : Ω), IsInt (p := p) o →
    ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) = (p : Ω) ^ v * o → ∃ (c : ℤ → Ω) (x' : Ω), Ev ψ c o x' := by
  intro p _ Ω _ _ hc T n ψ h d e a he v o ho hsum
  classical
  haveI := Basic.charZero_of_isClo hc
  set c : ℤ → Ω := fun r => ∑ t, e t * zp Ω ((a t).coeff r) with hcdef
  have hev : Ev ψ c (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)))
      (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (thL (a t)))) :=
    ⟨d, e, a, he, fun r => rfl, rfl, rfl⟩
  have hcong : Cong (p := p) v (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) 0 :=
    ⟨o, ho, by rw [sub_zero, hsum]⟩
  have hcr := ((GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit p Ω hc T n ψ h v c _ _ hev).1.1 hcong)
  choose y hy hcy using hcr
  obtain ⟨m, f, hf, hlat⟩ := GlobalTheory.T.exists_finite_padic_span_of_pow_p_mul_mem p Ω hc d e he v
  have hμ : ∀ r, ∃ μ : Fin m → ℤ_[p], y r = ∑ j, zp Ω (μ j) * f j := by
    intro r
    refine hlat (fun t => (a t).coeff r) (y r) (hy r) ?_
    have := hcy r
    rw [sub_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  choose μ hμ using hμ
  let μ' : ℤ → Fin m → ℤ_[p] := fun r => if ∀ t, (a t).coeff r = 0 then 0 else μ r
  have hsupp : ∀ j, (Function.support fun r => μ' r j) ⊆ ⋃ t ∈ (Finset.univ : Finset (Fin d)), (a t).support := by
    intro j r hr
    simp only [Function.mem_support] at hr
    by_cases h0 : ∀ t, (a t).coeff r = 0
    · exact absurd (by simp [μ', h0]) hr
    · push_neg at h0
      obtain ⟨t, ht⟩ := h0
      exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ t)) ht
  have hpwo : (⋃ t ∈ (Finset.univ : Finset (Fin d)), (a t).support).IsPWO :=
    (Finset.univ.isPWO_bUnion).2 fun t _ => (a t).isPWO_support
  let Λ : Fin m → Lau p := fun j => ⟨fun r => μ' r j, hpwo.mono (hsupp j)⟩
  have hΛ : ∀ j r, (Λ j).coeff r = μ' r j := fun _ _ => rfl

  let Λp : Fin m → Lau p := fun j => HahnSeries.C ((p : ℤ_[p]) ^ v) * Λ j
  have hzpp : zp Ω ((p : ℤ_[p]) ^ v) = (p : Ω) ^ v := by
    rw [← GlobalTheory.EvUniq.zpHom_apply, map_pow, map_natCast]
  have hcoef : ∀ r, c r = ∑ j, f j * zp Ω ((Λp j).coeff r) := by
    intro r
    have hc1 : ∀ j, zp Ω ((Λp j).coeff r) = (p : Ω) ^ v * zp Ω (μ' r j) := by
      intro j
      simp only [Λp, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, hΛ]
      rw [← GlobalTheory.EvUniq.zpHom_apply, map_mul, GlobalTheory.EvUniq.zpHom_apply, GlobalTheory.EvUniq.zpHom_apply, hzpp]
    simp only [hc1]
    by_cases h0 : ∀ t, (a t).coeff r = 0
    · have hμ0 : μ' r = 0 := by simp [μ', h0]
      have hz : zp Ω (0 : ℤ_[p]) = 0 := by rw [← GlobalTheory.EvUniq.zpHom_apply, map_zero]
      simp [hcdef, h0, hμ0, hz]
    · have hμr : μ' r = μ r := by simp [μ', h0]
      have := hcy r
      rw [sub_zero] at this
      rw [this, hμ r, hμr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  have hev2 : Ev ψ c (∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (Λp j)))
      (∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (thL (Λp j)))) :=
    ⟨m, f, Λp, hf, hcoef, rfl, rfl⟩
  have heq := (GlobalTheory.EvUniq.ev_unique p Ω hc T n ψ h c _ _ _ _ hev hev2).1
  have hval : ∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (Λp j)) =
      (p : Ω) ^ v * ∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (Λ j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Λp, map_mul, GlobalTheory.EvUniq.psi_C h, hzpp]
    ring
  have hp0 : (p : Ω) ^ v ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have ho' : o = ∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (Λ j)) := by
    rw [hsum, hval] at heq
    exact mul_left_cancel₀ hp0 heq
  exact ⟨fun r => ∑ j, f j * zp Ω ((Λ j).coeff r), _, m, f, Λ, hf, fun r => rfl, ho', rfl⟩

end GlobalTheory.GeoFix.Divide
end
end

section

open GlobalTheory.Col PowerSeries

namespace GlobalTheory

theorem normOp_isUnit {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] {h : PowerSeries R} (hu : IsUnit h) :
    IsUnit (normOp p h) := by
  unfold normOp
  exact hu.map _

theorem normOp_iterate_isUnit {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] {h : PowerSeries R} (hu : IsUnit h)
    (j : ℕ) : IsUnit ((normOp p)^[j] h) := by
  induction j with
  | zero => simpa using hu
  | succ j ih => rw [Function.iterate_succ_apply']; exact normOp_isUnit p ih

theorem normOp_iterate_congr : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ (h : PowerSeries R), IsUnit h → ∀ j : ℕ, ∃ r : PowerSeries R,
      (normOp p)^[j + 1] h = smap σ ((normOp p)^[j] h) + (p : PowerSeries R) ^ (j + 1) * r := by
  intro R _ p hp σ hσ h hu j
  induction j with
  | zero =>
    obtain ⟨r, hr⟩ := GlobalTheory.T.normOp_eq_smap_add_mul R p σ hσ h
    exact ⟨r, by simpa using hr⟩
  | succ j ih =>
    obtain ⟨r, hr⟩ := ih
    have hu2 : IsUnit (smap σ ((normOp p)^[j] h)) := (normOp_iterate_isUnit p hu j).map _
    obtain ⟨r', hr'⟩ := GlobalTheory.T.normOp_congr_mod_pow_succ R p σ hσ _ _ r (j + 1) (by omega) hu2 hr
    refine ⟨r', ?_⟩
    rw [Function.iterate_succ_apply' (normOp p) (j + 1), hr', GlobalTheory.T.colemanNormOperator_powerSeriesCoeffAutMap_comm R p σ, ← Function.iterate_succ_apply' (normOp p) j]

end GlobalTheory
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.eq_unit_mul_pow_cyclotomic_uniformizer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), b ≠ 0 → ∃ (n k : ℕ), 1 ≤ n ∧ ∃ u ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ u' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), u * u' = 1 ∧ b = u * (T.ζ n - 1) ^ k := by
  first | exact @GlobalTheory.K5.UnitPow.eq_unit_mul_pow | exact GlobalTheory.K5.UnitPow.eq_unit_mul_pow | (intros; apply GlobalTheory.K5.UnitPow.eq_unit_mul_pow <;> assumption)
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.frobenius_surjective_mod_prime_cyclotomicKummerTower : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω), ∀ x ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ y ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ z ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), x = y ^ p + (p : Ω) * z := by
  first | exact @GlobalTheory.K5.frob_surj_adjoin_tower | exact GlobalTheory.K5.frob_surj_adjoin_tower | (intros; apply GlobalTheory.K5.frob_surj_adjoin_tower <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.mass_degType_le_card_cycleType_div : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (A : Multiset ℕ → Prop), (mass g N fun f => A (degType g f)) ≤ ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => A σ.partition.parts).card : ℝ) / (N.factorial : ℝ) := by
  first | exact @GlobalTheory.BadShare.mass_degType_le_cycleType | exact GlobalTheory.BadShare.mass_degType_le_cycleType | (intros; apply GlobalTheory.BadShare.mass_degType_le_cycleType <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.levelDatum_idempotent_rank_ge_of_generic_free_rows_first : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), IsGeneric ρ → ∀ L : Lev g N, L.sharp = true → L.s = 0 → (1 - 1 / (g : ℝ)) * (g : ℝ) ^ L.k ≤ (rk ρ L.e : ℝ) := by
  first | exact @GlobalTheory.BadShare.rk_ge_of_isGeneric_of_s_eq_zero | exact GlobalTheory.BadShare.rk_ge_of_isGeneric_of_s_eq_zero | (intros; apply GlobalTheory.BadShare.rk_ge_of_isGeneric_of_s_eq_zero <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.levelDatum_idempotent_rank_le_root_exchange : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ L L' : Lev g N, L.sharp = true → L'.sharp = true → L.k = L'.k → L.s = L'.s + 1 → rk ρ L'.e ≤ rk ρ L.e := by
  first | exact @GlobalTheory.BadShare.RxStep.rk_le_step | exact GlobalTheory.BadShare.RxStep.rk_le_step | (intros; apply GlobalTheory.BadShare.RxStep.rk_le_step <;> assumption)
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem normOp_comp : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → idx A B ≠ 0 → idx A C ≠ 0 → ∀ v, Fixes W A v → normOp lam W B C (normOp lam W A B v) = normOp lam W A C v := by
  intro R X M _ _ _ _ _ σ w γ W h lam hlam A B C hA hB hC hAB hAC v hv
  induction hn : idx A B using Nat.strong_induction_on generalizing A v with
  | _ n ih =>
  by_cases hle : B ≤ A
  · have hAB' : A = B := by
      refine le_antisymm (fun x hx => (hB x).2 fun b hb => h.iso hA hx (hle hb)) hle
    subst hAB'
    obtain ⟨h1, h2⟩ := (GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A A hA).2.2 le_rfl
    have : normOp lam W A A v = v := by
      rw [normOp, h1, map_one, inv_one, one_smul, h2 v hv]
    rw [this]
  · obtain ⟨A', hA', hadj, hbet⟩ := GlobalTheory.T.exists_adjacent_selfDual_lattice_toward h A B hA hB hAB hle
    obtain ⟨x, hx, P, hP, hfin, hann, hgen⟩ := id hadj
    obtain ⟨e1, e2, -⟩ := GlobalTheory.T.adjacent_selfDual_lattices_index_simple h A A' hA hA' x hx P hP hfin hann hgen
    have hcard : 1 < Nat.card (R ⧸ P) := by
      haveI : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
      exact Finite.one_lt_card
    have hAA' : idx A A' ≠ 0 := by omega
    have hA'A : idx A' A ≠ 0 := by omega
    have hA'B : idx A' B ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hA'A hAB
    have hA'C : idx A' C ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hA'A hAC
    have hmul := (GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice h A A' B hA hA' hB hAA' hA'B hbet).1
    have hlt : idx A' B < n := by
      rw [← hn, hmul, e1]
      exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hA'B) hcard
    have hfix : Fixes W A' (normOp lam W A A' v) := by
      intro a ha
      rw [normOp, map_smul, ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A A' hA').2.1 hAA').2.1 v hv a ha]
    rw [← GlobalTheory.T.normalizedIntertwiner_comp_of_adjacent_lattices h lam hlam A A' B hA hA' hB hadj hAB v hv,
      ih _ hlt A' hA' hA'B hA'C _ hfix rfl,
      GlobalTheory.T.normalizedIntertwiner_comp_of_adjacent_lattices h lam hlam A A' C hA hA' hC hadj hAC v hv]

end GlobalTheory.FinWeil
end
