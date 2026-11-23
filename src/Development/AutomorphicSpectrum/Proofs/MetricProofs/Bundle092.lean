module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle085
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle027
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_smul_of_isMultiHomog {L : Type} [CommRing L] [Algebra ℂ L]
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) (c : K → L)
    (y : (Σ k, ι k) → L) :
    aeval (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * aeval y f := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∏ q : (Σ k, ι k), (c q.1 * y q) ^ m q =
      (∏ k, c k ^ a k) * ∏ q : (Σ k, ι k), y q ^ m q := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  rw [h1]; ring

def chartSub {L : Type} [CommRing L] [Algebra ℂ L] (w : (Σ k, ι k) → L) :
    MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ →ₐ[ℂ] L :=
  aeval fun j => w ((Fintype.equivFin (Σ k, ι k)).symm j)

theorem chartSub_renC {L : Type} [CommRing L] [Algebra ℂ L] (w : (Σ k, ι k) → L)
    (h : MvPolynomial (Σ k, ι k) ℂ) : chartSub w (renC (Σ k, ι k) h) = aeval w h := by
  simp [chartSub, renC, renameEquiv_apply, aeval_rename, Function.comp_def]

theorem chartSub_bind {L : Type} [CommRing L] [Algebra ℂ L] (w : (Σ k, ι k) → L)
    (p : (k : K) → ι k) (h1 : ∀ k, w ⟨k, p k⟩ = 1) (f : MvPolynomial (Σ k, ι k) ℂ) :
    chartSub w (bind₁ (lift p) f) = aeval w f := by
  have : (chartSub w).comp (bind₁ (lift p)) = aeval w := by
    refine MvPolynomial.algHom_ext fun q => ?_
    rw [AlgHom.comp_apply, bind₁_X_right, aeval_X]
    unfold lift
    split_ifs with h
    · obtain ⟨k, i⟩ := q
      simp only at h
      subst h
      rw [h1 k, map_one]
    · simp [chartSub]
  exact DFunLike.congr_fun this f

variable {L : Type} [CommRing L] [Algebra ℂ L] [Algebra (MvPolynomial (Σ k, ι k) ℂ) L]
  [IsScalarTower ℂ (MvPolynomial (Σ k, ι k) ℂ) L]

theorem aeval_algebraMap_X (g : MvPolynomial (Σ k, ι k) ℂ) :
    aeval (fun q => algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) g =
      algebraMap (MvPolynomial (Σ k, ι k) ℂ) L g := by
  have : aeval (fun q => algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) =
      IsScalarTower.toAlgHom ℂ (MvPolynomial (Σ k, ι k) ℂ) L :=
    MvPolynomial.algHom_ext fun q => by simp
  exact DFunLike.congr_fun this g

theorem map_ideal_le (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hS : IsMultiHomogIdeal S)
    (p : (k : K) → ι k) (c : K → L)
    (hc : ∀ k, c k * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X ⟨k, p k⟩) = 1) :
    (ideal S p).map (chartSub fun q => c q.1 * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) ≤
      S.map (algebraMap (MvPolynomial (Σ k, ι k) ℂ) L) := by
  rw [Ideal.map_le_iff_le_comap]
  unfold ideal
  rw [Ideal.map_le_iff_le_comap]
  intro h hh
  rw [Ideal.mem_comap, Ideal.mem_comap]
  have key : ∀ h ∈ chartIdeal S p, aeval (fun q => c q.1 * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) h ∈
      S.map (algebraMap (MvPolynomial (Σ k, ι k) ℂ) L) := by
    obtain ⟨G, hG, rfl⟩ := hS
    intro h hh
    have hle : chartIdeal (Ideal.span G) p ≤
        (Ideal.map (algebraMap (MvPolynomial (Σ k, ι k) ℂ) L) (Ideal.span G)).comap
          (aeval (fun q => c q.1 * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) :
            MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] L) := by
      refine sup_le ?_ ?_
      · rw [Ideal.span_le]
        intro g hg
        obtain ⟨b, hb⟩ := hG g hg
        rw [SetLike.mem_coe, Ideal.mem_comap, aeval_smul_of_isMultiHomog hb, aeval_algebraMap_X]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hg))
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap]
        simp [hc k]
    exact hle hh
  have e : (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) h = renC (Σ k, ι k) h := rfl
  rw [e, chartSub_renC]
  exact key h hh

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem relation_homogenises (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ)
    (a : K → ℕ) (n : ℕ) (s' : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)
    (hP : IsMultiHomogIdeal P) (hQ : IsMultiHomogIdeal Q) (hQp : Q.IsPrime)
    (hX : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) (hf : IsMultiHomog f a)
    (hs' : s' ∉ SncRes.ideal Q p)
    (hrel : s' * bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ^ n ⊔ SncRes.ideal P p) :
    ∃ s ∉ Q, s * f ∈ Q ^ n ⊔ P := by
  set x : MvPolynomial (Σ k, ι k) ℂ := ∏ k, X ⟨k, p k⟩ with hx
  let L := Localization.Away x
  let i : MvPolynomial (Σ k, ι k) ℂ →+* L := algebraMap _ L
  have hxu : IsUnit (i x) := IsLocalization.Away.algebraMap_isUnit x
  have hu : ∀ k, IsUnit (i (X ⟨k, p k⟩)) := fun k =>
    isUnit_of_dvd_unit (map_dvd i (Finset.dvd_prod_of_mem (fun k => (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ)) (Finset.mem_univ k))) hxu
  have hv : ∀ k, ∃ v, v * i (X ⟨k, p k⟩) = 1 := fun k => (hu k).exists_left_inv
  choose c hc using hv
  let w : (Σ k, ι k) → L := fun q => c q.1 * i (X q)
  have hw1 : ∀ k, w ⟨k, p k⟩ = 1 := hc
  let ψ := chartSub w
  have hψf : ψ (bind₁ (lift p) f) = (∏ k, c k ^ a k) * i f := by
    rw [chartSub_bind w p hw1, aeval_smul_of_isMultiHomog hf c, aeval_algebraMap_X]

  have h1 : ψ s' * ψ (bind₁ (lift p) f) ∈ (Q ^ n ⊔ P).map i := by
    have h2 : (ideal Q p ^ n ⊔ ideal P p).map ψ ≤ (Q ^ n ⊔ P).map i := by
      rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_sup, Ideal.map_pow]
      exact sup_le_sup (Ideal.pow_right_mono (map_ideal_le Q hQ p c hc) n)
        (map_ideal_le P hP p c hc)
    have := h2 (Ideal.mem_map_of_mem ψ hrel)
    rwa [map_mul] at this
  have hinv : (∏ k, i (X ⟨k, p k⟩) ^ a k) * ∏ k, c k ^ a k = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [← mul_pow, mul_comm, hc k, one_pow]
  have h3 : ψ s' * i f ∈ (Q ^ n ⊔ P).map i := by
    have := Ideal.mul_mem_left _ (∏ k, i (X ⟨k, p k⟩) ^ a k) h1
    rw [hψf] at this
    have e : (∏ k, i (X ⟨k, p k⟩) ^ a k) * (ψ s' * ((∏ k, c k ^ a k) * i f)) =
        ((∏ k, i (X ⟨k, p k⟩) ^ a k) * ∏ k, c k ^ a k) * (ψ s' * i f) := by ring
    rwa [e, hinv, one_mul] at this
  obtain ⟨e, s₀, hs₀⟩ := IsLocalization.Away.surj x (ψ s')
  have h4 : i (s₀ * f) ∈ (Q ^ n ⊔ P).map i := by
    rw [map_mul]
    change i s₀ * i f ∈ _
    rw [show i s₀ = ψ s' * i x ^ e from hs₀.symm]
    have := Ideal.mul_mem_left _ (i x ^ e) h3
    convert this using 1
    ring
  obtain ⟨m, hm, hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers x) L _ _).1 h4
  refine ⟨m * s₀, ?_, by rwa [mul_assoc]⟩
  intro hmem
  have hxQ : x ∉ Q := by
    intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff).1 h
    exact hX k hk
  obtain ⟨N, rfl⟩ := hm
  have hs₀Q : s₀ ∈ Q := by
    rcases hQp.mem_or_mem hmem with h | h
    · exact absurd (hQp.mem_of_pow_mem _ h) hxQ
    · exact h

  let J := ideal Q p
  let g : MvPolynomial (Σ k, ι k) ℂ →+* (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) :=
    (Ideal.Quotient.mk J).comp (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)
  have hg1 : ∀ k, g (X ⟨k, p k⟩) = 1 := by
    intro k
    have hmem : (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) (X ⟨k, p k⟩ - 1) ∈ J :=
      Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
    have := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at this
    exact this
  have hgx : g x = 1 := by
    rw [hx, map_prod]
    exact Finset.prod_eq_one fun k _ => hg1 k
  let Φ : L →+* (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) :=
    IsLocalization.Away.lift x (g := g) (by rw [hgx]; exact isUnit_one)
  have hΦ : ∀ h, Φ (i h) = g h := fun h => IsLocalization.Away.lift_eq x _ h
  have hΦc : ∀ k, Φ (c k) = 1 := by
    intro k
    have := congrArg Φ (hc k)
    rwa [map_mul, hΦ, hg1, mul_one, map_one] at this
  have hΦψ : Φ.comp (ψ : _ →+* L) = Ideal.Quotient.mk J := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · have e1 : ψ (C r) = i (C r) := by
        rw [show (C r : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) = algebraMap ℂ _ r from rfl,
          AlgHom.commutes]
        exact IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) L r
      show Φ (ψ (C r)) = _
      rw [e1, hΦ]
      simp [g]
    · show Φ (ψ (X j)) = _
      have e1 : ψ (X j) = w ((Fintype.equivFin (Σ k, ι k)).symm j) := by simp [ψ, chartSub]
      rw [e1]
      show Φ (c _ * i (X _)) = _
      rw [map_mul, hΦc, one_mul, hΦ]
      simp [g, renC, renameEquiv_apply]
  apply hs'
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h5 : Φ (ψ s') = Ideal.Quotient.mk J s' := DFunLike.congr_fun hΦψ s'
  have h6 := congrArg Φ hs₀
  rw [map_mul, map_pow, hΦ, hΦ, hgx, one_pow, mul_one, h5] at h6
  rw [h6]
  exact Ideal.Quotient.eq_zero_iff_mem.2
    (Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hs₀Q))

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
end
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv.Rate

theorem mInt_congr_φ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ Ψ : Fin e → LocPot X) (h : ∀ i, (Φ i).φ = (Ψ i).φ) (g : X → ℝ) :
    mInt A Φ g = mInt A Ψ g := by
  have hD : locDens A Φ = locDens A Ψ := by
    funext j y
    simp only [locDens, h]
  unfold mInt integralWith
  rw [hD]

theorem maMeasure_univ_eq {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ : LocPot X)
    (th : Fin e → LocPot X) (u : Fin e → X → ℝ) (hΘ : IsPotential A Θ)
    (hth : ∀ i, IsPotential A (th i)) (hu : ∀ i, A.Smooth (u i))
    (hP : ∀ i, IsPotential A (th i + LocPot.ofFun (u i) + Θ))
    (hPsh : ∀ i, IsPsh A (th i + LocPot.ofFun (u i) + Θ)) :
    maMeasure A (fun i => th i + LocPot.ofFun (u i) + Θ) Set.univ =
      ENNReal.ofReal (mInt A (fun i => th i + Θ) (fun _ => 1)) := by
  obtain ⟨hfin, hg⟩ := maMeasure_thm A (fun i => th i + LocPot.ofFun (u i) + Θ) hP hPsh
  have hI : Integrable (fun _ : X => (1 : ℝ)) (maMeasure A (fun i => th i + LocPot.ofFun (u i) + Θ)) :=
    integrable_const 1
  have hM := (hg _ measurable_const).1.2 hI
  have h2 := (hg _ measurable_const).2 hM
  have h3 : mInt A (fun i => th i + LocPot.ofFun (u i) + Θ) (fun _ => 1) =
      mInt A (fun i => (th i + Θ) + LocPot.ofFun (u i)) (fun _ => 1) := by
    refine mInt_congr_φ A _ _ (fun i => ?_) _
    funext x y
    show (th i).φ x y + u i y + Θ.φ x y = (th i).φ x y + Θ.φ x y + u i y
    ring
  rw [massIndep A (fun i => th i + Θ) u (fun i => isPotentialAdd A _ _ (hth i) hΘ) hu] at h3
  rw [← h3, h2, integral_const, smul_eq_mul, mul_one, ofReal_measureReal (measure_ne_top _ _)]

end GlobalTheory.CompanionTheory.Ar.Giv.Rate

namespace GlobalTheory.CompanionTheory.Ar.Giv


open GlobalTheory.CompanionTheory.Ar.Giv.Rate in
theorem convergenceRate_holds : ConvergenceRateStatement := by
  intro e X _ _ _ _ _ A Θ L s n m W hΘ hpos hL hS hSNC hnorm th ph phT th₀ ph₀ phT₀ C₅ C t₀
    hW hR hW₀ hR₀
  obtain ⟨K, t₂, ht₂, -, hT⟩ := tail_uniform tailBound_holds A Θ L s m W hΘ hpos hL hS hSNC hnorm
    th ph phT C₅ C t₀ hW hR
  have ht₀ : 0 < t₀ := hR₀.1
  refine ⟨(3 + |C|) * |mInt A (fun i => th i + Θ) (fun _ => 1)| + (|C| + |C₅|) * |K|,
    min t₂ (min t₀ (Real.exp (-Real.exp 1))), lt_min ht₂ (lt_min ht₀ (Real.exp_pos _)), ?_⟩
  intro t t' ht' htt' ht1 c
  have htpos : 0 < t := ht'.trans_le htt'
  have ht_t₂ : t ≤ t₂ := ht1.trans (min_le_left _ _)
  have ht_t₀ : t ≤ t₀ := ht1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht_e : t ≤ Real.exp (-Real.exp 1) := ht1.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlogt : Real.log (1 / t) = -Real.log t := by rw [one_div, Real.log_inv]
  have hℓe : Real.exp 1 ≤ Real.log (1 / t) := by
    have := Real.log_le_log htpos ht_e
    rw [Real.log_exp] at this
    linarith
  have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, Real.log (1 / t) = ℓ := ⟨_, rfl⟩
  rw [hℓ] at hℓe hlogt
  rw [hℓ]
  have hℓpos : 0 < ℓ := by linarith
  have hlogℓ : 1 ≤ Real.log ℓ := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hℓe
  have hℓu : ∀ u, 0 < u → u ≤ t → ℓ ≤ Real.log (1 / u) := fun u hu hut =>
    hℓ ▸ Real.log_le_log (by positivity) (one_div_le_one_div_of_le hu hut)

  have heps : ∀ u, 0 < u → u ≤ t → epsT C u ≤ |C| * (Real.log ℓ / ℓ) := by
    intro u hu hut
    have hlu := hℓu u hu hut
    have hmono := Real.log_div_self_antitoneOn (Set.mem_Ici.2 hℓe) (Set.mem_Ici.2 (hℓe.trans hlu)) hlu
    have hnn : 0 ≤ Real.log (Real.log (1 / u)) / Real.log (1 / u) :=
      div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
    unfold epsT
    rw [mul_div_assoc]
    calc C * (Real.log (Real.log (1 / u)) / Real.log (1 / u))
        ≤ |C| * (Real.log (Real.log (1 / u)) / Real.log (1 / u)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hnn
      _ ≤ |C| * (Real.log ℓ / ℓ) := mul_le_mul_of_nonneg_left hmono (abs_nonneg C)
  have hrpow : ∀ u, 0 < u → u ≤ t → u ^ ((1 : ℝ) / 3) ≤ 3 / ℓ := by
    intro u hu hut
    refine (Real.rpow_le_rpow hu.le hut (by norm_num)).trans ?_
    rw [Real.rpow_def_of_pos htpos]
    have h3 : Real.log t * (1 / 3) = -(ℓ / 3) := by rw [hlogt]; ring
    rw [h3, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    linarith [Real.add_one_le_exp (ℓ / 3)]
  obtain ⟨q, hq⟩ : ∃ q, q = Real.log ℓ ^ 2 / ℓ := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : 1 / ℓ ≤ q := hq ▸ div_le_div_of_nonneg_right (by nlinarith) hℓpos.le
  have hq2 : Real.log ℓ / ℓ ≤ q := hq ▸ div_le_div_of_nonneg_right (by nlinarith) hℓpos.le
  have hsmall : ∀ u, 0 < u → u ≤ t → u ^ ((1 : ℝ) / 3) + epsT C u ≤ (3 + |C|) * q := by
    intro u hu hut
    have h1 := hrpow u hu hut
    have h2 := heps u hu hut
    have h3 : |C| * (Real.log ℓ / ℓ) ≤ |C| * q := mul_le_mul_of_nonneg_left hq2 (abs_nonneg C)
    have h4 : 3 / ℓ = 3 * (1 / ℓ) := by ring
    nlinarith

  obtain ⟨-, hCt, hat, -, -, hdt, -, -⟩ := hR₀.2.2 t htpos ht_t₀
  obtain ⟨-, hCt', hat', -, -, hdt', -, -⟩ := hR₀.2.2 t' ht' (htt'.trans ht_t₀)
  have hsw := hW₀.2.2.2
  have hin : ∀ y ∉ bdry s, rW L s y < ℓ → |phT₀ t y - phT₀ t' y| ≤ (3 + |C|) * q := by
    intro y hy hry
    have h1 := hdt y hy (by rw [hℓ]; exact hry.le)
    have h2 := hdt' y hy (hry.le.trans (hℓu t' ht' htt'))
    have h3 := hsmall t htpos le_rfl
    have h4 := hsmall t' ht' htt'
    have h5 := hat y hy
    have h6 := hat' y hy
    rw [abs_le]
    constructor <;> linarith
  have hout : ∀ y ∉ bdry s, ℓ ≤ rW L s y →
      |phT₀ t y - phT₀ t' y| ≤ (|C| + |C₅|) * Real.log (rW L s y) := by
    intro y hy hry
    have hr1 : 1 ≤ Real.log (rW L s y) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (hℓe.trans hry)
    have h1 := hCt y
    have h2 := hCt' y
    have h5 := hat y hy
    have h6 := hat' y hy
    have h7 := (hsw y hy).1
    have h8 : C ≤ |C| * Real.log (rW L s y) := (le_abs_self C).trans (by nlinarith [abs_nonneg C])
    have h9 : C₅ * Real.log (rW L s y) ≤ |C₅| * Real.log (rW L s y) :=
      mul_le_mul_of_nonneg_right (le_abs_self C₅) (by linarith)
    rw [abs_le]
    constructor <;> nlinarith

  have hτ : ∀ i, 0 < (fun i => if c i then t else t') i ∧ (fun i => if c i then t else t') i ≤ t₂ := by
    intro i
    by_cases h : c i
    · simp only [h, if_true]; exact ⟨htpos, ht_t₂⟩
    · simp only [h]; exact ⟨ht', htt'.trans ht_t₂⟩
  obtain ⟨hPP, hTR⟩ := hT _ hτ
  obtain ⟨-, hlogR⟩ := hTR ℓ hℓe
  beta_reduce at hPP hlogR
  have hsm : ∀ i, A.Smooth (phT i (if c i then t else t')) := by
    intro i
    by_cases h : c i
    · simp only [h, if_true]; exact ((hR i).2.2 t htpos ht_t₀).1
    · simp only [h]; exact ((hR i).2.2 t' ht' (htt'.trans ht_t₀)).1
  have hmass := maMeasure_univ_eq A Θ th (fun i => phT i (if c i then t else t')) hΘ
    (fun i => (hW i).1) hsm (fun i => (hPP i).1) (fun i => (hPP i).2)
  have hnull : maMeasure A (fun i => th i + LocPot.ofFun (phT i (if c i then t else t')) + Θ)
      (bdry s) = 0 := bdry_null A L s m W hL hS hSNC _ (fun i => (hPP i).1)
  have hae := measure_eq_zero_iff_ae_notMem.1 hnull
  set μ := maMeasure A (fun i => th i + LocPot.ofFun (phT i (if c i then t else t')) + Θ) with hμ
  set M := mInt A (fun i => th i + Θ) (fun _ => (1 : ℝ)) with hM
  set k := |C| + |C₅| with hkdef
  have hk : 0 ≤ k := by positivity
  have ha : 0 ≤ (3 + |C|) * q := mul_nonneg (by positivity) hq0
  have hpt : ∀ᵐ y ∂μ, ENNReal.ofReal |phT₀ t y - phT₀ t' y| ≤
      ENNReal.ofReal ((3 + |C|) * q) + ((bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y}).indicator
        (fun y => ENNReal.ofReal k * ENNReal.ofReal (Real.log (rW L s y))) y := by
    filter_upwards [hae] with y hy
    by_cases hry : ℓ ≤ rW L s y
    · rw [Set.indicator_of_mem (show y ∈ (bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y} from ⟨hy, hry⟩),
        ← ENNReal.ofReal_mul hk]
      exact (ENNReal.ofReal_le_ofReal (hout y hy hry)).trans le_add_self
    · rw [Set.indicator_of_notMem (by exact fun h => hry h.2), add_zero]
      exact ENNReal.ofReal_le_ofReal (hin y hy (not_le.1 hry))
  have hsec : ∫⁻ y, ((bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y}).indicator
        (fun y => ENNReal.ofReal k * ENNReal.ofReal (Real.log (rW L s y))) y ∂μ ≤
      ENNReal.ofReal k * ENNReal.ofReal (|K| * q) := by
    refine (lintegral_indicator_le _ _).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hKq : K * Real.log ℓ ^ 2 / ℓ ≤ |K| * q := by
      rw [hq, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    gcongr
    exact hlogR.trans (ENNReal.ofReal_le_ofReal hKq)
  calc ∫⁻ y, ENNReal.ofReal |phT₀ t y - phT₀ t' y| ∂μ
      ≤ ∫⁻ y, (ENNReal.ofReal ((3 + |C|) * q) + ((bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y}).indicator
          (fun y => ENNReal.ofReal k * ENNReal.ofReal (Real.log (rW L s y))) y) ∂μ :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal ((3 + |C|) * q) * μ Set.univ + ∫⁻ y, ((bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y}).indicator
          (fun y => ENNReal.ofReal k * ENNReal.ofReal (Real.log (rW L s y))) y ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const]
    _ ≤ ENNReal.ofReal ((3 + |C|) * q) * ENNReal.ofReal |M| +
          ENNReal.ofReal k * ENNReal.ofReal (|K| * q) := by
        rw [hmass]
        gcongr
        exact le_abs_self _
    _ = ENNReal.ofReal ((3 + |C|) * q * |M| + k * (|K| * q)) := by
        rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hk,
          ← ENNReal.ofReal_add (mul_nonneg ha (abs_nonneg _)) (mul_nonneg hk (mul_nonneg (abs_nonneg _) hq0))]
    _ ≤ ENNReal.ofReal (((3 + |C|) * |M| + k * |K|) * Real.log ℓ ^ 2 / ℓ) :=
        ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hq]; ring))

end GlobalTheory.CompanionTheory.Ar.Giv
end
