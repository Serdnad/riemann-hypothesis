module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMinimalPrimePlace
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLocalOrder
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle107
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle056
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets MinimalPrimePlace

noncomputable section

namespace ReducedNormalisationPlace

variable {A B : Type*} [CommRing A] [CommRing B]

theorem fracMap_mk'_eq_zero_iff [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) (a : A)
    (u : nonZeroDivisors A) :
    fracMap π hker (IsLocalization.mk' (FractionRing A) a u) = 0 ↔ a ∈ RingHom.ker π := by
  rw [IsLocalization.map_mk', IsFractionRing.mk'_eq_zero_iff_eq_zero, RingHom.mem_ker]

theorem fracMap_eq_zero_iff {C : Type*} [CommRing C] [IsDomain B] [IsDomain C] (π : A →+* B) (π' : A →+* C)
    (hker : RingHom.ker π ∈ minimalPrimes A) (hker' : RingHom.ker π' ∈ minimalPrimes A)
    (h : RingHom.ker π = RingHom.ker π') (z : FractionRing A) :
    fracMap π hker z = 0 ↔ fracMap π' hker' z = 0 := by
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) z
  rw [fracMap_mk'_eq_zero_iff, fracMap_mk'_eq_zero_iff, h]

theorem eq_zero_of_forall_num_mem [IsReduced A] (z : FractionRing A)
    (h : ∀ p ∈ minimalPrimes A, ∀ (a : A) (u : nonZeroDivisors A),
      z = IsLocalization.mk' (FractionRing A) a u → a ∈ p) : z = 0 := by
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) z
  show IsLocalization.mk' (FractionRing A) a u = 0
  rw [eq_zero_of_forall_mem_minimalPrimes fun p hp ↦ h p hp a u rfl, IsLocalization.mk'_zero]

theorem exists_idempotent [IsNoetherianRing A] [IsReduced A] (p : Ideal A) (hp : p ∈ minimalPrimes A) :
    ∃ e : integralClosure A (FractionRing A), ∀ (B : Type) [CommRing B] [IsDomain B] (π : A →+* B),
      Function.Surjective π → ∀ hker : RingHom.ker π = p,
        fracMap π (by rw [hker]; exact hp) e = 1 ∧
          ∀ z, fracMap π (by rw [hker]; exact hp) z = 0 → (e : FractionRing A) * z = 0 := by
  have := hp.1.1
  have hk : RingHom.ker (Ideal.Quotient.mk p) ∈ minimalPrimes A := by rwa [Ideal.mk_ker]
  obtain ⟨e, he1, hek, -⟩ := exists_fracMap_unit (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective hk
  have he : IsIntegral A e := by
    simpa using isIntegral_mul_of_fracMap _ Ideal.Quotient.mk_surjective hk (x := 1) he1 hek
      (by rw [map_one]; exact isIntegral_one)
  refine ⟨⟨e, he⟩, fun B _ _ π _ hker ↦ ⟨?_, fun z hz ↦ hek z ?_⟩⟩
  · have hπ : RingHom.ker π ∈ minimalPrimes A := by rw [hker]; exact hp
    rw [← sub_eq_zero, ← map_one (fracMap π hπ), ← map_sub,
      fracMap_eq_zero_iff π (Ideal.Quotient.mk p) hπ hk (by rw [hker, Ideal.mk_ker]), map_sub, he1, map_one,
      sub_self]
  · have hπ : RingHom.ker π ∈ minimalPrimes A := by rw [hker]; exact hp
    exact (fracMap_eq_zero_iff π (Ideal.Quotient.mk p) hπ hk (by rw [hker, Ideal.mk_ker]) z).1 hz

end ReducedNormalisationPlace


open ReducedNormalisationPlace in
theorem ReducedNormalisationPlace.proof : ReducedNormalisationPlace.Statement := by
  intro R _ _ _ P
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  have := P.isMaximal.isPrime
  choose! e he using fun p (hp : p ∈ minimalPrimes R) ↦ exists_idempotent p hp
  have hprodK : ∏ p ∈ hfin.toFinset, (1 - (e p : FractionRing R)) = 0 := by
    refine eq_zero_of_forall_num_mem _ fun p hp a u hz ↦ ?_
    have := hp.1.1
    have hk : RingHom.ker (Ideal.Quotient.mk p) ∈ minimalPrimes R := by rwa [Ideal.mk_ker]
    have h0 : fracMap (Ideal.Quotient.mk p) hk (∏ q ∈ hfin.toFinset, (1 - (e q : FractionRing R))) = 0 := by
      rw [map_prod]
      refine Finset.prod_eq_zero (hfin.mem_toFinset.2 hp) ?_
      rw [map_sub, map_one,
        (he p hp (R ⧸ p) (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective Ideal.mk_ker).1, sub_self]
    rw [hz, fracMap_mk'_eq_zero_iff, Ideal.mk_ker] at h0
    exact h0
  have hprod : ∏ p ∈ hfin.toFinset, (1 - e p) = 0 := Subtype.ext (by push_cast; exact hprodK)
  obtain ⟨p, hpT, hp1⟩ := (Ideal.IsPrime.prod_mem_iff (p := P.asIdeal)).1
    (by rw [hprod]; exact P.asIdeal.zero_mem)
  have hpmin : p ∈ minimalPrimes R := hfin.mem_toFinset.1 hpT
  have hepP : e p ∉ P.asIdeal := fun h ↦
    P.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.asIdeal.add_mem h hp1))
  refine ⟨p, hpmin, fun S _ φ hφ hkerφ ↦ ?_⟩
  have hpr : (RingHom.ker φ).IsPrime := hkerφ ▸ hpmin.1.1
  have : IsDomain S :=
    MulEquiv.isDomain (R ⧸ RingHom.ker φ) (RingHom.quotientKerEquivOfSurjective hφ).symm.toMulEquiv
  have hker : RingHom.ker φ ∈ minimalPrimes R := by rw [hkerφ]; exact hpmin
  obtain ⟨he1, hek⟩ := he p hpmin S φ hφ hkerφ
  obtain ⟨_, -, -, hsurj⟩ := exists_fracMap_unit φ hφ hker
  have hN : Function.Surjective (normMap φ hker) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    have hint : IsIntegral R ((e p : FractionRing R) * x) :=
      isIntegral_mul_of_fracMap φ hφ hker he1 hek (by rw [hx]; exact y.2)
    refine ⟨⟨_, hint⟩, Subtype.ext ?_⟩
    show fracMap φ hker ((e p : FractionRing R) * x) = y
    rw [map_mul, he1, one_mul, hx]
  have hε1 : normMap φ hker (e p) = 1 := Subtype.ext he1
  have hε : ∀ z, normMap φ hker z = 0 → e p * z = 0 := fun z hz ↦
    Subtype.ext (hek z (congrArg Subtype.val hz))
  have hkerP : RingHom.ker (normMap φ hker) ≤ P.asIdeal := fun z hz ↦
    (P.isMaximal.isPrime.mem_or_mem (by rw [hε z hz]; exact P.asIdeal.zero_mem)).resolve_left hepP
  have hcm : (P.asIdeal.map (normMap φ hker)).comap (normMap φ hker) = P.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ hN, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 hkerP]
  have hmax : (P.asIdeal.map (normMap φ hker)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ hN P.isMaximal).resolve_left fun h ↦
      P.isMaximal.ne_top (by rw [← hcm, h, Ideal.comap_top])
  obtain ⟨E, hE⟩ := exists_localization_ringEquiv (normMap φ hker) hN (e p) hε1 hε
    (P.asIdeal.map (normMap φ hker))
  refine ⟨⟨_, hmax⟩, fun x ↦ ?_⟩
  have key : ∀ (Q : Ideal (integralClosure R (FractionRing R))) [Q.IsPrime], Q = P.asIdeal →
      ∀ E' : Localization.AtPrime Q ≃+* Localization.AtPrime (P.asIdeal.map (normMap φ hker)),
        (∀ r, E' (algebraMap _ _ r) = algebraMap _ _ (normMap φ hker r)) →
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap _ (Localization.AtPrime P.asIdeal) (algebraMap R (integralClosure R (FractionRing R)) x)) =
          Ring.ord (Localization.AtPrime (P.asIdeal.map (normMap φ hker)))
            (algebraMap _ (Localization.AtPrime (P.asIdeal.map (normMap φ hker)))
              (algebraMap S (integralClosure S (FractionRing S)) (φ x))) := by
    rintro Q _ rfl E' hE'
    rw [← ord_ringEquiv (R := Localization.AtPrime P.asIdeal)
      (S := Localization.AtPrime (P.asIdeal.map (normMap φ hker))) E', hE', normMap_algebraMap]
  exact key _ hcm E hE

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets

open scoped ENNReal

noncomputable section

theorem finsum_const_mul_ofReal {α : Type*} (c : ℝ≥0∞) (hc : c ≠ 0) (g : α → ℝ) (hg : ∀ x, 0 ≤ g x) :
    ∑ᶠ x, c * ENNReal.ofReal (g x) = c * ENNReal.ofReal (∑ᶠ x, g x) := by
  have hsupp : (Function.support fun x => c * ENNReal.ofReal (g x)) = Function.support g := by
    ext x
    simp only [Function.mem_support, ne_eq, mul_eq_zero, hc, false_or, ENNReal.ofReal_eq_zero, not_le]
    exact ⟨fun h => h.ne', fun h => lt_of_le_of_ne (hg x) (Ne.symm h)⟩
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum _ hfin, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp [hsupp]),
      ← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun i _ => hg i]
  · rw [finsum_of_infinite_support hfin, finsum_of_infinite_support (by rwa [hsupp]),
      ENNReal.ofReal_zero, mul_zero]

theorem gramVol_zero_map {e n : ℕ} (y : Fin e → ℂ) :
    gramVol (fun _ : Fin e → ℂ => (0 : Fin n → ℂ)) y = 0 := by
  have hw : (Fin.cons (0 : Fin n → ℂ) (fun _ : Fin e => (0 : Fin n → ℂ)) : Fin (e + 1) → Fin n → ℂ) = 0 := by
    ext a i
    refine Fin.cases ?_ (fun j => ?_) a <;> simp
  have hM0 : (Matrix.of fun _ _ => (0 : ℂ) : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) = 0 := rfl
  simp [gramVol, hw, hM0, Matrix.det_zero]

theorem lintegral_line_gram_abs {n : ℕ} (e : ℕ) (h : HermNorm n) (w : (Fin n → ℂ) → ℝ)
    (hw : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → w (t • x) = w x) (x : Fin n → ℂ) (hx : x ≠ 0) (G : ℝ)
    (hG : 0 ≤ G) :
    ∫⁻ t : ℂ, ENNReal.ofReal ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
          (fun z => |w (h.pointOf z)|) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x))) *
        ENNReal.ofReal (‖t‖ ^ (2 * e) * G) =
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
        (|w x| * ((e.factorial : ℝ) / Real.pi ^ e * G / h.dualNorm x ^ (2 * (e + 1))))) := by
  have hg : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → (fun x => |w x|) (t • x) = (fun x => |w x|) x :=
    fun t x ht => by simp only [hw t x ht]
  have key := integral_line_gram e h (fun x => |w x|) hg x hx G
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det
  have hinv : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  set ρ := ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ with hρ_def
  have hρ : 0 < ρ := by
    rw [hρ_def, norm_pos_iff]
    intro h0
    apply hx
    rw [← hinv, show (h.matᵀ)⁻¹ *ᵥ x = 0 by simpa using congrArg WithLp.ofLp h0, Matrix.mulVec_zero]
  have hpt : ∀ t : ℂ, h.pointOf (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) = t • x := by
    intro t
    have : (fun i => (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) i) = t • ((h.matᵀ)⁻¹ *ᵥ x) := by
      ext i
      simp
    simp only [HermNorm.pointOf, this, Matrix.mulVec_smul, hinv]
  have hae : (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => |w (h.pointOf z)|) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) =ᵐ[volume]
      fun t => (|w x| * G) * (ball (0 : ℂ) (1 / ρ)).indicator (fun t => ‖t‖ ^ (2 * e)) t := by
    have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with t ht
    have hiff : ‖t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ < 1 ↔ ‖t‖ < 1 / ρ := by
      rw [norm_smul, lt_div_iff₀ hρ]
    by_cases hb : ‖t‖ < 1 / ρ
    · rw [indicator_of_mem (mem_ball_zero_iff.2 (hiff.2 hb)),
        indicator_of_mem (mem_ball_zero_iff.2 hb), hpt, hw t x ht]
      ring
    · rw [indicator_of_notMem (fun h => hb (hiff.1 (mem_ball_zero_iff.1 h))),
        indicator_of_notMem (fun h => hb (mem_ball_zero_iff.1 h))]
      ring
  have hint : Integrable (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => |w (h.pointOf z)|) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) := by
    refine (((integrable_indicator_iff measurableSet_ball).2 ?_).const_mul (|w x| * G)).congr hae.symm
    exact ((continuous_norm.pow _).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) (1 / ρ))).mono_set ball_subset_closedBall
  have hfun : (fun t : ℂ => ENNReal.ofReal ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => |w (h.pointOf z)|) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x))) *
        ENNReal.ofReal (‖t‖ ^ (2 * e) * G)) = fun t => ENNReal.ofReal
        ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => |w (h.pointOf z)|)
          (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) :=
    funext fun t => (ENNReal.ofReal_mul (indicator_nonneg (fun _ _ => abs_nonneg _) _)).symm
  rw [hfun, ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t =>
    mul_nonneg (indicator_nonneg (fun _ _ => abs_nonneg _) _) (by positivity))]
  exact congrArg ENNReal.ofReal key

theorem sheetSum_lintegral_eq {n e : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (w : (Fin n → ℂ) → ℝ)
    (hw : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → w (t • x) = w x) (y : Fin (e + 1) → ℂ) :
    (∑ᶠ x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y, ∫⁻ t : ℂ,
      ENNReal.ofReal ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => |w (h.pointOf z)|)
        (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y))) *
      ENNReal.ofReal (‖t‖ ^ (2 * (e + 1)) * gramVol (fun y' =>
        (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y)) =
    ENNReal.ofReal (Real.pi ^ (e + 1 + 1) / ((e + 1 + 1).factorial : ℝ)) *
      ENNReal.ofReal (chartAbsDens (J ⊔ Ideal.span {linForm ℓ - 1}) A w
        (fun _ x => Real.log (h.dualNorm x)) y) := by
  have hc : ENNReal.ofReal (Real.pi ^ (e + 1 + 1) / ((e + 1 + 1).factorial : ℝ)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  unfold chartAbsDens sheetSum
  rw [finsum_mem_def, finsum_mem_def, ← finsum_const_mul_ofReal _ hc _
    (fun x => indicator_nonneg (fun x _ => by dsimp only; split_ifs; exacts [abs_nonneg _, le_rfl]) x)]
  refine finsum_congr fun x => ?_
  by_cases hx : x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y
  · rw [indicator_of_mem hx, indicator_of_mem hx]
    by_cases hs : ∃ s, IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A x s
    · have hsT : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x = hs.choose := by
        unfold sheetThrough; rw [dite_eq_left hs]
      obtain ⟨-, -, -, -, hsx, -⟩ := hs.choose_spec
      have hy : hs.choose y = x := by rw [← hx.2]; exact hsx
      have hx0 : x ≠ 0 := by
        rintro rfl
        have hmem := hx.1 (linForm ℓ - 1) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        simp [linForm] at hmem
      have hG := gramVol_nonneg (fun y' => (h.matᵀ)⁻¹ *ᵥ hs.choose y') y
      have hd : 0 ≤ h.dualNorm x ^ (2 * (e + 1 + 1)) :=
        pow_nonneg (by unfold HermNorm.dualNorm; positivity) _
      have hm := maDens_log_dualNorm_sheet h J ℓ A y x hs.choose hx hs.choose_spec
      beta_reduce at hm
      rw [dite_eq_left hs, hsT, hy, lintegral_line_gram_abs (e + 1) h w hw x hx0 _ hG]
      beta_reduce
      rw [hm, abs_mul,
        abs_of_nonneg (div_nonneg (mul_nonneg (by positivity) hG) hd),
        ← ENNReal.ofReal_mul (by positivity)]
    · have hsT : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x = 0 := by
        unfold sheetThrough; rw [dite_eq_right hs]
      rw [dite_eq_right hs, hsT]
      simp only [Pi.zero_apply, Matrix.mulVec_zero, gramVol_zero_map, mul_zero, ENNReal.ofReal_zero,
        lintegral_zero]
  · simp [indicator_of_notMem hx]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem StokesOnChart.proof (hD : ComplexSets.DiscriminantCover.Statement) (hL : CutOffLimit.Statement) :
    StokesOnChart.Statement := by
  have key : ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
      (f g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ), J.IsPrime →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
      SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      HasCompactSupport f → chartInt J A f (vecCons g φ) = chartInt J A g (vecCons f φ) := by
    intro n d J A f g φ hJ hdim hAf hf hg hφ hc
    obtain ⟨P, hP0, hPcov⟩ := hD n (d + 1) J A hJ hdim hAf

    have hsheet : ∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → ∃ s, IsSheetAt J A x s := by
      intro x hx hPx
      obtain ⟨-, -, hloc⟩ := hPcov (A *ᵥ x) hPx
      obtain ⟨U, V, s, hU, hyU, hV, hxV, hs, hsy, hAs, hZV⟩ := hloc x ⟨hx, rfl⟩
      refine ⟨s, U, hU, hyU, hs, hsy, fun w hw => ⟨hAs w hw, ?_⟩, V, hV.mem_nhds hxV, ?_⟩
      · have hw' : s w ∈ zeroSet J ∩ V := hZV ▸ Set.mem_image_of_mem s hw
        exact hw'.1
      · rintro x' hx' -
        rw [hZV] at hx'
        obtain ⟨w, hw, rfl⟩ := hx'
        rw [hAs w hw]
    obtain ⟨χ, hχs, hχU, hlim⟩ := hL n d J A P hJ hdim hAf hP0
    obtain ⟨h1, h2⟩ := hlim f g φ hf hg hφ hc
    refine tendsto_nhds_unique h1 (Tendsto.congr (fun k => ?_) h2)
    obtain ⟨U, hU, hDU, hχ0⟩ := hχU k
    obtain ⟨V, hV, hZV, hfV⟩ := hf
    have hcχ : HasCompactSupport (fun x => χ k x * f x) := hc.mul_left (f := χ k)
    refine (StokesOffDiscriminant.proof n d J A P hJ hdim hAf hP0 hsheet (fun x => χ k x * f x) g φ
      ⟨V, hV, hZV, (hχs k).contDiffOn.mul hfV⟩ hg hφ hcχ ⟨U, hU, hDU, fun x hx => ?_⟩).symm
    rw [hχ0 x hx, zero_mul]
  intro n d J A f g φ hJ hdim hAf hf hg hφ hc
  rcases hc with hc | hc
  · exact key n d J A f g φ hJ hdim hAf hf hg hφ hc
  · exact (key n d J A g f φ hJ hdim hAf hg hf hφ hc).symm

end GroundTheory.Heights₂.Heights
end
