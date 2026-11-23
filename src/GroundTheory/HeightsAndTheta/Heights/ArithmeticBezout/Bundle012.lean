module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle002
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle005
public import Mathlib.Analysis.CStarAlgebra.Classes
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
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
public import Mathlib.Data.ENat.BigOperators
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.Height
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

def matGauss {m n : ℕ} (π : Fin m → Fin n → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-∑ i, ∑ j, ‖π i j‖ ^ 2))

def ConeFibreAverage.Statement : Prop :=
  ∀ n m : ℕ, ∃ K : ℝ≥0∞, 0 < K ∧ K < ⊤ ∧
    ∀ (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J →
      (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
        ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
            ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
          K * Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J}

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

def ConeLocalMass.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
      ∀ R : ℝ, Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (coneSet h J ∩ Metric.ball 0 R) < ⊤

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace SectionLengthSum

theorem prime_between {A : Type*} [CommRing A] [IsNoetherianRing A] {J W Q : Ideal A} {f : A}
    (hWP : ∀ P ∈ J.minimalPrimes, P ≤ W → W ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    [hQ : Q.IsPrime] (hJQ : J ≤ Q) (hQW : Q ≤ W) : Q ∈ J.minimalPrimes ∨ Q = W := by
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hJQ
  have hPp : P.IsPrime := hP.1.1
  rcases eq_or_lt_of_le hPQ with h | hlt
  · exact Or.inl (h ▸ hP)
  rcases eq_or_lt_of_le hQW with h | hlt2
  · exact Or.inr h
  exfalso
  have hW := hWP P hP (hPQ.trans hQW)
  have hWp : W.IsPrime := hW.1.1
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  set g := Ideal.Quotient.mk P
  have hsurj : Function.Surjective g := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker g = P := Ideal.mk_ker
  have hcm : ∀ I : Ideal A, P ≤ I → (I.map g).comap g = I := fun I hI => by
    rw [Ideal.comap_map_of_surjective g hsurj, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hI]
  have : (Q.map g).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rw [hker]; exact hPQ)
  have : (W.map g).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rw [hker]; exact hPQ.trans hQW)
  have : (W.map g).FiniteHeight := ⟨Or.inr (h1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
  have : (Q.map g).FiniteHeight :=
    ⟨Or.inr ((Ideal.height_mono (Ideal.map_mono hQW)).trans_lt (h1.trans_lt (WithTop.coe_lt_top 1))).ne⟩
  have hbot : (⊥ : Ideal (A ⧸ P)) < Q.map g := by
    refine lt_of_le_of_ne bot_le fun h => hlt.ne ?_
    rw [← hcm Q hPQ, ← h, ← RingHom.ker_eq_comap_bot, hker]
  have hQW' : Q.map g < W.map g := by
    refine lt_of_le_of_ne (Ideal.map_mono hQW) fun h => hlt2.ne ?_
    rw [← hcm Q hPQ, h, hcm W (hPQ.trans hQW)]
  have h2 := Ideal.height_strict_mono_of_isPrime_of_isPrime hQW'
  have h3 := Ideal.height_strict_mono_of_isPrime_of_isPrime (I := ⊥) hbot
  have h4 : (Q.map g).height < 1 := h2.trans_le h1
  rw [Order.lt_one_iff] at h4
  rw [h4] at h3
  exact absurd h3 (not_lt_of_ge bot_le)

theorem length_ne_top_of_mem_minimalPrimes {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (I : Ideal B) (hI : IsLocalRing.maximalIdeal B ∈ I.minimalPrimes) : Module.length B (B ⧸ I) ≠ ⊤ := by
  have : IsArtinianRing (B ⧸ I) := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI
  have : IsArtinian B (B ⧸ I) := isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  exact Module.length_ne_top

theorem proof (hLoc : LocalSectionLengthSum.Statement) : SectionLengthSum.Statement := by
  intro A _ _ J W f hJ hf hW hWP
  classical
  have hWp : W.IsPrime := hW.1.1
  let B := Localization.AtPrime W
  let φ := algebraMap A B
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing W.primeCompl B inferInstance
  have hmin : ∀ Q : Ideal B, Q ∈ (J.map φ).minimalPrimes ↔ Q.comap φ ∈ J.minimalPrimes := fun Q => by
    rw [IsLocalization.minimalPrimes_map W.primeCompl B J]
    rfl
  have hcomapW : ∀ Q : Ideal B, Q.IsPrime → Q.comap φ ≤ W := fun Q hQ x hx => by
    by_contra hxW
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.map_units B (⟨x, hxW⟩ : W.primeCompl)))
  have hmapcomap : ∀ Q : Ideal B, (Q.comap φ).map φ = Q := fun Q =>
    IsLocalization.map_under W.primeCompl B Q
  have hcomapmap : ∀ P : Ideal A, P.IsPrime → P ≤ W → (P.map φ).comap φ = P := fun P hP hPW =>
    IsLocalization.under_map_of_isPrime_disjoint W.primeCompl B hP
      (Set.disjoint_left.mpr fun x hx hxP => hx (hPW hxP))
  have hJ' : (J.map φ).IsRadical := by
    show (J.map φ).radical ≤ J.map φ
    rw [← IsLocalization.map_radical W.primeCompl B J, hJ.radical]
  have hf' : ∀ Q ∈ (J.map φ).minimalPrimes, φ f ∉ Q := fun Q hQ hfQ => hf _ ((hmin Q).1 hQ) hfQ
  have hdim : ∀ Q : Ideal B, Q.IsPrime → J.map φ ≤ Q →
      Q ∈ (J.map φ).minimalPrimes ∨ Q = IsLocalRing.maximalIdeal B := by
    intro Q hQ hJQ
    have : (Q.comap φ).IsPrime := hQ.comap φ
    rcases prime_between hWP (Ideal.map_le_iff_le_comap.mp hJQ) (hcomapW Q hQ) with h | h
    · exact Or.inl ((hmin Q).2 h)
    · right
      rw [← hmapcomap Q, h]
      exact IsLocalization.AtPrime.map_eq_maximalIdeal W B
  have key := hLoc B (J.map φ) (φ f) hJ' hf' hdim
  have hsup : ∀ I : Ideal A, (I ⊔ Ideal.span {f}).map φ = I.map φ ⊔ Ideal.span {φ f} := fun I => by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hlm : ∀ I : Ideal A, localMult (I ⊔ Ideal.span {f}) W =
      (Module.length B (B ⧸ (I.map φ ⊔ Ideal.span {φ f}))).toNat := fun I => by
    unfold localMult
    rw [dite_eq_left hWp, hsup]
  have hfW : φ f ∈ IsLocalRing.maximalIdeal B := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W B]
    exact Ideal.mem_map_of_mem φ (hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))
  have hfin : ∀ Q ∈ (J.map φ).minimalPrimes,
      Module.length B (B ⧸ (Q ⊔ Ideal.span {φ f})) ≠ ⊤ := by
    intro Q hQ
    refine length_ne_top_of_mem_minimalPrimes _ ⟨⟨(IsLocalRing.maximalIdeal.isMaximal B).isPrime,
      sup_le (IsLocalRing.le_maximalIdeal hQ.1.1.ne_top) ((Ideal.span_singleton_le_iff_mem _).mpr hfW)⟩,
      fun Q₂ hQ₂ _ => ?_⟩
    rcases hdim Q₂ hQ₂.1 (hQ.1.2.trans (le_sup_left.trans hQ₂.2)) with h | h
    · exact absurd (hQ₂.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))) (hf' Q₂ h)
    · exact h.ge
  rw [hlm J, key, ENat.toNat_sum (fun Q hQ => hfin Q ((Set.Finite.mem_toFinset _).mp hQ))]
  symm
  refine Finset.sum_nbij' (fun P => P.map φ) (fun Q => Q.comap φ) ?_ ?_ ?_ ?_ ?_
  · intro P hP
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hP
    rw [Set.Finite.mem_toFinset, hmin, hcomapmap P hP.1.1.1 hP.2]
    exact hP.1
  · intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨(hmin Q).1 hQ, hcomapW Q hQ.1.1⟩
  · intro P hP
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hP
    exact hcomapmap P hP.1.1.1 hP.2
  · intro Q _
    exact hmapcomap Q
  · intro P _
    exact hlm P

end SectionLengthSum

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open scoped InnerProductSpace
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (maDensity cxHessian)

theorem ChartGramMA.proof : ChartGramMA.Statement := by
  intro e n v y hv h0

  obtain ⟨t, ht, hto, hyt⟩ := eventually_nhds_iff.1 hv
  have han : AnalyticOnNhd ℂ v t := by
    have hd : DifferentiableOn ℂ v t := fun y' hy' => (ht y' hy').differentiableWithinAt
    exact AnalyticOnNhd.pi fun j =>
      ReciprocityTheory.AnForm.Osgood.osgood e t _ hto (differentiableOn_pi.mp hd j)
  set L := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm with hL
  set u : (Fin e → ℂ) → EuclideanSpace ℂ (Fin n) := fun y' => L (v y') with hu_def
  have hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y' := by
    filter_upwards [hto.mem_nhds hyt] with y' hy'
    exact (L : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).analyticAt _ |>.comp (han y' hy')
  have hu0 : u y ≠ 0 := by
    simpa [hu_def, hL, PiLp.coe_symm_continuousLinearEquiv] using h0
  have hDu : ∀ b, fderiv ℂ u y b = L (fderiv ℂ v y b) := fun b => by
    have hc := (L : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).hasFDerivAt.comp y
      (hv.self_of_nhds).hasFDerivAt
    have hc' : HasFDerivAt u _ y := hc
    rw [hc'.fderiv]
    rfl

  have hφ : (fun (_ : Fin e) (y' : Fin e → ℂ) => Real.log ‖WithLp.toLp 2 (v y')‖) =
      fun _ y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re := by
    funext _ y'
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) (u y')
    have h' : (⟪u y', u y'⟫_ℂ).re = ‖u y'‖ ^ 2 := h
    rw [h', Real.log_pow]
    simp [hu_def, hL]

  set w : Fin (e + 1) → EuclideanSpace ℂ (Fin n) :=
    Fin.cons (u y) fun j => fderiv ℂ u y (Pi.single j 1) with hw
  set G : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := Matrix.of fun a b => ⟪w a, w b⟫_ℂ with hG_def
  have hmat : G = Matrix.of fun a b => ∑ i,
      star ((Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) a i) *
        (Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) b i := by
    ext a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
      simp only [hG_def, hw, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, hDu] <;>
      simp only [PiLp.inner_apply, RCLike.inner_apply'] <;>
      simp [hu_def, hL]
  have hgram : gramVol v y = G.det.re := by
    rw [hmat]; rfl
  have hG00 : G 0 0 ≠ 0 := by
    simpa [hG_def, hw] using hu0
  have hcx : cxHessian (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y =
      (2 * G 0 0)⁻¹ • Matrix.transpose (Matrix.of fun i j : Fin e =>
        G i.succ j.succ - G i.succ 0 * G 0 j.succ / G 0 0) := by
    ext i j
    rw [ChartGram.cxHessian_half_log hu hu0]
    simp only [hG_def, hw, Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Fin.cons_zero, Fin.cons_succ, smul_eq_mul]
    have : ⟪u y, u y⟫_ℂ ≠ 0 := by simpa [hG_def, hw] using hG00
    field_simp
  have hS := ChartGram.det_eq_corner_mul_schur G hG00
  have hN : G 0 0 = ((‖u y‖ ^ 2 : ℝ) : ℂ) := by
    simp [hG_def, hw]
  have hNpos : 0 < ‖u y‖ := norm_pos_iff.2 hu0
  unfold maDensity
  rw [hφ, ChartGram.mixedDisc_const, hcx, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin,
    hgram, hS]
  generalize (Matrix.of fun i j : Fin e => G i.succ j.succ - G i.succ 0 * G 0 j.succ / G 0 0).det = Z
  rw [hN]
  have hnorm : ‖WithLp.toLp 2 (v y)‖ = ‖u y‖ := rfl
  rw [hnorm]
  generalize ‖u y‖ = r at hNpos ⊢
  rw [show ((2 : ℂ) * ((r ^ 2 : ℝ) : ℂ))⁻¹ ^ e = (((2 * r ^ 2)⁻¹ ^ e : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul, pow_mul]
  have hpi : Real.pi ^ e * Real.pi⁻¹ ^ e = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ Real.pi_ne_zero, one_pow]
  have hr : r ^ (e * 2) * r⁻¹ ^ (e * 2) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hNpos.ne', one_pow]
  have h2 : (1 / 2 : ℝ) ^ e * 2 ^ e = 1 := by
    rw [← mul_pow]; norm_num
  field_simp
  linear_combination (r ^ 2 * Z.re * r ^ (e * 2) * r⁻¹ ^ (e * 2) * (1 / 2) ^ e * 2 ^ e) * hpi +
    (r ^ 2 * Z.re * (1 / 2) ^ e * 2 ^ e) * hr + (r ^ 2 * Z.re) * h2

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

def ConeMapArea.Statement : Prop :=
  ∀ (n e : ℕ) (ι : Type) [Countable ι] (U D : ι → Set (Fin e → ℂ))
    (v : ι → (Fin e → ℂ) → (Fin n → ℂ)) (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞),
    (∀ i, IsOpen (U i) ∧ MeasurableSet (D i) ∧ D i ⊆ U i ∧ DifferentiableOn ℂ (v i) (U i)) →
    Set.InjOn (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1))
      {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0} →
    Measurable F →
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
          ∫⁻ y in (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
              {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0}, F y
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0} *
          ∑' i, ∫⁻ x in D i, ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v i x)) *
            ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (v i) x)

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

def ConeMapAreaOne.Statement : Prop :=
  ∀ (n e : ℕ) (U D : Set (Fin e → ℂ)) (v : (Fin e → ℂ) → (Fin n → ℂ))
    (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞),
    IsOpen U → MeasurableSet D → D ⊆ U → DifferentiableOn ℂ v U →
    Set.InjOn (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1)) {q | q.1 ∈ D ∧ q.2 ≠ 0} →
    Measurable F →
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
          ∫⁻ y in (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1)) ''
              {q | q.1 ∈ D ∧ q.2 ≠ 0}, F y
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0} *
          ∫⁻ x in D, ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v x)) *
            ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol v x)

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Helpers

variable {F : Type*} [Field F] {n k : ℕ}

theorem incidence_mono {I W : Ideal (MvPolynomial (Fin n) F)} (hIW : I ≤ W)
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence W k) : u ∈ incidence I k := by
  obtain ⟨x, hx0, hxW, hxu⟩ := hu
  exact ⟨x, hx0, fun g hg => hxW g (hIW hg), hxu⟩

theorem exists_relComps_of_mem_incidence {J : Ideal (MvPolynomial (Fin n) F)}
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence J k) :
    ∃ W ∈ relComps J, u ∈ incidence W k := by
  obtain ⟨x, hx0, hxJ, hxu⟩ := hu
  let φ : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F := aeval x
  have hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have hJP : J ≤ RingHom.ker φ := fun g hg => RingHom.mem_ker.mpr (hxJ g hg)
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hJP
  refine ⟨W, ⟨hW, ?_⟩, x, hx0, fun g hg => RingHom.mem_ker.mp (hWP hg), hxu⟩
  by_contra hrel
  apply hx0
  funext j
  have hj : X j ∈ W := by
    by_contra hj
    exact hrel ⟨j, hj⟩
  have := RingHom.mem_ker.mp (hWP hj)
  simpa [φ] using this

theorem mem_support_fundCycle_iff {J : Ideal (MvPolynomial (Fin n) F)} (hJ : J.IsRadical)
    {W : Ideal (MvPolynomial (Fin n) F)} : W ∈ (fundCycle J).support ↔ W ∈ relComps J := by
  classical
  rw [Finsupp.mem_support_iff]
  unfold fundCycle
  rw [Finsupp.onFinset_apply]
  constructor
  · intro h
    by_contra h'
    exact h (if_neg h')
  · intro h
    rw [if_pos h, localMult_eq_one_of_isRadical hJ h.1]
    exact one_ne_zero

end Helpers

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChowFormBirationalAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F))
    (g : MvPolynomial (Fin (k + 1) × Fin n) F) (c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P)),
    IsProjPrime P → IsChowForm P (k + 1) g → ∑ j, c j * genPt P j = 1 →
      ∃ t : Fin n → F, (∑ l, C (t l) * pderiv (0, l) g) ∉ incIdeal P (k + 1) ∧
        ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) *
              C (∑ l, algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (t l) * genPt P l) =
            aeval (genSubst (genPt P) c) (∑ l, C (t l) * pderiv (0, l) g) * C (genPt P m)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def IncIdealSeparate.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (P Q : Ideal (MvPolynomial (Fin n) F)),
    IsProjPrime P → IsProjPrime Q → incIdeal Q k ≠ ⊥ → incIdeal Q k ≤ incIdeal P k → Q ≤ P

end

end GroundTheory.Heights₂.Heights
end
