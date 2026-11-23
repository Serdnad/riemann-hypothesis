module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle057
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsHomogeneousGrL
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Veronese

theorem pair_eq {D : ℕ} {i j k l : Fin (D + 1)} (hij : i ≤ j) (hkl : k ≤ l)
    (h : (Finsupp.single i 1 + Finsupp.single j 1 : Fin (D + 1) →₀ ℕ) = Finsupp.single k 1 + Finsupp.single l 1) :
    i = k ∧ j = l := by
  have hm : ({i} + {j} : Multiset (Fin (D + 1))) = {k} + {l} := by
    have := congrArg Finsupp.toMultiset h
    simpa only [map_add (f := _), Finsupp.toMultiset_single, one_nsmul] using this
  have h1 : i = k ∨ i = l := by
    have : i ∈ ({k} + {l} : Multiset (Fin (D + 1))) := hm ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self i))
    simpa using this
  have h2 : j = k ∨ j = l := by
    have : j ∈ ({k} + {l} : Multiset (Fin (D + 1))) := hm ▸ Multiset.mem_add.2 (Or.inr (Multiset.mem_singleton_self j))
    simpa using this
  have h3 : k = i ∨ k = j := by
    have : k ∈ ({i} + {j} : Multiset (Fin (D + 1))) := hm.symm ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self k))
    simpa using this
  have h4 : l = i ∨ l = j := by
    have : l ∈ ({i} + {j} : Multiset (Fin (D + 1))) := hm.symm ▸ Multiset.mem_add.2 (Or.inr (Multiset.mem_singleton_self l))
    simpa using this
  rw [Fin.le_iff_val_le_val] at hij hkl
  simp only [Fin.ext_iff] at h1 h2 h3 h4 ⊢
  omega

theorem exponent_injective (D : ℕ) :
    Function.Injective fun q : Ix (Idx D) =>
      (Finsupp.single q.2.1.1 1 + Finsupp.single q.2.1.2 1 : Fin (D + 1) →₀ ℕ) := by
  intro q q' h
  obtain ⟨u, ⟨⟨i, j⟩, hij⟩⟩ := q
  obtain ⟨u', ⟨⟨k, l⟩, hkl⟩⟩ := q'
  obtain ⟨rfl, rfl⟩ := pair_eq hij hkl h
  cases u
  cases u'
  rfl

def polyMap (D : ℕ) : MvPolynomial (Fin (D + 1)) ℤ →+* Fld D :=
  (algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Fld D)).comp (MvPolynomial.map (Int.castRingHom ℚ))

theorem polyMap_injective (D : ℕ) : Function.Injective (polyMap D) :=
  (IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Fld D)).comp
    (MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ)))

theorem x_linearIndependent (D : ℕ) : LinearIndependent ℤ (x D) := by
  have hmono : LinearIndependent ℤ fun q : Ix (Idx D) =>
      (X q.2.1.1 * X q.2.1.2 : MvPolynomial (Fin (D + 1)) ℤ) := by
    have h := (basisMonomials (Fin (D + 1)) ℤ).linearIndependent.comp _ (exponent_injective D)
    have e : (fun q : Ix (Idx D) => (X q.2.1.1 * X q.2.1.2 : MvPolynomial (Fin (D + 1)) ℤ)) =
        ⇑(basisMonomials (Fin (D + 1)) ℤ) ∘ fun q : Ix (Idx D) =>
          (Finsupp.single q.2.1.1 1 + Finsupp.single q.2.1.2 1 : Fin (D + 1) →₀ ℕ) := by
      funext q
      simp only [Function.comp_apply, coe_basisMonomials, X, monomial_mul, mul_one]
    rw [e]
    exact h
  have h2 := hmono.map' (polyMap D).toAddMonoidHom.toIntLinearMap
    (LinearMap.ker_eq_bot.mpr (polyMap_injective D))
  have e2 : x D = ⇑(polyMap D).toAddMonoidHom.toIntLinearMap ∘ fun q : Ix (Idx D) =>
      (X q.2.1.1 * X q.2.1.2 : MvPolynomial (Fin (D + 1)) ℤ) := by
    funext q
    simp [x, t, polyMap, map_mul]
  rw [e2]
  exact h2

theorem isSmoothMetric_metric (D : ℕ) : IsSmoothMetric (metric D) := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scale D) :=
    contDiff_pi.2 fun q => contDiff_const.mul (contDiff_apply ℝ (fun _ => ℂ) q)
  exact (ProjLine.isSmoothMetric_fs (J := Ix (Idx D))).comp hs.contDiffOn fun z hz => scale_ne_zero hz

theorem isConjInvariant_metric (D : ℕ) : IsConjInvariant (metric D) := by
  intro z
  have h : scale D (fun q => conj (z q)) = fun q => conj (scale D z q) := by
    funext q
    simp [scale, map_mul, Complex.conj_ofReal]
  show (fsMetric (ι := Ix (Idx D))).ρ (scale D _) = (fsMetric (ι := Ix (Idx D))).ρ (scale D z)
  rw [h]
  exact ProjLine.isConjInvariant_fs (scale D z)

theorem eval_smul_homog {ι : Type*} {φ : MvPolynomial ι ℂ} {n : ℕ} (hφ : φ.IsHomogeneous n) (c : ℂ)
    (z : ι → ℂ) : eval (c • z) φ = c ^ n * eval z φ := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra h
    exact (mem_support_iff.mp hd) (hφ.coeff_eq_zero h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hs : d.degree = ∑ i ∈ d.support, d i := rfl
  rw [← hdeg, hs]
  ring

theorem pairVal_smul {D n : ℕ} {b b' : MvPolynomial (Ix (Idx D)) ℚ}
    (hb : ∃ f : MvPolynomial (Ix (Idx D)) ℤ, f.IsHomogeneous n ∧ b = MvPolynomial.map (Int.castRingHom ℚ) f)
    (hb' : ∃ f : MvPolynomial (Ix (Idx D)) ℤ, f.IsHomogeneous n ∧ b' = MvPolynomial.map (Int.castRingHom ℚ) f)
    (c : ℂ) (z : Ix (Idx D) → ℂ) (hc : c ≠ 0) :
    pairVal (metric D) n b b' (c • z) = pairVal (metric D) n b b' z := by
  obtain ⟨f, hf, rfl⟩ := hb
  obtain ⟨f', hf', rfl⟩ := hb'
  unfold pairVal
  rw [eval_smul_homog ((hf.map _).map _), eval_smul_homog ((hf'.map _).map _), (metric D).smul]
  have key : c ^ n * conj (c ^ n) = (((‖c‖ ^ (2 * n) : ℝ)) : ℂ) := by
    rw [map_pow, ← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hK : (((‖c‖ ^ (2 * n) : ℝ)) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
    exact_mod_cast (pow_pos this _).ne'
  have hL : ∀ A B : ℂ, A * c ^ n * conj (B * c ^ n) = (((‖c‖ ^ (2 * n) : ℝ)) : ℂ) * (A * conj B) := by
    intro A B
    rw [← key, map_mul]
    ring
  rw [mul_comm (c ^ n), mul_comm (c ^ n), hL, mul_pow]
  push_cast
  exact mul_div_mul_left _ _ (by exact_mod_cast hK)

end Veronese

open Veronese

theorem SecondVeronese.proof (hA : VeroneseArith.Statement) (hS : VeroneseSemipos.Statement)
    (hR : VeroneseResolution.Statement) (hC : VeroneseChi.Statement) (hT : VeroneseTop.Statement)
    (hG : VeroneseGenDeg.Statement) : SecondVeronese.Statement := by
  intro D hD
  obtain ⟨J, R, meas, borel, dV, hvol, htr⟩ := hR D hD
  let d : HSMDatum D (Fld D) (Idx D) :=
    { x := x D, m := metric D, P0 := ⊥, J := J, R := R, meas := meas, borel := borel, dV := dV,
      one_le := hD, arith := hA D hD, indep := x_linearIndependent D, smooth := isSmoothMetric_metric D,
      conjInv := isConjInvariant_metric D, normalForm_baseLattice_le_dualSpan_sup_line := bot_le, semipos := hS D, vol := hvol }
  refine ⟨Fld D, inferInstance, inferInstance, Idx D, inferInstance, d, fun n => ?_,
    fun I hI => hT D hD I hI, hG D hD⟩

  have hgram : ∀ {r : ℕ} (b : Fin r → MvPolynomial (Ix (Idx D)) ℚ),
      (∀ k, ∃ f : MvPolynomial (Ix (Idx D)) ℤ, f.IsHomogeneous n ∧ b k = MvPolynomial.map (Int.castRingHom ℚ) f) →
      resGram d n b = gram D n b := by
    intro r b hb
    ext k l
    have e1 := htr (fun z => pairVal (metric D) n (b k) (b l) z)
      (fun c z hc => pairVal_smul (hb k) (hb l) c z hc)
    have e2 := htr (fun z => pairVal (metric D) n (b k) (b l) (conjPt z)) fun c z hc => by
      have : conjPt (c • z) = conj c • conjPt z := by
        funext q
        simp [conjPt]
      simp only [this]
      exact pairVal_smul (hb k) (hb l) _ _ ((map_ne_zero _).mpr hc)
    unfold resGram gram resPt
    rw [e1, e2]
  rw [← hC D hD n]
  unfold resChi Veronese.chi
  split_ifs with h1
  · rw [hgram _ h1.choose_spec.1]
  · rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace MonomialShift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem exists_chart {y : (Σ k, ι k) → Ω} {d : ℕ} (hY : IsArithVar (mCoordIdeal y) d) :
    ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  have hrel := hY.2.1.2.2
  refine ⟨fun k => (hrel k).choose, fun k h0 => (hrel k).choose_spec ?_⟩
  change _ ∈ RingHom.ker _
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem norm_prod_le {P : Ideal (MRing ι)} {A : HermLine ι} {a : K → ℕ} (hM : MonomialsBounded P A a)
    (c : ∀ k, ι k) (j n : ℕ) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    ‖∏ k, z ⟨k, c k⟩ ^ (j * a k + n)‖ ≤ A.h z ^ j * (fsH ι).h z ^ n := by
  classical
  have e1 : ‖∏ k, z ⟨k, c k⟩ ^ (j * a k + n)‖ =
      (∏ k, ‖z ⟨k, c k⟩‖ ^ a k) ^ j * (∏ k, ‖z ⟨k, c k⟩‖) ^ n := by
    rw [norm_prod, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow]
    ring

  let μ : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p => if p.2 = c p.1 then a p.1 else 0
  have hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = a k := by
    intro k
    simp [μ]
  have hmon : ∏ p, z p ^ μ p = ∏ k, z ⟨k, c k⟩ ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [μ, pow_ite]
  have hA : ∏ k, ‖z ⟨k, c k⟩‖ ^ a k ≤ A.h z := by
    have := hM z hz μ hμ
    rw [hmon, norm_prod] at this
    simpa [norm_pow] using this
  have hH : ∏ k, ‖z ⟨k, c k⟩‖ ≤ (fsH ι).h z := by
    have hfs : (fsH ι).h z = ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
      rw [fsH, GroundTheory.Heights₂.Heights.Inter.ofMetrics_fs_h]
      simp
    rw [hfs]
    refine Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ (c k))
  rw [e1]
  gcongr
  exact pow_nonneg (A.pos z hz.1).le _

theorem isSmoothHerm_zcomb_fsH {A : HermLine ι} (hA : IsSmoothHerm A) (q : ℕ) :
    IsSmoothHerm (HermLine.zcomb A (fsH ι) q 1) := by
  have hH : IsSmoothHerm (fsH ι) := GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1
  have hfun : (HermLine.zcomb A (fsH ι) q 1).h = fun z => A.h z ^ q * (fsH ι).h z := by
    funext z
    change A.h z ^ ((q : ℕ) : ℤ) * (fsH ι).h z ^ (1 : ℤ) = _
    rw [zpow_natCast, zpow_one]
  unfold IsSmoothHerm at hA hH ⊢
  rw [hfun]
  exact (hA.pow q).mul hH

theorem proof (hPack : PackingStatement) : MonomialShift.Statement := by
  intro K _ ι _ Ω _ y D a A P0 q τ n hY hBir ha hP0 hsemi hM hq hτ
  classical
  obtain ⟨c, hc⟩ := exists_chart hY

  obtain ⟨e, he⟩ : ∃ e : K → ℕ, e = fun k => (q * n - τ) * a k + n := ⟨_, rfl⟩
  have hBa : ∀ k, (HermLine.zcomb A (fsH ι) q 1).a k = (q : ℤ) * a k + 1 := by
    intro k
    simp [HermLine.zcomb, fsH, HermLine.ofMetrics, ha]
  have hdeg : ∀ k, (n : ℤ) * (HermLine.zcomb A (fsH ι) q 1).a k = τ * A.a k + e k := by
    intro k
    rw [hBa, he]
    simp only [ha]
    push_cast [Nat.cast_sub hτ]
    ring

  obtain ⟨mv, hmv⟩ : ∃ mv : Ω, mv = ∏ k, y ⟨k, c k⟩ ^ e k := ⟨_, rfl⟩
  have hmv0 : mv ≠ 0 := by
    rw [hmv]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hmvx : aeval y (xpow c e) = mv := by
    simp [hmv, xpow]

  have hlat : ∀ s ∈ chartLatNm y A.a τ, mv * s ∈ chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n := by
    intro s hs c' hc'
    have h1 := hs c' hc'
    have h2 : ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ e k ∈ integralClosure (chartRingZ y c') Ω := by
      have hmem : ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ e k ∈ chartRingZ y c' :=
        Subalgebra.prod_mem _ fun k _ =>
          pow_mem (Algebra.subset_adjoin
            (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c' p.1⟩) ⟨k, c k⟩)) _
      exact (integralClosure (chartRingZ y c') Ω).algebraMap_mem ⟨_, hmem⟩
    have hsplit : ∀ k, y ⟨k, c' k⟩ ^ (-((n : ℤ) * (HermLine.zcomb A (fsH ι) q 1).a k)) =
        y ⟨k, c' k⟩ ^ (-((τ : ℤ) * A.a k)) * (y ⟨k, c' k⟩ ^ e k)⁻¹ := by
      intro k
      rw [hdeg k, neg_add, zpow_add₀ (hc' k), zpow_neg (y _) ((e k : ℕ) : ℤ), zpow_natCast]
    have key : mv * s * ∏ k, y ⟨k, c' k⟩ ^ (-((n : ℤ) * (HermLine.zcomb A (fsH ι) q 1).a k)) =
        (s * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * A.a k))) * ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ e k := by
      simp only [hsplit, div_eq_mul_inv, mul_pow, inv_pow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hmv]
      ring
    rw [key]
    exact mul_mem h1 h2

  have hsmall : ∀ s, IsSmallH (mCoordIdeal y) y A τ s →
      IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1) n (mv * s) := by
    intro s hs dg dh g h z hg hh hd hgh hz
    have hmh := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (isMultiHomog_xpow c e) hh
    have hb := hs dg (e + dh) g (xpow c e * h) z hg hmh
      (fun k => by have := hd k; have := hdeg k; simp only [Pi.add_apply]; push_cast; linarith)
      (by rw [hgh, map_mul, hmvx]; ring) hz
    have hApos : 0 < A.h z := A.pos z hz.1
    have hxz : eval z (map (Int.castRingHom ℂ) (xpow c e)) = ∏ k, z ⟨k, c k⟩ ^ ((q * n - τ) * a k + n) := by
      simp [xpow, he]
    have hBh : (HermLine.zcomb A (fsH ι) q 1).h z = A.h z ^ ((q : ℕ) : ℤ) * (fsH ι).h z ^ (1 : ℤ) := rfl
    calc ‖eval z (map (Int.castRingHom ℂ) g)‖
        ≤ ‖eval z (map (Int.castRingHom ℂ) (xpow c e * h))‖ * A.h z ^ τ := hb
      _ = ‖∏ k, z ⟨k, c k⟩ ^ ((q * n - τ) * a k + n)‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
          rw [map_mul, eval_mul, norm_mul, hxz]
      _ ≤ (A.h z ^ (q * n - τ) * (fsH ι).h z ^ n) * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
          gcongr
          exact norm_prod_le hM c (q * n - τ) n hz
      _ = ‖eval z (map (Int.castRingHom ℂ) h)‖ * (HermLine.zcomb A (fsH ι) q 1).h z ^ n := by
          rw [hBh, zpow_natCast, zpow_one, mul_pow, ← pow_mul,
            show A.h z ^ (q * n) = A.h z ^ (q * n - τ) * A.h z ^ τ by rw [← pow_add, Nat.sub_add_cancel hτ]]
          ring

  let f : {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} →
      {t : chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n //
        IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1) n (t : Ω)} :=
    fun s => ⟨⟨mv * s.1, hlat s.1 s.1.2⟩, hsmall s.1 s.2⟩
  have hinj : Function.Injective f := by
    intro s t hst
    have h := congrArg (fun u => ((u.1 : chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n) : Ω)) hst
    exact Subtype.ext (Subtype.ext (mul_left_cancel₀ hmv0 h))
  have hfin := (hPack K ι Ω y D (HermLine.zcomb A (fsH ι) q 1)
    (chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a) hY hBir (isSmoothHerm_zcomb_fsH hsemi.1 q)
    (fun _ => le_rfl)).1 n
  have : Finite {t : chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n //
      IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1) n (t : Ω)} := hfin.to_subtype
  have hcard := Nat.card_le_card_of_injective f hinj
  unfold smallSectionCount
  rcases Nat.eq_zero_or_pos (Nat.card {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)})
    with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

end MonomialShift

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

theorem SemiposTwist.proof : SemiposTwist.Statement := by
  intro K _ ι _ P0 P L p q hL
  set U : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hU
  have hUo : IsOpen U := by
    have e : U = ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
      ext z
      simp [hU]
    rw [e]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_iUnion fun i => (continuous_apply _).isOpen_preimage _ isOpen_ne
  have hH : IsSmoothHerm (fsH ι) := FsLineSmooth.proof K ι
  have hsm : IsSmoothHerm (HermLine.zcomb L (fsH ι) q p) := by
    have e : (HermLine.zcomb L (fsH ι) q p).h = fun z => L.h z ^ q * (fsH ι).h z ^ p := by
      funext z
      show L.h z ^ (q : ℤ) * (fsH ι).h z ^ (p : ℤ) = _
      rw [zpow_natCast, zpow_natCast]
    unfold IsSmoothHerm
    rw [e]
    exact (hL.1.pow q).mul (hH.pow p)
  refine ⟨hsm, fun z hz w hw => ?_⟩
  have hzU : z ∈ U := hz.1
  have hlog : ∀ A : HermLine ι, IsSmoothHerm A → ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z :=
    fun A hA => ((hA.contDiffAt (hUo.mem_nhds hzU)).of_le (WithTop.coe_le_coe.2 le_top)).log
      (A.pos z hzU).ne'
  have h1 := hlog L hL.1
  have h2 := hlog (fsH ι) hH
  have hev : (fun y => Real.log ((HermLine.zcomb L (fsH ι) q p).h y)) =ᶠ[𝓝 z]
      fun y => (0 + (q : ℝ) * Real.log (L.h y)) + (p : ℝ) * Real.log ((fsH ι).h y) := by
    filter_upwards [hUo.mem_nhds hzU] with y hy
    show Real.log (L.h y ^ (q : ℤ) * (fsH ι).h y ^ (p : ℤ)) = _
    rw [Real.log_mul (zpow_pos (L.pos y hy) _).ne' (zpow_pos ((fsH ι).pos y hy) _).ne',
      Real.log_zpow, Real.log_zpow]
    push_cast
    ring
  have hLz : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log (L.h y)) z w := hL.2 z hz w hw
  have hHz : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log ((fsH ι).h y)) z w :=
    FsLineLevi.proof K ι z w hzU
  have e1 := ReciprocityTheory.AnForm.levi_add_smul (f := fun y => 0 + (q : ℝ) * Real.log (L.h y))
    (g := fun y => Real.log ((fsH ι).h y)) (p : ℝ) (contDiffAt_const.add (contDiffAt_const.mul h1)) h2 w
  have e2 := ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => (0 : ℝ))
    (g := fun y => Real.log (L.h y)) (q : ℝ) contDiffAt_const h1 w
  have hl0 : ReciprocityTheory.AnForm.levi (fun _ => (0 : ℝ)) z w = 0 := by simp [ReciprocityTheory.AnForm.levi]
  change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
  rw [ReciprocityTheory.AnForm.levi_congr hev, e1, e2, hl0]
  have a1 := mul_nonneg (Nat.cast_nonneg (α := ℝ) q) hLz
  have a2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) p) hHz
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

section Objects

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

def blockForms {κ : Type} (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) : (Σ k, GlobalTheory κ k) → MRing ι :=
  fun q => ∑ i, C (M q i) * X ⟨k₀, i⟩

end Objects

def BlockGraphImage.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsBlockImage y k₀ M N x →
    imageZ (inrV (ι := ι) (ι₂ := GlobalTheory κ)) (graphIdeal (mCoordIdeal y) (blockForms k₀ M)) = coordIdeal ℤ x

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end
