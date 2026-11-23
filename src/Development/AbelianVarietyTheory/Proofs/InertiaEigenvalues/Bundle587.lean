module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle559
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle262
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle558
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.EisShift

theorem taylor_coeff_pred {R : Type*} [CommRing R] (f : Polynomial R) (hf : f.Monic) (n : ℕ)
    (hn : f.natDegree = n + 1) (r : R) :
    (Polynomial.taylor r f).coeff n = f.coeff n + ((n + 1 : ℕ) : R) * r := by
  have h1 : (Polynomial.hasseDeriv n f).natDegree ≤ 1 := by
    have := Polynomial.natDegree_hasseDeriv_le f n
    omega
  have hl : f.coeff (1 + n) = 1 := by
    rw [add_comm, ← hn]; exact hf.coeff_natDegree
  rw [Polynomial.taylor_coeff, Polynomial.eq_X_add_C_of_natDegree_le_one h1]
  simp only [Polynomial.hasseDeriv_coeff, hl, zero_add, Nat.choose_self, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [add_comm 1 n, Nat.choose_succ_self_right]
  push_cast
  ring

theorem sq_dvd {R O : Type*} [CommRing R] [IsDomain R] [CommRing O] [IsLocalRing O] [Algebra R O]
    (p : R) (hp : p ≠ 0) (π : O) (hπ : ¬ IsUnit π) (E : Polynomial R) (hE : E.Monic)
    (h2 : 2 ≤ E.natDegree) (hd : ∀ i < E.natDegree, p ∣ E.coeff i)
    (w : Rˣ) (h0 : E.coeff 0 = p * w) (hr : Polynomial.aeval π E = 0) :
    π ^ 2 ∣ algebraMap R O p := by
  have hg : Polynomial.C p ∣ E - Polynomial.X ^ E.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i E.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]; exact hd i h
    · rw [if_pos h, h, hE.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h, sub_self]; exact dvd_zero _
  obtain ⟨g, hg⟩ := hg
  have hg0 : g.coeff 0 = w := by
    have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q 0) hg
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul] at this
    rw [if_neg (by omega), sub_zero, h0] at this
    exact (mul_left_cancel₀ hp this).symm
  have hu : IsUnit (Polynomial.aeval π g) := by
    have e : Polynomial.aeval π g
        = algebraMap R O w + π * Polynomial.aeval π g.divX := by
      conv_lhs => rw [← Polynomial.X_mul_divX_add g]
      simp [hg0, add_comm]
    by_contra hn
    have h1 : Polynomial.aeval π g ∈ IsLocalRing.maximalIdeal O := hn
    have h3 : π * Polynomial.aeval π g.divX ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_right _ _ hπ
    have h4 := Ideal.sub_mem _ h1 h3
    rw [e, add_sub_cancel_right] at h4
    exact h4 ((Units.isUnit w).map (algebraMap R O))
  have e := congrArg (Polynomial.aeval π) hg
  simp only [map_sub, hr, map_pow, Polynomial.aeval_X, map_mul, Polynomial.aeval_C, zero_sub] at e
  rw [← hu.dvd_mul_right, ← e, dvd_neg]
  exact pow_dvd_pow _ h2

theorem exists_uniformiser : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (Wq l a) O] [Module.Finite (Wq l a) O], Function.Injective (algebraMap (Wq l a) O) → (∀ x : O, ∃ c : Wq l a, ¬ IsUnit (x - algebraMap (Wq l a) O c)) → ∃ (π : O) (Ep : Polynomial (Wq l a)), Irreducible π ∧ (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) ∧ (∃ i, ¬ l ∣ i ∧ Ep.coeff i ≠ 0) ∧ Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f := by
  intro l _ a _ O _ _ _ _ _ hinj hres
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨E, hm, hpos, hd, ⟨w, h0⟩, hr, hs, hmin⟩ := GlobalTheory.T.eisenstein_minpoly_uniformizer_witt_totallyRamified l a O hinj hres π hπ
  by_cases h : ∃ i, ¬ l ∣ i ∧ E.coeff i ≠ 0
  · exact ⟨π, E, hπ, ⟨hm, hpos, hd, w, h0⟩, h, hr, hs, hmin⟩
  push_neg at h
  haveI : CharZero (Wq l a) := by
    refine charZero_of_inj_zero fun n hn => ?_
    by_contra hn0
    have hx : (n : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hn0
    have e := congrArg (algebraMap ℤ_[l] (Wq l a)) (PadicInt.unitCoeff_spec hx)
    rw [map_natCast, hn, map_mul, map_pow, map_natCast] at e
    exact mul_ne_zero ((Units.isUnit _).map (algebraMap ℤ_[l] (Wq l a))).ne_zero
      (pow_ne_zero _ (WittVector.p_nonzero l (Fq l a))) e.symm
  have hl : l.Prime := Fact.out
  have hl0 : (l : Wq l a) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hle : l ∣ E.natDegree := by
    by_contra hn
    have := h _ hn
    rw [hm.coeff_natDegree] at this
    exact one_ne_zero this
  have h2 : 2 ≤ E.natDegree := hl.two_le.trans (Nat.le_of_dvd hpos hle)
  obtain ⟨t, ht⟩ := sq_dvd (l : Wq l a) hl0 π hπ.not_isUnit E hm h2 hd w h0 hr
  have hu : IsUnit (1 + π * t) := by
    by_contra hn
    have h1 : 1 + π * t ∈ IsLocalRing.maximalIdeal O := hn
    have h3 : π * t ∈ IsLocalRing.maximalIdeal O := Ideal.mul_mem_right _ _ hπ.not_isUnit
    have h4 := Ideal.sub_mem _ h1 h3
    rw [add_sub_cancel_right] at h4
    exact h4 isUnit_one
  have hπ' : Irreducible (π + algebraMap (Wq l a) O l) := by
    have : π + algebraMap (Wq l a) O l = π * (1 + π * t) := by rw [ht]; ring
    rw [this]
    exact (irreducible_mul_isUnit hu).2 hπ
  obtain ⟨F, fm, fpos, fd, fw, fr, fs, fmin⟩ := GlobalTheory.T.eisenstein_minpoly_uniformizer_witt_totallyRamified l a O hinj hres _ hπ'
  refine ⟨_, F, hπ', ⟨fm, fpos, fd, fw⟩, ?_, fr, fs, fmin⟩
  have d1 : F ∣ Polynomial.taylor (-(l : Wq l a)) E := by
    apply fmin
    rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
    simpa using hr
  have d2 : E ∣ Polynomial.taylor (l : Wq l a) F := by
    apply hmin
    rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
    simpa using fr
  have mt : ∀ (r : Wq l a) (f : Polynomial (Wq l a)), f.Monic → (Polynomial.taylor r f).Monic := by
    intro r f hf
    rw [Polynomial.taylor_apply]
    exact hf.comp_X_add_C r
  have n2 := Polynomial.natDegree_le_of_dvd d2 (mt _ _ fm).ne_zero
  rw [Polynomial.natDegree_taylor] at n2
  have heq : Polynomial.taylor (-(l : Wq l a)) E = F :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le fm (mt _ _ hm) d1
      (by rw [Polynomial.natDegree_taylor]; exact n2)
  obtain ⟨n, hn⟩ : ∃ n, E.natDegree = n + 1 := ⟨E.natDegree - 1, by omega⟩
  have hnd : ¬ l ∣ n := by
    intro hc
    rw [hn] at hle
    exact hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hc).1 hle))
  refine ⟨n, hnd, ?_⟩
  rw [← heq, taylor_coeff_pred E hm n hn, h n hnd, zero_add]
  exact mul_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)) (neg_ne_zero.2 hl0)

end GlobalTheory.EisShift
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.TiltDiv

variable {l : ℕ} [Fact l.Prime]

theorem norm_OC_le_one (x : Per.OC l) : ‖(x : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 x.2

theorem mk_untilt_iterate (x : OCb l) (n : ℕ) :
    Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)})
      (PreTilt.untilt ((frobeniusEquiv (OCb l) l).symm^[n] x)) = PreTilt.coeff n x := by
  rw [PreTilt.mk_untilt_eq_coeff_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]

theorem untilt_zero : PreTilt.untilt (0 : OCb l) = 0 := Perfection.teichmuller_zero

theorem untilt_eq_zero_iff {x : OCb l} : PreTilt.untilt x = 0 ↔ x = 0 := by
  refine ⟨fun h => Perfection.ext fun n => ?_, fun h => h ▸ untilt_zero⟩
  have h1 := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n
  rw [h, pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at h1
  change PreTilt.coeff n x = PreTilt.coeff n 0
  rw [← mk_untilt_iterate, h1, map_zero, map_zero]

def ofCompatible (y : ℕ → Per.OC l) (hy : ∀ n, y (n + 1) ^ l = y n) : OCb l :=
  (⟨fun n => Ideal.Quotient.mk _ (y n), fun n => by rw [← map_pow, hy]⟩ :
    Perfection (ModP (Per.OC l) l) l)

theorem dvd_of_norm_untilt_le {a b : OCb l} (hb : b ≠ 0)
    (h : ‖((PreTilt.untilt a : Per.OC l) : ℂ_[l])‖ ≤ ‖((PreTilt.untilt b : Per.OC l) : ℂ_[l])‖) :
    b ∣ a := by
  set φ := (frobeniusEquiv (OCb l) l).symm
  have hnorm : ∀ (x : OCb l) (n : ℕ), ‖((PreTilt.untilt (φ^[n] x) : Per.OC l) : ℂ_[l])‖ ^ l ^ n =
      ‖((PreTilt.untilt x : Per.OC l) : ℂ_[l])‖ := by
    intro x n
    rw [← norm_pow, ← SubmonoidClass.coe_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow]
  have hbn : ∀ n, ((PreTilt.untilt (φ^[n] b) : Per.OC l) : ℂ_[l]) ≠ 0 := by
    intro n h0
    apply hb
    have h0' : PreTilt.untilt (φ^[n] b) = 0 := Subtype.ext h0
    rw [← untilt_eq_zero_iff, ← PreTilt.untilt_iterate_frobeniusEquiv_symm_pow b n, h0',
      zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
  have hle : ∀ n,
      ‖((PreTilt.untilt (φ^[n] a) : Per.OC l) : ℂ_[l])‖ ≤ ‖((PreTilt.untilt (φ^[n] b) : Per.OC l) : ℂ_[l])‖ := by
    intro n
    have hpn : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hpn, hnorm, hnorm]
    exact h
  have hstep : ∀ (x : OCb l) (n : ℕ), PreTilt.untilt (φ^[n + 1] x) ^ l = PreTilt.untilt (φ^[n] x) := by
    intro x n
    rw [Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]
  let y : ℕ → Per.OC l := fun n =>
    ⟨((PreTilt.untilt (φ^[n] a) : Per.OC l) : ℂ_[l]) / PreTilt.untilt (φ^[n] b), (GlobalTheory.RingBasics.mem_OC _).2 (by
      rw [norm_div]; exact div_le_one_of_le₀ (hle n) (norm_nonneg _))⟩
  have hy : ∀ n, y (n + 1) ^ l = y n := by
    intro n
    ext
    simp only [y, SubmonoidClass.coe_pow, div_pow]
    rw [← SubmonoidClass.coe_pow, ← SubmonoidClass.coe_pow, hstep, hstep]
  refine ⟨ofCompatible y hy, Perfection.ext fun n => ?_⟩
  change PreTilt.coeff n a = PreTilt.coeff n (b * ofCompatible y hy)
  rw [map_mul]
  change _ = _ * Ideal.Quotient.mk _ (y n)
  rw [← mk_untilt_iterate, ← mk_untilt_iterate, ← map_mul]
  congr 1
  ext
  rw [MulMemClass.coe_mul]
  change _ = _ * (_ / _)
  rw [mul_div_cancel₀ _ (hbn n)]

end GlobalTheory.TiltDiv

end

noncomputable section

namespace GlobalTheory.TiltDiv

variable {l : ℕ} [Fact l.Prime]

theorem norm_pow_natDegree_eq_of_eisenstein {R : Type*} [CommRing R] (P : Polynomial R) (hm : P.Monic)
    (hpos : 0 < P.natDegree) (hdvd : ∀ i < P.natDegree, ((l : ℕ) : R) ∣ P.coeff i)
    (w : Rˣ) (h0 : P.coeff 0 = ((l : ℕ) : R) * w) (Ψ : R →+* ℂ_[l]) (hΨ : ∀ y, ‖Ψ y‖ ≤ 1)
    (z : ℂ_[l]) (hz1 : ‖z‖ ≤ 1) (hz : P.eval₂ Ψ z = 0) :
    ‖z ^ P.natDegree‖ = ‖((l : ℕ) : ℂ_[l])‖ := by
  obtain ⟨m, hm'⟩ : ∃ m, P.natDegree = m + 1 := ⟨P.natDegree - 1, by omega⟩
  have hl0 : 0 < ‖((l : ℕ) : ℂ_[l])‖ :=
    norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hl1 : ‖((l : ℕ) : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hc : ∀ i < P.natDegree, ‖Ψ (P.coeff i)‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ := by
    intro i hi
    obtain ⟨y, hy⟩ := hdvd i hi
    rw [hy, map_mul, map_natCast, norm_mul]
    calc _ ≤ ‖((l : ℕ) : ℂ_[l])‖ * 1 := by gcongr; exact hΨ y
      _ = _ := mul_one _
  have hw : ‖Ψ w‖ = 1 := by
    have h1 : Ψ w * Ψ ↑w⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have ha := hΨ w
    have hb := hΨ ↑w⁻¹
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    nlinarith [norm_nonneg (Ψ w), norm_nonneg (Ψ ↑w⁻¹)]
  have hc0 : ‖Ψ (P.coeff 0)‖ = ‖((l : ℕ) : ℂ_[l])‖ := by
    rw [h0, map_mul, map_natCast, norm_mul, hw, mul_one]
  have htop : P.coeff (m + 1) = 1 := by rw [← hm']; exact hm.coeff_natDegree
  rw [Polynomial.eval₂_eq_sum_range, hm', Finset.sum_range_succ, Finset.sum_range_succ', htop,
    map_one, one_mul, pow_zero, mul_one] at hz
  set S := ∑ i ∈ Finset.range m, Ψ (P.coeff (i + 1)) * z ^ (i + 1) with hSdef
  have hS : ‖S‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ * ‖z‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i + 1 < P.natDegree := by rw [hm']; simpa using Finset.mem_range.1 hi
    have hp : ‖z‖ ^ (i + 1) ≤ ‖z‖ := pow_le_of_le_one (norm_nonneg _) hz1 (by omega)
    exact mul_le_mul (hc _ hi') hp (by positivity) (norm_nonneg _)
  have hzpow : z ^ (m + 1) = -(Ψ (P.coeff 0) + S) := by linear_combination hz
  have hSl : ‖S‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ := hS.trans (by nlinarith [norm_nonneg z])
  have hup : ‖z ^ (m + 1)‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ := by
    rw [hzpow, norm_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hc0.le hSl)
  have hzlt : ‖z‖ < 1 := by
    by_contra hge
    push_neg at hge
    have : 1 ≤ ‖z‖ ^ (m + 1) := one_le_pow₀ hge
    rw [norm_pow] at hup
    linarith
  have hSlt : ‖S‖ < ‖((l : ℕ) : ℂ_[l])‖ := hS.trans_lt (by nlinarith [norm_nonneg z])
  have hlow : ‖((l : ℕ) : ℂ_[l])‖ ≤ ‖z ^ (m + 1)‖ := by
    have h3 : Ψ (P.coeff 0) = -(z ^ (m + 1) + S) := by linear_combination hz
    have h4 := IsUltrametricDist.norm_add_le_max (z ^ (m + 1)) S
    rw [← norm_neg (z ^ (m + 1) + S), ← h3, hc0] at h4
    rcases le_max_iff.1 h4 with h5 | h5
    · exact h5
    · linarith
  rw [hm']
  exact le_antisymm hup hlow

end GlobalTheory.TiltDiv

end

noncomputable section

namespace GlobalTheory.TiltDiv

theorem flat_pow_natDegree_eq_mul_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ϖ : OCb l),
    ϖ.untilt = ((l : ℕ) : Per.OC l) →
    ∃ x : OCb l, IsUnit x ∧ bk.flat ^ bk.Ep.natDegree = ϖ * x := by
  intro l _ K bk ϖ hϖ
  set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ X) with hr
  have h1 : bk.flat.untilt = intToOC K r := by
    rw [← WittVector.fontaineTheta_teichmuller, ← bk.ev_X]
    exact bk.θ_ev r X (by rw [hr, RingEquiv.apply_symm_apply])
  let Ψ0 : (Wq l bk.a)⟦X⟧ →+* ℂ_[l] := (PadicComplexInt l).subtype.comp
    ((intToOC K).comp (bk.str.symm.toRingHom.comp (Ideal.Quotient.mk _)))
  let Ψ : Wq l bk.a →+* ℂ_[l] := Ψ0.comp (Polynomial.coeToPowerSeries.ringHom.comp Polynomial.C)
  have hΨ : ∀ y, ‖Ψ y‖ ≤ 1 := fun y => norm_OC_le_one _
  set z : ℂ_[l] := Ψ0 (Polynomial.coeToPowerSeries.ringHom Polynomial.X) with hzdef
  have hzX : z = ((bk.flat.untilt : Per.OC l) : ℂ_[l]) := by
    rw [h1, hzdef, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
    rfl
  have hz1 : ‖z‖ ≤ 1 := by rw [hzX]; exact norm_OC_le_one _
  have hE : Ψ0 (bk.Ep : (Wq l bk.a)⟦X⟧) = 0 := by
    have : Ideal.Quotient.mk (Ideal.span {(bk.Ep : (Wq l bk.a)⟦X⟧)}) (bk.Ep : (Wq l bk.a)⟦X⟧) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    simp only [Ψ0, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this, map_zero]
  have hz : bk.Ep.eval₂ Ψ z = 0 := by
    rw [← hE, hzdef, ← Polynomial.hom_eval₂, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X]
    rfl
  have hnorm := norm_pow_natDegree_eq_of_eisenstein bk.Ep bk.monic bk.deg_pos bk.dvd_coeff
    bk.coeff_zero.choose bk.coeff_zero.choose_spec Ψ hΨ z hz1 hz
  rw [hzX, ← SubmonoidClass.coe_pow, ← map_pow] at hnorm
  have hl0 : 0 < ‖((l : ℕ) : ℂ_[l])‖ :=
    norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hϖn : ‖((ϖ.untilt : Per.OC l) : ℂ_[l])‖ = ‖((l : ℕ) : ℂ_[l])‖ := by
    rw [hϖ]; norm_cast
  rw [← hϖn] at hnorm
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [untilt_zero] at hϖn
    simp at hϖn
    linarith
  obtain ⟨x, hx⟩ := dvd_of_norm_untilt_le hϖ0 hnorm.le
  refine ⟨x, ?_, hx⟩
  have hxn : ‖((x.untilt : Per.OC l) : ℂ_[l])‖ = 1 := by
    have h2 := hnorm
    rw [hx, map_mul, MulMemClass.coe_mul, norm_mul, hϖn] at h2
    have h3 : ‖((l : ℕ) : ℂ_[l])‖ * ‖((x.untilt : Per.OC l) : ℂ_[l])‖ = ‖((l : ℕ) : ℂ_[l])‖ * 1 := by
      rw [mul_one]; exact h2
    exact mul_left_cancel₀ hl0.ne' h3
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [untilt_zero] at hxn
    simp at hxn
  refine isUnit_of_dvd_one (dvd_of_norm_untilt_le hx0 ?_)
  rw [map_one, OneMemClass.coe_one, norm_one, hxn]

end GlobalTheory.TiltDiv

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.AcrisPow
variable {l : ℕ} [hl : Fact l.Prime]

theorem eventually_lt_two_pow (A B : ℕ) : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → A * n + B < 2 ^ n := by
  refine ⟨4 * (A + B + 1), fun n hn => ?_⟩
  set m := 2 * (A + B + 1) with hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show m ≤ n by omega)
  have hk : m ≤ k := by omega
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : k < 2 ^ k := Nat.lt_two_pow_self
  have h3 : (m + 1) * (k + 1) ≤ 2 ^ m * 2 ^ k := Nat.mul_le_mul h1 h2
  rw [pow_add]
  have h4 : A * (m + k) + B < (m + 1) * (k + 1) := by nlinarith
  omega

theorem dvd_pow_acris0 (ξ : Ainf l) (hξ : Per.θ l ξ = 0) :
    ((l : ℕ) : Per.Acris0 l) ∣ algebraMap (Ainf l) (Per.Acris0 l) ξ ^ l := by
  have hp : l.Prime := Fact.out
  have hlu : IsUnit ((l : ℕ) : Per.AinfP l) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Per.AinfP l) ((l : ℕ) : Per.Ainf l)
    rwa [map_natCast] at this
  have hf : IsUnit ((l.factorial : ℕ) : Per.AinfP l) := by
    obtain ⟨c, hc⟩ := GlobalTheory.Per.exists_factorial_mul_eq_pow_ainf l l
    have h2 := congrArg (algebraMap (Per.Ainf l) (Per.AinfP l)) hc
    rw [map_mul, map_pow, map_natCast, map_natCast] at h2
    exact isUnit_of_mul_isUnit_left (h2 ▸ hlu.pow l)
  obtain ⟨v, hv⟩ := hf.exists_right_inv
  have hx : ((l.factorial : ℕ) : Per.AinfP l) * (v * algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l := by rw [← mul_assoc, hv, one_mul]
  generalize v * algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l = x at hx
  have hxD : x ∈ Per.Acris0 l := GlobalTheory.RingIface.dividedPower_mem_Acris0 l ξ l x hξ hx
  have hfac : ((l.factorial : ℕ) : Per.AinfP l) =
      ((l : ℕ) : Per.AinfP l) * (((l - 1).factorial : ℕ) : Per.AinfP l) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hp.ne_zero]
  refine ⟨(((l - 1).factorial : ℕ) : Per.Acris0 l) * ⟨x, hxD⟩, Subtype.ext ?_⟩
  simp only [SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap, Subalgebra.coe_mul, SubringClass.coe_natCast]
  rw [← hx, hfac, mul_assoc]

theorem dvd_X_pow {K : FinExt l} (bk : BK K) :
    (l : Per.Acris l) ∣ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ^ (bk.Ep.natDegree * l) := by
  set f := algebraMap (Ainf l) (Per.Acris l)
  have hξ : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have h1 : (l : Per.Acris l) ∣ f (bk.ev bk.E) ^ l := by
    have := map_dvd (algebraMap (Per.Acris0 l) (Per.Acris l)) (dvd_pow_acris0 _ hξ)
    rw [map_natCast, map_pow, ← GlobalTheory.RingIface.tower l] at this
    exact this
  have h2 : (l : Per.Acris l) ∣ f (bk.ev bk.E) - f (bk.ev X) ^ bk.Ep.natDegree := by
    have := map_dvd f (AinfDiv.dvd_E bk)
    rwa [map_natCast, map_sub, map_pow] at this
  have h3 : (l : Per.Acris l) ∣ f (bk.ev bk.E) ^ l - (f (bk.ev X) ^ bk.Ep.natDegree) ^ l :=
    h2.trans (sub_dvd_pow_sub_pow _ _ l)
  have h4 := dvd_sub h1 h3
  rw [sub_sub_cancel, ← pow_mul] at h4
  simpa [RingHom.comp_apply] using h4

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (c M : ℕ), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    (l : Per.Acris l) ^ (c * n + M) ∣ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ^ (l ^ n - 1) := by
  intro l _ K bk c M
  set e := bk.Ep.natDegree
  obtain ⟨n₀, hn₀⟩ := eventually_lt_two_pow (e * l * c) (e * l * M)
  refine ⟨n₀, fun n hn => ?_⟩
  have hlt := hn₀ n hn
  have h2l : 2 ^ n ≤ l ^ n := Nat.pow_le_pow_left (Fact.out : l.Prime).two_le n
  have hle : e * l * (c * n + M) ≤ l ^ n - 1 := by
    have : e * l * (c * n + M) = e * l * c * n + e * l * M := by ring
    omega
  have hk := pow_dvd_pow_of_dvd (dvd_X_pow bk) (c * n + M)
  rw [← pow_mul] at hk
  exact hk.trans (pow_dvd_pow _ hle)

end GlobalTheory.AcrisPow
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.untiltOfTiltRoot_flat_algebraic_and_galois_fix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ n : ℕ, ∃ z : Om l, ((GlobalTheory.MemLoc.rootT bk.flat n : OC l) : ℂ_[l]) = (z : ℂ_[l])) ∧ ∀ (g : GQ l) (y : OCb l), (∀ n : ℕ, Per.σO g (GlobalTheory.MemLoc.rootT bk.flat n) = GlobalTheory.MemLoc.rootT y n) → Per.σF g bk.flat = y := by
  first | exact @GlobalTheory.BSP.rootT_flat_alg_and_fix | exact GlobalTheory.BSP.rootT_flat_alg_and_fix | (intros; apply GlobalTheory.BSP.rootT_flat_alg_and_fix <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.ainf_divisibility_breuilKisin_facts : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ (n : ℕ) (y : Ainf l), ((l : ℕ) : Ainf l) * y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ (2 * n + 2) → y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ n) ∧ (∀ y : Ainf l, ((l : ℕ) : Ainf l) ∣ bk.ev X * y → ((l : ℕ) : Ainf l) ∣ y) ∧ (∀ y : Ainf l, (∀ m : ℕ, ∃ z, ((l : ℕ) : Ainf l) ∣ y - bk.ev X ^ m * z) → ((l : ℕ) : Ainf l) ∣ y) ∧ bk.flat ≠ 0 ∧ ¬ IsUnit bk.flat ∧ IsAdicComplete (Ideal.span {bk.flat}) (OCb l) ∧ ((l : ℕ) : Ainf l) ∣ bk.ev bk.E - bk.ev X ^ bk.Ep.natDegree := by
  first | exact @GlobalTheory.BSP.AinfDiv.main | exact GlobalTheory.BSP.AinfDiv.main | (intros; apply GlobalTheory.BSP.AinfDiv.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_flat_radius_ideal_facts : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), bk.flat ≠ 0 ∧ ¬ IsUnit bk.flat ∧ (0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹) ∧ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S) ^ bk.Ep.natDegree} = bk.J := by
  first | exact @GlobalTheory.BSP.flat_disc | exact GlobalTheory.BSP.flat_disc | (intros; apply GlobalTheory.BSP.flat_disc <;> assumption)
end
