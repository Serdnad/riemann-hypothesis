module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle098
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle128
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle099
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Formalism.GradedWeylDivisibility.StatementA
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.Pst.StLat

theorem exists_mul_eq_pow_pred {l : ℕ} [Fact l.Prime] {j m : ℕ} (hj : j ≠ 0) (hm : ¬ l ^ m ∣ j) :
    ∃ c : ℤ_[l], ((j : ℕ) : ℤ_[l]) * c = (l : ℤ_[l]) ^ (m - 1) := by
  first
  | exact @_root_.GlobalTheory.PolynomialNormBound.main
  | exact _root_.GlobalTheory.PolynomialNormBound.main
  | (apply _root_.GlobalTheory.PolynomialNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialNormBound.main ..)

theorem not_pow_dvd {l m j : ℕ} (h1 : j ≠ 0) (h2 : j < 2 * l ^ m) (h3 : j ≠ l ^ m) : ¬ l ^ m ∣ j := by
  rintro ⟨t, rfl⟩
  rcases t with _ | _ | t
  · simp at h1
  · simp at h3
  · have : l ^ m * 2 ≤ l ^ m * (t + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
    omega

theorem log_trunc_pow : ∀ (l : ℕ) [Fact l.Prime] (ϖ : _root_.Formalism.Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, _root_.Formalism.Per.FilP l n = Ideal.span {betaD ϖ ^ n}) → ∀ u : _root_.Formalism.Per.BdRp l, IsLogP (beta ϖ) u →
  ∀ m : ℕ, 1 ≤ m → ∃ s ∈ Sg ϖ, ∃ e : _root_.Formalism.Per.BdRp l, (e = 1 ∨ e = -1) ∧
    betaD ϖ ^ (2 * l ^ m) ∣ ((l : ℕ) : _root_.Formalism.Per.BdRp l) * (((l : ℕ) : _root_.Formalism.Per.BdRp l) ^ (m - 1) * u - s) -
      e * betaD ϖ ^ (l ^ m) := by
  intro l _ ϖ hker hfil u hu m hm
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set M := l ^ (m + 1) with hM
  set n := 2 * M with hn
  have hlpos : 0 < l := (Fact.out : l.Prime).pos
  have hMpos : 0 < M := pow_pos hlpos _
  set β := beta ϖ with hβ

  have hc : ∀ j : ℕ, ∃ c : ℤ_[l], (j ≠ 0 ∧ j < n ∧ j ≠ M) → ((j : ℕ) : ℤ_[l]) * c = (l : ℤ_[l]) ^ m := by
    intro j
    by_cases h : j ≠ 0 ∧ j < n ∧ j ≠ M
    · obtain ⟨c, hc⟩ := exists_mul_eq_pow_pred (l := l) (m := m + 1) h.1 (not_pow_dvd h.1 h.2.1 h.2.2)
      exact ⟨c, fun _ => by simpa using hc⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose c hc using hc
  let d : ℕ → ℤ_[l] := fun j => if j = M ∨ j = n then 0 else c j
  let a : ℕ → _root_.Formalism.Per.AinfP l := fun k => (-1) ^ k * Per.zP l (d (k + 1)) * β ^ (k + 1)
  let S : _root_.Formalism.Per.AinfP l := ∑ k ∈ Finset.range n, a k
  let e0 : _root_.Formalism.Per.AinfP l := (-1) ^ (M - 1)
  let T : _root_.Formalism.Per.AinfP l := (-1) ^ (n - 1) * ((l : ℕ) : _root_.Formalism.Per.AinfP l) ^ (m + 1) *
    ((n.factorial / (n - 1 + 1) : ℕ) : _root_.Formalism.Per.AinfP l) * β ^ (n - 1 + 1)
  have hS : S ∈ Sa ϖ := by
    refine Subalgebra.sum_mem _ fun k _ => ?_
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ?_ _) ?_) (Subalgebra.pow_mem _ ?_ _)
    · exact Subalgebra.neg_mem _ (Subalgebra.one_mem _)
    · first
      | exact Subalgebra.algebraMap_mem _ _
      | (rw [GlobalTheory.RingIface.padicIntMap_eq_algebraMap_comp]; exact Subalgebra.algebraMap_mem _ _)
    · exact Algebra.subset_adjoin (Set.mem_singleton _)

  have hterm : ∀ k ∈ Finset.range n, ((l : ℕ) : _root_.Formalism.Per.AinfP l) ^ (m + 1) *
      ((-1) ^ k * ((n.factorial / (k + 1) : ℕ) : _root_.Formalism.Per.AinfP l) * β ^ (k + 1)) =
      ((n.factorial : ℕ) : _root_.Formalism.Per.AinfP l) * ((l : ℕ) : _root_.Formalism.Per.AinfP l) * a k +
      (if k = M - 1 then ((n.factorial : ℕ) : _root_.Formalism.Per.AinfP l) * ((-1) ^ k * β ^ (k + 1)) else 0) +
      (if k = n - 1 then (-1) ^ k * ((l : ℕ) : _root_.Formalism.Per.AinfP l) ^ (m + 1) *
        ((n.factorial / (k + 1) : ℕ) : _root_.Formalism.Per.AinfP l) * β ^ (k + 1) else 0) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hdvd : (k + 1) ∣ n.factorial := Nat.dvd_factorial (by omega) (by omega)
    have hq : (((n.factorial / (k + 1) : ℕ) : _root_.Formalism.Per.AinfP l)) * ((k + 1 : ℕ) : _root_.Formalism.Per.AinfP l) =
        ((n.factorial : ℕ) : _root_.Formalism.Per.AinfP l) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    by_cases h1 : k = M - 1
    · have h2 : ¬ k = n - 1 := by omega
      have hk1 : k + 1 = M := by omega
      have hda : d (k + 1) = 0 := by simp [d, hk1]
      rw [if_pos h1, if_neg h2]
      simp only [a, hda, map_zero, mul_zero, zero_mul, add_zero, zero_add]
      rw [← hq, hk1, hM, Nat.cast_pow]
      ring
    · by_cases h2 : k = n - 1
      · have hk1 : k + 1 = n := by omega
        have hda : d (k + 1) = 0 := by simp [d, hk1]
        rw [if_neg h1, if_pos h2]
        simp only [a, hda, map_zero, mul_zero, zero_mul, add_zero, zero_add]
        ring
      · have hne : ¬ (k + 1 = M ∨ k + 1 = n) := by omega
        have hda : d (k + 1) = c (k + 1) := by simp only [d, hne, if_false]
        have hck := hc (k + 1) ⟨by omega, by omega, by omega⟩
        have hck' := congrArg (Per.zP l) hck
        rw [map_mul, map_natCast, map_pow, map_natCast] at hck'
        rw [if_neg h1, if_neg h2]
        simp only [a, hda, add_zero]
        rw [← hq]
        linear_combination -(-1) ^ k * ((n.factorial / (k + 1) : ℕ) : _root_.Formalism.Per.AinfP l) * β ^ (k + 1) *
          ((l : ℕ) : _root_.Formalism.Per.AinfP l) * hck'
  have hsum : ((l : ℕ) : _root_.Formalism.Per.AinfP l) ^ (m + 1) * ∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : _root_.Formalism.Per.AinfP l) * β ^ (k + 1) =
      ((n.factorial : ℕ) : _root_.Formalism.Per.AinfP l) * (((l : ℕ) : _root_.Formalism.Per.AinfP l) * S + e0 * β ^ M) + T := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq', ← Finset.mul_sum]
    have hm1 : M - 1 ∈ Finset.range n := Finset.mem_range.2 (by omega)
    have hn1 : n - 1 ∈ Finset.range n := Finset.mem_range.2 (by omega)
    rw [if_pos hm1, if_pos hn1, Nat.sub_add_cancel (by omega : 1 ≤ M)]
    simp only [S, e0, T]
    ring
  have hβI : β ∈ Per.kerP l := by rw [hker]; exact Ideal.mem_span_singleton_self _
  have hT : T ∈ Per.kerP l ^ n := by
    have : β ^ (n - 1 + 1) ∈ Per.kerP l ^ n := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      exact Ideal.pow_mem_pow hβI n
    exact Ideal.mul_mem_left _ _ this

  let s : _root_.Formalism.Per.BdRp l := algebraMap (_root_.Formalism.Per.AinfP l) (_root_.Formalism.Per.BdRp l) S
  refine ⟨s, Subring.mem_map.2 ⟨S, hS, rfl⟩, algebraMap (_root_.Formalism.Per.AinfP l) (_root_.Formalism.Per.BdRp l) e0, ?_, ?_⟩
  · rcases neg_one_pow_eq_or (_root_.Formalism.Per.AinfP l) (M - 1) with h | h
    · left; simp [e0, h]
    · right; simp [e0, h]
  · rw [← Ideal.mem_span_singleton, ← hfil]
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
    have hev : ∀ x : _root_.Formalism.Per.AinfP l, Per.ev l n (algebraMap (_root_.Formalism.Per.AinfP l) (_root_.Formalism.Per.BdRp l) x) =
        Ideal.Quotient.mk _ x := fun x => GlobalTheory.RingIface.ev_alg l n x
    let q : _root_.Formalism.Per.AinfP l →+* _root_.Formalism.Per.AinfP l ⧸ Per.kerP l ^ n := Ideal.Quotient.mk _
    have hunit : IsUnit ((n.factorial : ℕ) : _root_.Formalism.Per.AinfP l ⧸ Per.kerP l ^ n) := by
      have := (GlobalTheory.RingBasics.isUnit_nat l n.factorial n.factorial_ne_zero).map q
      rwa [map_natCast] at this
    have hqT : q T = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hT
    have hs2 := congrArg q hsum
    simp only [map_add (f := _), map_mul, map_pow, map_natCast, hqT, add_zero] at hs2
    have hun := hu n
    apply hunit.mul_left_cancel
    rw [mul_zero]
    simp only [betaD, map_sub, map_mul, map_pow, map_natCast, s, hev]
    change ((n.factorial : ℕ) : _root_.Formalism.Per.AinfP l ⧸ Per.kerP l ^ n) * (((l : ℕ) : _) * (((l : ℕ) : _) ^ m * Per.ev l n u - q S) -
      q e0 * q β ^ M) = 0
    change _ = q _ at hun
    linear_combination ((l : ℕ) : _root_.Formalism.Per.AinfP l ⧸ Per.kerP l ^ n) ^ (m + 1) * hun + hs2

end GlobalTheory.Pst.StLat
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

variable {l : ℕ} [Fact l.Prime]

theorem map_linv (f : _root_.Formalism.Per.AinfP l →+* _root_.Formalism.Per.AinfP l) : f (linv l) = linv l := by
  have h := congrArg f (mul_linv (l := l))
  rw [map_mul, map_natCast, map_one] at h
  have h2 := mul_linv (l := l)
  linear_combination (linv l) * h - f (linv l) * h2

theorem beta_mem_kerP (ϖ : _root_.Formalism.Per.Fl l) (hu : ϖ.untilt = ((l : ℕ) : _root_.Formalism.Per.OC l)) : beta ϖ ∈ Per.kerP l := by
  rw [← ThetaD.fontaineTheta_eq_zero]
  have h := congrArg (Per.θP l) (l_mul_beta ϖ)
  rw [map_mul, map_sub, map_natCast, ThetaD.fontaineTheta_algebraMap₂, WittVector.fontaineTheta_teichmuller, hu] at h
  have hl : ((l : ℕ) : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  refine (mul_eq_zero.1 (h.trans ?_)).resolve_left hl
  simp

theorem gal_beta (g : GQ l) (ϖ e : _root_.Formalism.Per.Fl l) (h : _root_.Formalism.Per.σF g ϖ = ϖ * e) :
    Per.extP (_root_.Formalism.Per.σA g) (beta ϖ) = beta ϖ + algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) (GlobalTheory.MemLoc.mu e) +
      beta ϖ * algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) (GlobalTheory.MemLoc.mu e) := by
  have e1 : _root_.Formalism.Per.σA g (_root_.Formalism.Per.tm ϖ) = _root_.Formalism.Per.tm ϖ * _root_.Formalism.Per.tm e := by
    have h1 := gal_quot g ϖ e h 1
    simp only [map_one, mul_one, map_sub] at h1
    exact sub_left_injective h1
  rw [beta, map_sub, map_mul, map_one, map_linv, GlobalTheory.RingBasics.awayMap_algebraMap₂, e1, map_mul]
  simp only [GlobalTheory.MemLoc.mu, map_sub, map_one]
  ring

theorem isLogP_map {e : _root_.Formalism.Per.Fl l} (he : e.untilt = 1) {t : _root_.Formalism.Per.Acris l} (ht : IsLogA e t)
    {j : _root_.Formalism.Per.Acris l →+* _root_.Formalism.Per.BdRp l} (hj : IsCrisP j) :
    IsLogP (algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) (GlobalTheory.MemLoc.mu e)) (j t) := by
  intro n
  have hu : ∀ k : ℕ, ∃ u : _root_.Formalism.Per.AinfP l, ((k + 1 : ℕ) : _root_.Formalism.Per.AinfP l) * u = 1 := fun k =>
    (GlobalTheory.RingBasics.isUnit_nat l _ k.succ_ne_zero).exists_right_inv
  choose u hu using hu
  have hf : ∀ k : ℕ, IsUnit ((k.factorial : ℕ) : _root_.Formalism.Per.AinfP l) := fun k =>
    GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero
  obtain ⟨d, hd⟩ := (hf n).exists_right_inv
  obtain ⟨c, hc⟩ : ∃ c : _root_.Formalism.Per.AinfP l, ((n.factorial : ℕ) : _root_.Formalism.Per.AinfP l) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : _root_.Formalism.Per.AinfP l) *
        (algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) (GlobalTheory.MemLoc.mu e)) ^ (k + 1) :=
    ⟨d * _, by rw [← mul_assoc, hd, one_mul]⟩
  have key := (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l j hj).2.2 n t (algebraMap (_root_.Formalism.Per.AinfP l) (_root_.Formalism.Per.BdRp l) c) (by
    intro r
    obtain ⟨N, hN⟩ := ht r
    obtain ⟨s, hs, z, hz⟩ := hN (max N n) (le_max_left _ _)
    refine ⟨s, z, 0, by rw [← hz]; ring, ?_⟩
    rw [map_zero, mul_zero, map_zero, ← map_sub, LogFun.ev_alg, Ideal.Quotient.eq_zero_iff_mem,
      LogFun.partial_eq u hu _ _ _ (hf _) hs, LogFun.partial_eq u hu _ _ _ (hf _) hc, ← neg_sub]
    exact neg_mem (LogFun.partial_sub_mem _ u _ (LogFun.mu_mem he) (le_max_right _ _)))
  rw [key, LogFun.ev_alg, ← map_natCast (Ideal.Quotient.mk (Per.kerP l ^ n)), ← map_mul, hc]

theorem gal_log : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (Co : Core l), Co.ζ = P.ζQ → ∀ ϖ : _root_.Formalism.Per.Fl l,
  (∀ m : ℕ, (rootT ϖ m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (lRoot l m)) → ϖ.untilt = ((l : ℕ) : _root_.Formalism.Per.OC l) →
  ∀ u : _root_.Formalism.Per.BdRp l, IsLogP (beta ϖ) u → ∀ g : GQ l,
    Per.σDp g u = u + Co.j (algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.zA l (kummer P g)) * Co.t) := by
  intro l _ P Co hζ ϖ hr hu u hlog g
  have hd : ∀ m, g (lRoot l m) = Co.ζ m ^ (PadicInt.toZModPow m (kummer P g)).val * lRoot l m := fun m => by
    rw [hζ]; exact isKummer_kummer P g m
  have hd' : ∀ m, g (lRoot l m) / lRoot l m = Co.ζ m ^ (PadicInt.toZModPow m (kummer P g)).val := fun m => by
    rw [hd, mul_div_cancel_right₀ _ (lRoot_ne_zero l m)]
  obtain ⟨e, he⟩ := exists_tilt (fun m => Co.ζ m ^ (PadicInt.toZModPow m (kummer P g)).val)
    (fun m => by rw [← hd', ← hd', div_pow, ← map_pow, lRoot_succ]) 1 (by simp [Co.ζ_zero])
  have he1 : e.untilt = 1 := Subtype.ext (by
    have := he 0
    rw [Co.ζ_zero, one_pow, map_one] at this
    exact this)
  have hxe : _root_.Formalism.Per.σF g ϖ = ϖ * e := gal_eq_mul g ϖ e fun m => by
    rw [hr, he, ← map_mul, mul_comm, ← hd]
    exact GlobalTheory.RingBasics.σC_coe g _
  obtain ⟨y, -, hy, -⟩ := exists_isLogA l e he1
  rw [← log_eq Co e (kummer P g) y he hy]
  refine IsLogP.add (beta_mem_kerP ϖ hu) (LogFun.mu_mem he1) hlog (isLogP_map he1 hy Co.j_cris) ?_
  have h := IsLogP.gal hlog g
  rwa [gal_beta g ϖ e hxe] at h

end GlobalTheory.Pst.StLat
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H

noncomputable section

namespace GlobalTheory.DatumJets.Place

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

theorem norm_int_le (ι : K →+* ℂ_[p]) (y : 𝓞 K) : ‖ι (y : K)‖ ≤ 1 :=
  GlobalTheory.MomPlace.norm_le_one_of_isIntegral_int (by
    convert map_isIntegral_int ι (RingOfIntegers.isIntegral_coe y)
    exact Subsingleton.elim _ _)

def smallIdeal (ι : K →+* ℂ_[p]) : Ideal (𝓞 K) where
  carrier := {y | ‖ι (y : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : ι ((a + b : 𝓞 K) : K) = ι (a : K) + ι (b : K) := by simp
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : ι ((c • a : 𝓞 K) : K) = ι (c : K) * ι (a : K) := by simp
    rw [this, norm_mul]
    have h1 := norm_int_le ι c
    nlinarith [norm_nonneg (ι (c : K)), norm_nonneg (ι (a : K))]

theorem mem_smallIdeal (ι : K →+* ℂ_[p]) (y : 𝓞 K) : y ∈ smallIdeal ι ↔ ‖ι (y : K)‖ < 1 := Iff.rfl

theorem smallIdeal_isPrime (ι : K →+* ℂ_[p]) : (smallIdeal ι).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro a b hab
    rw [mem_smallIdeal] at hab
    rw [mem_smallIdeal, mem_smallIdeal]
    have : ι ((a * b : 𝓞 K) : K) = ι (a : K) * ι (b : K) := by simp
    rw [this, norm_mul] at hab
    by_contra hcon
    push Not at hcon
    nlinarith [hcon.1, hcon.2]

theorem dvd_of_natCast_mem {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) {q M : ℕ} (hq : q.Prime)
    (h1 : (q : R) ∈ I) (h2 : (M : R) ∈ I) : q ∣ M := by
  by_contra hnd
  have hc : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).2 hnd
  obtain ⟨u, v, huv⟩ : IsCoprime (q : R) (M : R) := Nat.Coprime.cast hc
  exact hI ((Ideal.eq_top_iff_one _).2
    (huv ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem exists_embedding (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    ∃ ι : K →+* ℂ_[p], w.asIdeal = smallIdeal ι := by
  by_contra hcon
  push Not at hcon
  have hnle : ∀ σ : K →ₐ[ℚ] ℂ_[p], ¬ w.asIdeal ≤ smallIdeal (σ : K →+* ℂ_[p]) := by
    intro σ hle
    exact hcon (σ : K →+* ℂ_[p]) (w.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top hle)
  have σ0 : K →ₐ[ℚ] ℂ_[p] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hav : ¬ ((w.asIdeal : Set (𝓞 K)) ⊆
      ⋃ σ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] ℂ_[p])) : Set (K →ₐ[ℚ] ℂ_[p])),
        (smallIdeal (σ : K →+* ℂ_[p]) : Set (𝓞 K))) := by
    rw [Ideal.subset_union_prime σ0 σ0 (fun σ _ _ _ => smallIdeal_isPrime _)]
    rintro ⟨σ, -, hle⟩
    exact hnle σ hle
  obtain ⟨x, hxw, hx⟩ := Set.not_subset.1 hav
  have hxσ : ∀ σ : K →ₐ[ℚ] ℂ_[p], 1 ≤ ‖σ (x : K)‖ := by
    intro σ
    by_contra hlt
    exact hx (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ σ)) (not_le.1 hlt))
  have hN : ((Algebra.norm ℤ x).natAbs : 𝓞 K) ∈ w.asIdeal := by
    have h1 := Ideal.absNorm_mem (Ideal.span {x})
    rw [Ideal.absNorm_span_singleton] at h1
    exact (Ideal.span_singleton_le_iff_mem _).2 hxw h1
  have hpN : p ∣ (Algebra.norm ℤ x).natAbs :=
    dvd_of_natCast_mem w.asIdeal w.isPrime.ne_top Fact.out hw hN
  obtain ⟨m, hm⟩ : (p : ℤ) ∣ Algebra.norm ℤ x := Int.natCast_dvd.2 hpN
  have hprod : ((Algebra.norm ℤ x : ℤ) : ℂ_[p]) = ∏ σ : K →ₐ[ℚ] ℂ_[p], σ (x : K) := by
    rw [← Algebra.norm_eq_prod_embeddings ℚ ℂ_[p] (x : K), ← Algebra.coe_norm_int x]
    simp
  have h1 : 1 ≤ ‖((Algebra.norm ℤ x : ℤ) : ℂ_[p])‖ := by
    rw [hprod, norm_prod]
    exact Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
      le_rfl fun σ _ => hxσ σ
  have h2 : ((Algebra.norm ℤ x : ℤ) : ℂ_[p]) = (p : ℂ_[p]) * ((m : ℤ) : ℂ_[p]) := by
    rw [hm]; push_cast; ring
  have h3 : ‖((m : ℤ) : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ m
  rw [h2, norm_mul] at h1
  have h4 := norm_p_lt_one (p := p)
  nlinarith [norm_nonneg (p : ℂ_[p]), norm_nonneg ((m : ℤ) : ℂ_[p])]

theorem valuation_le_one_of_norm (ι : K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) (x : K) (hx : ‖ι x‖ ≤ 1) :
    w.valuation K x ≤ 1 := by
  by_contra hcon
  have hgt : 1 < w.valuation K x := not_le.1 hcon
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hgt
  have hinv : w.valuation K x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hgt
  obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x⁻¹ hinv.le
  have hd : 1 ≤ ‖ι ((d : 𝓞 K) : K)‖ := not_lt.1 fun hlt => d.2 ((hw _).2 hlt)
  have hn : n ∈ w.asIdeal := by
    rw [← w.valuation_lt_one_iff_mem (K := K)]
    change w.valuation K (algebraMap (𝓞 K) K n) < 1
    rw [← h, map_mul]
    calc w.valuation K x⁻¹ * w.valuation K (algebraMap (𝓞 K) K d) ≤ w.valuation K x⁻¹ * 1 :=
          mul_le_mul_right (w.valuation_le_one _) _
      _ < 1 := by rwa [mul_one]
  have hn' := (hw n).1 hn
  have h2 : ((d : 𝓞 K) : K) = x * (n : K) := by
    have h' : x⁻¹ * ((d : 𝓞 K) : K) = (n : K) := h
    rw [← h', ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
  rw [h2, map_mul, norm_mul] at hd
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι (n : K))]

theorem placeAbove : GlobalTheory.DatumJets.PlaceAbove := by
  intro K _ _ σ p _ w hw
  obtain ⟨ι, hι⟩ := exists_embedding w hw
  have hw' : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1 := fun y => by rw [hι]; rfl
  obtain ⟨lam, hlam⟩ := GlobalTheory.MomPlace.exists_extension K p σ ι
  refine ⟨lam, fun k => ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt
  rw [(hlam k).2]
  exact ⟨fun h => valuation_le_one_of_norm ι w hw' k h.2,
    fun h => ⟨(hlam k).1, GlobalTheory.MomPlace.norm_le_one_of_valuation K p ι w hw' k h⟩⟩

end GlobalTheory.DatumJets.Place
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.SplitRead

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem eig_lpOfChar (ξ : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ) (σ : Weil h) :
    (WD.lpOfChar h ξ hξ).eig σ = {(ξ σ : ℂ)} := by
  rw [WD.lpOfChar, WD.eig_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp

theorem cls_eq_ofChar (χ : (w.adicCompletion E)ˣ →* ℂˣ) (c : Irr (w.adicCompletion E) 1)
    (hc : Nonempty (c.π.Equiv (detRep (Fin 1) χ))) :
    ∃ hχ : IsSmoothChar χ, cls (toIrrRep c) = .ofChar χ hχ := by
  obtain ⟨φ⟩ := hc
  have h1 : IsSmoothChar (detChar (Fin 1) χ) := (isSmooth_ofChar_iff _).1
    ((IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).isSmooth c.smooth)
  have h2 : Continuous (Matrix.GeneralLinearGroup.scalar (R := w.adicCompletion E) (Fin 1)) :=
    Units.continuous_map (continuous_matrix fun i j => by
      rw [Subsingleton.elim i j]; simpa using continuous_id')
  have h3 : (detChar (Fin 1) χ).comp (Matrix.GeneralLinearGroup.scalar (Fin 1)) = χ := by
    refine MonoidHom.ext fun z => congrArg χ ?_
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  exact ⟨h3 ▸ h1.comp _ h2, congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ⟨φ⟩)⟩

theorem IsRec.recUnit {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRec h rc) :
    RecUnit fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  intro χ c hu hc g α hα
  obtain ⟨hχ, e⟩ := cls_eq_ofChar χ c hc
  simp only [e, H.one, eig_lpOfChar, Multiset.mem_singleton] at hα
  rw [hα]
  exact hu _

end GlobalTheory.LocLanglands
end
end

section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

theorem _root_.GlobalTheory.T.isWeightedHomogeneous_div_and_diag_eq_choose_smul : ∀ (R : Type) [CommRing R] (r n : ℕ) (μ : Fin r → ℕ) (f : MvPolynomial (Fin r × Fin n) R), IsWeightedHomogeneous (rowW r n) f μ → (∀ (a b : Fin r) (k : ℕ), ∃ μ' : Fin r → ℕ, IsWeightedHomogeneous (rowW r n) (rowDiv R a b k f) μ') ∧ ∀ (a : Fin r) (k : ℕ), rowDiv R a a k f = ((μ a).choose k) • f := by
  first | exact @GlobalTheory.ValCmp.rowDiv_rowWeight | exact GlobalTheory.ValCmp.rowDiv_rowWeight | (intros; apply GlobalTheory.ValCmp.rowDiv_rowWeight <;> assumption)
end
