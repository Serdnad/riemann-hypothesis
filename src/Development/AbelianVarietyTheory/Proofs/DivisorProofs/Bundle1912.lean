module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle077
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle198
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle168
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafHypothesesConst
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

@[expose] public section

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

open GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.SplitChar GlobalTheory.NormSum.UnramHecke Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.NormKill

variable {D : D7}

theorem vl_le_of_dvd {p N : ℕ} (h : p ∣ N) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    vl D v (N : AE D) ≤ vl D v (p : AE D) := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_le_of_le_one_right' (vl_le (natCast_mem _ _) v)

theorem exists_global_congN {N : ℕ} (hN : 1 < N) (x : (AE D)ˣ) :
    ∃ a : D.host.Eˣ, ∃ s ∈ OhE D, ((incU D a * x⁻¹ : (AE D)ˣ) : AE D) - 1 = (N : AE D) * s := by
  obtain ⟨n, hn, hx⟩ := GlobalTheory.HeckeVal.exists_denom D ((x⁻¹ : (AE D)ˣ) : AE D)
  obtain ⟨a, r, hr, e⟩ := exists_approx (x : AE D) (Nat.mul_pos (by omega : 0 < N) hn)
  have h1 : inc D a * ((x⁻¹ : (AE D)ˣ) : AE D) - 1 = (N : AE D) * (-(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D)))) := by
    rw [Nat.cast_mul] at e
    linear_combination x.mul_inv - ((x⁻¹ : (AE D)ˣ) : AE D) * e
  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E (Nat.minFac_prime (by omega : N ≠ 1))
    have h2 := congrArg (vl D v) h1
    rw [map_zero, zero_mul, zero_sub, Valuation.map_neg, map_one, map_mul] at h2
    have h3 : vl D v (N : AE D) < 1 := (vl_le_of_dvd (Nat.minFac_dvd N) v).trans_lt (val_nat_lt hv)
    have h4 := (mul_le_of_le_one_right' (vl_le (neg_mem (mul_mem hr hx)) v)).trans_lt h3
    rw [← h2] at h4
    exact lt_irrefl _ h4
  exact ⟨Units.mk0 a ha, _, neg_mem (mul_mem hr hx), h1⟩

theorem vl_norm_sub_one {N : ℕ} {z : (AE D)ˣ} {s : AE D} (hs : s ∈ OhE D) (e : (z : AE D) - 1 = (N : AE D) * s)
    (v : HeightOneSpectrum (𝓞 D.host.E)) :
    vl D v (((z * sgU D z : (AE D)ˣ) : AE D) - 1) ≤ vl D v (N : AE D) := by
  obtain ⟨v', hv', -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv v
  have hN1 : ∀ w, vl D w (N : AE D) ≤ 1 := fun w => vl_le (natCast_mem _ _) w
  have h1 : ∀ w, vl D w ((z : AE D) - 1) ≤ vl D w (N : AE D) := fun w => by
    rw [e, map_mul]
    exact mul_le_of_le_one_right' (vl_le hs w)
  have h2 : vl D v (sgA D z - 1) ≤ vl D v (N : AE D) := by
    rw [← map_one (sgA D), ← map_sub, vl_sgA (conjPl_symm hv')]
    refine (h1 v').trans (le_of_eq ?_)
    rw [← vl_sgA (conjPl_symm hv'), map_natCast]
  have e2 : ((z * sgU D z : (AE D)ˣ) : AE D) - 1 =
      ((z : AE D) - 1) * (sgA D z - 1) + (((z : AE D) - 1) + (sgA D z - 1)) := by
    change (z : AE D) * sgA D z - 1 = _
    ring
  rw [e2]
  refine Valuation.map_add_le _ ?_ (Valuation.map_add_le _ (h1 v) h2)
  rw [map_mul]
  exact (mul_le_of_le_one_right' (h2.trans (hN1 v))).trans (h1 v)

theorem vl_pow_le {p m : ℕ} (hp : p ∣ m) {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : _root_.Formalism.L2.Host.OverP D.host p v) (k : ℕ) :
    vl D v ((m ^ (k + 1) : ℕ) : AE D) ≤ WithZero.exp (-((k : ℤ) + 1)) := by
  have h1 : vl D v (m : AE D) ≤ WithZero.exp (-1) := by
    have := GlobalTheory.Mem.KerDet.le_exp_neg_one ((vl_le_of_dvd hp v).trans_lt (val_nat_lt hv))
    simpa using this
  rw [Nat.cast_pow, map_pow]
  calc vl D v (m : AE D) ^ (k + 1) ≤ WithZero.exp (-1) ^ (k + 1) := pow_le_pow_left₀ zero_le h1 _
    _ = WithZero.exp (-((k : ℤ) + 1)) := by
      rw [← WithZero.exp_nsmul]
      congr 1
      simp

theorem chi_norm_global (χ : _root_.Formalism.L2.Host.HChar D.host.E) {n : D.what₂.Tau → ℤ} (hi : χ.HasInf (embT D) n) (a : D.host.Eˣ) :
    χ.1 (finIdl D (incU D a * sgU D (incU D a))) = 1 := by
  obtain ⟨k', hk⟩ := exists_real_norm a
  have hu : ((_root_.Formalism.L2.Host.upF D.host.F k' : D.host.Eˣ) : D.host.E) = (a : D.host.E) * D.host.conj a := by
    haveI : Nontrivial (AE D) := by
      obtain ⟨v, -⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E Nat.prime_two
      refine ⟨⟨0, 1, fun h => ?_⟩⟩
      have := congrArg (vl D v) h
      rw [map_zero, map_one] at this
      exact zero_ne_one this
    apply (inc D).injective
    have := congrArg Units.val hk
    change inc D a * sgA D (inc D a) = inc D _ at this
    rw [← this, sgA_inc, map_mul]
  have hinf : χ.inf (_root_.Formalism.L2.Host.upF D.host.F k') = 1 := by
    apply Units.ext
    rw [hi, Units.val_one]
    refine Finset.prod_eq_one fun τ _ => ?_
    have h0 : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
    have h1 : embT D τ ((_root_.Formalism.L2.Host.upF D.host.F k' : D.host.Eˣ) : D.host.E) = ((Complex.normSq (embT D τ (a : D.host.E)) : ℝ) : ℂ) := by
      rw [hu, map_mul, _root_.GlobalTheory.NormSum.UnramHecke.emb_conj, Complex.mul_conj]
    have h2 : (0 : ℝ) < Complex.normSq (embT D τ (a : D.host.E)) := Complex.normSq_pos.2 h0
    rw [h1, Complex.norm_real, Real.norm_of_nonneg h2.le, div_self (by exact_mod_cast h2.ne'), one_zpow]
  rw [hk, finIdl_incU]
  have h1 := χ.2.2 (_root_.Formalism.L2.Host.upF D.host.F k')
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul] at h1
  have h2 : χ.1 (_root_.Formalism.L2.Host.infDiag (_root_.Formalism.L2.Host.upF D.host.F k')) = 1 := hinf
  rw [h2, one_mul] at h1
  exact h1

theorem chi_norm_cong (χ : _root_.Formalism.L2.Host.HChar D.host.E) (S : Finset ℕ) (k : ℕ) (ht : χ.TrivOn D.host.F)
    (hl : ∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) (z : (AE D)ˣ)
    (hz : ∀ q ∈ S, ∀ v, Formalism.L2.Host.OverP D.host q v →
      vl D v (((z * sgU D z : (AE D)ˣ) : AE D) - 1) ≤ WithZero.exp (-((k : ℤ) + 1))) :
    χ.1 (finIdl D (z * sgU D z)) = 1 := by
  obtain ⟨c, -, -, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have hG : ∀ v k', _root_.GlobalTheory.Mem.Chr.locF (L := D.host.E) D.host.F v k' ∈ (χ.1.comp (finPartI D.host.E)).ker := fun v k' => by
    rw [MonoidHom.mem_ker]
    exact GlobalTheory.Mem.KerDet.map_finPartI_locF ht v k'
  obtain ⟨b, hb, hun, hc⟩ := exists_of_balanced hu _ hG _ (norm_balanced z)
  rw [MonoidHom.mem_ker] at hb
  rw [← finPartI_finIdl, ← mul_inv_cancel_left b (finIdl D (z * sgU D z)), map_mul, map_mul]
  rw [show χ.1 (finPartI D.host.E b) = 1 from hb, one_mul]
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E χ.1 χ.2.1 _ (finPartI_mem_unitIdl.2 hun) (fun _ => rfl) fun v y hy => ?_
  have hy' : (y : v.adicCompletion D.host.E) = ((b⁻¹ * finIdl D (z * sgU D z) : _root_.Neutral.B1.Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 v := hy
  have hyu : _root_.Formalism.L2.Host.IsUnitAt v y := by
    unfold _root_.Formalism.L2.Host.IsUnitAt
    rw [hy']
    exact hun v
  change χ.loc v y = 1
  rcases hl v with hU | ⟨q, hq, hov, hL⟩
  · exact hU y hyu
  · have hlt : WithZero.exp (-((k : ℤ) + 1)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have h0 : Valued.v ((finIdl D (z * sgU D z) : AdeleRing (𝓞 D.host.E) D.host.E).2 v - 1) < 1 := by
      rw [vl_sub_one]
      exact (hz q hq v hov).trans_lt hlt
    have hv1 : IdlFact.valAt v (finIdl D (z * sgU D z)) = 1 := by
      rw [IdlFact.valAt_apply, ← sub_add_cancel ((finIdl D (z * sgU D z) : AdeleRing (𝓞 D.host.E) D.host.E).2 v) 1, add_comm]
      exact Valuation.map_one_add_of_lt _ h0
    have h3 : Units.map (GlobalTheory.Mem.LocTriv.ev v) (b⁻¹ * finIdl D (z * sgU D z)) = Units.map (GlobalTheory.Mem.LocTriv.ev v) (finIdl D (z * sgU D z)) := by
      rw [map_mul, map_inv, hc v hv1, inv_one, one_mul]
    have h4 := congrArg Units.val h3
    refine hL y hyu ?_
    rw [hy']
    change Valued.v (((b⁻¹ * finIdl D (z * sgU D z) : _root_.Neutral.B1.Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 v - 1) ≤ _
    have h4' : ((b⁻¹ * finIdl D (z * sgU D z) : _root_.Neutral.B1.Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 v =
        (finIdl D (z * sgU D z) : AdeleRing (𝓞 D.host.E) D.host.E).2 v := h4
    rw [h4', vl_sub_one]
    refine (hz q hq v hov).trans ?_
    rw [WithZero.exp_le_exp]
    omega

theorem mul_eq_mul_mul_inv {G : Type} [CommGroup G] (x y u v : G) : x * y = (u * v) * ((u * x⁻¹) * (v * y⁻¹))⁻¹ := by
  simp [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

theorem chi_finIdl_norm_eq_one : ∀ (D : D7) (χ : _root_.Formalism.L2.Host.HChar D.host.E) (n : D.what₂.Tau → ℤ) (S : Finset ℕ) (k : ℕ), χ.TrivOn D.host.F → χ.HasInf (embT D) n → (∀ q ∈ S, q.Prime) → (∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) → ∀ x : (AE D)ˣ, χ.1 (finIdl D (x * sgU D x)) = 1 := by
  intro D χ n S k ht hi hS hl x
  have hP : 0 < ∏ q ∈ S, q := Finset.prod_pos fun q hq => (hS q hq).pos
  have hm : 1 < (2 * ∏ q ∈ S, q) ^ (k + 1) := Nat.one_lt_pow (by omega) (by omega)
  obtain ⟨a, s, hs, e⟩ := exists_global_congN (D := D) hm x
  have hz : ∀ q ∈ S, ∀ v, Formalism.L2.Host.OverP D.host q v →
      vl D v ((((incU D a * x⁻¹) * sgU D (incU D a * x⁻¹) : (AE D)ˣ) : AE D) - 1) ≤ WithZero.exp (-((k : ℤ) + 1)) :=
    fun q hq v hov => (vl_norm_sub_one hs e v).trans
      (vl_pow_le (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hq) 2) hov k)
  have h1 := chi_norm_cong χ S k ht hl _ hz
  have h2 := chi_norm_global χ hi a
  have e2 : x * sgU D x = (incU D a * sgU D (incU D a)) * ((incU D a * x⁻¹) * sgU D (incU D a * x⁻¹))⁻¹ := by
    rw [map_mul, map_inv]
    exact mul_eq_mul_mul_inv _ _ _ _
  rw [e2, map_mul, map_mul, map_inv, map_inv, h2, h1, inv_one, one_mul]

end GlobalTheory.NormKill
end
end

section

noncomputable section

namespace GlobalTheory.EtaTildeNorm

section SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.IdlFact GlobalTheory.Mem.Chr.KDVal
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Col2.SplitChar

theorem map_finPartI_locF {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra F L] (χ : _root_.Formalism.L2.Host.HChar L)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ.1 (finPartI L (_root_.GlobalTheory.Mem.Chr.locF F v k)) = χ.resFin v k := by
  unfold _root_.Formalism.L2.Host.HChar.resFin
  rw [MonoidHom.finsetProd_apply]
  unfold _root_.GlobalTheory.Mem.Chr.locF
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun Q _ => congrArg χ.1 (GlobalTheory.Mem.KerDet.finPartI_localIdele Q _)

theorem eq_one (D : D7) (χ : _root_.Formalism.L2.Host.HChar D.host.E) (hχ : _root_.Formalism.L2.Host.IsEtaT D.host χ) (x : (AE D)ˣ) :
    χ.1 (finIdl D (x * sgU D x)) = 1 := by
  classical
  obtain ⟨c, hc, hcm, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have ec : c.toRingEquiv = D.host.conj.toRingEquiv := RingEquiv.ext hc
  set a : _root_.Neutral.B1.Ideles D.host.E := finIdl D (x * sgU D x) with ha_def
  have ha : a ∈ balanced (L := D.host.E) D.host.F := norm_balanced x
  let T : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
    (finite_valAt_ne_one a).toFinset.image fun w => w.under (𝓞 D.host.F)
  let m : HeightOneSpectrum (𝓞 D.host.F) → ℤ := fun v =>
    if h : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v then -WithZero.log (valAt h.choose a) else 0
  let b : _root_.Neutral.B1.Ideles D.host.E := ∏ v ∈ T, _root_.GlobalTheory.Mem.Chr.locF (L := D.host.E) D.host.F v (_root_.Formalism.L2.Host.unif v) ^ m v
  have hm : ∀ w : HeightOneSpectrum (𝓞 D.host.E), m (w.under (𝓞 D.host.F)) = -WithZero.log (valAt w a) := fun w => by
    have hex : ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := ⟨w, rfl⟩
    simp only [m]
    rw [dite_eq_left hex, ha w hex.choose hex.choose_spec]
  have hval : ∀ w, valAt w b = valAt w a := fun w => by
    have h1 : ∀ v, v ≠ w.under (𝓞 D.host.F) → valAt w (_root_.GlobalTheory.Mem.Chr.locF (L := D.host.E) D.host.F v (_root_.Formalism.L2.Host.unif v) ^ m v) = 1 :=
      fun v hv => by rw [map_zpow, valAt_locF, if_neg hv.symm, one_zpow]
    simp only [b]
    rw [map_prod]
    by_cases hw : w.under (𝓞 D.host.F) ∈ T
    · rw [Finset.prod_eq_single_of_mem _ hw (fun v _ hv => h1 v hv), map_zpow, valAt_locF, if_pos rfl, hu,
        ordF_unif_self, ← WithZero.exp_zsmul, hm]
      simp only [smul_eq_mul, mul_neg, neg_neg, mul_one]
      exact WithZero.exp_log (valAt_ne_zero w a)
    · rw [Finset.prod_eq_one (fun v hv => h1 v (fun e => hw (e ▸ hv)))]
      by_contra hne
      exact hw (Finset.mem_image_of_mem _ (by simpa using fun e => hne e.symm))
  have hu' : b⁻¹ * a ∈ unitIdl D.host.E := fun w => by
    rw [← valAt_apply, map_mul, map_inv, hval]
    exact inv_mul_cancel₀ (valAt_ne_zero w a)

  have h1 : χ.1 (finPartI D.host.E (b⁻¹ * a)) = 1 :=
    GlobalTheory.Mem.LocTriv.eq_one_of_local _ χ.1 χ.2.1 _ (finPartI_mem_unitIdl.2 hu') (fun _ => rfl) fun v y hy =>
      hχ.unr v y (by
        unfold _root_.Formalism.L2.Host.IsUnitAt
        rw [hy]
        exact hu' v)

  have h2 : χ.1 (finPartI D.host.E b) = 1 := by
    simp only [b]
    rw [map_prod, map_prod]
    refine Finset.prod_eq_one fun v hv => ?_
    rw [map_zpow, map_zpow, map_finPartI_locF, hχ.res.1 v, _root_.Formalism.L2.Host.etaFin]
    split_ifs with hcard
    · rw [ordF_unif_self, zpow_one]
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hv
      rw [hm]
      obtain ⟨w', hw', -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv w
      have hund : w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) :=
        (under_eq_iff_conjPl c hcm.rank hcm.ne w w').2 (Or.inr (by rw [ec]; exact hw'))
      have hmem : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) →
          Q ∈ _root_.Formalism.L2.Host.aboveF (L := D.host.E) D.host.F (w.under (𝓞 D.host.F)) := fun Q hQ => by
        simp [_root_.Formalism.L2.Host.aboveF, hQ]
      have hww : w' = w := Finset.card_le_one.1 hcard.le _ (hmem w' hund) _ (hmem w rfl)
      subst hww
      have e1 : valAt w' a = vl D w' (x : AE D) * vl D w' (x : AE D) := by
        change vl D w' ((x : AE D) * sgA D x) = _
        rw [map_mul, vl_sgA hw' x]
      have h0 : vl D w' (x : AE D) ≠ 0 := by
        intro h
        have := valAt_ne_zero w' a
        rw [e1, h, zero_mul] at this
        exact this rfl
      rw [e1, WithZero.log_mul h0 h0]
      exact Even.neg_one_zpow (Even.add_self _).neg
    · exact one_zpow _
  have e : a = b * (b⁻¹ * a) := (mul_inv_cancel_left b a).symm
  have e2 : finPartI D.host.E a = a := by rw [ha_def]; exact finPartI_finIdl D _
  rw [← e2, e, map_mul, map_mul, h1, h2, one_mul]

end SlopeTestRemainingChoices

end GlobalTheory.EtaTildeNorm

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

theorem GlobalTheory.EtaTildeNorm.map_finIdl_norm : ∀ (D : D7) (χ : HChar D.host.E), Formalism.L2.Host.IsEtaT D.host χ →
    ∀ x : (AE D)ˣ, χ.1 (finIdl D (x * sgU D x)) = 1 :=
  fun D χ hχ x => GlobalTheory.EtaTildeNorm.eq_one D χ hχ x
end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.HeckeCont

open Formalism.L2.Host GlobalTheory.Mem.Col2.SplitChar

theorem le_exp_neg_one_of_lt_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem eq_one_of_cong : ∀ (D : D7) (χ : HChar D.host.E) (S : Finset ℕ) (k : ℕ), (∀ q ∈ S, q.Prime) → (∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) → ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) → χ.1 (finIdl D u) = 1 := by
  intro D χ S k hS hv
  refine ⟨(∏ q ∈ S, q) ^ k, pow_pos (Finset.prod_pos fun q hq => (hS q hq).pos) k, ?_⟩
  rintro u hu ⟨s, hs, e⟩
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local _ χ.1 χ.2.1 (finIdl D u) (finIdl_unit hu) (fun w => ?_) (fun v x hx => ?_)
  · rw [finIdl_fst]
    rfl
  · have hU : Valued.v ((finIdl D u : AdeleRing (𝓞 D.host.E) D.host.E).2 v) = 1 := finIdl_unit hu v
    have hxU : IsUnitAt v x := by
      show Valued.v (x : v.adicCompletion D.host.E) = 1
      rw [hx]
      exact hU
    rcases hv v with hunr | ⟨q, hq, hov, hlev⟩
    · exact hunr x hxU
    · refine hlev x hxU ?_
      rw [hx, vl_sub_one, e]
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun q : ℕ => q) hq
      have hP : OverP D.host (∏ q ∈ S, q) v := by
        show (((∏ q ∈ S, q : ℕ)) : 𝓞 D.host.E) ∈ v.asIdeal
        rw [hc, Nat.cast_mul]
        exact Ideal.mul_mem_right _ _ hov
      have h1 := le_exp_neg_one_of_lt_one (val_nat_lt hP)
      rw [map_mul, Nat.cast_pow, map_pow]
      calc vl D v ((∏ q ∈ S, q : ℕ) : AE D) ^ k * vl D v s ≤ vl D v ((∏ q ∈ S, q : ℕ) : AE D) ^ k :=
            mul_le_of_le_one_right' (vl_le hs v)
        _ ≤ WithZero.exp (-1 : ℤ) ^ k := pow_le_pow_left₀ zero_le' h1 k
        _ = WithZero.exp (-(k : ℤ)) := by rw [← WithZero.exp_nsmul]; congr 1; simp

end GlobalTheory.HeckeCont
end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.SqNum.UnrKill

open GlobalTheory.Mem.Col2.SplitChar

theorem vl_nat_coprime {D : D7} {q m : ℕ} (hm : Nat.Coprime m q) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : Formalism.L2.Host.OverP D.host q v) : vl D v (m : AE D) = 1 := by
  refine le_antisymm (vl_le (natCast_mem _ _) v) (not_lt.1 fun hlt => ?_)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hm
  have hab' := congrArg (Int.cast : ℤ → AE D) hab
  push_cast at hab'
  have h2 : vl D v ((a : AE D) * m) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' (vl_le (intCast_mem _ _) v)).trans_lt hlt
  have h3 : vl D v ((b : AE D) * q) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' (vl_le (intCast_mem _ _) v)).trans_lt (val_nat_lt hv)
  have h4 := Valuation.map_add_lt _ h2 h3
  rw [hab', map_one] at h4
  exact lt_irrefl _ h4

theorem le_exp_neg_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem vl_le_of_zeroAt {D : D7} {q : ℕ} {x : AE D} (h : ZeroAt D q x) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : Formalism.L2.Host.OverP D.host q v) (k : ℕ) : vl D v x ≤ WithZero.exp (-(k : ℤ)) := by
  obtain ⟨m, -, hm, s, hs, e⟩ := h k
  have h1 := vl_nat_coprime hm hv
  have h2 : vl D v x = vl D v (q : AE D) ^ k * vl D v s := by
    rw [← one_mul (vl D v x), ← h1, ← map_mul, e, map_mul, map_pow]
  rw [h2]
  refine (mul_le_of_le_one_right' (vl_le hs v)).trans ?_
  calc vl D v (q : AE D) ^ k ≤ WithZero.exp (-1 : ℤ) ^ k := pow_le_pow_left₀ zero_le' (le_exp_neg_one (val_nat_lt hv)) k
    _ = WithZero.exp (-(k : ℤ)) := by rw [← WithZero.exp_nsmul]; congr 1; simp

end GlobalTheory.FunObj.SqNum.UnrKill


open GlobalTheory.FunObj.SqNum.UnrKill GlobalTheory.Mem.Col2.SplitChar in
theorem GlobalTheory.FunObj.SqNum.hchar_finIdl_eq_one_of_zeroAt : ∀ (D : D7) (χ : HChar D.host.E) (S : Finset ℕ) (k : ℕ), (∀ q ∈ S, q.Prime ∧ ¬ InertQ D q) → (∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) → ∀ u, IntU D u → (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((u : AE D) - 1)) → χ.1 (finIdl D u) = 1 := by
  intro D χ S k hS hχ u hu hz
  have hU := finIdl_unit hu
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E χ.1 χ.2.1 (finIdl D u) hU
    (fun w => by rw [finIdl_fst]; rfl) (fun v x hx => ?_)
  have hxu : Formalism.L2.Host.IsUnitAt v x := by
    show Valued.v (x : v.adicCompletion D.host.E) = 1
    rw [hx]
    exact hU v
  rcases hχ v with h | ⟨q, hq, hov, hl⟩
  · exact h x hxu
  · refine hl x hxu ?_
    rw [hx, vl_sub_one]
    exact vl_le_of_zeroAt (hz q (hS q hq).1 (hS q hq).2) hov k
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.FlagCell

def uniR {R : Type*} [CommRing R] {m : ℕ} (n : Low m → R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun a b => if h : b < a then n ⟨(a, b), h⟩ else if a = b then 1 else 0

theorem uniR_apply {R : Type*} [CommRing R] {m : ℕ} (n : Low m → R) (a b : Fin m) :
    uniR n a b = if h : b < a then n ⟨(a, b), h⟩ else if a = b then 1 else 0 := rfl

theorem map_uniR {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ} (n : Low m → R) :
    (uniR n).map f = uniR fun s => f (n s) := by
  ext a b
  simp only [Matrix.map_apply, uniR_apply]
  split_ifs <;> simp

end GlobalTheory.FlagCell
end
end
