module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Formalism.PairingDivisors.PairingDivisorProofs.Height
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle001
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySubsingletonEtaleOverPolynomi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Ideal.Norm.RelNorm
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.NormLevel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem absNorm_eq_under_of_idemAt {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm (P.asIdeal.under (𝓞 D.host.F)) := by
  classical
  have hns := Formalism.IndefR.Fin.idemAt_split he
  let c : 𝓞 D.host.E ≃+* 𝓞 D.host.E := Formalism.DivisionValues.cO D.host.E
  have hc : ∀ x : 𝓞 D.host.E, ((c x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) := fun x => rfl
  have hcc : ∀ x, c (c x) = x := fun x => RingOfIntegers.ext (by rw [hc, hc, star_star])
  have hcF : ∀ a : 𝓞 D.host.F, c (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a :=
    fun a => RingOfIntegers.ext (by
      rw [hc]
      exact Formalism.IndefR.Eqv.star_algebraMapF D (a : D.host.F))
  let Q : Ideal (𝓞 D.host.E) := P.asIdeal.comap (c : 𝓞 D.host.E →+* 𝓞 D.host.E)
  have hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQv : Q.under (𝓞 D.host.F) = P.asIdeal.under (𝓞 D.host.F) := by
    ext a
    show c (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ∈ P.asIdeal ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P.asIdeal
    rw [hcF]
  have hne : Q ≠ P.asIdeal := by
    intro h
    apply hns
    intro x hx
    have hx' : c x ∈ Q := by
      show c (c x) ∈ P.asIdeal
      rw [hcc]; exact hx
    rw [h] at hx'
    exact ⟨c x, hx', hc x⟩
  set p := P.asIdeal.under (𝓞 D.host.F) with hp
  have hp0 : p ≠ ⊥ := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
  have hpP : p.IsPrime := Ideal.IsPrime.comap _
  have hpM : p.IsMaximal := hpP.isMaximal hp0
  haveI hl1 : P.asIdeal.LiesOver p := ⟨rfl⟩
  haveI hl2 : Q.LiesOver p := ⟨hQv.symm⟩
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 D.host.E)
  rw [← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E, D.sp.cm.deg2] at hsum
  let P1 : p.primesOver (𝓞 D.host.E) := ⟨P.asIdeal, P.isPrime, hl1⟩
  let Q1 : p.primesOver (𝓞 D.host.E) := ⟨Q, hQp, hl2⟩
  have h12 : P1 ≠ Q1 := fun h => hne (congrArg Subtype.val h).symm
  have hpos : ∀ R : p.primesOver (𝓞 D.host.E),
      1 ≤ R.1.ramificationIdx (𝓞 D.host.F) * R.1.inertiaDeg (𝓞 D.host.F) := fun R =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hle : P1.1.ramificationIdx (𝓞 D.host.F) * P1.1.inertiaDeg (𝓞 D.host.F) +
      Q1.1.ramificationIdx (𝓞 D.host.F) * Q1.1.inertiaDeg (𝓞 D.host.F) ≤ 2 := by
    rw [← hsum, ← Finset.sum_pair (f := fun R : p.primesOver (𝓞 D.host.E) =>
      R.1.ramificationIdx (𝓞 D.host.F) * R.1.inertiaDeg (𝓞 D.host.F)) h12]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h1 := hpos P1
  have h2 := hpos Q1
  have hef : P.asIdeal.ramificationIdx (𝓞 D.host.F) * P.asIdeal.inertiaDeg (𝓞 D.host.F) = 1 := by
    change P1.1.ramificationIdx (𝓞 D.host.F) * P1.1.inertiaDeg (𝓞 D.host.F) = 1
    omega
  have hf : P.asIdeal.inertiaDeg (𝓞 D.host.F) = 1 := Nat.eq_one_of_mul_eq_one_left hef
  rw [← Ideal.absNorm_pow_inertiaDeg p P.asIdeal, hf, pow_one]

variable {T : Type} {L : LevCh D T}


open Classical in
theorem absNorm_w (P : Places L) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ P.S0) :
    Ideal.absNorm (P.w v).asIdeal = Ideal.absNorm v.asIdeal := by
  have hv' : v ∈ insert P.v0 (S1 D) := by
    rcases P.mem_S0_of_sum_eq.1 hv with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem h
  obtain ⟨e, he⟩ := P.w_split v hv'
  have hu : (P.w v).asIdeal.under (𝓞 D.host.F) = v.asIdeal := by
    rw [← HeightOneSpectrum.under_asIdeal, P.under_w hv]
  rw [absNorm_eq_under_of_idemAt he, hu]

theorem absNorm_condE : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L), Ideal.absNorm (GlobalTheory.FunObj.SqNum.condE P) = GlobalTheory.FunObj.SqNum.levQ P := by
  intro D T L P
  unfold GlobalTheory.FunObj.SqNum.condE GlobalTheory.FunObj.SqNum.levQ
  rw [map_prod]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [map_pow, absNorm_w P hv]

end GlobalTheory.FunObj.NormLevel

end
end

section

open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.FunObj.SqNum.LowVal

theorem coeff_zero_mul_pow_mem {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {β : ℂ} {p : K[X]}
    (h : IsMinPol σ β p) {c : ℕ} (hc0 : (c : K) ≠ 0) (hc : IsIntegral ℤ ((c : ℂ) * β)) :
    ∃ a : 𝓞 K, p.coeff 0 * (c : K) ^ p.natDegree = (a : K) := by
  letI : Algebra K ℂ := σ.toAlgebra
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  haveI : IsScalarTower (𝓞 K) K ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ℤ (𝓞 K) ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hβ : IsIntegral K β := ⟨p, h.1, h.2.2⟩
  have es : (c : K) • β = (c : ℂ) * β := by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_natCast]
  have hγ : IsIntegral (𝓞 K) ((c : K) • β) := by
    rw [es]; exact hc.tower_top
  have e1 := IsIntegrallyClosed.minpoly_smul (R := K) hc0 hβ
  have e2 := minpoly.isIntegrallyClosed_eq_field_fractions' K hγ
  rw [← h.eq_minpoly] at e1
  refine ⟨(minpoly (𝓞 K) ((c : K) • β)).coeff 0, ?_⟩
  rw [RingOfIntegers.coe_eq_algebraMap, ← coeff_map, ← e2, e1, coeff_scaleRoots, Nat.sub_zero]

theorem natCast_not_mem {K : Type} [Field K] [NumberField K] {w : Formalism.PairingDivisionLocalBalance.Pl K} {l n : ℕ} (hn : n.Coprime l)
    (hw : (l : 𝓞 K) ∈ w.asIdeal) : (n : 𝓞 K) ∉ w.asIdeal := by
  intro h
  obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 hn).map (Int.castRingHom (𝓞 K))
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← e]
  exact add_mem (Ideal.mul_mem_left _ _ (by simpa using h)) (Ideal.mul_mem_left _ _ (by simpa using hw))

theorem vw_coeff_zero_ge : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]) (l N : ℕ),
    GlobalTheory.FunObj.SqNum.IsMinPol σ β p → l.Prime → GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ (N : ℤ) * β) →
    ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, (l : 𝓞 K) ∈ w.asIdeal → -(((N * p.natDegree : ℕ) : ℤ) * vw w (l : K)) ≤ vw w (p.coeff 0) := by
  intro K _ _ _ σ β p l N h hl ⟨n, hn, hi⟩ w hw
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' (Nat.coprime_zero_left l |>.1 hn)
  have hc : IsIntegral ℤ (((n * l ^ N : ℕ) : ℂ) * β) := by
    convert hi using 1
    push_cast
    rw [zpow_natCast]
    ring
  have hl0 : (l : K) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hn0' : (n : K) ≠ 0 := by exact_mod_cast hn0
  have hc0 : ((n * l ^ N : ℕ) : K) ≠ 0 := by
    push_cast
    exact mul_ne_zero hn0' (pow_ne_zero _ hl0)
  obtain ⟨a, ha⟩ := coeff_zero_mul_pow_mem h hc0 hc
  have h1 : 0 ≤ vw w (p.coeff 0 * ((n * l ^ N : ℕ) : K) ^ p.natDegree) := by
    rw [ha]; exact Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w a
  have hvn : vw w (n : K) = 0 := by
    have := Formalism.DivisionValues.ReductionFirst.vw_unit w (n : 𝓞 K) (natCast_not_mem hn hw)
    simpa using this
  have hvl := Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w l
  by_cases hp0 : p.coeff 0 = 0
  · rw [hp0, Formalism.DivisionValues.ValuationRepresentative.vw_zero]
    have : (0 : ℤ) ≤ ((N * p.natDegree : ℕ) : ℤ) := Int.natCast_nonneg _
    nlinarith
  · rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hp0 (pow_ne_zero _ hc0), Formalism.PairingDivisionLocalBalance.vw_pow w _ hc0] at h1
    push_cast at h1
    rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hn0' (pow_ne_zero _ hl0), Formalism.PairingDivisionLocalBalance.vw_pow w _ hl0, hvn] at h1
    push_cast
    nlinarith

end GlobalTheory.FunObj.SqNum.LowVal
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.ChiGrid

theorem botBig_add_botSmall_le_two_e_add_two_cen (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) :
    ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) ≤
      2 * ((GlobalTheory.ChiGrid.num D C τ).e (j + 1) + GlobalTheory.ChiGrid.cen D C τ (D.R.m - i)) := by
  set P := D.hc τ with hP
  set G := GlobalTheory.SignedHC.GridData.ofHCParam P (sLen D) (gap D C) 0 with hG
  obtain ⟨hv, hb, -⟩ := GlobalTheory.SignedHC.GridData.ofHCParam_spec P (sLen D) (gap D C) 0
  have he := (GlobalTheory.SignedHC.GridData.ofHCParam_spec P (sLen D) (gap D C) (cen D C τ)).2.2 j
  have hne : (num D C τ).e (j + 1) = (GlobalTheory.SignedHC.GridData.ofHCParam P (sLen D) (gap D C) (cen D C τ)).e (j.1 + 1) := rfl
  have hj := j.2
  have hi := i.2
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hGm : G.m = D.R.m := rfl
  have hGk : G.k = D.R.k := rfl
  have hGga : G.ga = gap D C := rfl
  have h1 := P.gap_be j
  have e0 : P.b ⟨0, by omega⟩ = (G.b 1 : ℚ) := hb ⟨0, by omega⟩
  have ej : P.b j = (G.b (j.1 + 1) : ℚ) := hb j
  have h2 : P.b ⟨0, by omega⟩ ≤ P.b j := by
    rcases Nat.eq_zero_or_pos j.1 with h0 | hj0
    · exact le_of_eq (congrArg P.b (Fin.ext (by simp [h0])))
    · have := G.b_mono 1 (j.1 + 1) le_rfl (by omega) (by rw [hGm]; omega)
      rw [e0, ej]; exact_mod_cast this.le
  have hu2 := P.u_last_gt (by omega) (by omega)
  have hu1 := P.v_gt_u ⟨D.R.k - 2, by omega⟩
  have hu : P.u ⟨D.R.k - 2 + 1, by omega⟩ = P.u ⟨D.R.k - 1, by omega⟩ :=
    congrArg P.u (Fin.ext (by dsimp only; omega))
  have ev0 : P.v ⟨0, by omega⟩ = (G.v 2 : ℚ) := hv ⟨0, by omega⟩
  have evl : P.v ⟨D.R.k - 2, by omega⟩ = (G.v D.R.k : ℚ) := by
    have := hv ⟨D.R.k - 2, by omega⟩
    dsimp only at this
    rwa [Nat.sub_add_cancel (by omega : 2 ≤ D.R.k)] at this
  have hvv : G.v D.R.k < G.v 2 := G.v_anti 2 D.R.k le_rfl (by omega) (by rw [hGk])
  have hvv' : (G.v D.R.k : ℚ) < G.v 2 := by exact_mod_cast hvv
  rw [hu] at hu1
  rw [evl] at hu1
  have hc : G.mid (D.R.m - i) < (cen D C τ (D.R.m - i) : ℚ) + 1 := Int.lt_floor_add_one _
  have hmid : G.mid (D.R.m - i) = G.a (D.R.m - i) + G.ga / 2 := G.mid_eq (by omega)
  have ha : G.a (D.R.m - i) = (G.v 2 : ℚ) + 1 / 2 + ((i : ℚ) + 1) * (gap D C : ℚ) := by
    simp only [GlobalTheory.SignedHC.GridData.a, hGm, hGga]
    rw [Nat.cast_sub hi.le]; ring
  rw [hmid, ha, hGga] at hc
  have hg := (isLeast_gap D C).1.2.1
  have hN : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have hr : D.R.r + 1 = D.R.k + D.R.m := by unfold Formalism.BasicNotions.Ranks.r; omega
  have m1 : (j.1 + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
  have m2 : j.1 * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
  have m3 : (i.1 + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have m4 : i.1 * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have hrank : rankV D (i.1 + 1) (j.1 + 1) + rankV D i.1 j.1 ≤ 2 * bigN D := by
    unfold rankV bigN; nlinarith
  have hbot : GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j ≤
      rankV D (i.1 + 1) (j.1 + 1) + rankV D i.1 j.1 := by
    unfold GlobalTheory.FunObj.SqNum.botBig GlobalTheory.FunObj.SqNum.botSmall; omega
  have hR : GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j + 1 ≤ gap D C := by omega
  have hR' : ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℚ) + 1 ≤ (gap D C : ℚ) := by
    exact_mod_cast hR
  have hpos : (0 : ℚ) ≤ (i : ℚ) * (gap D C : ℚ) := by positivity
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have h0 : (0 : ℚ) ≤ ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℚ) := by positivity
  have key : ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℚ) <
      2 * ((num D C τ).e (j + 1) : ℚ) + 2 * (cen D C τ (D.R.m - i) : ℚ) := by
    rw [hne, ← he]
    nlinarith
  have key' : ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) <
      2 * ((num D C τ).e (j + 1) + cen D C τ (D.R.m - i)) := by
    have : (((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) : ℚ) <
        ((2 * ((num D C τ).e (j + 1) + cen D C τ (D.R.m - i)) : ℤ) : ℚ) := by
      push_cast; push_cast at key; linarith
    exact_mod_cast this
  exact key'.le

end GlobalTheory.ChiGrid
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.FunObj.SqNum.CondExps

theorem exists_condExps : ∀ (D : D7) [IsCMField D.host.E] {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (s : ℕ)
    (κ : D.what₂.Tau → ℕ) (χ : HChar D.host.E), IsValChar (cmPhi D) s κ (condF G.pl) ∅ χ →
    ∃ a : HeightOneSpectrum (𝓞 D.host.E) →₀ ℕ, (∀ v, ExpAt χ v (a v)) ∧
      (a.prod fun v k => Ideal.absNorm v.asIdeal ^ k) ≤ levQ G.pl ^ 2 := by
  intro D _ T Lc sc G s κ χ hχ
  let 𝔣 : Ideal (𝓞 D.host.F) := condF G.pl
  let 𝔐 : Ideal (𝓞 D.host.E) := 𝔣.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
  have hrank : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 :=
    (IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E).symm.trans
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
  have hnorm𝔣 : Ideal.absNorm 𝔣 = levQ G.pl := by
    simp only [𝔣, condF, levQ, map_prod, map_pow]
  have hlev : 0 < levQ G.pl := Finset.prod_pos fun v _ =>
    pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _
  have hnorm𝔐 : Ideal.absNorm 𝔐 = levQ G.pl ^ 2 := by
    rw [Ideal.absNorm_algebraMap, hrank, hnorm𝔣]
  have h𝔐0 : 𝔐 ≠ ⊥ := fun h => by
    have h' := hnorm𝔐
    rw [h, Ideal.absNorm_bot] at h'
    exact (pow_pos hlev 2).ne' h'.symm
  let f : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun P => expIn (condF G.pl) (P.under (𝓞 D.host.F))
  have hdvd : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.asIdeal ^ f P ∣ 𝔐 := fun P => by
    have h1 : (P.under (𝓞 D.host.F)).asIdeal ^ f P ∣ 𝔣 := pow_multiplicity_dvd _ _
    have h2 : P.asIdeal ∣ (P.under (𝓞 D.host.F)).asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) :=
      Ideal.dvd_iff_le.2 Ideal.map_comap_le
    obtain ⟨c, hc⟩ := h1
    calc P.asIdeal ^ f P ∣ ((P.under (𝓞 D.host.F)).asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) ^ f P :=
          pow_dvd_pow_of_dvd h2 _
      _ ∣ 𝔐 := by
          refine ⟨c.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), ?_⟩
          show 𝔣.map _ = _
          rw [hc, Ideal.map_mul, Ideal.map_pow]
  have hfin : (Function.support f).Finite := by
    refine (Ideal.finite_factors h𝔐0).subset fun P hP => ?_
    exact (dvd_pow_self _ hP).trans (hdvd P)
  refine ⟨Finsupp.ofSupportFinite f hfin, fun P => ?_, ?_⟩
  · exact (hχ.2.2.2 (P.under (𝓞 D.host.F)) P rfl).2 (Finset.notMem_empty _)
  · set a := Finsupp.ofSupportFinite f hfin
    have hJ : (a.prod fun P k => P.asIdeal ^ k) ∣ 𝔐 := by
      refine Finset.prod_dvd_of_coprime (fun P _ Q _ hPQ => ?_) fun P _ => ?_
      · exact (Ideal.isCoprime_of_isMaximal fun h => hPQ (HeightOneSpectrum.ext h)).pow
      · exact hdvd P
    have e : (a.prod fun v k => Ideal.absNorm v.asIdeal ^ k) = Ideal.absNorm (a.prod fun P k => P.asIdeal ^ k) := by
      simp only [Finsupp.prod, map_prod, map_pow]
    rw [e, ← hnorm𝔐]
    exact Nat.le_of_dvd (hnorm𝔐 ▸ pow_pos hlev 2) (map_dvd Ideal.absNorm hJ)

end GlobalTheory.FunObj.SqNum.CondExps
end
end

section

open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.FunObj.SqNum

theorem IsMinPol.scaleRoots_eq {K : Type} [Field K] {σ : K →+* ℂ} {β : ℂ} {u : K} {p q : K[X]}
    (hp : IsMinPol σ β p) (hq : IsMinPol σ (σ u * β) q) (hu : u ≠ 0) : q = p.scaleRoots u := by
  let := σ.toAlgebra
  have ep := hp.eq_minpoly
  have eq := hq.eq_minpoly
  have hr0 : (p.scaleRoots u).eval₂ σ (σ u * β) = 0 := scaleRoots_eval₂_eq_zero σ hp.2.2
  have hs0 : (q.scaleRoots u⁻¹).eval₂ σ β = 0 := by
    have := scaleRoots_eval₂_eq_zero σ (s := u⁻¹) hq.2.2
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul] at this
  have d1 : q ∣ p.scaleRoots u := by
    rw [eq]; exact minpoly.dvd K (σ u * β) hr0
  have d2 : p ∣ q.scaleRoots u⁻¹ := by
    rw [ep]; exact minpoly.dvd K β hs0
  have hq0 : q.scaleRoots u⁻¹ ≠ 0 := scaleRoots_ne_zero hq.1.ne_zero _
  have le1 : p.natDegree ≤ q.natDegree := by
    have := natDegree_le_of_dvd d2 hq0
    rwa [natDegree_scaleRoots] at this
  exact (eq_of_monic_of_dvd_of_natDegree_le hq.1 ((monic_scaleRoots_iff u).2 hp.1) d1
    (by rw [natDegree_scaleRoots]; exact le1)).symm

end GlobalTheory.FunObj.SqNum

theorem GlobalTheory.FunObj.SqNum.meanVal_vw_smul : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (u : K) (p q : K[X]), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → GlobalTheory.FunObj.SqNum.IsMinPol σ (σ u * β) q → β ≠ 0 → u ≠ 0 → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, GlobalTheory.FunObj.SqNum.meanVal_vw w q = GlobalTheory.FunObj.SqNum.meanVal_vw w p + vw w u := by
  intro K _ _ _ σ β u p q hp hq hβ hu w
  obtain ⟨hc, hd⟩ := hp.ne_zero hβ
  rw [hp.scaleRoots_eq hq hu]
  unfold GlobalTheory.FunObj.SqNum.meanVal_vw
  rw [natDegree_scaleRoots, coeff_scaleRoots, Nat.sub_zero]
  have hm : vw w (p.coeff 0 * u ^ p.natDegree) = vw w (p.coeff 0) + p.natDegree * vw w u := by
    unfold vw
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul K w (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 hc)
        (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 (pow_ne_zero _ hu)),
      ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]
  rw [hm]
  have : (p.natDegree : ℝ) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
end

section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.BotPairSmall

def cvec (D : D7) (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (o a d : ℕ) (e0 : VC D a d → ℂ) : VC D a d → ℂ :=
  ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
    Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d))
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)

def blockSet (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : Set (GA D N) :=
  {h | h ∈ intG D N ∧ ∀ i j : Fin N, j.1 < a → a ≤ i.1 →
    ((h : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪}

def blockJ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : Subgroup (GA D N) := Subgroup.closure (blockSet D 𝔪 a N)

theorem blockJ_le (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : blockJ D 𝔪 a N ≤ intG D N :=
  (Subgroup.closure_le _).2 fun _ h => h.1

theorem conj_smul_ne_bot (D : D7) {𝔪 : Ideal (𝓞 D.host.E)} (h : 𝔪 ≠ ⊥) : D.host.conj • 𝔪 ≠ ⊥ := by
  intro e
  apply h
  have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) e
  simpa [smul_smul] using this

end GlobalTheory.BotPairSmall
end
end

section

namespace GlobalTheory.HatProductMembership

open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.FunObj.SqNum

theorem mul_mem_hat_mul {D : D7} {I J : Ideal (𝓞 D.host.E)} {x y : AE D}
    (hx : x ∈ hatId D I) (hy : y ∈ hatId D J) : x * y ∈ hatId D (I * J) := by
  unfold hatId at hx hy ⊢
  induction hx using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨u, hu, s, hs, rfl⟩ := ha
    induction hy using AddSubgroup.closure_induction with
    | mem b hb =>
      obtain ⟨v, hv, t, ht, rfl⟩ := hb
      refine AddSubgroup.subset_closure
        ⟨u * v, Ideal.mul_mem_mul hu hv, s * t, (OhE D).mul_mem hs ht, ?_⟩
      have h : ((u * v : 𝓞 D.host.E) : D.host.E) = (u : D.host.E) * (v : D.host.E) := rfl
      rw [h, map_mul]
      ring
    | zero => rw [mul_zero]; exact zero_mem _
    | add b c _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg b _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg a _ h => rw [neg_mul]; exact neg_mem h

end GlobalTheory.HatProductMembership
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistCohomology_subsingleton_etale_over_polynomial_algClosed : ∀ (q : ℕ) [NeZero q] (K E : Type) [Field K] [IsAlgClosed K] [CommRing E] [Algebra (Polynomial K) E] [Algebra.Etale (Polynomial K) E], IsUnit (q : K) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp E) n i) := by
  first | (exact @GlobalTheory.EtAlgCD.etale_polynomial_cd_le_one) | (exact GlobalTheory.EtAlgCD.etale_polynomial_cd_le_one) | (intros; apply GlobalTheory.EtAlgCD.etale_polynomial_cd_le_one <;> assumption)
end
