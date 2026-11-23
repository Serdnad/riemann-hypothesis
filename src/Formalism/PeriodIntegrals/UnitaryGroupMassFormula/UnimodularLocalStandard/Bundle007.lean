module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.DescentStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepHSelfInt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepSingleSat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem keyStartRam_of_unit (hU : UnitVecRam) : KeyStartRam := by
  intro a b c d ha hd lam hlam m _ _ Λ l x y T i₀ hK hld
  subst l
  have hK0 := hK
  obtain ⟨hOK, hsd, hθ, -, h2, hdp, hQ, hi₀, -⟩ := hK0
  set L := cmL a b d ha hd lam hlam with hL
  set κ := repKappa a b d ha hd lam hlam with hκdef
  set Q : ℤ := a * x ^ 2 + b * x * y + c * y ^ 2 with hQdef
  set f := fvec a b d lam x y i₀ with hf
  have hκ : κ ≠ 0 := rep_kappa_ne a b d ha hd lam hlam
  have hκc : conj κ = κ := kappa_real a b d ha hd lam hlam
  have hHf : stdH L m f f = κ * (Q : ℂ) := rep_norm_f a b c d ha hd lam hlam m hOK.1 x y i₀
  have hQ0 : (Q : ℂ) ≠ 0 := by
    have : Q ≠ 0 := fun h => hQ (h ▸ dvd_zero _)
    exact_mod_cast this
  have hfT : ∀ j ∈ T, f j = 0 := by
    intro j hj
    have hne : j ≠ i₀ := fun h => hi₀ (h ▸ hj)
    simp [hf, fvec, hne]
  have hfmem : f ∈ stdLat L m := rep_fvec_mem a b d ha hd lam hlam m x y i₀
  set M := relIdx Λ (stdLat L m) with hMdef
  have hMf : M • f ∈ Λ := by
    have h := AddSubgroup.nsmul_index_mem (Λ.addSubgroupOf (stdLat L m)) ⟨f, hfmem⟩
    rw [AddSubgroup.mem_addSubgroupOf] at h
    simpa [hMdef, relIdx, AddSubgroup.relIndex] using h
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast h2
  have hgf : M • f = (M : ℂ) • f := (Nat.cast_smul_eq_nsmul ℂ M f).symm
  set g := M • f with hg
  have hHs : ∀ (α β : ℂ) (u v : m → ℂ), stdH L m (α • u) (β • v) = α * conj β * stdH L m u v := by
    intro α β u v
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul]
    ring
  have hgT : ∀ j ∈ T, g j = 0 := by
    intro j hj
    simp [hgf, hfT j hj]
  have hg0 : g ≠ 0 := by
    intro h
    have h' : stdH L m g g = 0 := by rw [h]; simp
    rw [hgf, hHs, hHf] at h'
    have : (M : ℂ) * conj (M : ℂ) * (κ * Q) ≠ 0 := by
      simp only [map_natCast]
      exact mul_ne_zero (mul_ne_zero hMc hMc) (mul_ne_zero hκ hQ0)
    exact this h'
  have hgS : SatMem d Λ g := rep_sat_of_mem d Λ hMf hdp
  have hd1 : ¬ (d : ℤ) ∣ 1 := by
    intro h
    have := Int.eq_one_of_dvd_one (by positivity) h
    exact hdp.one_lt.ne' (by exact_mod_cast this)
  obtain ⟨y1, hy1S, hy1T, -, p1, q1, hp1, hq1, hy1H⟩ :=
    hU a b c d ha hd lam hlam m Λ x y T i₀ hK 0 (rep_sat_zero d Λ hdp) (by simp) (Or.inl rfl)
      g hgS hgT (by simp) hg0
  have hp1c : (p1 : ℂ) ≠ 0 := by
    have : p1 ≠ 0 := fun h => hp1 (h ▸ dvd_zero _)
    exact_mod_cast this
  have hq1c : (q1 : ℂ) ≠ 0 := by
    have : q1 ≠ 0 := fun h => hq1 (h ▸ dvd_zero _)
    exact_mod_cast this
  obtain ⟨n', c₂, s', hs', hpair⟩ := sat_pair hOK hsd hθ hdp hgS hy1S
  rw [← hL, ← hκdef] at hy1H hpair
  have hs'c : (s' : ℂ) ≠ 0 := by
    have : s' ≠ 0 := fun h => hs' (h ▸ dvd_zero _)
    exact_mod_cast this
  have hθc : conj (cmTheta b d) = (b : ℂ) - cmTheta b d := by
    have := rep_theta_add_conj b d
    linear_combination this
  set γ0 : ℂ := (q1 : ℂ) * ((n' : ℂ) - c₂ * conj (cmTheta b d)) with hγ0
  set z : m → ℂ := (((p1 * s' : ℤ) : ℂ)) • g - γ0 • y1 with hz
  have hzS : SatMem d Λ z := by
    have h1 := rep_sat_zsmul d Λ hgS (p1 * s')
    have h2 := rep_sat_elt d Λ hdp hθ hy1S (q1 * n') (q1 * c₂) 1 hd1
    have h3 : ((((q1 * n' : ℤ) : ℂ) - ((q1 * c₂ : ℤ) : ℂ) * conj (cmTheta b d)) / ((1 : ℤ) : ℂ)) = γ0 := by
      rw [hγ0]; push_cast; ring
    rw [h3] at h2
    exact rep_sat_sub d Λ hdp h1 h2
  have hzT : ∀ j ∈ T, z j = 0 := by
    intro j hj
    simp [hz, hgT j hj, hy1T j hj]
  have hzy : stdH L m z y1 = 0 := by
    have e1 : stdH L m z y1 = ((p1 * s' : ℤ) : ℂ) * stdH L m g y1 - γ0 * stdH L m y1 y1 := by
      simp only [hz, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [e1, hpair, hy1H, hγ0]
    push_cast
    field_simp
    ring
  by_cases hz0 : z = 0
  · set r : ℂ := ((p1 * s' : ℤ) : ℂ) * M with hr
    have hr0 : r ≠ 0 := by
      rw [hr]; push_cast
      exact mul_ne_zero (mul_ne_zero hp1c hs'c) hMc
    have hrc : conj r = r := by rw [hr]; simp
    have hrf : r • f = γ0 • y1 := by
      have : ((p1 * s' : ℤ) : ℂ) • g = γ0 • y1 := sub_eq_zero.mp (by rw [← hz]; exact hz0)
      rw [hgf, smul_smul] at this
      simpa [hr] using this
    set β : ℂ := γ0 / r with hβ
    have hβN : β * conj β = ((Q * q1 : ℤ) : ℂ) / ((p1 : ℤ) : ℂ) := by
      have e := congrArg (fun v => stdH L m v v) hrf
      simp only [hHs, hHf, hy1H, hrc] at e
      field_simp at e
      rw [hβ, map_div₀, hrc, div_mul_div_comm, div_eq_div_iff (mul_ne_zero hr0 hr0) hp1c]
      push_cast
      linear_combination -e
    have hβK : IsK b d β := by
      refine ⟨q1 * (n' - c₂ * b), q1 * c₂, p1 * s' * M, ?_, ?_⟩
      · have : ((p1 * s' * M : ℤ) : ℂ) ≠ 0 := by
          push_cast; exact mul_ne_zero (mul_ne_zero hp1c hs'c) hMc
        exact_mod_cast this
      · rw [hβ, hγ0, hθc]
        have : ((p1 * s' * (M : ℤ) : ℤ) : ℂ) = r := by rw [hr]; push_cast; ring
        rw [this]
        field_simp
        push_cast
        ring
    have hQq : ¬ (d : ℤ) ∣ Q * q1 := not_dvd_mul' hdp hQ hq1
    obtain ⟨s, hs⟩ := norm_square hOK hβK hQq hp1 hβN
    obtain ⟨k, hk⟩ := hs
    refine ⟨(s : ℂ) • y1, ⟨rep_sat_zsmul d Λ hy1S s, ?_, k, Q * q1, hQq, ?_⟩⟩
    · intro j hj; simp [hy1T j hj]
    · rw [hHs, hy1H, hHf]
      have hk' : (s : ℂ) ^ 2 * p1 = Q * q1 + d * k := by
        have := congrArg (fun t : ℤ => (t : ℂ)) hk
        push_cast at this
        linear_combination this
      simp only [map_intCast]
      push_cast
      field_simp
      linear_combination hk'
  · obtain ⟨y2, hy2S, hy2T, hy21, p2, q2, hp2, hq2, hy2H⟩ :=
      hU a b c d ha hd lam hlam m Λ x y T i₀ hK y1 hy1S hy1T (Or.inr ⟨p1, q1, hp1, hq1, by
        rw [hy1H]⟩) z hzS hzT hzy hz0
    rw [← hL, ← hκdef] at hy2H
    rw [← hL] at hy21
    have hp2c : (p2 : ℂ) ≠ 0 := by
      have : p2 ≠ 0 := fun h => hp2 (h ▸ dvd_zero _)
      exact_mod_cast this
    have hq2c : (q2 : ℂ) ≠ 0 := by
      have : q2 ≠ 0 := fun h => hq2 (h ▸ dvd_zero _)
      exact_mod_cast this
    have hy12 : stdH L m y1 y2 = 0 := by
      have := rep_H_conj (L := L) (m := m) y2 y1
      rw [hy21, map_zero] at this
      exact this.symm
    have hodd : d % 2 = 1 := by
      have := hOK.2.2.1
      omega
    obtain ⟨s, t, hst⟩ := pigeon hdp hodd (p1 * q2) (p2 * q1) (Q * q1 * q2)
      (not_dvd_mul' hdp hp1 hq2) (not_dvd_mul' hdp hp2 hq1)
    obtain ⟨k, hk⟩ := hst
    have hQq : ¬ (d : ℤ) ∣ Q * (q1 * q2) := not_dvd_mul' hdp hQ (not_dvd_mul' hdp hq1 hq2)
    refine ⟨(s : ℂ) • y1 + (t : ℂ) • y2,
      ⟨rep_sat_add d Λ hdp (rep_sat_zsmul d Λ hy1S s) (rep_sat_zsmul d Λ hy2S t), ?_, k, Q * (q1 * q2), hQq, ?_⟩⟩
    · intro j hj; simp [hy1T j hj, hy2T j hj]
    · have e : stdH L m ((s : ℂ) • y1 + (t : ℂ) • y2) ((s : ℂ) • y1 + (t : ℂ) • y2) =
          (s : ℂ) ^ 2 * stdH L m y1 y1 + (t : ℂ) ^ 2 * stdH L m y2 y2 := by
        simp only [map_add (f := _), LinearMap.add_apply, hHs, hy12, hy21, map_intCast]
        ring
      rw [e, hy1H, hy2H, hHf]
      have hk' : (s : ℂ) ^ 2 * (p1 * q2) + (t : ℂ) ^ 2 * (p2 * q1) = Q * q1 * q2 + d * k := by
        have := congrArg (fun t : ℤ => (t : ℂ)) hk
        push_cast at this
        linear_combination this
      push_cast
      field_simp
      linear_combination hk'

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem unitVecRam : UnitVecRam := by
  classical
  intro a b c d ha hd lam hlam m _ _ Λ x0 y0 T i₀ hK x hxs hxT hx z₀ hz₀ hz₀T hz₀x hz₀ne
  obtain ⟨hOK, hΛ, hθ, h1, h2, hl, hQ, hi₀, hT⟩ := hK
  have hdp : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hκ0 : repKappa a b d ha hd lam hlam ≠ 0 := rep_kappa_ne a b d ha hd lam hlam
  have hr0 : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    exact_mod_cast this.ne'
  have hπ : 2 * cmTheta b d - b = Complex.I * ((Real.sqrt d : ℝ) : ℂ) := by unfold cmTheta; ring
  have hπ0 : (2 * cmTheta b d - b) ≠ 0 := by rw [hπ]; exact mul_ne_zero Complex.I_ne_zero hr0
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hππ : (2 * cmTheta b d - b)⁻¹ * conj (2 * cmTheta b d - b)⁻¹ = (d : ℂ)⁻¹ := by
    rw [map_inv₀, ← mul_inv]
    congr 1
    rw [hπ, map_mul, Complex.conj_I, Complex.conj_ofReal]
    linear_combination (-((Real.sqrt d : ℝ) : ℂ) ^ 2) * Complex.I_sq + rep_sqrt_sq d
  have nz : ∀ {z : ℤ}, ¬ (d : ℤ) ∣ z → (z : ℂ) ≠ 0 := by
    intro z hz h; apply hz; rw [show z = 0 by exact_mod_cast h]; exact dvd_zero _

  obtain ⟨n0, s0, hs0, e0⟩ := sat_norm hOK hΛ hθ hl hz₀
  have hn0 : n0 ≠ 0 := by
    intro h
    apply H_self_ne m (cmL a b d ha hd lam hlam) hz₀ne
    rw [e0, h]; simp
  let P : ℕ → Prop := fun j => SatMem d Λ (((2 * cmTheta b d - b)⁻¹) ^ j • z₀)
  have hbound : ∀ j, P j → j ≤ n0.natAbs := by
    intro j hj
    obtain ⟨p, q, hq, e⟩ := sat_norm hOK hΛ hθ hl hj
    have eH : stdH (cmL a b d ha hd lam hlam) m (((2 * cmTheta b d - b)⁻¹) ^ j • z₀) (((2 * cmTheta b d - b)⁻¹) ^ j • z₀)
        = ((d : ℂ)⁻¹) ^ j * stdH (cmL a b d ha hd lam hlam) m z₀ z₀ := by
      rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul, map_pow,
        ← mul_assoc, ← mul_pow, hππ]
    rw [eH, e0] at e
    have e' : repKappa a b d ha hd lam hlam * ((p : ℂ) / q) =
        repKappa a b d ha hd lam hlam * ((n0 : ℂ) / ((s0 : ℂ) * (d : ℂ) ^ j)) := by
      calc _ = repKappa a b d ha hd lam hlam * p / q := by ring
        _ = _ := e.symm
        _ = _ := by ring
    have e'' := mul_left_cancel₀ hκ0 e'
    rw [div_eq_div_iff (nz hq) (mul_ne_zero (nz hs0) (pow_ne_zero _ hdc))] at e''
    have hZ : p * (s0 * (d : ℤ) ^ j) = n0 * q := by exact_mod_cast e''
    have hdj : (d : ℤ) ^ j ∣ n0 := by
      have h' : (d : ℤ) ^ j ∣ n0 * q := ⟨p * s0, by rw [← hZ]; ring⟩
      have hcop : IsCoprime ((d : ℤ) ^ j) q := IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hdp).mpr hq)
      exact hcop.dvd_of_dvd_mul_right h'
    have hle : d ^ j ≤ n0.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hdj
      rw [Int.natAbs_pow, Int.natAbs_natCast] at this
      exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn0) this
    have hlt : j < d ^ j := Nat.lt_pow_self hl.one_lt
    omega
  have hP0 : P 0 := by simpa [P] using hz₀
  set J := Nat.findGreatest P n0.natAbs with hJ
  have hPJ : P J := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  have hPJ1 : ¬ P (J + 1) := by
    intro h
    by_cases hle : J + 1 ≤ n0.natAbs
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hle h
    · exact hle (hbound _ h)
  set xh : m → ℂ := ((2 * cmTheta b d - b)⁻¹) ^ J • z₀ with hxh
  have hxhT : ∀ j ∈ T, xh j = 0 := by intro j hj; simp [xh, hz₀T j hj]
  have hxhx : stdH (cmL a b d ha hd lam hlam) m xh x = 0 := by
    rw [hxh, LinearMap.map_smul, LinearMap.smul_apply, hz₀x, smul_zero]
  have hnot : ¬ SatMem d Λ ((2 * cmTheta b d - b)⁻¹ • xh) := by
    rw [hxh, smul_smul, ← pow_succ']; exact hPJ1
  have hxhs : SatMem d Λ xh := hPJ
  obtain ⟨s, hs, hsx⟩ := hPJ
  have hs' : ¬ (d : ℤ) ∣ (s : ℤ) := fun h => hs (by exact_mod_cast h)

  obtain ⟨y, hy, n, c₂, hny, hdn⟩ : ∃ y ∈ Λ, ∃ n c₂ : ℤ,
      stdH (cmL a b d ha hd lam hlam) m (s • xh) y = repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) ∧
      ¬ (d : ℤ) ∣ 2 * n - c₂ * b := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    refine ⟨s, hs, ?_⟩
    rw [smul_comm, ← hΛ]
    intro y' hy'
    obtain ⟨n', c', e1, -⟩ := rep_H_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hsx hy'
    obtain ⟨k, hk⟩ := hcon y' hy' n' c' e1
    refine ⟨-k, ?_⟩
    unfold altE
    rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, e1, im_pi_inv, hk]
    push_cast
    field_simp

  set yz := zT T y with hyzdef
  have hyz : SatMem d Λ yz := rep_zT_sat a b c d ha hd lam hlam m hOK Λ hΛ hθ hl x0 y0 hQ T hT hy
  set μ := stdH (cmL a b d ha hd lam hlam) m yz x / stdH (cmL a b d ha hd lam hlam) m x x with hμdef
  set y' := yz - μ • x with hy'def
  have hy's : SatMem d Λ y' := by
    rcases hx with rfl | ⟨p, q, hp, hq, e⟩
    · simpa [y'] using hyz
    · obtain ⟨n2, c3, s2, hs2, e2⟩ := sat_pair hOK hΛ hθ hl hyz hxs
      have hμ : μ = (((q * n2 : ℤ) : ℂ) - ((q * c3 : ℤ) : ℂ) * conj (cmTheta b d)) / ((s2 * p : ℤ) : ℂ) := by
        have hp0 := nz hp
        have hq0 := nz hq
        have hs20 := nz hs2
        rw [hμdef, e2, e]
        push_cast
        field_simp
      refine rep_sat_sub d Λ hl hyz ?_
      rw [hμ]
      exact rep_sat_elt d Λ hl hθ hxs _ _ _ (not_dvd_mul' hl hs2 hp)
  have hy'T : ∀ j ∈ T, y' j = 0 := by
    intro j hj; simp [y', yz, zT, hj, hxT j hj]
  have hy'x : stdH (cmL a b d ha hd lam hlam) m y' x = 0 := by
    rcases hx with rfl | ⟨p, q, hp, hq, e⟩
    · simp
    · have hxx : stdH (cmL a b d ha hd lam hlam) m x x ≠ 0 := by
        rw [e]; exact div_ne_zero (mul_ne_zero hκ0 (nz hp)) (nz hq)
      rw [hy'def, map_sub, LinearMap.sub_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, hμdef,
        div_mul_cancel₀ _ hxx, sub_self]
  have hxhy' : stdH (cmL a b d ha hd lam hlam) m xh y' = stdH (cmL a b d ha hd lam hlam) m xh y := by
    rw [hy'def, map_sub, (stdH (cmL a b d ha hd lam hlam) m xh).map_smulₛₗ μ x, hxhx, smul_zero, sub_zero]
    exact rep_H_zT a b d ha hd lam hlam m T hxhT
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast nz hs'
  have hxhy : stdH (cmL a b d ha hd lam hlam) m xh y =
      repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) / s := by
    have e3 : stdH (cmL a b d ha hd lam hlam) m (s • xh) y = (s : ℂ) * stdH (cmL a b d ha hd lam hlam) m xh y := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hny] at e3
    rw [eq_div_iff hsc]
    linear_combination (-1 : ℂ) * e3

  obtain ⟨p1, q1, hq1, e1⟩ := sat_norm hOK hΛ hθ hl hxhs
  obtain ⟨p2, q2, hq2, e2⟩ := sat_norm hOK hΛ hθ hl hy's
  by_cases hp1 : (d : ℤ) ∣ p1
  · by_cases hp2 : (d : ℤ) ∣ p2
    · refine ⟨xh + y', rep_sat_add d Λ hl hxhs hy's, ?_, ?_, ?_⟩
      · intro j hj; simp [hxhT j hj, hy'T j hj]
      · rw [map_add (f := _), LinearMap.add_apply, hxhx, hy'x, add_zero]
      · refine ⟨p1 * q2 * s + p2 * q1 * s + (2 * n - c₂ * b) * q1 * q2, q1 * q2 * s, ?_,
          not_dvd_mul' hl (not_dvd_mul' hl hq1 hq2) hs', ?_⟩
        · intro hdv
          have e4 : (2 * n - c₂ * b) * q1 * q2 =
              (p1 * q2 * s + p2 * q1 * s + (2 * n - c₂ * b) * q1 * q2) - (p1 * q2 * s + p2 * q1 * s) := by ring
          have : (d : ℤ) ∣ (2 * n - c₂ * b) * q1 * q2 := by
            rw [e4]
            exact dvd_sub hdv (dvd_add ((hp1.mul_right _).mul_right _) ((hp2.mul_right _).mul_right _))
          exact not_dvd_mul' hl (not_dvd_mul' hl hdn hq1) hq2 this
        · have hyx : stdH (cmL a b d ha hd lam hlam) m y' xh =
              repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * cmTheta b d) / s := by
            rw [← rep_H_conj (cmL a b d ha hd lam hlam) m xh y', hxhy', hxhy]
            simp only [map_div₀, map_mul, map_sub, map_intCast, map_natCast, Complex.conj_conj,
              kappa_real a b d ha hd lam hlam]
          rw [map_add (stdH (cmL a b d ha hd lam hlam) m) xh y', LinearMap.add_apply, map_add (f := _), map_add (f := _), e1, e2, hxhy',
            hxhy, hyx]
          have htb := rep_theta_add_conj b d
          have hA : (q1 : ℂ) * (q1 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (nz hq1)
          have hB : (q2 : ℂ) * (q2 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (nz hq2)
          have hC : (s : ℂ) * (s : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hsc
          set κ := repKappa a b d ha hd lam hlam
          push_cast
          simp only [div_eq_mul_inv, mul_inv]
          linear_combination
            (-κ * p2 * (q2 : ℂ)⁻¹ * ((s : ℂ) * (s : ℂ)⁻¹) - κ * (s : ℂ)⁻¹ * (2 * n - c₂ * b) * ((q2 : ℂ) * (q2 : ℂ)⁻¹)) * hA +
            (-κ * p1 * (q1 : ℂ)⁻¹ * ((s : ℂ) * (s : ℂ)⁻¹) - κ * (s : ℂ)⁻¹ * (2 * n - c₂ * b)) * hB +
            (-κ * p1 * (q1 : ℂ)⁻¹ - κ * p2 * (q2 : ℂ)⁻¹) * hC +
            (-κ * (s : ℂ)⁻¹ * c₂) * htb
    · exact ⟨y', hy's, hy'T, hy'x, p2, q2, hp2, hq2, e2⟩
  · exact ⟨xh, hxhs, hxhT, hxhx, p1, q1, hp1, hq1, e1⟩

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end
