module

public import Development.AutomorphicArithmetic.CharacterBoxes.Bundle002
public import Development.AutomorphicArithmetic.CharacterBoxes.Bundle003
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.HC UpperTheory.Top

private theorem UpperTheory.Top.realBox_level {φ : Frame} (H : HostRaw φ) (χ : PChar)
    (h : H.IsCharE χ.χ) : χ.N ∣ H.QS * H.q * H.d := by
  obtain ⟨θ, hθ⟩ := h
  rw [H.isPrimOf_iff] at hθ
  subst hθ
  exact DirichletCharacter.conductor_dvd_level _

private theorem UpperTheory.Top.realBox_main (M : ℕ) (φ : Frame) (H : HostRaw φ) (eps Y X : ℝ)
    (hpr : ∀ l : ℕ, l.Prime → l ∣ H.QS → l ∣ 2 * M) (hM : ordCompl[2] H.QS ∣ M) (hg : PairGood M eps Y X H.q H.d)
    (χ : PChar) (hχ : H.IsCharE χ.χ) (hr : χ.IsReal) (hqd : H.q ∣ χ.N ∨ H.d ∣ χ.N) :
    ZeroBox (height M eps Y (if H.d ∣ χ.N then 1 else 0)) χ.χ ∧
      (χ.N : ℝ) ≤ height (ordCompl[2] H.QS) eps Y (if H.d ∣ χ.N then 1 else 0) := by
  have hP := hg.pair
  have hq := hP.q_prime
  have hd := hP.d_prime
  have hq8 := hP.q_mod
  have hd16 := hP.d_mod
  have hq2 : H.q ≠ 2 := by intro h; rw [h] at hq8; norm_num at hq8
  have hd2 : H.d ≠ 2 := by intro h; rw [h] at hd16; norm_num at hd16
  have hqd' : H.q ≠ H.d := by intro h; rw [h] at hq8; omega
  have hlev := UpperTheory.Top.realBox_level H χ hχ
  obtain ⟨ρ, i, j, hρr, hρN, hN, hval⟩ :=
    realSplit χ H.QS H.q H.d hr H.QS_pos hq hd hq2 hd2 hqd' H.QS_coprime hlev
  have hKdvd : ordCompl[2] H.QS ∣ H.QS := Nat.ordCompl_dvd _ _
  have hK0 : 0 < ordCompl[2] H.QS := Nat.ordCompl_pos 2 H.QS_pos.ne'
  have hnot : ∀ l, l.Prime → l ≠ 2 → l ∣ H.q * H.d → ¬ l ∣ ρ.N := by
    intro l hl hl2 hlqd hlρ
    have h8 := hlρ.trans hρN
    rcases (Nat.Prime.dvd_mul hl).1 h8 with h | h
    · have : l ∣ 2 := hl.dvd_of_dvd_pow (n := 3) (by norm_num; exact h)
      exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 this)
    · have h1 := Nat.dvd_gcd (h.trans hKdvd) hlqd
      rw [H.QS_coprime.gcd_eq_one] at h1
      exact hl.not_dvd_one h1
  have hqρ := hnot _ hq hq2 (dvd_mul_right _ _)
  have hdρ := hnot _ hd hd2 (dvd_mul_left _ _)
  have hcopN : ∀ a : ℕ, a.Coprime (2 * M * H.q * H.d) → a.Coprime χ.N := by
    intro a ha
    refine Nat.coprime_of_dvd fun l hl hla hlN => ?_
    have hl' : l ∣ 2 * M * H.q * H.d := by
      rcases (Nat.Prime.dvd_mul hl).1 (hlN.trans hlev) with h | h
      · rcases (Nat.Prime.dvd_mul hl).1 h with h | h
        · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (hpr l hl h) _) _
        · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _
      · exact Dvd.dvd.mul_left h _
    have h1 := Nat.dvd_gcd hla hl'
    rw [ha.gcd_eq_one] at h1
    exact hl.not_dvd_one h1
  have hind : An.Induces χ.χ (tw ρ.val H.q H.d i j) (2 * M * H.q * H.d) := by
    unfold An.Induces
    exact ⟨χ.prim, fun a ha => hval a (hcopN a ha)⟩
  have hi01 : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have hj01 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  have hij : i ≠ 0 ∨ j ≠ 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨rfl, rfl⟩ := hc
    rw [show H.q ^ ((0 : Fin 2) : ℕ) = 1 by simp, show H.d ^ ((0 : Fin 2) : ℕ) = 1 by simp,
      mul_one, mul_one] at hN
    rcases hqd with h | h <;> rw [hN] at h
    exacts [hqρ h, hdρ h]
  have hbox := hg.boxes ρ hρr (hρN.trans (mul_dvd_mul_left 8 hM)) i j hij χ.N χ.χ hind
  have hdq : ¬ H.d ∣ H.q := fun h => hqd' ((Nat.prime_dvd_prime_iff_eq hd hq).1 h).symm
  have hdqi : ∀ k : ℕ, ¬ H.d ∣ H.q ^ k := fun k h => hdq (hd.dvd_of_dvd_pow h)
  have hjd : (if H.d ∣ χ.N then (1 : Fin 2) else 0) = j := by
    rcases hj01 with rfl | rfl
    · rw [if_neg]
      rw [hN, show H.d ^ ((0 : Fin 2) : ℕ) = 1 by simp, mul_one]
      intro h
      rcases (Nat.Prime.dvd_mul hd).1 h with h | h
      exacts [hdρ h, hdqi _ h]
    · rw [if_pos]
      rw [hN]
      exact dvd_mul_of_dvd_right (dvd_pow_self _ (by simp)) _
  have hqe : (H.q : ℝ) ≤ Real.exp (Y ^ (eps / 5)) :=
    (Real.log_le_iff_le_exp (by exact_mod_cast hq.pos)).1 hP.q_up
  have hde : (H.d : ℝ) ≤ Real.exp (Y ^ (eps / 5) * Real.log Y ^ 2) :=
    (Real.log_le_iff_le_exp (by exact_mod_cast hd.pos)).1 hP.d_up
  have hρle : (ρ.N : ℝ) ≤ 8 * ((ordCompl[2] H.QS : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (by norm_num) hK0) hρN
  have hbound : (χ.N : ℝ) ≤ height (ordCompl[2] H.QS) eps Y j := by
    have hq1 : (1:ℝ) ≤ H.q := by exact_mod_cast hq.one_lt.le
    have hqi : (H.q:ℝ) ^ (i:ℕ) ≤ Real.exp (Y ^ (eps / 5)) :=
      (pow_le_pow_right₀ hq1 (Nat.lt_succ_iff.1 i.isLt)).trans (by rw [pow_one]; exact hqe)
    have hdj : (H.d:ℝ) ^ (j:ℕ) ≤ Real.exp (Y ^ (eps / 5) * Real.log Y ^ 2) ^ (j:ℕ) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hde _
    rw [hN, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
    unfold height
    exact mul_le_mul (mul_le_mul hρle hqi (by positivity) (by positivity)) hdj
      (by positivity) (by positivity)
  rw [hjd]
  exact ⟨hbox, hbound⟩

theorem UpperTheory.Top.realBox :
    ∀ (M : ℕ) (φ : Frame) (H : HostRaw φ) (eps Y X : ℝ), 0 < M → (∀ l : ℕ, l.Prime → l ∣ H.QS → l ∣ 2 * M) → ordCompl[2] H.QS ∣ M →
      PairGood M eps Y X H.q H.d →
      (∀ χ : PChar, H.IsCharE χ.χ → χ.IsReal → (H.q ∣ χ.N ∨ H.d ∣ χ.N) →
        ZeroBox (height M eps Y (if H.d ∣ χ.N then 1 else 0)) χ.χ ∧
          (χ.N : ℝ) ≤ height (ordCompl[2] H.QS) eps Y (if H.d ∣ χ.N then 1 else 0)) ∧ RealBox H := by
  intro M φ H eps Y X _ hpr hM hg
  refine ⟨fun χ hχ hr hqd => UpperTheory.Top.realBox_main M φ H eps Y X hpr hM hg χ hχ hr hqd, ?_⟩
  intro ψ hψ hr hqd β hβ
  have h := (UpperTheory.Top.realBox_main M φ H eps Y X hpr hM hg ψ hψ hr hqd).1
  refine h (β : ℂ) (by simpa using hβ) ?_
  simp only [Complex.ofReal_im, abs_zero]
  unfold height
  positivity
end

section

open Formalism.HC UpperTheory.Top

theorem UpperTheory.Top.winPairs :
    ∀ (ψ : PChar) (eps c : ℝ), 0 < eps → eps < 1 / 52 → 1 ≤ c → VWinAt ψ 401 → PairEx →
      ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧ ∀ x : ℝ, Z ≤ x → x ≤ Z ^ ((3 : ℝ) / 2) →
        ∃ (Y : ℝ) (q d e : ℕ), WinDatum ψ eps J c x Y q d e := by
  intro ψ eps c heps heps52 hc hV hP
  obtain ⟨e, he⟩ := exists_pageN eps heps
  obtain ⟨J, hJ, X0, hX0⟩ := hV eps heps heps52 e he
  have hN : 0 < ψ.N := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨Y1, hY1⟩ := hP ψ.N hN eps J heps heps52 hJ
  have ha : 0 < 2 + 8 * eps := by linarith
  have hc0 : 0 ≤ c := by linarith
  obtain ⟨k, hk1, hka⟩ : ∃ k : ℝ, 1 ≤ k ∧ k ^ (2 + 8 * eps) = c := by
    refine ⟨c ^ (1 / (2 + 8 * eps)), Real.one_le_rpow hc (one_div_nonneg.2 ha.le), ?_⟩
    rw [one_div, Real.rpow_inv_rpow hc0 ha.ne']
  have hk0 : 0 ≤ k := by linarith
  refine ⟨J, hJ, fun y => ?_⟩
  have hJ0 : J ≠ 0 := ne_of_gt (by linarith)
  have hJi : 0 ≤ 1 / J := one_div_nonneg.2 (by linarith)
  obtain ⟨M, hM1, hMy, hMY1, hMk3, hMk400⟩ : ∃ M : ℝ, 1 ≤ M ∧ y ≤ M ∧ Y1 ≤ M ∧
      k ^ (3 : ℝ) ≤ M ∧ k ^ (400 : ℝ) ≤ M :=
    ⟨max 1 (max y (max Y1 (max (k ^ (3 : ℝ)) (k ^ (400 : ℝ))))), by simp, by simp, by simp, by simp, by simp⟩
  obtain ⟨X, hXX0, hXM⟩ : ∃ X : ℝ, X0 ≤ X ∧ M ^ J ≤ X := ⟨max X0 (M ^ J), le_max_left _ _, le_max_right _ _⟩
  have hM0 : 0 ≤ M := by linarith
  have hX1 : 1 ≤ X := (Real.one_le_rpow hM1 (by linarith)).trans hXM
  have hX0' : 0 ≤ X := by linarith
  have hY0M : M ≤ X ^ (1 / J) := by
    calc M = (M ^ J) ^ (1 / J) := by rw [one_div, Real.rpow_rpow_inv hM0 hJ0]
      _ ≤ X ^ (1 / J) := Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) hXM hJi
  have hXJ : (X ^ (1 / J)) ^ J = X := by rw [one_div, Real.rpow_inv_rpow hX0' hJ0]
  obtain ⟨q, d, hpg⟩ := hY1 (X ^ (1 / J)) (hMY1.trans hY0M)
  obtain ⟨W, hW0, hW2, hWV⟩ := hX0 X hXX0 q d hpg.pair
  have hWM : M ≤ W := hY0M.trans hW0
  have hW1 : 1 ≤ W := hM1.trans hWM
  have hWnn : 0 ≤ W := by linarith
  have hk3 : k ^ (3 : ℝ) ≤ W := hMk3.trans hWM
  have hlem : (k * W) ^ ((3 : ℝ) / 2) ≤ W ^ (2 : ℝ) := by
    have h1 : (k * W) ^ ((3 : ℝ) / 2) = ((k * W) ^ (3 : ℝ)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul (mul_nonneg hk0 hWnn)]
      norm_num
    have h2 : W ^ (2 : ℝ) = (W ^ (4 : ℝ)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul hWnn]
      norm_num
    rw [h1, h2]
    apply Real.rpow_le_rpow (Real.rpow_nonneg (mul_nonneg hk0 hWnn) _) _ (by norm_num)
    rw [Real.mul_rpow hk0 hWnn, show (4 : ℝ) = 1 + 3 by norm_num, Real.rpow_add (by linarith : 0 < W),
      Real.rpow_one]
    exact mul_le_mul_of_nonneg_right hk3 (Real.rpow_nonneg hWnn _)
  refine ⟨k * W, hMy.trans (hWM.trans (le_mul_of_one_le_left hWnn hk1)), fun x hZx hxZ => ?_⟩
  have hkpos : 0 < k := by linarith
  have hxW2 : x ≤ W ^ (2 : ℝ) := hxZ.trans hlem
  have hxX : x ≤ X := hxW2.trans hW2
  have hx1 : W ≤ x := (le_mul_of_one_le_left hWnn hk1).trans hZx
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨x', rfl⟩ : ∃ x', x = k * x' := ⟨x / k, by field_simp⟩
  have hWx' : W ≤ x' := le_of_mul_le_mul_left hZx hkpos
  have hx'0 : 0 ≤ x' := hWnn.trans hWx'
  have hx'1 : 1 ≤ x' := hW1.trans hWx'
  have hx'x : x' ≤ k * x' := le_mul_of_one_le_left hx'0 hk1
  have hpage : x' ^ (2 + 8 * eps) ≤ 2 ^ (e x') ∧ 2 ^ (e x') ≤ 2 * x' ^ (2 + 8 * eps) := he x' hx'1
  have hpow : (k * x') ^ (2 + 8 * eps) = c * x' ^ (2 + 8 * eps) := by rw [Real.mul_rpow hk0 hx'0, hka]
  refine ⟨X ^ (1 / J), q, d, e x', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Real.rpow_le_rpow hx0 hxX hJi
  · exact hW0.trans hx1
  · exact hpg.mono (by rw [hXJ]; exact hxX)
  · rw [hpow]
    exact mul_le_mul_of_nonneg_left hpage.1 hc0
  · rw [hpow]
    calc c * 2 ^ (e x') ≤ c * (2 * x' ^ (2 + 8 * eps)) := mul_le_mul_of_nonneg_left hpage.2 hc0
      _ = 2 * (c * x' ^ (2 + 8 * eps)) := by ring
  · intro E _ _ hE
    have hv := hWV x' hWx' (hx'x.trans hxW2) E hE
    refine hv.mono ?_ ?_
    · apply Nat.floor_mono
      rw [Real.mul_rpow hk0 hx'0, show (401 : ℝ) = 1 + 400 by norm_num, Real.rpow_add (by linarith : 0 < x'),
        Real.rpow_one]
      exact mul_le_mul_of_nonneg_right (hMk400.trans (hWM.trans hWx')) (Real.rpow_nonneg hx'0 _)
    · exact Real.sqrt_le_sqrt (Real.exp_le_exp.2 (Real.rpow_le_rpow hx'0 hx'x heps.le))
end

section

open Formalism.HC UpperTheory.Top

theorem UpperTheory.Top.isChiField :
    ∀ (ψ : PChar) (φ : Frame) (H : HostRaw φ), KerChi ψ H → IsChiField ψ φ.e H.q H.d H.E := by
  intro ψ φ H h
  obtain ⟨hψ, hart⟩ := h
  have hyp := H.hyp
  unfold Formalism.FrobeniusOrbits.HostHyp at hyp
  have hq := hyp.1.pos
  have hd := hyp.2.1.pos
  have hQS := H.QS_pos
  have hNpos : 0 < H.QS * H.q * H.d := Nat.mul_pos (Nat.mul_pos hQS hq) hd
  haveI : NeZero (H.QS * H.q * H.d) := ⟨hNpos.ne'⟩
  have hζ := H.cycZeta_prim
  refine ⟨H.QS * H.q * H.d, inferInstance, H.cycEmb, H.cycZeta, ?_, ?_, ?_, ?_, hζ, ?_⟩
  · exact dvd_trans H.tower_dvd (dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _))
  · exact dvd_trans hψ (dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _))
  · exact dvd_trans (dvd_mul_left _ _) (dvd_mul_right _ _)
  · exact dvd_mul_left _ _
  · intro τ a hτ
    have hprim : IsPrimitiveRoot (H.cycZeta ^ a) (H.QS * H.q * H.d) := by
      rw [← hτ]
      exact hζ.map_of_injective τ.injective
    have hcop : a.Coprime (H.QS * H.q * H.d) := (hζ.pow_iff_coprime hNpos a).mp hprim
    have hcop' : a.Coprime H.condN := hcop
    rw [← hart a hcop']
    set u := ZMod.unitOfCoprime a hcop' with hu
    have hτu : τ H.cycZeta = H.cycZeta ^ (u : ZMod (H.QS * H.q * H.d)).val := by
      rw [hτ]
      have hv : (u : ZMod (H.QS * H.q * H.d)).val = a % (H.QS * H.q * H.d) := by
        rw [hu, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      rw [hv]
      conv_lhs => rw [← Nat.mod_add_div a (H.QS * H.q * H.d)]
      rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    have hspec := H.art_spec u τ hτu
    constructor
    · intro hfix
      have hg : H.gal.symm (H.art u) = 1 := by
        ext x
        apply H.cycEmb.injective
        exact (hspec x).trans (hfix x)
      have h1 := congrArg H.gal hg
      rw [MulEquiv.apply_symm_apply, map_one] at h1
      exact h1
    · intro h1 x
      have h2 := hspec x
      rw [h1, map_one] at h2
      rw [← h2]
      rfl
end

section

open Formalism.HC UpperTheory.Top

private theorem UpperTheory.Top.boundedTw_key (ψ : PChar) (φ : Frame) (H : HostRaw φ) (htw : TwistForm ψ H) (hdiv : ψ.N ∣ H.QS)
    (hpr : ∀ l : ℕ, l.Prime → l ∣ H.QS → l ∣ 2 * ψ.N) (θ : φ.Char) (hθ : θ ∈ H.Bounded (Level.cyc ψ).KEPT)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (hχ : H.IsPrimOf θ χ) :
    ∃ (ξ : DirichletCharacter ℂ ψ.N) (i j : Fin 2), (i ≠ 0 ∨ j ≠ 0) ∧
      An.Induces χ (tw (fun a => ξ (a : ZMod ψ.N)) H.q H.d i j) (2 * ψ.N * H.q * H.d) := by
  have hθ' : θ ∈ φ.Xp ∧ ¬H.Kept (Level.cyc ψ).KEPT θ ∨ θ ∈ φ.Xm := hθ
  have hχ' : An.Induces χ (H.dirAt θ) H.condN := hχ
  have htriv : Frame.TrivialOnFirstFactor θ := by
    rcases hθ' with ⟨h, -⟩ | h
    · exact h.1
    · exact h.1
  obtain ⟨ξ, hξ, i, j, hiod, heq⟩ := htw θ htriv
  have hNc : ψ.N ∣ H.condN := Dvd.dvd.mul_right (Dvd.dvd.mul_right hdiv _) _
  refine ⟨ξ, i, j, ?_, hχ'.1, ?_⟩
  · by_contra hij
    push_neg at hij
    obtain ⟨rfl, rfl⟩ := hij
    rcases hθ' with ⟨-, hnk⟩ | hm
    · apply hnk
      refine ⟨PChar.of ξ, (Level.mem_ofSub _ _).2 ⟨ξ, hξ, rfl⟩, (PChar.of ξ).prim, fun a ha => ?_⟩
      have ha' : a.Coprime ψ.N := Nat.Coprime.coprime_dvd_right hNc ha
      rw [(An.induces_of ξ).2 a ha', heq a ha]
      simp [tw]
    · have h1 := hm.2
      rw [h1] at hiod
      have h2 := congrArg Units.val hiod
      norm_num at h2
  · intro a ha
    have hq : a.Coprime H.q :=
      Nat.Coprime.coprime_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) ha
    have hd : a.Coprime H.d := Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) ha
    have hQ : a.Coprime H.QS := by
      apply Nat.coprime_of_dvd
      intro l hl hla hlQ
      have hl2 : l ∣ 2 * ψ.N * H.q * H.d :=
        dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (hpr l hl hlQ) _) _
      exact hl.not_dvd_one (ha.gcd_eq_one ▸ Nat.dvd_gcd hla hl2)
    have hc : a.Coprime H.condN := Nat.Coprime.mul_right (Nat.Coprime.mul_right hQ hq) hd
    rw [hχ'.2 a hc, heq a hc]

theorem UpperTheory.Top.boundedTw :
    ∀ (ψ : PChar) (φ : Frame) (H : HostRaw φ) (eps Y x : ℝ), 0 < eps → 1 ≤ x → Y ≤ x → TwistForm ψ H → ψ.N ∣ H.QS →
      (∀ l : ℕ, l.Prime → l ∣ H.QS → l ∣ 2 * ψ.N) → PairGood ψ.N eps Y x H.q H.d →
      H.BoundedCharsPointwise (Level.cyc ψ).KEPT x eps ∧
        ∀ θ ∈ H.Bounded (Level.cyc ψ).KEPT, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf θ χ → ‖An.logDerivativeAtOne χ‖ ≤ 4 * Real.log x := by
  intro ψ φ H eps Y x he hx hY htw hdiv hpr hg
  refine ⟨fun θ hθ N _ χ hχ => ?_, fun θ hθ N _ χ hχ => ?_⟩
  · obtain ⟨ξ, i, j, hij, hI⟩ := UpperTheory.Top.boundedTw_key ψ φ H htw hdiv hpr θ hθ N χ hχ
    exact (hg.bounds ξ i j hij N χ hI x hY le_rfl).1.trans
      (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
  · obtain ⟨ξ, i, j, hij, hI⟩ := UpperTheory.Top.boundedTw_key ψ φ H htw hdiv hpr θ hθ N χ hχ
    exact (hg.bounds ξ i j hij N χ hI x hY le_rfl).2
end
