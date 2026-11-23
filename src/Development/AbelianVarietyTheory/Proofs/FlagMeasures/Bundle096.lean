module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle091
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle053
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle092
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarFrameStabilizerLocalFixerSectionProduct
public import Formalism.PeriodIntegrals.Bundle019
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle002

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), (∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → S.IsTerm (c.dat d) (c.lat t.abelian₂) ∧ LocNG.om P t = S.om (c.dat d) (c.lat t.abelian₂) ∧ (LocNG.BBne (H := H) t ↔ ¬ S.BBzero (c.dat d) (c.lat t.abelian₂))) ∧ (∀ (d : LocNG.Datum P) Λ, S.IsTerm (c.dat d) Λ → ∃ t, LocNG.IsTermOver P d t ∧ c.lat t.abelian₂ = Λ) ∧ ∀ δ Λ, S.IsTerm δ Λ → ∃ d : LocNG.Datum P, δ = c.dat d := by
  first | exact @GlobalTheory.HL.CoordTermWt.terms_correspond | exact GlobalTheory.HL.CoordTermWt.terms_correspond | (intros; apply GlobalTheory.HL.CoordTermWt.terms_correspond <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem inf_stabilizer_smul_eq_conj {G X : Type*} [Group G] [MulAction G X] (H : Subgroup G)
    {h : G} (hh : h ∈ H) (x : X) :
    H ⊓ MulAction.stabilizer G (h • x) = MulAut.conj h • (H ⊓ MulAction.stabilizer G x) := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hh) h1) hh, ?_⟩
    rw [mul_smul, mul_smul, h2, inv_smul_smul]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := H.mul_mem (H.mul_mem hh h1) (H.inv_mem hh)
      simpa [mul_assoc] using this
    · rw [mul_smul, mul_smul, inv_smul_eq_iff] at h2
      exact h2

theorem invVol_conj_of_invVol_conj {G : Type} [Group G] (K A B : Subgroup G) (g : G)
    (hA : K.relIndex A ≠ 0) (hA' : A.relIndex K ≠ 0) (hB : K.relIndex B ≠ 0) (hB' : B.relIndex K ≠ 0)
    (h : invVol K (MulAut.conj g • A) = invVol K A) :
    invVol K (MulAut.conj g • B) = invVol K B := by
  have e : ∀ A B : Subgroup G,
      (MulAut.conj g • A).relIndex (MulAut.conj g • B) = A.relIndex B := fun A B =>
    Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) A B
      (MulAut.conj g).injective
  have hpos : 0 < invVol K (MulAut.conj g • A) := by
    rw [h]; exact (invVol_mul_pos_le_conj K A A hA hA' hA hA').2.1
  have hAB : A.relIndex B ≠ 0 := Subgroup.relIndex_ne_zero_trans hA' hB
  have hBA : B.relIndex A ≠ 0 := Subgroup.relIndex_ne_zero_trans hB' hA
  have c1 : K.relIndex (MulAut.conj g • A) ≠ 0 := by
    intro h0
    simp [invVol, h0] at hpos
  have c2 : (MulAut.conj g • A).relIndex K ≠ 0 := by
    intro h0
    simp [invVol, h0] at hpos
  have c3 : K.relIndex (MulAut.conj g • B) ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans c1 (by rw [e]; exact hAB)
  have c4 : (MulAut.conj g • B).relIndex K ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans (by rw [e]; exact hBA) c2
  rw [(invVol_mul_pos_le_conj K _ _ c1 c2 c3 c4).1, (invVol_mul_pos_le_conj K A B hA hA' hB hB').1, h]
  congr 1
  rw [invVol, invVol, e, e]

theorem Frames.nu_pos_and_smul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → 0 < S.nu d ∧ ∀ h ∈ S.H0, S.nu (h • d) = S.nu d := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  obtain ⟨hv, hd⟩ := GlobalTheory.T.stabilizer_commensurable_invVolume_smul_complement L r k S
  obtain ⟨d1, d2⟩ := hd d Λ hT
  have hSD := (GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT).1
  obtain ⟨l1, l2, l3⟩ := hv Λ hSD.1
  refine ⟨(invVol_mul_pos_le_conj _ _ _ d1 d2 d1 d2).2.1, fun h hh => ?_⟩
  have := l3 h hh
  rw [inf_stabilizer_smul_eq_conj _ hh] at this
  unfold Frames.nu
  rw [inf_stabilizer_smul_eq_conj _ hh]
  exact invVol_conj_of_invVol_conj _ _ _ h l1 l2 d1 d2 this

end GlobalTheory.HL
end

section

open GlobalTheory.Diag.PG Filter

noncomputable section

namespace GlobalTheory.Diag.PG.SqrtBound

theorem poly_ineq {t K a : ℝ} (ht2 : 2 ≤ t) (htK : K ≤ t) (ha : a ≤ K) : a * t + t ^ 2 ≤ t ^ 4 / 2 := by
  have ht0 : 0 ≤ t := by linarith
  have hat : a * t ≤ t * t := mul_le_mul_of_nonneg_right (ha.trans htK) ht0
  have h4 : 4 ≤ t ^ 2 := by nlinarith
  nlinarith

theorem scale_facts {eps x : ℝ} (heps : 0 < eps) (hx : 1 ≤ x) :
    Real.log x ≤ 4 * x ^ (eps / 4) / eps ∧ x ^ (eps / 2) = (x ^ (eps / 4)) ^ 2 ∧
      x ^ eps = (x ^ (eps / 4)) ^ 4 := by
  have hx0 : 0 ≤ x := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have h := Real.log_le_rpow_div hx0 (by positivity : 0 < eps / 4)
    calc Real.log x ≤ x ^ (eps / 4) / (eps / 4) := h
      _ = 4 * x ^ (eps / 4) / eps := by field_simp
  · rw [← Real.rpow_mul_natCast hx0]; push_cast; ring_nf
  · rw [← Real.rpow_mul_natCast hx0]; push_cast; ring_nf

theorem exp_bound {eps A x K : ℝ} (heps : 0 < eps) (hA : 0 < A) (hx : 1 ≤ x)
    (ht2 : 2 ≤ x ^ (eps / 4)) (htK : K ≤ x ^ (eps / 4)) (hK : |Real.log A| + 40 / eps ≤ K) :
    A * x ^ 10 * Real.exp (x ^ (eps / 2)) ≤ Real.exp (x ^ eps / 2) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hlog, h2, h4⟩ := scale_facts heps hx
  set t := x ^ (eps / 4) with ht
  have hp := poly_ineq (a := |Real.log A| + 40 / eps) ht2 htK hK
  have h1 : Real.log A ≤ |Real.log A| := le_abs_self _
  have h3 : |Real.log A| ≤ |Real.log A| * t := le_mul_of_one_le_right (abs_nonneg _) (by linarith)
  have h5 : 10 * Real.log x ≤ 40 / eps * t := by
    calc 10 * Real.log x ≤ 10 * (4 * t / eps) := by linarith
      _ = 40 / eps * t := by ring
  have key : Real.log A + 10 * Real.log x + t ^ 2 ≤ t ^ 4 / 2 := by nlinarith
  have e10 : Real.exp (10 * Real.log x) = x ^ 10 := by
    rw [show (10 : ℝ) * Real.log x = Real.log (x ^ 10) by rw [Real.log_pow]; norm_num]
    exact Real.exp_log (by positivity)
  calc A * x ^ 10 * Real.exp (x ^ (eps / 2))
        = Real.exp (Real.log A + 10 * Real.log x + x ^ (eps / 2)) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log hA, e10]
    _ ≤ Real.exp (x ^ eps / 2) := Real.exp_le_exp.2 (by rw [h2, h4]; linarith)

theorem log_bound {eps C x K : ℝ} (heps : 0 < eps) (hC : 0 ≤ C) (hx : 1 ≤ x)
    (ht2 : 2 ≤ x ^ (eps / 4)) (htK : K ≤ x ^ (eps / 4)) (hK : 20 * C / eps ≤ K) :
    Real.log x * (5 * C) ≤ x ^ eps / 2 := by
  obtain ⟨hlog, -, h4⟩ := scale_facts heps hx
  set t := x ^ (eps / 4) with ht
  have ht0 : 0 ≤ t := by linarith
  have hp := poly_ineq (a := 20 * C / eps) ht2 htK hK
  have hat : 0 ≤ 20 * C / eps * t := by positivity
  have h1 : Real.log x * (5 * C) ≤ 4 * t / eps * (5 * C) :=
    mul_le_mul_of_nonneg_right hlog (by positivity)
  have h2 : 4 * t / eps * (5 * C) = 20 * C / eps * t := by ring
  rw [h4]
  nlinarith

theorem rankNums_sizes : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x →
    ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → 1 ≤ Del ∧ C * (m * k * Del) ≤ Real.sqrt (bx x eps) ∧
      max (k ^ C) (bx x eps ^ ((1 : ℝ) / 4)) ≤ Real.sqrt (bx x eps) ∧ 12 * k * Del ≤ Real.sqrt (bx x eps) ∧
      Real.sqrt (bx x eps) ≤ bx x eps ^ 2 ∧ bx x eps ^ 2 ≤ bx x eps ^ (3 : ℝ) ∧
      (C ≤ CD → (k * f * x ^ eps) ^ C ≤ Del) := by
  intro eps CD heps _ hCD C hC
  set K0 := max (max 2 (|Real.log C| + 40 / eps)) (max (|Real.log 12| + 40 / eps) (20 * C / eps)) with hK0
  have hK0pos : 0 ≤ K0 := le_trans (by norm_num) (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨max 1 (K0 ^ (4 / eps)), ?_⟩
  intro x hx m f k lrd Del h
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have htK0 : K0 ≤ x ^ (eps / 4) := by
    have h1 : K0 ^ (4 / eps) ≤ x := le_trans (le_max_right _ _) hx
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ eps / 4)
    rwa [← Real.rpow_mul hK0pos, show 4 / eps * (eps / 4) = (1 : ℝ) by field_simp, Real.rpow_one] at h2
  have ht2 : 2 ≤ x ^ (eps / 4) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) htK0
  have htA : |Real.log C| + 40 / eps ≤ x ^ (eps / 4) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) htK0
  have ht12 : |Real.log 12| + 40 / eps ≤ x ^ (eps / 4) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) htK0
  have htC : 20 * C / eps ≤ x ^ (eps / 4) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) htK0

  have hm1 : 1 ≤ m := le_trans (Real.one_le_rpow hx1 (by norm_num)) h.m_lo
  have hm4 : m ≤ m ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hm1 3]
  have hf1 : 1 ≤ f := le_trans (by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hm1 4]) h.mf
  have hk1 : 1 ≤ k := le_trans hf1 h.fk
  have hk5 : k ≤ x ^ 5 := by
    have := h.k_hi
    rwa [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have hm5 : m ≤ x ^ 5 := le_trans (le_trans hm4 (le_trans h.mf h.fk)) hk5
  have hxe1 : 1 ≤ x ^ eps := Real.one_le_rpow hx1 heps.le

  have hB1 : 1 ≤ k * f * x ^ eps := by
    have : 1 ≤ k * f := by nlinarith
    nlinarith
  have hDel1 : 1 ≤ Del := le_trans (Real.one_le_rpow hB1 (by linarith)) h.Del_lo
  have hDelE : Del ≤ Real.exp (x ^ (eps / 2)) :=
    (Real.log_le_iff_le_exp (by linarith)).1 h.Del_hi

  have hsq : Real.sqrt (bx x eps) = Real.exp (x ^ eps / 2) := by
    rw [Real.sqrt_eq_rpow, bx, ← Real.exp_mul]; ring_nf
  have hE0 : 0 ≤ Real.exp (x ^ (eps / 2)) := (Real.exp_pos _).le
  have hx10 : m * k ≤ x ^ 10 := by
    have : x ^ 10 = x ^ 5 * x ^ 5 := by ring
    rw [this]; exact mul_le_mul hm5 hk5 (by linarith) (by positivity)
  have hb1 : 1 ≤ bx x eps := Real.one_le_exp (by positivity)
  refine ⟨hDel1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsq]
    calc C * (m * k * Del) ≤ C * x ^ 10 * Real.exp (x ^ (eps / 2)) := by
          rw [mul_assoc C]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hx10 hDelE (by linarith) (by positivity)) hC.le
      _ ≤ Real.exp (x ^ eps / 2) := exp_bound heps hC hx1 ht2 htA le_rfl
  · rw [hsq]
    refine max_le ?_ ?_
    · have hk0 : 0 < k := by linarith
      rw [Real.rpow_def_of_pos hk0]
      refine Real.exp_le_exp.2 (le_trans ?_ (log_bound heps hC.le hx1 ht2 htC le_rfl))
      have hlk : Real.log k ≤ 5 * Real.log x := by
        have h5 := Real.log_le_log hk0 hk5
        rw [Real.log_pow] at h5; push_cast at h5; linarith
      nlinarith
    · rw [bx, ← Real.exp_mul]
      exact Real.exp_le_exp.2 (by nlinarith [Real.rpow_nonneg hx0.le eps])
  · rw [hsq]
    calc 12 * k * Del ≤ 12 * x ^ 10 * Real.exp (x ^ (eps / 2)) := by
          have hk10 : k ≤ x ^ 10 := le_trans hk5 (pow_le_pow_right₀ hx1 (by norm_num))
          rw [mul_assoc, mul_assoc (12 : ℝ)]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hk10 hDelE (by linarith) (by positivity)) (by norm_num)
      _ ≤ Real.exp (x ^ eps / 2) := exp_bound heps (by norm_num) hx1 ht2 ht12 le_rfl
  · rw [hsq, bx, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by push_cast; nlinarith [Real.rpow_nonneg hx0.le eps])
  · rw [show bx x eps ^ 2 = bx x eps ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast _ 2).symm]
    exact Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
  · intro hCC
    exact le_trans (Real.rpow_le_rpow_of_exponent_le hB1 hCC) h.Del_lo

end GlobalTheory.Diag.PG.SqrtBound

end
end

section

open GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

theorem gaps_exceed :
    ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x →
      ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → ∀ r : ℝ, k ≤ r → r ≤ 2 * k →
      C * k * m ^ 4 + r * m ^ 10 < 4 * Del ∧ C * k * m ^ 4 + r * m ^ 10 < Real.sqrt (bx x eps) ∧
      C * k * m ^ 4 + r * m ^ 10 < x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps ∧
      C * r ^ 19 * f ^ 5 * x ^ eps ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
  intro eps CD heps _heps' hCD C hC
  refine ⟨max (max 1 (C + 2)) (max (C ^ (100 / eps)) ((16 : ℝ) ^ (2 / eps))), ?_⟩
  intro x hx m f k lrd Del h r hkr hrk
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxC : C + 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxC' : C ^ (100 / eps) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx16 : (16 : ℝ) ^ (2 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 ≤ x := by linarith
  have hm1 : 1 ≤ m := le_trans (Real.one_le_rpow hx1 (by norm_num)) h.m_lo
  have hm4 : x ≤ m ^ 4 := by
    have h1 : (x ^ ((1 : ℝ) / 4)) ^ 4 ≤ m ^ 4 := by
      gcongr
      exact h.m_lo
    have h2 : (x ^ ((1 : ℝ) / 4)) ^ 4 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
    linarith
  have hf : x ≤ f := le_trans hm4 h.mf
  have hk : x ≤ k := le_trans hf h.fk
  have hr : x ≤ r := le_trans hk hkr
  have hf1 : 1 ≤ f := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hL : 1 ≤ x ^ eps := Real.one_le_rpow hx1 heps.le
  have hL' : 1 ≤ x ^ (eps / 100) := Real.one_le_rpow hx1 (by positivity)
  have hm10 : m ^ 10 ≤ f ^ 3 := by
    have h1 : m ^ 10 ≤ m ^ 12 := pow_le_pow_right₀ hm1 (by norm_num)
    have h2 : m ^ 12 = (m ^ 4) ^ 3 := by ring
    have h3 : (m ^ 4) ^ 3 ≤ f ^ 3 := by gcongr; exact h.mf
    linarith
  have hf3 : f ≤ f ^ 3 := by
    have := pow_le_pow_right₀ hf1 (show 1 ≤ 3 by norm_num); simpa using this
  have hS : C * k * m ^ 4 + r * m ^ 10 ≤ (C + 2) * k * f ^ 3 := by
    have h1 : C * k * m ^ 4 ≤ C * k * f ^ 3 := by
      have : m ^ 4 ≤ f ^ 3 := le_trans h.mf hf3
      gcongr
    have h2 : r * m ^ 10 ≤ (2 * k) * f ^ 3 := by
      gcongr
    nlinarith
  have hSpos : 0 < C * k * m ^ 4 + r * m ^ 10 := by positivity

  have hy1 : 1 ≤ k * f * x ^ eps := by
    have : 1 ≤ k * f := one_le_mul_of_one_le_of_one_le hk1 hf1
    exact one_le_mul_of_one_le_of_one_le this hL
  have hDel3 : (k * f * x ^ eps) ^ (3 : ℕ) ≤ Del := by
    have := Real.rpow_le_rpow_of_exponent_le hy1 hCD
    rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    linarith [h.Del_lo]
  have hDelpos : 0 < Del := by
    have : 0 < (k * f * x ^ eps) ^ (3 : ℕ) := by positivity
    linarith
  have hc1 : C * k * m ^ 4 + r * m ^ 10 < 4 * Del := by
    have hkf3 : 0 < k * f ^ 3 := by positivity
    have hk2 : C + 2 < 4 * k ^ 2 := by nlinarith
    have e1 : (C + 2) * k * f ^ 3 < 4 * k ^ 2 * (k * f ^ 3) := by nlinarith
    have e2 : 4 * k ^ 2 * (k * f ^ 3) ≤ 4 * (k * f * x ^ eps) ^ (3 : ℕ) := by
      have hkf : k * f ≤ k * f * x ^ eps := le_mul_of_one_le_right (by positivity) hL
      have : (k * f) ^ 3 ≤ (k * f * x ^ eps) ^ 3 := by gcongr
      nlinarith
    linarith

  set t := x ^ (eps / 2) with ht
  have ht16 : 16 ≤ t := by
    have h1 : ((16 : ℝ) ^ (2 / eps)) ^ (eps / 2) ≤ x ^ (eps / 2) :=
      Real.rpow_le_rpow (by positivity) hx16 (by positivity)
    have h2 : ((16 : ℝ) ^ (2 / eps)) ^ (eps / 2) = 16 := by
      rw [← Real.rpow_mul (by norm_num)]
      have : 2 / eps * (eps / 2) = 1 := by field_simp
      rw [this, Real.rpow_one]
    linarith
  have hxe : x ^ eps = t ^ 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; congr 1; push_cast; ring
  have hDelE : Del ≤ Real.exp t := by
    have := h.Del_hi
    rw [Real.log_le_iff_le_exp hDelpos] at this
    exact this
  have hc2 : C * k * m ^ 4 + r * m ^ 10 < Real.sqrt (bx x eps) := by
    rw [Real.lt_sqrt hSpos.le]
    have e1 : (C * k * m ^ 4 + r * m ^ 10) ^ 2 < (4 * Real.exp t) ^ 2 := by
      have : C * k * m ^ 4 + r * m ^ 10 < 4 * Real.exp t := by linarith
      gcongr
    have e2 : (4 * Real.exp t) ^ 2 = Real.exp (Real.log 16 + 2 * t) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
      rw [show 2 * t = t + t by ring, Real.exp_add]; ring
    have e3 : Real.log 16 + 2 * t ≤ x ^ eps := by
      have : Real.log 16 ≤ 16 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      rw [hxe]; nlinarith
    have e4 : Real.exp (Real.log 16 + 2 * t) ≤ bx x eps := by
      unfold bx; exact Real.exp_le_exp.mpr e3
    linarith

  have hc3 : C * k * m ^ 4 + r * m ^ 10 < x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
    have hf35 : f ^ 3 ≤ f ^ 5 := pow_le_pow_right₀ hf1 (by norm_num)
    have e1 : C * k * m ^ 4 + r * m ^ 10 ≤ (C + 2) * r * f ^ 5 := by
      have : (C + 2) * k * f ^ 3 ≤ (C + 2) * r * f ^ 5 := by gcongr
      linarith
    have hx18 : x ≤ x ^ 18 := by
      have := pow_le_pow_right₀ hx1 (show 1 ≤ 18 by norm_num); simpa using this
    have hr18 : x ^ 18 ≤ r ^ 18 := by gcongr
    have e2 : (C + 2) * r * f ^ 5 < r ^ 18 * (r * f ^ 5) := by
      have hp : 0 < r * f ^ 5 := by positivity
      have hC18 : C + 2 < r ^ 18 := by
        have hx2 : x ^ 2 ≤ x ^ 18 := pow_le_pow_right₀ hx1 (by norm_num)
        have : x < x ^ 2 := by nlinarith
        linarith
      have := mul_lt_mul_of_pos_right hC18 hp
      calc (C + 2) * r * f ^ 5 = (C + 2) * (r * f ^ 5) := by ring
        _ < r ^ 18 * (r * f ^ 5) := this
    have e3 : r ^ 18 * (r * f ^ 5) = r ^ 19 * f ^ 5 := by ring
    have e4 : r ^ 19 * f ^ 5 ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
      have hp : 0 ≤ r ^ 19 * f ^ 5 := by positivity
      have h1 : 1 ≤ x ^ (eps / 100) * x ^ eps := one_le_mul_of_one_le_of_one_le hL' hL
      have := mul_le_mul_of_nonneg_right h1 hp
      calc r ^ 19 * f ^ 5 = 1 * (r ^ 19 * f ^ 5) := by ring
        _ ≤ (x ^ (eps / 100) * x ^ eps) * (r ^ 19 * f ^ 5) := this
        _ = x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by ring
    linarith

  have hc4 : C * r ^ 19 * f ^ 5 * x ^ eps ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
    have hCx : C ≤ x ^ (eps / 100) := by
      have h1 : (C ^ (100 / eps)) ^ (eps / 100) ≤ x ^ (eps / 100) :=
        Real.rpow_le_rpow (by positivity) hxC' (by positivity)
      have h2 : (C ^ (100 / eps)) ^ (eps / 100) = C := by
        rw [← Real.rpow_mul hC.le]
        have : 100 / eps * (eps / 100) = 1 := by field_simp
        rw [this, Real.rpow_one]
      linarith
    have hp : 0 ≤ r ^ 19 * f ^ 5 * x ^ eps := by positivity
    have := mul_le_mul_of_nonneg_right hCx hp
    calc C * r ^ 19 * f ^ 5 * x ^ eps = C * (r ^ 19 * f ^ 5 * x ^ eps) := by ring
      _ ≤ x ^ (eps / 100) * (r ^ 19 * f ^ 5 * x ^ eps) := this
      _ = x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by ring
  exact ⟨hc1, hc2, hc3, hc4⟩

end GlobalTheory.Diag.PG
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.diagonal_torus_transitive_generic_characters : ∀ (k : Type) [Field k] [Finite k] (n t : ℕ) (ψ ψ' : AddChar k ℂ) (χ χ' : ℕ → MulChar k ℂ), ψ ≠ 1 → ψ' ≠ 1 → ∃ d : Fin n → kˣ, ∀ M : Matrix (Fin n) (Fin n) k, (InJ n t n false M ↔ InJ n t n false (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1))) ∧ lamJ ψ' χ' n t 0 n M = (lamJ ψ χ n t 0 n (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1)))⁻¹ := by
  first | exact @GlobalTheory.St.G.Torus.torus_transitive | exact GlobalTheory.St.G.Torus.torus_transitive | (intros; apply GlobalTheory.St.G.Torus.torus_transitive <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.haar_frameStabilizer_local_fixer_section_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure → (∀ s ∈ Ssub (Fv F v) σ J P, ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∫⁻ h, f (s * (h : HA (Fv F v) σ J) * s⁻¹) ∂μ0 = ∫⁻ h, f (h : HA (Fv F v) σ J) ∂μ0) → ∀ μU : Measure ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), μU.IsAddHaarMeasure → ∃ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure ∧ ∀ h : HA (Fv F v) σ J → ℝ≥0∞, Measurable h → ∀ t : ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) → HA (Fv F v) σ J, (∀ x b, lin (Fv F v) σ J (t x) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a)) → ∫⁻ s, h s ∂(amb μS) = ∫⁻ x, ∫⁻ s0, h ((s0 : HA (Fv F v) σ J) * t x) ∂μ0 ∂μU := by
  first | exact @GlobalTheory.HaarSectionProd.haar_S_local | exact GlobalTheory.HaarSectionProd.haar_S_local | (intros; apply GlobalTheory.HaarSectionProd.haar_S_local <;> assumption)
end

section

open GlobalTheory.Mom

namespace GlobalTheory.BesselMultOne

theorem psi_eq_psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Formalism.QuantumDeterminants.psi k r z c = PI.BesselMapUniq.psiGen k r z (fun _ => c) := by
  funext g
  unfold Formalism.QuantumDeterminants.psi Formalism.QuantumDeterminants.ell PI.BesselMapUniq.psiGen PI.BesselMapUniq.ellA
  rw [Finset.mul_sum]

theorem dsigW_eq {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    PI.UpqRep.dsigW (k := k) (r := r) σ w v = Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v := by
  induction w generalizing v with
  | nil => rfl
  | cons X w ih => simp only [PI.UpqRep.dsigW, Formalism.MainNotions.S.dsigW, ih]; rfl

theorem isBesselMapSm_of {k r : ℕ} {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {z : Fin (2 * r + k + 1) → ℂ}
    {ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (W →L[ℂ] W)} {B : H → W}
    (h : Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z ψ σ π B) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B := by
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  refine ⟨h1, h2, h3, C, Ws, h4, fun v hv => ?_⟩
  simp only [dsigW_eq]
  exact h5 v hv

end GlobalTheory.BesselMultOne
end

section

noncomputable section

open NumberField

namespace GlobalTheory.RowLatXS

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

def Ia (Λ : Submodule (𝓞 E) S.V) (F : Formalism.MainNotions.S.FlagG S r T) (a : Fin r) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {t | ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t}

end GlobalTheory.RowLatXS
end
end
