module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle061
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimeIncidenceFiniteFibresStable
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle067
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem intAt_zpow_mul {P : HeightOneSpectrum (𝓞 E)} {e : ℤ} (he : 0 ≤ e) {a : E} (ha : IntAt P a) :
    IntAt P ((qOf P : E) ^ e * a) := by
  lift e to ℕ using he
  rw [zpow_natCast]
  exact GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul e ha

theorem intV_inX {P : HeightOneSpectrum (𝓞 E)} {n c : ℕ} {z : Fin n → E} (hz : IntV P z) : IntV P (Loc.inX E n c z) := by
  intro l
  rw [inX_apply]
  split_ifs
  · exact hz _
  · exact ⟨0, 1, one_notMem P, by simp⟩

theorem intV_eN (P : HeightOneSpectrum (𝓞 E)) (N i : ℕ) : IntV P (Loc.eN E N i) := by
  intro l
  simp only [Loc.eN]
  split_ifs
  · exact intAt_one P
  · exact ⟨0, 1, one_notMem P, by simp⟩

theorem intV_sum {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} {ι : Type} (s : Finset ι) (f : ι → Fin N → E)
    (h : ∀ i ∈ s, IntV P (f i)) : IntV P (∑ i ∈ s, f i) := by
  intro l
  rw [Finset.sum_apply]
  exact intAt_sum s _ (fun i hi => h i hi l)

theorem intV_glue {P : HeightOneSpectrum (𝓞 E)} {n c : ℕ} {z : Fin n → E} (hz : IntV P z) (i : Fin c) :
    IntV P (if i.1 = 0 then Loc.inX E n c z else 0) := by
  split_ifs
  · exact intV_inX hz
  · exact IntV.zero P

theorem decomp {n c : ℕ} (x : Fin (n + c) → E) :
    x = Loc.inX E n c (fun a => x (Fin.castAdd c a)) + ∑ i : Fin c, x (Fin.natAdd n i) • Loc.eN E (n + c) (n + i.1) := by
  funext l
  refine Fin.addCases (fun a => ?_) (fun b => ?_) l
  · have h1 : ∀ i : Fin c, Loc.eN E (n + c) (n + i.1) (Fin.castAdd c a) = 0 := by
      intro i
      simp only [Loc.eN, Fin.val_castAdd]
      rw [if_neg]
      omega
    simp [inX_castAdd, Finset.sum_apply, h1]
  · have h2 : ∀ i : Fin c, Loc.eN E (n + c) (n + i.1) (Fin.natAdd n b) = if i = b then 1 else 0 := by
      intro i
      by_cases hib : i = b
      · subst hib
        simp [Loc.eN]
      · simp only [Loc.eN, Fin.val_natAdd, if_neg hib]
        rw [if_neg]
        intro h
        apply hib
        ext
        omega
    have h3 : Loc.inX E n c (fun a => x (Fin.castAdd c a)) (Fin.natAdd n b) = 0 := by
      rw [inX_apply, dite_eq_right (by simp)]
    simp [Finset.sum_apply, h2, h3]

theorem mem_nfLat {P : HeightOneSpectrum (𝓞 E)} {n c : ℕ} {e : Fin c → ℤ} (he : ∀ i, e i ≤ 0) {z : Sp E n}
    (hz : IntV P z) {x : Sp E (n + c)} (hx : IntV P x) : x ∈ nfLat P n c e z := by
  have hq : (qOf P : E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  set w : Sp E n := ∑ i : Fin c, x (Fin.natAdd n i) • (if i.1 = 0 then z else 0) with hw
  refine ⟨(fun a => x (Fin.castAdd c a)) - w, ?_, fun i => x (Fin.natAdd n i) * (qOf P : E) ^ (-e i), ?_, ?_⟩
  · rw [mem_stdAt_iff, sub_eq_add_neg]
    refine IntV.add (fun l => hx _) (IntV.neg ?_)
    refine intV_sum _ _ (fun i _ => IntV.smul (hx _) ?_)
    split_ifs
    · exact hz
    · exact IntV.zero P
  · intro i
    show IntAt P (x (Fin.natAdd n i) * (qOf P : E) ^ (-e i))
    rw [mul_comm]
    exact intAt_zpow_mul (by linarith [he i]) (hx _)
  · have hs : ∀ i : Fin c, (x (Fin.natAdd n i) * (qOf P : E) ^ (-e i)) • nfGen (qOf P) n c e z i =
        x (Fin.natAdd n i) • Loc.eN E (n + c) (n + i.1) +
          Loc.inX E n c (x (Fin.natAdd n i) • (if i.1 = 0 then z else 0)) := by
      intro i
      simp only [nfGen, smul_smul, mul_assoc, ← zpow_add₀ hq, neg_add_cancel, zpow_zero, mul_one, smul_add]
      congr 1
      split_ifs <;> simp

    rw [Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_add_distrib, ← map_sum, ← hw, map_sub]
    conv_lhs => rw [decomp x]
    abel

theorem smul_int_of_mem_nfLat {P : HeightOneSpectrum (𝓞 E)} {n c j : ℕ} {e : Fin c → ℤ} (he : ∀ i, -(j : ℤ) ≤ e i)
    {z : Sp E n} (hz : IntV P z) {x : Sp E (n + c)} (hx : x ∈ nfLat P n c e z) : IntV P (((qOf P : E) ^ j) • x) := by
  obtain ⟨l, hl, s, hs, rfl⟩ := hx
  have hq : (qOf P : E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  rw [mem_stdAt_iff] at hl
  have key : ∀ i : Fin c, ((qOf P : E) ^ j) • (s i • nfGen (qOf P) n c e z i) =
      ((qOf P : E) ^ ((j : ℤ) + e i) * s i) •
        (Loc.eN E (n + c) (n + i.1) + if i.1 = 0 then Loc.inX E n c z else 0) := by
    intro i
    simp only [nfGen, smul_smul]
    congr 1
    rw [zpow_add₀ hq, zpow_natCast]
    ring
  rw [smul_add, Finset.smul_sum, ← LinearMap.map_smul (Loc.inX E n c)]
  refine IntV.add (intV_inX (fun k => ?_)) (intV_sum _ _ (fun i _ => ?_))
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul j (hl k)
  · rw [key i]
    refine IntV.smul ?_ (IntV.add (intV_eN P _ _) (intV_glue hz i))
    exact intAt_zpow_mul (by linarith [he i]) (hs i)

end Lattice

theorem inclAt (X : Fields) (Pr : Primes X) (R : Ranks) : InclAt Pr R := by
  intro j P hP h k hNF hk
  obtain ⟨e, z, he, hz, himg⟩ := hNF
  have hk' : ∀ x, k x ∈ lamYat (Pr := Pr) (R := R) j P ↔ x ∈ lamYat (Pr := Pr) (R := R) j P := hk
  rw [mem_stdAt_iff] at hz
  constructor
  · intro x hx
    have hxi : IntV P x := (mem_lamYat (R := R) hP x).1 hx
    have hmem : x ∈ nfLat P (R.N j) (cOf R j) e z := mem_nfLat (fun i => (he i).2) hz hxi
    rw [← himg] at hmem
    obtain ⟨y', hy', rfl⟩ := hmem
    refine ⟨k.symm y', ?_, ?_⟩
    · rw [← hk']
      simpa using hy'
    · simp [LinearEquiv.mul_apply]
  · intro x hx
    have h1 : h (k x) ∈ nfLat P (R.N j) (cOf R j) e z := by
      rw [← himg]
      exact ⟨k x, (hk' x).2 hx, rfl⟩
    have h2 := smul_int_of_mem_nfLat (fun i => (he i).1) hz h1
    rw [mem_lamYat hP]
    intro l
    have h3 := h2 l
    simpa [LinearEquiv.mul_apply] using h3

end GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem words_real_bound {x e G F m n : ℝ} {k : ℕ} (hx : 1 < x) (he : 0 < e) (hG : 1 ≤ G) (hF : 1 ≤ F)
    (hm0 : 0 ≤ m) (hn0 : 0 ≤ n) (hm : m ≤ 2 * Real.sqrt (x * x ^ (-(e / 8)))) (hn : n ≤ 2 * x ^ (2 + 8 * e))
    (hk : x ^ (9 / 2 + 10 * e) ≤ (k : ℝ)) (hk3 : 3 ≤ k)
    (hK : 2 * (256 * G + F + 2) + 3 ≤ x ^ e) :
    3 * Real.exp (G * m ^ 5 * (2 * n) * x ^ e) ^ 2 * x ^ F ≤ (2 : ℝ) ^ (k - 3) := by
  have hx0 : 0 < x := by linarith
  set y := x ^ (9 / 2 + 9 * e) with hy
  have hxy : x ≤ y := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ y := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have hy1 : 1 ≤ y := by linarith
  have hm' : m ≤ 2 * x ^ (1 / 2 : ℝ) := by
    refine hm.trans ?_
    rw [← Real.sqrt_eq_rpow]
    have h1 : x ^ (-(e / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by linarith)
    have : Real.sqrt (x * x ^ (-(e / 8))) ≤ Real.sqrt x := Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hm5 : m ^ 5 ≤ 32 * x ^ (5 / 2 : ℝ) := by
    have h1 : m ^ 5 ≤ (2 * x ^ (1 / 2 : ℝ)) ^ 5 := pow_le_pow_left₀ hm0 hm' 5
    have h2 : (x ^ (1 / 2 : ℝ)) ^ 5 = x ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    rw [mul_pow, h2] at h1
    linarith
  have hprod : x ^ (5 / 2 : ℝ) * x ^ (2 + 8 * e) * x ^ e = y := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, hy]; congr 1; ring
  have hxe : 0 < x ^ e := Real.rpow_pos_of_pos hx0 e
  have hA : m ^ 5 * (2 * n) * x ^ e ≤ 128 * y := by
    rw [← hprod]
    have h1 : m ^ 5 * (2 * n) ≤ (32 * x ^ (5 / 2 : ℝ)) * (2 * (2 * x ^ (2 + 8 * e))) :=
      mul_le_mul hm5 (by linarith) (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_right h1 hxe.le
    linarith
  have hky : y * x ^ e ≤ (k : ℝ) := by
    refine le_trans (le_of_eq ?_) hk
    rw [hy, ← Real.rpow_add hx0]; congr 1; ring
  have hlogx : Real.log x ≤ y := by
    have := Real.log_le_sub_one_of_pos hx0
    linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hk' : 2 * ((256 * G + F + 2) * y) ≤ ((k - 3 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk3]
    push_cast
    have := mul_le_mul_of_nonneg_left hK (by linarith : (0 : ℝ) ≤ y)
    nlinarith
  have hR : (2 : ℝ) ^ (k - 3) = Real.exp (((k - 3 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hR, Real.rpow_def_of_pos hx0 F, ← Real.exp_nat_mul]
  calc 3 * Real.exp (((2 : ℕ) : ℝ) * (G * m ^ 5 * (2 * n) * x ^ e)) * Real.exp (Real.log x * F)
      ≤ Real.exp 2 * Real.exp (((2 : ℕ) : ℝ) * (G * m ^ 5 * (2 * n) * x ^ e)) * Real.exp (Real.log x * F) := by
        gcongr
    _ = Real.exp (2 + ((2 : ℕ) : ℝ) * (G * m ^ 5 * (2 * n) * x ^ e) + Real.log x * F) := by
        rw [Real.exp_add, Real.exp_add]
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have h1 : G * (m ^ 5 * (2 * n) * x ^ e) ≤ G * (128 * y) :=
          mul_le_mul_of_nonneg_left hA (by linarith)
        have h2 : Real.log x * F ≤ y * F := mul_le_mul_of_nonneg_right hlogx (by linarith)
        have h4 : ((k - 3 : ℕ) : ℝ) * (1 / 2) ≤ ((k - 3 : ℕ) : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
        push_cast
        nlinarith

theorem szRow_card_words_le : SzRow (fun C D L => (Fintype.card D.what₂.Word ≤ 2 ^ (D.R.k - 3))) := by
  intro eps he he' C hC
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hP, -, hmid, -⟩ := hC
  have hG : 1 ≤ C.CGam := hmid _ (by simp [FC.cMid])
  have hF : 1 ≤ C.P.CF := hmid _ (by simp [FC.cMid])
  have hG' : 1 ≤ C.CGam * C.P.Cpde := by nlinarith
  have hP0 : 0 < C.P.Cpde := by linarith
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨(2 * (256 * (C.CGam * C.P.Cpde) + C.P.CF + 2) + 3) ^ eps⁻¹, ?_⟩⟩⟩
  intro D L hLe hx hV
  have hK : 2 * (256 * (C.CGam * C.P.Cpde) + C.P.CF + 2) + 3 ≤ L.sc.x ^ eps := by
    have h0 : (0 : ℝ) ≤ 2 * (256 * (C.CGam * C.P.Cpde) + C.P.CF + 2) + 3 := by linarith
    have := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hx he.le
    rwa [Real.rpow_inv_rpow h0 he.ne'] at this
  have hn0 := hV.ranks.n_le_of_o hV.host.o_le
  obtain ⟨-, ⟨-, hm⟩, ⟨hk, -⟩, -⟩ := hV.ranks
  have hk3 : 3 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  rw [hV.words, Nat.ceil_le]
  rw [hLe] at hn0 hk
  have hn : (D.R.n : ℝ) / C.P.Cpde ≤ 2 * L.sc.x ^ (2 + 8 * eps) := by
    rw [div_le_iff₀ hP0]; linarith
  simp only [Scale.delta1, hLe] at hm
  have := words_real_bound L.sc.one_lt_alt he hG' hF (Nat.cast_nonneg D.R.m)
    (div_nonneg (Nat.cast_nonneg D.R.n) hP0.le) hm hn hk hk3 hK
  have e : C.CGam * C.P.Cpde * (D.R.m : ℝ) ^ 5 * (2 * ((D.R.n : ℝ) / C.P.Cpde))
      = C.CGam * (D.R.m : ℝ) ^ 5 * (2 * (D.R.n : ℝ)) := by
    field_simp
  rw [e] at this
  simp only [GamL, Scale.L, Ranks.f, hV.CGam_eq, hLe]
  push_cast
  exact this

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX

def stdConst (CT2 C8 p m l : ℝ) : FC where
  Ct := 401
  Cc := 2
  CT2 := CT2
  CGam := m
  Csz := m
  Cr := 1
  CTu := 25
  Cdg := 1
  C5 := 1
  full := True
  GK := ⟨m, l, l, l, l, l, l, l, l, l, l, 5, 4, 1, l⟩
  cX := ⟨1, ⟨12, 3, m⟩⟩
  P :=
    { CkLow := l, Ck6 := l, CfL := l, cLL := l⁻¹, CnW := 10, Crho := l, CDelG := l, CLw := 11 * 405, Cj0 := 405,
      Cw := l, cw := 9 / 10, CDel := l, CCount := l, Ch0r := l, Ch0k := l, Ch0N := l, Cgap := l, CetaF := 6,
      CY := l, CYL := 9, Cpde := C8, CccK := 1, CF := m }
  T := { CP := p, eP := 12, Cp := 1, Cb := l, cTO := 377, ChT := l, CbN := l }

theorem stdConst_cPre (CT2 C8 p m l c : ℝ) (h : c ∈ (stdConst CT2 C8 p m l).cPre) : c = p := by
  simpa [FC.cPre, stdConst] using h

theorem stdConst_cMid (CT2 C8 p m l c : ℝ)
    (h : c ∈ (stdConst CT2 C8 p m l).cMid (stdConst CT2 C8 p m l).P.CF) : c = m := by
  simpa [FC.cMid, stdConst] using h

theorem stdConst_cLast (CT2 C8 p m l c : ℝ) (h : c ∈ (stdConst CT2 C8 p m l).cLast) : c = l := by
  simpa [FC.cLast, stdConst] using h

theorem exists_std_large (K K0 : TransportedAlt) (CT2 C8 : ℝ) (h8 : 1 ≤ C8) :
    ∃ C : FC, Std C ∧ C.CT2 = CT2 ∧ C.P.Cpde = C8 ∧ C.Large K C.P.CF ∧ C.Large K0 C.P.CF ∧ C.GK.Nonneg := by
  obtain ⟨p, hp1, hpK, hpK0⟩ : ∃ p : ℝ, 1000 ≤ p ∧ K.pre ≤ p ∧ K0.pre ≤ p :=
    ⟨max 1000 (max K.pre K0.pre), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  obtain ⟨m, hm1, hmK, hmK0⟩ : ∃ m : ℝ, 1 ≤ m ∧ K.mid (stdConst CT2 C8 p 0 0).cOut ≤ m ∧
      K0.mid (stdConst CT2 C8 p 0 0).cOut ≤ m :=
    ⟨max 1 (max _ _), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  obtain ⟨l, hl1, hlK, hlK0⟩ : ∃ l : ℝ, 1 ≤ l ∧
      K.last ((stdConst CT2 C8 p m 0).cOut ++ (stdConst CT2 C8 p m 0).cMid m) ≤ l ∧
      K0.last ((stdConst CT2 C8 p m 0).cOut ++ (stdConst CT2 C8 p m 0).cMid m) ≤ l :=
    ⟨max 1 (max _ _), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  have hm0 : 0 ≤ m := by linarith
  have hl0 : 0 ≤ l := by linarith
  refine ⟨stdConst CT2 C8 p m l, ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h8, hp1, ?_, ?_⟩,
    rfl, rfl, ⟨?_, trivial, ?_, ?_⟩, ⟨?_, trivial, ?_, ?_⟩, ?_⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_rfl, rfl⟩
  · intro c hc; rw [stdConst_cMid _ _ _ _ _ _ hc]; exact hm1
  · intro c hc; rw [stdConst_cLast _ _ _ _ _ _ hc]; exact hl1
  · intro c hc; rw [stdConst_cPre _ _ _ _ _ _ hc]; exact hpK
  · intro c hc; rw [stdConst_cMid _ _ _ _ _ _ hc]; exact hmK
  · intro c hc; rw [stdConst_cLast _ _ _ _ _ _ hc]; exact hlK
  · intro c hc; rw [stdConst_cPre _ _ _ _ _ _ hc]; exact hpK0
  · intro c hc; rw [stdConst_cMid _ _ _ _ _ _ hc]; exact hmK0
  · intro c hc; rw [stdConst_cLast _ _ _ _ _ _ hc]; exact hlK0
  · exact ⟨hm0, hl0, hl0, hl0, hl0, hl0, hl0, hl0, hl0, hl0, hl0, by norm_num [stdConst], by norm_num [stdConst],
      by norm_num [stdConst], hl0⟩

end GlobalTheory.EX

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem exists_even_between (A : ℝ) (hA : 2 ≤ A) : ∃ m : ℕ, Even m ∧ A ≤ m ∧ (m : ℝ) ≤ 2 * A := by
  refine ⟨2 * ⌈A / 2⌉₊, even_two_mul _, ?_, ?_⟩
  · have := Nat.le_ceil (A / 2)
    push_cast; linarith
  · have := Nat.ceil_lt_add_one (a := A / 2) (by linarith)
    push_cast; linarith

theorem exists_ranks_of_frame (φ : Formalism.HC.Frame) (k m T W : ℕ) (hk : Even k) (hm : Even m) (h2 : 2 ≤ m) (h3 : m + 3 ≤ k)
    (hmf : m ≤ 2 * φ.ord) (hfk : 2 * φ.ord ≤ k) :
    ∃ R : Ranks, R.toFrame = φ ∧ R.k = k ∧ R.m = m ∧ R.r + R.t = 8 * R.f * R.r + 4 + T * (8 * W) := by
  obtain ⟨r, hr⟩ : ∃ r, r = k + m - 1 := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = 2 * φ.ord := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = f * r := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = T * W := ⟨_, rfl⟩
  have hpr : r ≤ p := by
    rw [hp]; exact Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨k', hk'⟩ := hk
  obtain ⟨m', hm'⟩ := hm
  have hmt : m ≤ 8 * p + 4 + 8 * q - r + 1 := by omega
  refine ⟨⟨φ, k, m, 8 * p + 4 + 8 * q - r, ⟨k', hk'⟩, ⟨m', hm'⟩, ?_, h2, h3, by omega, by omega, hmf, hfk, ?_⟩,
    rfl, rfl, rfl, ?_⟩
  · rw [Nat.odd_iff]; omega
  · rw [sq]
    exact (Nat.mul_le_mul_left m hmt).trans (Nat.le_add_left _ _)
  · show (k + m - 1) + (8 * p + 4 + 8 * q - r) = 8 * (2 * φ.ord) * (k + m - 1) + 4 + T * (8 * W)
    rw [← hr, ← hf, mul_assoc 8 f r, ← hp, mul_left_comm T 8 W, ← hq]
    omega

theorem exists_ranks_rankVal_frame : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
    ∀ φ : Formalism.HC.Frame, s.x ^ (2 + 8 * s.eps) ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps) →
      ∃ R : Ranks, R.toFrame = φ ∧ RankVal s R := by
  intro eps h0 h1
  refine ⟨16, fun s hs hx φ he1 hp2 => ?_⟩
  subst hs
  have hx1 : (1 : ℝ) ≤ s.x := by linarith
  have hx0 : (0 : ℝ) < s.x := by linarith
  have hH1 : s.x ^ 2 ≤ s.x ^ (2 + 8 * s.eps) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hH2 : s.x ^ (2 + 8 * s.eps) ≤ s.x ^ 3 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have he2 : (φ.ord : ℝ) ≤ 2 * s.x ^ 3 := by linarith
  have hB : s.x ^ 4 ≤ s.x ^ (9 / 2 + 10 * s.eps) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hd : s.x * s.delta1 = s.x ^ (1 - s.eps / 8) := by
    unfold Scale.delta1
    rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
  have hA1 : 2 ≤ Real.sqrt (s.x * s.delta1) := by
    apply Real.le_sqrt_of_sq_le
    rw [hd]
    have h1 : s.x ^ (1 / 2 : ℝ) ≤ s.x ^ (1 - s.eps / 8) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h2 : (4 : ℝ) ≤ s.x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      apply Real.le_sqrt_of_sq_le
      linarith
    linarith
  have hA2 : Real.sqrt (s.x * s.delta1) ≤ s.x := by
    rw [Real.sqrt_le_left hx0.le, hd, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have p2 : 16 * s.x ≤ s.x ^ 2 := by nlinarith
  have p3 : 16 * s.x ^ 2 ≤ s.x ^ 3 := by nlinarith
  have p4 : 16 * s.x ^ 3 ≤ s.x ^ 4 := by nlinarith
  obtain ⟨m, hm, hm1, hm2⟩ := exists_even_between _ hA1
  obtain ⟨k, hk, hk1, hk2⟩ := exists_even_between (s.x ^ (9 / 2 + 10 * s.eps)) (by linarith)
  have a1 : 2 ≤ m := by
    have : ((2 : ℕ) : ℝ) ≤ m := by push_cast; linarith
    exact_mod_cast this
  have a2 : m + 3 ≤ k := by
    have : (m : ℝ) + 3 ≤ k := by linarith
    exact_mod_cast this
  have a3 : m ≤ 2 * φ.ord := by
    have : (m : ℝ) ≤ 2 * (φ.ord : ℝ) := by linarith
    exact_mod_cast this
  have a4 : 2 * φ.ord ≤ k := by
    have : 2 * (φ.ord : ℝ) ≤ k := by linarith
    exact_mod_cast this
  obtain ⟨R, rfl, rfl, rfl, hR⟩ := exists_ranks_of_frame φ k m (TOv s)
    ⌈10 * ((k + m - 1 : ℕ) : ℝ) * (((2 * φ.ord : ℕ) : ℝ) +
      ((2 * φ.ord : ℕ) : ℝ) ^ 2 * ((k : ℝ) - 1) ^ 3 * s.L ^ 2 / m) / 8⌉₊ hk hm a1 a2 a3 a4
  exact ⟨R, rfl, ⟨he1, hp2⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, hR⟩

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

theorem _root_.GlobalTheory.T.levelPrime_incidence_finite_fibres_stable : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (v : X.A.vT), (∀ p, {p₁ | M.Inc v p p₁}.Finite ∧ {p₀ | M.Inc v p₀ p}.Finite) ∧ (∀ (g : M.G) p p₁, M.Inc v p p₁ ↔ M.Inc v (g • p) (g • p₁)) ∧ ∀ (p : M.Pt) x, (p.2 v).1.f x = 1 → ∃! q, (p.2 v).IsUp x q := by
  first | exact @GlobalTheory.LvT.inc_finite_stable | exact GlobalTheory.LvT.inc_finite_stable | (intros; apply GlobalTheory.LvT.inc_finite_stable <;> assumption)
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.discOneScale_ratio_ideal_ring_algebraic_unit : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ₀ ^ 12 = GlobalTheory.MomOne.discr D.host.d → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → Nat.Coprime (Ideal.absNorm cc) q → δ / δ₀ ∈ Qbar ∧ ∀ ι : ℂ ≃+* ℂ_[q], ‖ι (δ / δ₀)‖ = 1 := by
  first | exact @GlobalTheory.MomDelta.delta_ratio | exact GlobalTheory.MomDelta.delta_ratio | (intros; apply GlobalTheory.MomDelta.delta_ratio <;> assumption)
end
