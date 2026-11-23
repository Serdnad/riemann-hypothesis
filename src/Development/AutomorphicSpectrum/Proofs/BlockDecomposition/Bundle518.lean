module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle493
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle036
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle499
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle224
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle483
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DefsPlus
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle495
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

@[expose] public section

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.FMem

variable {n : ℕ}

theorem contDiff_entry (a b : Fin n) : ContDiff ℝ ∞ (fun g : Mat n => g a b) :=
  contDiff_apply_apply ℝ a b

theorem contDiff_det_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] {M : Mat n → Matrix ι ι ℂ}
    (h : ∀ a b, ContDiff ℝ ∞ fun g => M g a b) : ContDiff ℝ ∞ fun g => (M g).det := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => h _ _

theorem contDiff_lm (j : Fin n) : ContDiff ℝ ∞ (lm j) :=
  contDiff_det_of_entries fun _ _ => contDiff_entry _ _

theorem contDiff_gm (j : Fin n) : ContDiff ℝ ∞ (gm j) := by
  refine contDiff_det_of_entries fun a b => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
  refine ContDiff.sum fun k _ => (contDiff_entry _ _).mul ?_
  exact Complex.conjCLE.contDiff.comp (contDiff_entry _ _)

theorem zpow_contDiffOn {f : Mat n → ℂ} {s : Set (Mat n)} (hf : ContDiffOn ℝ ∞ f s)
    (h : ∀ x ∈ s, f x ≠ 0) (m : ℤ) : ContDiffOn ℝ ∞ (fun x => f x ^ m) s := by
  obtain ⟨k, rfl | rfl⟩ := m.eq_nat_or_neg
  · simpa only [zpow_natCast] using hf.pow k
  · simp only [_root_.zpow_neg, zpow_natCast]
    exact (hf.pow k).inv fun x hx => pow_ne_zero k (h x hx)


open scoped ComplexOrder in
theorem gm_ne_zero (j : Fin n) {g : Mat n} (hg : g ∈ GLs n) : gm j g ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 : (g.submatrix (ini j) id)ᴴ *ᵥ v = 0 :=
    (Matrix.self_mul_conjTranspose_mulVec_eq_zero _ v).mp hAv
  have hu : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
  have hAB : g.submatrix (ini j) id * (g⁻¹).submatrix id (ini j) = 1 := by
    have h2 := Matrix.submatrix_mul g g⁻¹ (ini j) id (ini j) Function.bijective_id
    have hi : Function.Injective (ini j) := Fin.castLE_injective _
    rw [Matrix.mul_nonsing_inv g hu, Matrix.submatrix_one _ hi] at h2
    exact h2.symm
  have hBA : ((g⁻¹).submatrix id (ini j))ᴴ * (g.submatrix (ini j) id)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hAB, Matrix.conjTranspose_one]
  apply hv
  calc v = (((g⁻¹).submatrix id (ini j))ᴴ * (g.submatrix (ini j) id)ᴴ) *ᵥ v := by
        rw [hBA, Matrix.one_mulVec]
    _ = ((g⁻¹).submatrix id (ini j))ᴴ *ᵥ ((g.submatrix (ini j) id)ᴴ *ᵥ v) :=
        (Matrix.mulVec_mulVec _ _ _).symm
    _ = 0 := by rw [h1, Matrix.mulVec_zero]

theorem muZ_antitone {lam : Fin n → ℤ} {lev : Fin n → ℕ} (hlam : Antitone lam) (hlev : Monotone lev) :
    Antitone (muZ lam lev) := by
  intro a b hab
  have h1 := hlam hab
  have h2 : lev a ≤ lev b := hlev hab
  have c1 : (univ.filter fun c => lev b < lev c).card ≤ (univ.filter fun c => lev a < lev c).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
  have c2 : (univ.filter fun c => lev c < lev a).card ≤ (univ.filter fun c => lev c < lev b).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
  simp only [muZ]
  omega

theorem dif_nonneg_of_antitone {v : Fin n → ℤ} (h : Antitone v) (j : Fin n) (hj : (j : ℕ) + 1 < n) :
    0 ≤ dif v j := by
  have hnext : j ≤ (⟨j + 1, hj⟩ : Fin n) := Fin.le_def.mpr (Nat.le_succ _)
  simpa only [dif, dite_eq_left hj, sub_nonneg] using h hnext

theorem lm_ne_zero (j : Fin n) (hj : ¬ (j : ℕ) + 1 < n) {g : Mat n} (hg : g ∈ GLs n) : lm j g ≠ 0 := by
  have hb : Function.Bijective (ini j) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨Fin.castLE_injective _, by
      have := j.isLt
      simp only [Fintype.card_fin]
      omega⟩
  have e : lm j g = g.det := Matrix.det_submatrix_equiv_self (Equiv.ofBijective _ hb) g
  rw [e]
  exact hg

end GlobalTheory.CompanionTheory.ModelS.FMem

namespace GlobalTheory.CompanionTheory.ModelS


open FMem in
theorem fRaw_mem_SmF : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    GlobalTheory.CompanionTheory.ModelS.fRaw lam lev ∈ GlobalTheory.CompanionTheory.ModelS.SmF n := by
  intro n lam hlam lev hlev
  refine ⟨?_, fun g hg => Set.indicator_of_notMem hg _⟩
  have key : ContDiffOn ℝ ∞
      (fun g => ∏ j, lm j g ^ dif (muZ lam lev) j * gm j g ^ dif (yZ lam lev) j) (GLs n) := by
    refine contDiffOn_prod fun j _ => ContDiffOn.mul ?_
      (zpow_contDiffOn (contDiff_gm j).contDiffOn (fun g hg => gm_ne_zero j hg) _)
    by_cases hj : (j : ℕ) + 1 < n
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (dif_nonneg_of_antitone (muZ_antitone hlam hlev.1) j hj)
      simp only [hk, zpow_natCast]
      exact ((contDiff_lm j).pow k).contDiffOn
    · exact zpow_contDiffOn (contDiff_lm j).contDiffOn (fun g hg => lm_ne_zero j hj hg) _
  exact key.congr fun g hg => Set.indicator_of_mem hg _

end GlobalTheory.CompanionTheory.ModelS
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS.FMul

open GlobalTheory.CompanionTheory.ModelS

variable {n : ℕ}

theorem ini_injective (j : Fin n) : Function.Injective (ini j) :=
  Fin.castLE_injective j.isLt

theorem rows_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    (p * g).submatrix (ini j) id = p.submatrix (ini j) (ini j) * g.submatrix (ini j) id := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, id]
  symm
  refine Fintype.sum_of_injective (ini j) (ini_injective j) _ _ ?_ (fun i => rfl)
  intro k hk
  have hjk : j < k := by
    by_contra h
    have h' : (k : ℕ) ≤ j := by
      have := not_lt.1 h
      exact Fin.le_def.1 this
    exact hk ⟨⟨k, by omega⟩, by ext; rfl⟩
  have haj : ini j a ≤ j := by
    have := a.isLt
    rw [Fin.le_def]
    show (a : ℕ) ≤ j
    omega
  rw [hz _ _ haj hjk, zero_mul]

theorem lm_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    lm j (p * g) = lm j p * lm j g := by
  have h : (p * g).submatrix (ini j) (ini j) =
      p.submatrix (ini j) (ini j) * g.submatrix (ini j) (ini j) := by
    ext a c
    exact congrFun (congrFun (rows_mul j p g hz) a) (ini j c)
  delta lm
  rw [h, Matrix.det_mul]

theorem gm_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    gm j (p * g) = lm j p * star (lm j p) * gm j g := by
  delta gm lm
  rw [rows_mul j p g hz, Matrix.conjTranspose_mul]
  have h : p.submatrix (ini j) (ini j) * g.submatrix (ini j) id *
      ((g.submatrix (ini j) id)ᴴ * (p.submatrix (ini j) (ini j))ᴴ) =
      p.submatrix (ini j) (ini j) * (g.submatrix (ini j) id * (g.submatrix (ini j) id)ᴴ) *
        (p.submatrix (ini j) (ini j))ᴴ := by
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  ring

theorem gm_one (j : Fin n) : gm j (1 : Mat n) = 1 := by
  have h : ((1 : Mat n).submatrix (ini j) id) * ((1 : Mat n).submatrix (ini j) id)ᴴ = 1 := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one,
      Matrix.submatrix_one _ (ini_injective j)]
  delta gm
  rw [h, Matrix.det_one]

theorem gm_left (j : Fin n) (p : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    gm j p = lm j p * star (lm j p) := by
  have := gm_mul j p 1 hz
  rwa [Matrix.mul_one, gm_one, mul_one] at this

theorem dif_eq_zero (lam : Fin n → ℤ) (lev : Fin n → ℕ) (hl : IsLev lam lev) (j : Fin n) (h : (j : ℕ) + 1 < n)
    (he : lev j = lev ⟨j + 1, h⟩) : dif (muZ lam lev) j = 0 ∧ dif (yZ lam lev) j = 0 := by
  obtain ⟨-, hl⟩ := hl
  have hlam := hl _ _ he
  have hmu : muZ lam lev j = muZ lam lev ⟨j + 1, h⟩ := by
    delta muZ
    simp only [hlam, he]
  have hy : yZ lam lev j = yZ lam lev ⟨j + 1, h⟩ := by
    delta yZ
    simp only [hlam, hmu]
  delta dif
  constructor
  · simp only [dite_eq_left h, hmu, sub_self]
  · simp only [dite_eq_left h, hy, sub_self]

theorem fRaw_mul : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∀ g ∈ GLs n,
      GlobalTheory.CompanionTheory.ModelS.fRaw lam lev (p * g) = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev p * GlobalTheory.CompanionTheory.ModelS.fRaw lam lev g := by
  intro n lam _ lev hl p hp g hg
  obtain ⟨hp1, hp2⟩ := hp
  have hpg : p * g ∈ GLs n := by
    show (p * g).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hp1 hg
  delta fRaw
  simp only [Set.indicator_of_mem hpg, Set.indicator_of_mem hp1, Set.indicator_of_mem hg]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hgood : ∀ a b : Fin n, a ≤ j → j < b → lev a < lev b
  · have hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0 := fun a b h1 h2 => hp2 a b (hgood a b h1 h2)
    rw [lm_mul j p g hz, gm_mul j p g hz, ← gm_left j p hz, mul_zpow, mul_zpow, mul_mul_mul_comm]
  · push Not at hgood
    obtain ⟨a, b, haj, hjb, hba⟩ := hgood
    have hmono := hl.1
    have hb : (j : ℕ) < b := Fin.lt_def.1 hjb
    have h : (j : ℕ) + 1 < n := by have := b.isLt; omega
    have h1 : lev j ≤ lev ⟨j + 1, h⟩ := hmono (Fin.le_def.2 (by simp))
    have h2 : lev ⟨j + 1, h⟩ ≤ lev b := hmono (Fin.le_def.2 (by simpa using hb))
    have h3 : lev a ≤ lev j := hmono haj
    have he : lev j = lev ⟨j + 1, h⟩ := by omega
    obtain ⟨d1, d2⟩ := dif_eq_zero lam lev hl j h he
    simp only [d1, d2, zpow_zero, mul_one]

end GlobalTheory.CompanionTheory.ModelS.FMul
end
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.ReversedBlocks

variable {n : ℕ}

theorem lower_iff (P : Fin n → Prop) [DecidablePred P] (hP : ∀ a b, a ≤ b → P b → P a) (b : Fin n) :
    P b ↔ (b : ℕ) < (univ.filter P).card :=
  _root_.UpperTheory.Reformulated.B.Re1.lower_iff P hP b

def lowC (lev : Fin n → ℕ) (a : Fin n) : ℕ := (univ.filter fun b => lev b < lev a).card

def topC (lev : Fin n → ℕ) (a : Fin n) : ℕ := (univ.filter fun b => lev b ≤ lev a).card

theorem lt_iff {lev : Fin n → ℕ} (hm : Monotone lev) (a b : Fin n) : lev b < lev a ↔ (b : ℕ) < lowC lev a :=
  lower_iff (fun b => lev b < lev a) (fun _ _ h hb => lt_of_le_of_lt (hm h) hb) b

theorem le_iff {lev : Fin n → ℕ} (hm : Monotone lev) (a b : Fin n) : lev b ≤ lev a ↔ (b : ℕ) < topC lev a :=
  lower_iff (fun b => lev b ≤ lev a) (fun _ _ h hb => le_trans (hm h) hb) b

theorem high_add_topC (lev : Fin n → ℕ) (a : Fin n) :
    (univ.filter fun b => lev a < lev b).card + topC lev a = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun b => lev a < lev b)
  simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h
  unfold topC
  exact h

def rv (lev : Fin n → ℕ) (a : Fin n) : ℕ := lowC lev a + (topC lev a - 1) - a

theorem rv_bounds {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) :
    lowC lev a ≤ a ∧ (a : ℕ) < topC lev a ∧ rv lev a + a + 1 = lowC lev a + topC lev a := by
  have h1 : ¬ (a : ℕ) < lowC lev a := fun h => lt_irrefl _ ((lt_iff hm a a).2 h)
  have h2 : (a : ℕ) < topC lev a := (le_iff hm a a).1 le_rfl
  unfold rv
  omega

theorem rv_lt {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : rv lev a < n := by
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  have := high_add_topC lev a
  omega

def rf {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : Fin n := ⟨rv lev a, rv_lt hm a⟩

theorem lev_rf {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : lev (rf hm a) = lev a := by
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  apply le_antisymm
  · exact (le_iff hm a _).2 (by simp only [rf]; omega)
  · exact not_lt.1 fun h => by
      have := (lt_iff hm a _).1 h
      simp only [rf] at this
      omega

theorem rf_rf {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : rf hm (rf hm a) = a := by
  have hl := lev_rf hm a
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  obtain ⟨k1, k2, k3⟩ := rv_bounds hm (rf hm a)
  have e1 : lowC lev (rf hm a) = lowC lev a := by simp only [lowC, hl]
  have e2 : topC lev (rf hm a) = topC lev a := by simp only [topC, hl]
  apply Fin.ext
  have e3 : ((rf hm a : Fin n) : ℕ) = rv lev a := rfl
  have e4 : ((rf hm (rf hm a) : Fin n) : ℕ) = rv lev (rf hm a) := rfl
  omega

theorem exists_perm_yZ : ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev →
    ∃ σ : Equiv.Perm (Fin n), ∀ a : Fin n,
      (GlobalTheory.CompanionTheory.ModelS.yZ lam lev a : ℂ) + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ) = infOf lam false (σ a) := by
  intro n lam lev h
  obtain ⟨hm, hc⟩ := h
  refine ⟨Function.Involutive.toPerm (rf hm) (rf_rf hm), fun a => ?_⟩
  have hv : (Function.Involutive.toPerm (rf hm) (rf_rf hm)) a = rf hm a := rfl
  rw [hv]
  have hl : lam (rf hm a) = lam a := hc _ _ (lev_rf hm a)
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  have h4 := high_add_topC lev a
  have c3 : ((rv lev a : ℕ) : ℂ) + ((a : ℕ) : ℂ) + 1 = (lowC lev a : ℂ) + (topC lev a : ℂ) := by exact_mod_cast h3
  have c4 : (((univ.filter fun b => lev a < lev b).card : ℕ) : ℂ) + (topC lev a : ℂ) = (n : ℂ) := by exact_mod_cast h4
  have e3 : (((rf hm a : Fin n) : ℕ) : ℂ) = (rv lev a : ℂ) := rfl
  have hlow : (((univ.filter fun b => lev b < lev a).card : ℕ) : ℂ) = (lowC lev a : ℂ) := rfl
  simp only [GlobalTheory.CompanionTheory.ModelS.yZ, GlobalTheory.CompanionTheory.ModelS.muZ, infOf, hl, e3]
  push_cast
  rw [hlow]
  linear_combination (-1 : ℂ) * c3 - c4

end GlobalTheory.CompanionTheory.ModelS.ReversedBlocks
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar




noncomputable section
namespace GlobalTheory.CompanionTheory.WSum

variable {D : D7}

theorem trace_incA_algebraMap_mul (D : D7) (β : D.host.F) (z : AE D) :
    Algebra.trace (AF D.host.F) (AE D) (incA D (algebraMap D.host.F D.host.E β) * z) =
      algebraMap D.host.F (AF D.host.F) β * Algebra.trace (AF D.host.F) (AE D) z := by
  have h : incA D (algebraMap D.host.F D.host.E β) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) β) := by
    show (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E β) =
      (algebraMap D.host.F (AF D.host.F) β) ⊗ₜ[D.host.F] (1 : D.host.E)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [h, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem theta_half_rs {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    {α β : D.host.F} (hβ : β + β = α) (s : ℝ) (t : AE D) (ρ : D.what₂.Tau) :
    θ ρ (infPart D (incA D (algebraMap D.host.F D.host.E β) * (rs σ s * t))) =
      ((1 / 2 * s : ℝ) : ℂ) * θ ρ (infPart D (incA D (algebraMap D.host.F D.host.E α) * t)) := by
  have hi : ∀ e, θ ρ (infPart D (incA D e)) = tauE D ρ e := fun e => (hσ.inf ρ).1 e
  have hs : θ ρ (infPart D (rs σ s)) = (s : ℂ) := hσ.comp _ ρ
  have hb : tauE D ρ (algebraMap D.host.F D.host.E α) =
      tauE D ρ (algebraMap D.host.F D.host.E β) + tauE D ρ (algebraMap D.host.F D.host.E β) := by
    rw [← map_add (f := _), ← map_add (f := _), hβ]
  rw [map_mul (infPart D), map_mul (θ ρ), hi, map_mul (infPart D), map_mul (θ ρ), hs,
    map_mul (infPart D), map_mul (θ ρ), hi, hb]
  push_cast
  ring

theorem psi_halfTr_rs : ∀ (D : D7) (ψ ψ₀ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ₀ (-1) → ∀ α : D.host.F,
    (∀ x, ψ x = ψ₀ (algebraMap D.host.F (AF D.host.F) α * x)) → ∀ (θ : InfFam D)
    (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (t : AE D) (s : ℝ),
    ψ (halfTr (rs σ s * t)) = Complex.exp (2 * Real.pi * Complex.I * ((s * lam θ α t : ℝ) : ℂ)) := by
  intro D ψ ψ₀ h₀ α hψ θ σ hσ t s
  obtain ⟨β, hβ', hβ⟩ : ∃ β : D.host.F, β = α * (1 / 2) ∧ β + β = α := ⟨_, rfl, by ring⟩
  set z' : AE D := incA D (algebraMap D.host.F D.host.E β) * (rs σ s * t) with hz'
  have hR : algebraMap D.host.F (AF D.host.F) α * halfTr (rs σ s * t) =
      Algebra.trace (AF D.host.F) (AE D) z' := by
    rw [hz', trace_incA_algebraMap_mul, hβ', map_mul, mul_assoc]
    rfl
  have hfin : finPart D z' = 0 := by
    have h0 : finPart D (rs σ s) = 0 := hσ.fin _
    rw [hz', map_mul (finPart D), map_mul (finPart D) (rs σ s), h0, zero_mul, mul_zero]
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set R := Algebra.trace (AF D.host.F) (AE D) z' with hRdef
  have h1 : ψ₀ R = psiInf D.host.F ψ₀ (fstA D.host.F R) := by
    unfold psiInf
    rw [← hT]
  have h2 := h₀.2.2 θ hσ.inf (fstA D.host.F R)
  have h3 : ∀ ρ, θ ρ (fstA D.host.F R ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((s * (θ ρ (infPart D (incA D (algebraMap D.host.F D.host.E α) * t))).re : ℝ) : ℂ) := by
    intro ρ
    rw [hRdef, GlobalTheory.PhaseReal.theta_trace θ hσ.inf ρ z', hz', theta_half_rs hσ hβ, Complex.re_ofReal_mul]
    congr 1
    ring
  rw [hψ, hR, h1, h2]
  congr 1
  simp only [h3]
  rw [← Complex.ofReal_sum, ← Finset.mul_sum]
  unfold lam
  push_cast
  ring

end GlobalTheory.CompanionTheory.WSum
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD

noncomputable section

namespace GlobalTheory.CompanionTheory.DualMapAct

theorem act_dual : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}, ∀ (o : Op E a) (φ : Sm E a)
    (h1 : (fun g => star (φ.1 (invA E a g))) ∈ Sm E a)
    (h2 : (fun g => star ((act (invTOp o) φ).1 (invA E a g))) ∈ Sm E a),
    act o (⟨fun g => star (φ.1 (invA E a g)), h1⟩ : Sm E a) =
      ⟨fun g => star ((act (invTOp o) φ).1 (invA E a g)), h2⟩ :=
  fun o φ _ _ => GlobalTheory.CompanionTheory.DualAct.act_star_invT o φ _ _ (fun _ => rfl) (fun _ => rfl)

end GlobalTheory.CompanionTheory.DualMapAct

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels PositivityTheory.SiegelWeilFormula

theorem _root_.GlobalTheory.T.adelic_skew_matrices_locally_compact_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ),
    (∀ β : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), β ∈ nA σ Y b ↔ βᵀ + ((ε : ℤ) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • β.map (cA σ) = 0) →
    IsClosed (nA σ Y b : Set (Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) ∧ IsTopologicalAddGroup (nA σ Y b) ∧
    LocallyCompactSpace (nA σ Y b) ∧ SecondCountableTopology (nA σ Y b) ∧ T2Space (nA σ Y b) ∧ BorelSpace (nA σ Y b) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelRadTop.nA_top | exact GlobalTheory.CompanionTheory.SiegelRadTop.nA_top | (intros; apply GlobalTheory.CompanionTheory.SiegelRadTop.nA_top <;> assumption)
end
