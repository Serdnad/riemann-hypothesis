module

public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.Bundle001
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.Bundle002
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DetIdealsKernelNormOne
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.HenselQuad

@[expose] public section

section

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq Formalism.L2.Th1.H

variable {D : Car}

theorem sum_three_comm {a b c : ℕ} (F : Fin a → Fin b → Fin c → ℂ) :
    ∑ i, ∑ j, ∑ k, F i j k = ∑ k, ∑ j, ∑ i, F i j k := by
  calc ∑ i, ∑ j, ∑ k, F i j k = ∑ i, ∑ k, ∑ j, F i j k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, F i j k := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, F i j k := Finset.sum_congr rfl fun k _ => Finset.sum_comm

private theorem formV_apply' (A : ℝ) {N N' : ℕ} (z w : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' z w = (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (A : ℂ) := rfl

theorem formV_phi {N N' : ℕ} (A : ℝ) (M : Matrix (Fin N') (Fin N') D.host.E) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (phi M x) y =
      Ker.formV A D.what₂.Tau N N' x (phi (letI := D.host.cmStar; Mᴴ) y) := by
  rw [formV_apply', formV_apply']
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_

  simp only [phi_apply, Matrix.conjTranspose_apply, Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.embT_star', Complex.star_def, map_sum,
  map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  refine (sum_three_comm _).trans ?_
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

variable (D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ)

def HH : Sesq (TaylorLogMetric.VC D N N') := Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N'

def qq (x : TaylorLogMetric.VC D N N') : ℝ := Real.sqrt D.host.d / 2 * (HH D cc δ N N' x x).re

def cp (x y : TaylorLogMetric.VC D N N') : ℝ :=
  Real.sqrt D.host.d / 2 * ((HH D cc δ N N' x y).re + (HH D cc δ N N' y x).re)

def bet (x y : TaylorLogMetric.VC D N N') : ℝ := cp D cc δ N N' x y - (HH D cc δ N N' x y).im

def Good (x y : TaylorLogMetric.VC D N N') : Prop := ∃ k : ℤ, bet D cc δ N N' x y = 2 * k

variable {D cc δ N N'}

theorem qq_add (x y : TaylorLogMetric.VC D N N') :
    qq D cc δ N N' (x + y) = qq D cc δ N N' x + qq D cc δ N N' y + cp D cc δ N N' x y := by
  simp only [qq, cp, map_add (f := _), LinearMap.add_apply, Complex.add_re]
  ring

theorem bet_add_left (x x' y : TaylorLogMetric.VC D N N') :
    bet D cc δ N N' (x + x') y = bet D cc δ N N' x y + bet D cc δ N N' x' y := by
  simp only [bet, cp, map_add (f := _), LinearMap.add_apply, Complex.add_re, Complex.add_im]
  ring

theorem bet_add_right (x y y' : TaylorLogMetric.VC D N N') :
    bet D cc δ N N' x (y + y') = bet D cc δ N N' x y + bet D cc δ N N' x y' := by
  simp only [bet, cp, map_add (f := _), LinearMap.add_apply, Complex.add_re, Complex.add_im]
  ring

theorem bet_phi (e : Matrix (Fin N') (Fin N') D.host.E) (x y : TaylorLogMetric.VC D N N') :
    bet D cc δ N N' (phi e x) (phi e y) = bet D cc δ N N' x (phi (letI := D.host.cmStar; eᴴ * e) y) := by
  letI := D.host.cmStar
  have h1 : ∀ a b : TaylorLogMetric.VC D N N', HH D cc δ N N' (phi e a) (phi e b) = HH D cc δ N N' a (phi (eᴴ * e) b) := by
    intro a b
    simp only [HH]
    rw [formV_phi, ← phi_mul]
  have h2 : ∀ a b : TaylorLogMetric.VC D N N', HH D cc δ N N' (phi (eᴴ * e) a) b = HH D cc δ N N' a (phi (eᴴ * e) b) := by
    intro a b
    simp only [HH]
    rw [formV_phi, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  show cp D cc δ N N' (phi e x) (phi e y) - (HH D cc δ N N' (phi e x) (phi e y)).im =
    cp D cc δ N N' x (phi (eᴴ * e) y) - (HH D cc δ N N' x (phi (eᴴ * e) y)).im
  simp only [cp, h1, h2]

theorem negpow (b : ℤ) : ((-1 : ℂ) ^ b) = Complex.exp ((Real.pi : ℂ) * Complex.I * (b : ℂ)) := by
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  ring

theorem al_of_q {z : TaylorLogMetric.VC D N N'} {m : ℤ} (h : qq D cc δ N N' z = m) : TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) z = (-1 : ℂ) ^ m := by
  have h' : Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z z).re = m := h
  unfold TaylorLogMetric.al
  rw [h', round_intCast]

private theorem exists_int_eq_add_two_mul_of_exp_eq {a b : ℝ}
    (h : Complex.exp ((Real.pi : ℂ) * Complex.I * (a : ℂ)) = Complex.exp ((Real.pi : ℂ) * Complex.I * (b : ℂ))) :
    ∃ n : ℤ, a = b + 2 * n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have h2 : ((a : ℂ) - b - 2 * n) * ((Real.pi : ℂ) * Complex.I) = 0 := by
    linear_combination hn
  have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero
  have h3 := (mul_eq_zero.mp h2).resolve_right hpi
  have h4 : ((a - b - 2 * n : ℝ) : ℂ) = 0 := by push_cast; exact h3
  have h5 := Complex.ofReal_eq_zero.mp h4
  linarith

private theorem cp_eq_qq_add_sub {x y : TaylorLogMetric.VC D N N'} {mx my mxy : ℤ} (hx : qq D cc δ N N' x = mx)
    (hy : qq D cc δ N N' y = my) (hxy : qq D cc δ N N' (x + y) = mxy) :
    cp D cc δ N N' x y = (mxy : ℝ) - mx - my := by
  have h := qq_add (cc := cc) (δ := δ) x y
  rw [hxy, hx, hy] at h
  linarith

theorem good_of_law {x y : TaylorLogMetric.VC D N N'} {mx my mxy : ℤ} (hx : qq D cc δ N N' x = mx) (hy : qq D cc δ N N' y = my)
    (hxy : qq D cc δ N N' (x + y) = mxy)
    (hlaw : TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (x + y) = TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x * TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) y *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE (HH D cc δ N N') x y : ℂ))) :
    Good D cc δ N N' x y := by
  have hc := cp_eq_qq_add_sub hx hy hxy
  rw [al_of_q hxy, al_of_q hx, al_of_q hy] at hlaw
  have hpow : ((-1 : ℂ) ^ mxy) = (-1 : ℂ) ^ mx * (-1 : ℂ) ^ my * (-1 : ℂ) ^ (mxy - mx - my) := by
    rw [mul_assoc, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    congr 1
    ring
  rw [hpow] at hlaw
  have hne : ((-1 : ℂ) ^ mx * (-1 : ℂ) ^ my) ≠ 0 := by
    apply mul_ne_zero <;> exact zpow_ne_zero _ (by norm_num)
  have he := mul_left_cancel₀ hne hlaw
  rw [negpow] at he
  obtain ⟨n, hn⟩ := exists_int_eq_add_two_mul_of_exp_eq (a := altE (HH D cc δ N N') x y) (b := (mxy : ℝ) - mx - my) (by
    rw [← he]
    push_cast
    ring_nf)
  refine ⟨-n, ?_⟩
  show cp D cc δ N N' x y - (HH D cc δ N N' x y).im = 2 * ((-n : ℤ) : ℝ)
  simp only [altE] at hn
  rw [hc]
  push_cast
  linarith

theorem law_of_good {x y : TaylorLogMetric.VC D N N'} {mx my mxy : ℤ} (hx : qq D cc δ N N' x = mx) (hy : qq D cc δ N N' y = my)
    (hxy : qq D cc δ N N' (x + y) = mxy) (hg : Good D cc δ N N' x y) :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (x + y) = TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x * TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) y *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE (HH D cc δ N N') x y : ℂ)) := by
  have hc := cp_eq_qq_add_sub hx hy hxy
  obtain ⟨k, hk⟩ := hg
  have hA0 : altE (HH D cc δ N N') x y = (mxy : ℝ) - mx - my - 2 * k := by
    simp only [bet] at hk
    simp only [altE]
    linarith
  have hA : ((altE (HH D cc δ N N') x y : ℝ) : ℂ) = ((mxy - mx - my - 2 * k : ℤ) : ℂ) := by
    rw [hA0]
    push_cast
    ring
  rw [al_of_q hxy, al_of_q hx, al_of_q hy, hA, ← negpow, mul_assoc,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  have he : mx + (my + (mxy - mx - my - 2 * k)) = mxy + 2 * (-k) := by ring
  rw [he, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), _root_.zpow_mul]
  norm_num

theorem good_of_lat {Y : AddSubgroup (TaylorLogMetric.VC D N N')} (hsc : IsSemiChar (HH D cc δ N N') Y (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)))
    (hq : ∀ z ∈ Y, ∃ m : ℤ, qq D cc δ N N' z = m) {x y : TaylorLogMetric.VC D N N'} (hx : x ∈ Y) (hy : y ∈ Y) :
    Good D cc δ N N' x y := by
  obtain ⟨mx, hmx⟩ := hq x hx
  obtain ⟨my, hmy⟩ := hq y hy
  obtain ⟨mxy, hmxy⟩ := hq (x + y) (Y.add_mem hx hy)
  exact good_of_law hmx hmy hmxy (hsc.2 x hx y hy)

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs
end
end

section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H

theorem iopSelf (D : Car) : IopSelf D := by
  intro T N N' La' G hG
  funext z
  have hq : ∀ q : ↥La' ⧸ La'.addSubgroupOf La', q = 0 := by
    intro q
    refine QuotientAddGroup.induction_on q fun x => ?_
    exact (QuotientAddGroup.eq_zero_iff x).2 (by simp [AddSubgroup.addSubgroupOf_self])
  have hidx : (La'.addSubgroupOf La').index = 1 := by
    rw [AddSubgroup.addSubgroupOf_self, AddSubgroup.index_top]
  simp only [TaylorLogMetric.Iop, hidx, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul]
  rw [finsum_eq_single _ 0 (fun q hq' => absurd (hq q) hq')]
  exact hG.2 _ (Quotient.out (0 : ↥La' ⧸ La'.addSubgroupOf La')).2 z

section Chi

variable {D : Car}

theorem character_factor_change_right (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hM : DetMul D) {N N' : ℕ} (hN' : Even N')
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) {L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h1 : SD D L') (h2 : SD D L'') :
    Cd.Base.chiFac χ N N' L L'' = χ (TaylorLogMetric.detId D L' L'') ^ (-((N / 2 : ℕ) : ℤ)) * Cd.Base.chiFac χ N N' L L' := by
  unfold Cd.Base.chiFac
  rw [hM N' (StandardLatticesGL3.stdL D N') L' L'' hN' (sd0 N') h1 h2,
    hχ.1 _ _ (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N' _ _ hN' (sd0 N') h1)
      (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N' _ _ hN' h1 h2), mul_zpow]
  ring

theorem character_factor_change_left (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hM : DetMul D) {N N' : ℕ} (hN : Even N)
    {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (h1 : SD D L) (h2 : SD D L₁) :
    Cd.Base.chiFac χ N N' L₁ L' = χ (TaylorLogMetric.detId D L L₁) ^ (((N' / 2 : ℕ) : ℤ)) * Cd.Base.chiFac χ N N' L L' := by
  unfold Cd.Base.chiFac
  rw [hM N (StandardLatticesGL3.stdL D N) L L₁ hN (sd0 N) h1 h2,
    hχ.1 _ _ (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N _ _ hN (sd0 N) h1)
      (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N _ _ hN h1 h2), mul_zpow]
  ring

theorem emb_star_unit (τ : D.what₂.Tau) (x : D.host.E) (hx : letI := D.host.cmStar; x * star x = 1) :
    (letI := D.host.cmStar; TaylorLogMetric.embT D τ (star x)) = (TaylorLogMetric.embT D τ x)⁻¹ := by
  letI := D.host.cmStar
  have h := congrArg (TaylorLogMetric.embT D τ) hx
  rw [map_mul, map_one] at h
  exact eq_inv_of_mul_eq_one_right h

private theorem inv_mul_zpow_mul_inv_mul_zpow_neg (a b P Q : ℂ) (m n : ℕ) :
    (P⁻¹ * a) ^ (m : ℤ) * (Q⁻¹ * b) ^ (-(n : ℤ)) = a ^ (m : ℤ) * b ^ (-(n : ℤ)) * (P⁻¹ ^ m * Q ^ n) := by
  rw [mul_zpow, mul_zpow, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast,
    inv_pow, inv_pow, inv_inv]
  ring

theorem character_factor_unitary_action (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hS : DetSmul D) (hU : NormOneUnitIdeal D) {N N' : ℕ}
    (hN : Even N) (hN' : Even N') :
    letI := D.host.cmStar
    ∀ (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E), SD D L → SD D L' →
    Cd.Base.chiFac χ N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L') =
      Cd.Base.chiFac χ N N' L L' *
        ((∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) *
          (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) ^ (N / 2)) := by
  intro L L' γ γ' hL hL'
  letI := D.host.cmStar
  have hd : (γ : Matrix (Fin N) (Fin N) D.host.E).det ∈ unitary D.host.E :=
    Matrix.det_of_mem_unitary γ.2
  have hd' : (γ' : Matrix (Fin N') (Fin N') D.host.E).det ∈ unitary D.host.E :=
    Matrix.det_of_mem_unitary γ'.2
  have e1 := hS N (StandardLatticesGL3.stdL D N) L γ hN (sd0 N) hL
  have e2 := hS N' (StandardLatticesGL3.stdL D N') L' γ' hN' (sd0 N') hL'
  have c1 := hχ.1 (𝓞 D.host.E ∙ (γ : Matrix (Fin N) (Fin N) D.host.E).det) _ (hU ⟨_, hd⟩)
    (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N _ L hN (sd0 N) hL)
  have c2 := hχ.1 (𝓞 D.host.E ∙ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) _ (hU ⟨_, hd'⟩)
    (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N' _ L' hN' (sd0 N') hL')
  have u1 : χ (𝓞 D.host.E ∙ (γ : Matrix (Fin N) (Fin N) D.host.E).det) =
      ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det)⁻¹ := hχ.2 ⟨_, hd⟩
  have u2 : χ (𝓞 D.host.E ∙ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) =
      ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det)⁻¹ := hχ.2 ⟨_, hd'⟩
  have s1 : ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det) =
      ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det)⁻¹ :=
    Finset.prod_congr rfl fun τ _ => emb_star_unit τ _ hd.2
  simp only [Cd.Base.chiFac]
  rw [e1, e2, c1, c2, u1, u2, s1, Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  exact inv_mul_zpow_mul_inv_mul_zpow_neg _ _ _ _ _ _

end Chi

section Pull

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem pull_smul (T : TaylorLogMetric.Tor D) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D T γ γ' (c • G) = c • TaylorLogMetric.pull D T γ γ' G := rfl

theorem pull_comp {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ γ' G =
      TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ 1 (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) 1 γ' G) := by
  funext z
  simp only [TaylorLogMetric.pull, TaylorLogMetric.tor0]
  congr 1
  funext τ
  simp [Matrix.map_one, Matrix.mul_assoc]
  rfl

end Pull

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
end
end

section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Matrix
open Formalism.L2.Ker.Cd.IntegralLatticeDensity

variable (D : Car)

theorem detId_eq_vol {N : ℕ} {L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L) :
    TaylorLogMetric.detId D L L' = DN.vol D L' * CU.cS D (DN.vol D L) := by
  refine le_antisymm ?_ (DN.vol_mul_cS_le D L L' (DN.sd_int D hL))
  have hu : DN.vol D L * CU.cS D (DN.vol D L) = 1 :=
    le_antisymm (DN.vol_mul_cS_le_one D L (DN.sd_int D hL)) (DN.unitDisc D N L hL)
  calc TaylorLogMetric.detId D L L' = TaylorLogMetric.detId D L L' * (DN.vol D L * CU.cS D (DN.vol D L)) := by
        rw [hu, mul_one]
    _ = TaylorLogMetric.detId D L L' * DN.vol D L * CU.cS D (DN.vol D L) := (mul_assoc _ _ _).symm
    _ ≤ DN.vol D L' * CU.cS D (DN.vol D L) := by
        have h := DN.detId_mul_vol_le D L L'
        rw [Submodule.mul_le]
        intro m hm n hn
        exact Submodule.mul_mem_mul (h hm) hn

theorem vol_unit {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L) :
    DN.vol D L * CU.cS D (DN.vol D L) = 1 := by
  exact le_antisymm (DN.vol_mul_cS_le_one D L (DN.sd_int D hL)) (DN.unitDisc D N L hL)

theorem detMul : DetMul D := by
  intro N L L' L'' _ hL hL' hL''
  rw [detId_eq_vol D hL, detId_eq_vol D hL, detId_eq_vol D hL']
  calc DN.vol D L'' * CU.cS D (DN.vol D L)
      = DN.vol D L'' * CU.cS D (DN.vol D L) * (DN.vol D L' * CU.cS D (DN.vol D L')) := by
        rw [vol_unit D hL', mul_one]
    _ = DN.vol D L' * CU.cS D (DN.vol D L) * (DN.vol D L'' * CU.cS D (DN.vol D L')) := by ring

theorem norm_one_unit_ideal : NormOneUnitIdeal D := by
  intro z
  refine ⟨CU.cS D (Submodule.span (𝓞 D.host.E) {(z : D.host.E)}), fun x => Iff.rfl, ?_⟩
  rw [CU.cS_span, Submodule.span_mul_span, Set.singleton_mul_singleton, Submodule.one_eq_span]
  congr 2
  rw [← Formalism.BasicNotions.Examples₂.star_eq_conj D.host (z : D.host.E)]
  exact z.2.2

private theorem smulLat_mem_lemma {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (γ γ' : Matrix (Fin N) (Fin N) D.host.E) (h1 : γ' * γ = 1) (h2 : γ * γ' = 1) (z : Fin N → D.host.E) :
    z ∈ SDLat.smulLat γ L ↔ γ' *ᵥ z ∈ L := by
  unfold SDLat.smulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    show γ' *ᵥ (γ *ᵥ v) ∈ L
    rwa [mulVec_mulVec, h1, one_mulVec]
  · intro h
    refine ⟨γ' *ᵥ z, h, ?_⟩
    show γ *ᵥ (γ' *ᵥ z) = z
    rw [mulVec_mulVec, h2, one_mulVec]

theorem detSmul : DetSmul D := by
  intro N L₀ L γ _ hL₀ hL
  letI := D.host.cmStar
  have hγ : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1 := γ.2.1
  have hγ' : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 := γ.2.2
  rw [detId_eq_vol D hL₀, detId_eq_vol D hL₀, ← mul_assoc]
  congr 1
  unfold DN.vol
  rw [Submodule.span_mul_span]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_mul, Set.mem_singleton_iff]
  constructor
  · rintro ⟨U', hU', rfl⟩
    refine ⟨_, rfl, (star (γ : Matrix (Fin N) (Fin N) D.host.E) * U').det, ⟨star (γ : Matrix (Fin N) (Fin N) D.host.E) * U', fun j => ?_, rfl⟩, ?_⟩
    · exact (smulLat_mem_lemma D L _ _ hγ hγ' _).mp (hU' j)
    · rw [← det_mul, ← mul_assoc, hγ', one_mul]
  · rintro ⟨_, rfl, _, ⟨U, hU, rfl⟩, rfl⟩
    refine ⟨(γ : Matrix (Fin N) (Fin N) D.host.E) * U, fun j => ?_, (det_mul _ _).symm⟩
    rw [smulLat_mem_lemma D L _ _ hγ hγ']
    show star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ ((γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ fun i => U i j) ∈ L
    rw [mulVec_mulVec, hγ, one_mulVec]
    exact hU j

theorem stdH_unitary {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (hu' : (letI := D.host.cmStar; star γ * γ) = 1) (a b : Fin N → D.host.E) :
    (letI := D.host.cmStar; stdH D.host.E N (γ *ᵥ a) (γ *ᵥ b)) = (letI := D.host.cmStar; stdH D.host.E N a b) := by
  letI := D.host.cmStar
  show dotProduct (star (γ *ᵥ a)) (γ *ᵥ b) = dotProduct (star a) b
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← star_eq_conjTranspose, hu', vecMul_one]

theorem smulSD : SmulSD D := by
  intro N L γ hL
  letI := D.host.cmStar
  have hγ : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1 := γ.2.1
  have hγ' : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 := γ.2.2
  have hin : ∀ v ∈ L, (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ v ∈ SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L := fun v hv => by
    rw [smulLat_mem_lemma D L _ _ hγ hγ', mulVec_mulVec, hγ, one_mulVec]
    exact hv
  have hex : ∀ x ∈ SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L, ∃ v ∈ L, (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ v = x := fun x hx =>
    ⟨_, (smulLat_mem_lemma D L _ _ hγ hγ' x).mp hx, by rw [mulVec_mulVec, hγ', one_mulVec]⟩
  unfold SD Formalism.BasicNotions.IsSDLat at hL
  obtain ⟨hfg, hspan, hdual⟩ := hL
  unfold SD Formalism.BasicNotions.IsSDLat
  refine ⟨?_, ?_, ?_⟩
  · unfold SDLat.smulLat
    exact hfg.map _
  · unfold SDLat.smulLat
    rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hspan, Submodule.map_top,
      LinearMap.range_eq_top]
    intro y
    refine ⟨star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ y, ?_⟩
    rw [Matrix.toLin'_apply, mulVec_mulVec, hγ', one_mulVec]
  · intro y

    have key : ∀ v, stdH D.host.E N ((γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ v) y = stdH D.host.E N v (star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ y) := by
      intro v
      have hy : y = (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ (star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ y) := by rw [mulVec_mulVec, hγ', one_mulVec]
      conv_lhs => rw [hy]
      exact stdH_unitary D (γ : Matrix (Fin N) (Fin N) D.host.E) hγ v _
    rw [smulLat_mem_lemma D L _ _ hγ hγ', hdual]
    constructor
    · intro h x hx
      obtain ⟨v, hv, rfl⟩ := hex x hx
      rw [key v]
      exact h v hv
    · intro h v hv
      rw [← key v]
      exact h _ (hin v hv)

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
end
end
