module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle016
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle019
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ZOfSurjBdd
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DetSecondCayleyBlockNe
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle018
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle008
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle009
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle011
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle010
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle003

@[expose] public section

section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.HolTPf

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

abbrev EE (n : ℕ) := Fin n → Fin n → ℂ

theorem herm_re (v : EE n) : (Matrix.of ((1 / 2 : ℂ) • (v + fun i j => star (v j i)))).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.of_apply]
  ring

theorem herm_im (v : EE n) :
    (Matrix.of ((1 / (2 * Complex.I) : ℂ) • (v - fun i j => star (v j i)))).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.of_apply]
  field_simp
  ring

theorem split_re_im (v : EE n) :
    v = (1 / 2 : ℂ) • (v + fun i j => star (v j i)) + Complex.I • ((1 / (2 * Complex.I) : ℂ) • (v - fun i j => star (v j i))) := by
  funext i j
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

private theorem herm_Hpk_smul_left (k : EE n) (hk : (Matrix.of k).IsHermitian) (t : ℝ) :
    (Matrix.of ((t : ℂ) • k)).IsHermitian := by
  ext i j
  have h2 := congrFun (congrFun hk i) j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply] at h2 ⊢
  simp [h2]

theorem const_of_transl (G : EE n → ℂ) (hG : DifferentiableOn ℂ G (Dom n))
    (hT : ∀ W ∈ Dom n, ∀ k : EE n, (Matrix.of k).IsHermitian → G (W + k) = G W) :
    ∀ W ∈ Dom n, ∀ W' ∈ Dom n, G W = G W' := by
  have key : ∀ W ∈ Dom n, fderiv ℂ G W = 0 := by
    intro W hW
    have hGd : HasFDerivAt G (fderiv ℂ G W) W :=
      ((hG W hW).differentiableAt (isOpen_dom'.mem_nhds hW)).hasFDerivAt
    have hk0 : ∀ k : EE n, (Matrix.of k).IsHermitian → fderiv ℂ G W k = 0 := by
      intro k hk
      have hc : HasDerivAt (fun t : ℝ => W + (t : ℂ) • k) k 0 := by
        have h1 := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.smul_const k).const_add W
        simpa using h1
      have hcomp := (hGd.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
      have hfun : (G ∘ fun t : ℝ => W + (t : ℂ) • k) = fun _ => G W := by
        funext t
        exact hT W hW _ (herm_Hpk_smul_left k hk t)
      rw [hfun] at hcomp
      simpa using hcomp.unique (hasDerivAt_const _ _)
    refine ContinuousLinearMap.ext fun v => ?_
    calc fderiv ℂ G W v = fderiv ℂ G W ((1 / 2 : ℂ) • (v + fun i j => star (v j i)) +
          Complex.I • ((1 / (2 * Complex.I) : ℂ) • (v - fun i j => star (v j i)))) := by
          rw [← split_re_im v]
      _ = 0 := by
          rw [map_add (f := _), hk0 _ (herm_re v), map_smul, hk0 _ (herm_im v)]
          simp
  intro W hW W' hW'
  exact convex_dom'.is_const_of_fderivWithin_eq_zero hG
    (fun x hx => by rw [fderivWithin_of_isOpen isOpen_dom' hx]; exact key x hx) hW hW'

private theorem exp_trace_mul_H_const_on_dom (H : EE n → ℂ) (hH : DifferentiableOn ℂ H (Dom n))
    (β : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (hc : c * c = 1) (hcs : star c = c)
    (hT : ∀ W ∈ Dom n, ∀ h : EE n, (Matrix.of h).IsHermitian →
      H (W + c • h) = Complex.exp (Complex.I * (β * Matrix.of h).trace) * H W) :
    ∀ W ∈ Dom n, ∀ W' ∈ Dom n,
      Complex.exp (-(c * Complex.I * (β * Matrix.of W).trace)) * H W =
        Complex.exp (-(c * Complex.I * (β * Matrix.of W').trace)) * H W' := by
  apply const_of_transl (fun W => Complex.exp (-(c * Complex.I * (β * Matrix.of W).trace)) * H W)
  · refine DifferentiableOn.mul ?_ hH
    apply Differentiable.differentiableOn
    have hl : Differentiable ℂ (fun W : EE n => (β * Matrix.of W).trace) := by
      simp only [Matrix.trace, Matrix.mul_apply, Matrix.of_apply, Matrix.diag]
      fun_prop
    fun_prop
  · intro W hW k hk
    have hof : Matrix.of (c • k) = c • Matrix.of k := rfl
    have hh : (Matrix.of (c • k)).IsHermitian := by
      rw [hof, Matrix.IsHermitian, Matrix.conjTranspose_smul, hcs, hk.eq]
    have hWk : W + k = W + c • (c • k) := by
      ext i j
      simp [smul_smul, hc]
    have htr : (β * Matrix.of (W + k)).trace = (β * Matrix.of W).trace + (β * Matrix.of k).trace := by
      rw [← Matrix.of_add_of, Matrix.mul_add, Matrix.trace_add]
    have htr2 : (β * Matrix.of (c • k)).trace = c * (β * Matrix.of k).trace := by
      rw [hof, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hHk : H (W + k) = Complex.exp (Complex.I * (c * (β * Matrix.of k).trace)) * H W := by
      rw [hWk, hT W hW _ hh, htr2]
    try dsimp only
    rw [hHk, htr, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring

theorem holomorphic_translation_levi : ∀ (n p q : ℕ) (e : ℤ) (φ : GR n → ℂ), IsHolW p q e φ → ∀ β : Matrix (Fin n) (Fin n) ℂ,
    (∀ (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), h.IsHermitian → mR x = nU h →
      φ (x * y) = Complex.exp (Complex.I * (β * h).trace) * φ y) →
    ∀ (a a' : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), mR x = Matrix.fromBlocks a 0 0 a' → aᴴ * β * a = β →
      φ (x * y) = F0 p q e x * φ y := by
  intro n p q e φ hφ β hβ a a' x y hx ha
  obtain ⟨H, hH, hφH⟩ := hφ
  obtain ⟨Z, hZ⟩ : ∃ Z : GR n → Matrix (Fin n) (Fin n) ℂ,
      ∀ y, Z y = if q = 0 then zOf y else -(zOf y)ᴴ := ⟨_, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = if q = 0 then 1 else -1 := ⟨_, rfl⟩
  have hφ' : ∀ y, φ y = F0 p q e y * H (Z y) := fun y => by rw [hZ]; exact hφH y
  have hdom : ∀ y : GR n, Z y ∈ Dom n := by
    intro y
    rw [hZ]
    split_ifs
    · exact zOf_mem' y
    · exact neg_conj_mem' (zOf_mem' y)
  have hsurj : ∀ W ∈ Dom n, ∃ y : GR n, Z y = W := by
    intro W hW
    simp only [hZ]
    split_ifs
    · exact zOf_surj' hW
    · obtain ⟨y, hy⟩ := zOf_surj' (neg_conj_mem' hW)
      refine ⟨y, ?_⟩
      rw [hy]
      simp only [Matrix.conjTranspose_neg, neg_neg, Matrix.conjTranspose_conjTranspose]
      rfl
  have hnU : ∀ (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), h.IsHermitian → mR x = nU h →
      Z (x * y) = Z y + c • h := by
    intro h x y hh hx
    rw [hZ, hZ, hc, zOf_nU' h x y hx]
    split_ifs
    · simp
    · rw [Matrix.conjTranspose_add, hh.eq]
      simp
      abel
  have hlevi : ∀ y : GR n, Z (x * y) = a * Z y * aᴴ := by
    intro y
    rw [hZ, hZ, zOf_levi' a a' x y hx]
    split_ifs
    · rfl
    · simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hT : ∀ W ∈ Dom n, ∀ h : EE n, (Matrix.of h).IsHermitian →
      H (W + c • h) = Complex.exp (Complex.I * (β * Matrix.of h).trace) * H W := by
    intro W hW h hh
    obtain ⟨y0, hy0⟩ := hsurj W hW
    obtain ⟨x0, hx0⟩ := nU_mem' hh
    have h1 := hβ _ x0 y0 hh hx0
    rw [hφ', hφ', spherical_section_unipotent_invariant p q e _ x0 y0 hx0, hnU _ x0 y0 hh hx0] at h1
    have e0 : (W + c • h : EE n) = Z y0 + c • Matrix.of h := by
      rw [hy0]
      rfl
    rw [e0]
    apply mul_left_cancel₀ (spherical_section_ne_zero_group p q e y0)
    rw [h1, hy0]
    ring
  have hc2 : c * c = 1 := by
    rw [hc]
    split_ifs <;> norm_num
  have hcs : star c = c := by
    rw [hc]
    split_ifs <;> simp
  have hconst := exp_trace_mul_H_const_on_dom H hH β c hc2 hcs hT
  have htr : (β * (a * Z y * aᴴ)).trace = (β * Z y).trace := by
    rw [show β * (a * Z y * aᴴ) = (β * a * Z y) * aᴴ by simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm,
      show aᴴ * (β * a * Z y) = (aᴴ * β * a) * Z y by simp [Matrix.mul_assoc], ha]
  have hHeq : H (a * Z y * aᴴ) = H (Z y) := by
    have h1 := hconst _ (hlevi y ▸ hdom (x * y)) _ (hdom y)
    have htr' : (β * Matrix.of (a * Z y * aᴴ)).trace = (β * Matrix.of (Z y)).trace := htr
    rw [htr'] at h1
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) h1
  rw [hφ' (x * y), hφ' y, spherical_section_levi_mul p q e a a' x y hx, hlevi y, hHeq]
  ring

end PositivityTheory.Rg.Sw.HSt.HolTPf
end
end

section

namespace PositivityTheory.Rg.Sw.HSt

theorem locTau : LocTau := asmLT lt1 lt2 lt3 crux

end PositivityTheory.Rg.Sw.HSt
end

section

noncomputable section

open Matrix Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.SiegelWeilFormula

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def toC (L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ) (hL : ∀ v, L (Complex.I • v) = Complex.I * L v) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ where
  toFun := L
  map_add' := L.map_add
  map_smul' c v := by
    have hv : c • v = (c.re : ℝ) • v + (c.im : ℝ) • (Complex.I • v) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
      conv_lhs => rw [← Complex.re_add_im c]
      ring
    rw [hv, map_add L, L.map_smul, L.map_smul, hL, RingHom.id_apply, smul_eq_mul]
    simp only [Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im c]
    ring
  cont := L.cont

theorem cauchy_riemann_derivative_eq (A : M2 n) (Φ : M2 n → ℂ) (x : M2 n) (d1 d2 : ℂ)
    (h1 : HasDerivAt (fun t : ℝ => Φ (x * II.cE (Z1 A) t)) d1 0)
    (h2 : HasDerivAt (fun t : ℝ => Φ (x * II.cE (Z2 A) t)) d2 0) : rC A Φ x = d1 + Complex.I * d2 := by
  have key : ∀ E : M2 n, (fun t : ℝ => Φ (x * NormedSpace.exp ((t : ℂ) • E))) = fun t : ℝ => Φ (x * II.cE E t) := by
    intro E; funext t; simp only [II.cE, Complex.coe_smul]
  change deriv (fun t : ℝ => Φ (x * NormedSpace.exp ((t : ℂ) • Z1 A))) 0 +
    Complex.I * deriv (fun t : ℝ => Φ (x * NormedSpace.exp ((t : ℂ) • Z2 A))) 0 = _
  rw [key, key, h1.deriv, h2.deriv]

theorem crLem_of (hsec : LocSec) (hfib : Fib) (ha : CauchyRiemannFacts) : CRLem := by
  intro n m e φ Φ Ω hΩ hGΩ hΦ hΦφ hlaw hrC
  classical
  have hF0 : ∀ y : GR n, F0 m 0 e y ≠ 0 := by
    intro y
    rw [ha.1]
    unfold holomorphicScalarSection
    exact mul_ne_zero (zpow_ne_zero _ (det_ne_zero_of_inG y.2)) (zpow_ne_zero _ (AbsSt.detU1 n y).1)
  set H : Matrix (Fin n) (Fin n) ℂ → ℂ := fun Z =>
    if h : ∃ y : GR n, zOfE (mR y) = Z then φ h.choose / F0 m 0 e h.choose else 0 with hHdef
  have hH : ∀ y : GR n, φ y = F0 m 0 e y * H (zOfE (mR y)) := by
    intro y
    have hex : ∃ y' : GR n, zOfE (mR y') = zOfE (mR y) := ⟨y, rfl⟩
    simp only [hHdef, dif_pos hex]
    have hz : zOfE (mR hex.choose) = zOfE (mR y) := hex.choose_spec
    have hk := hfib n hex.choose y hz
    have hkK : (hex.choose⁻¹ * y) ∈ AbsSt.KR n := hk
    have e1 : y = hex.choose * (hex.choose⁻¹ * y) := by group
    have h1 : φ y = φ hex.choose * F0 m 0 e (hex.choose⁻¹ * y) := by
      conv_lhs => rw [e1]
      exact hlaw _ _ hk
    have h2 : F0 m 0 e y = F0 m 0 e hex.choose * F0 m 0 e (hex.choose⁻¹ * y) := by
      conv_lhs => rw [e1]
      exact ((AbsSt.mult n m 0 e).1 _ _ hkK).1
    rw [h1, h2]
    field_simp [hF0 hex.choose]
  refine ⟨fun Z => H (Matrix.of Z), ?_, fun y => ?_⟩
  swap
  · simp only [↓reduceIte]
    exact hH y
  intro Z0' hZ0
  set Z0 : Matrix (Fin n) (Fin n) ℂ := Matrix.of Z0' with hZ0def
  obtain ⟨s, hs, hsd⟩ := hsec n Z0 hZ0
  obtain ⟨hxG, hxd, hxz⟩ := hs.self_of_nhds
  set x0 := s Z0 with hx0
  set y0 := toGR x0 hxG with hy0
  have hu1 : (u1 x0).det ≠ 0 := (AbsSt.detU1 n y0).1
  obtain ⟨hzd, hFd, hlow, hsig, hW⟩ := ha.2 n x0 hxd hu1
  have hFx0 : holomorphicScalarSection m e x0 ≠ 0 := by
    have := hF0 y0
    rwa [ha.1] at this
  have heq : H =ᶠ[𝓝 Z0] fun Z => Φ (s Z) * (holomorphicScalarSection m e (s Z))⁻¹ := by
    filter_upwards [hs] with Z hZ
    obtain ⟨hG, -, hzZ⟩ := hZ
    have h1 := hH (toGR (s Z) hG)
    rw [mR_toGR, hzZ, ← hΦφ (toGR (s Z) hG), mR_toGR] at h1
    have h2 : F0 m 0 e (toGR (s Z) hG) = holomorphicScalarSection m e (s Z) := by rw [ha.1, mR_toGR]
    have h4 : holomorphicScalarSection m e (s Z) ≠ 0 := by rw [← h2]; exact hF0 _
    rw [← div_eq_mul_inv, eq_div_iff h4, mul_comm, ← h2, ← h1]
  have hΦd : DifferentiableAt ℝ Φ x0 :=
    (hΦ.contDiffAt (hΩ.mem_nhds (hGΩ hxG))).differentiableAt (by simp)
  have hsd' : DifferentiableAt ℝ s Z0 := hsd.differentiableAt one_ne_zero
  have hFr : DifferentiableAt ℝ (holomorphicScalarSection m e) x0 := (hFd m e).restrictScalars ℝ
  have hzr : DifferentiableAt ℝ zOfE x0 := hzd.restrictScalars ℝ
  have hR : DifferentiableAt ℝ (fun Z => Φ (s Z) * (holomorphicScalarSection m e (s Z))⁻¹) Z0 :=
    (hΦd.comp Z0 hsd').mul ((hFr.comp Z0 hsd').inv hFx0)
  have hHd : DifferentiableAt ℝ H Z0 := hR.congr_of_eventuallyEq heq
  set L := fderiv ℝ H Z0 with hLdef
  have hHd' : DifferentiableAt ℝ H (zOfE x0) := by rw [hxz]; exact hHd

  have key : ∀ Q : Matrix (Fin n) (Fin n) ℂ,
      L (Complex.I • (fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)))) =
        Complex.I * L (fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q))) := by
    intro Q
    set g : M2 n → ℂ := fun x => holomorphicScalarSection m e x * H (zOfE x) with hg
    have hcurve : ∀ E : M2 n, sig E = E → ∀ t : ℝ, Φ (x0 * II.cE E t) = g (x0 * II.cE E t) := by
      intro E hE t
      have hp : InG (x0 * II.cE E t) := inG_mul hxG (inG_cE hE t)
      have := hH (toGR _ hp)
      rw [mR_toGR, ha.1, mR_toGR] at this
      rw [← hΦφ (toGR _ hp), mR_toGR] at this
      exact this
    have hr : rC (lowQ Q) Φ x0 = 0 := hrC y0 Q
    have hder : ∀ E : M2 n, sig E = E → HasDerivAt (fun t : ℝ => Φ (x0 * II.cE E t))
        (fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * E) * H Z0 + holomorphicScalarSection m e x0 * L (fderiv ℂ zOfE x0 (x0 * E))) 0 := by
      intro E hE
      have hc : HasDerivAt (fun t : ℝ => x0 * II.cE E t) (x0 * E) 0 :=
        (II.mulL x0).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (II.cE_hasDerivAt0 E)
      have hc0 : x0 * II.cE E 0 = x0 := by rw [II.cE_zero, Matrix.mul_one]
      have hFc : HasDerivAt (fun t : ℝ => holomorphicScalarSection m e (x0 * II.cE E t)) (fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * E)) 0 := by
        have h : HasFDerivAt (holomorphicScalarSection m e) ((fderiv ℂ (holomorphicScalarSection m e) x0).restrictScalars ℝ) (x0 * II.cE E 0) := by
          rw [hc0]; exact (hFd m e).hasFDerivAt.restrictScalars ℝ
        exact h.comp_hasDerivAt (0 : ℝ) hc
      have hzc : HasDerivAt (fun t : ℝ => zOfE (x0 * II.cE E t)) (fderiv ℂ zOfE x0 (x0 * E)) 0 := by
        have h : HasFDerivAt zOfE ((fderiv ℂ zOfE x0).restrictScalars ℝ) (x0 * II.cE E 0) := by
          rw [hc0]; exact hzd.hasFDerivAt.restrictScalars ℝ
        exact h.comp_hasDerivAt (0 : ℝ) hc
      have hHc : HasDerivAt (fun t : ℝ => H (zOfE (x0 * II.cE E t))) (L (fderiv ℂ zOfE x0 (x0 * E))) 0 := by
        have h : HasFDerivAt H L (zOfE (x0 * II.cE E 0)) := by
          rw [hc0, hxz]; exact hHd.hasFDerivAt
        exact h.comp_hasDerivAt (0 : ℝ) hzc
      have hprod := hFc.mul hHc
      rw [hc0, hxz] at hprod
      refine hprod.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
      exact hcurve E hE t
    rw [cauchy_riemann_derivative_eq (lowQ Q) Φ x0 _ _ (hder _ (conj_real_part_fixed _)) (hder _ (conj_imaginary_part_fixed _))] at hr
    have hsum : ∀ (D : M2 n →L[ℂ] Matrix (Fin n) (Fin n) ℂ), D (x0 * Z1 (lowQ Q)) + Complex.I • D (x0 * Z2 (lowQ Q)) =
        D (x0 * lowQ Q) := by
      intro D
      rw [← D.map_smul, ← map_add D, ← Matrix.mul_smul, ← Matrix.mul_add, real_add_imaginary_part]
    have hsum' : ∀ (D : M2 n →L[ℂ] ℂ), D (x0 * Z1 (lowQ Q)) + Complex.I * D (x0 * Z2 (lowQ Q)) =
        D (x0 * lowQ Q) := by
      intro D
      rw [← smul_eq_mul Complex.I (D _), ← D.map_smul, ← map_add D, ← Matrix.mul_smul, ← Matrix.mul_add, real_add_imaginary_part]
    have hsumF : fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * Z1 (lowQ Q)) + Complex.I * fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * Z2 (lowQ Q)) =
        0 := (hsum' _).trans ((hlow Q).2 m e)
    have hsumZ := hsum (fderiv ℂ zOfE x0)
    rw [(hlow Q).1] at hsumZ
    have hv1 : fderiv ℂ zOfE x0 (x0 * Z1 (lowQ Q)) = -(Complex.I • fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q))) :=
      eq_neg_of_add_eq_zero_left hsumZ
    rw [hv1, map_neg] at hr
    have hr2 : holomorphicScalarSection m e x0 * (-L (Complex.I • fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q))) +
        Complex.I * L (fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)))) = 0 := by
      rw [← hr]
      linear_combination (-(H Z0)) * hsumF
    rcases mul_eq_zero.1 hr2 with h | h
    · exact absurd h hFx0
    · linear_combination -h

  have hsurj : ∀ v : Matrix (Fin n) (Fin n) ℂ, ∃ Q, fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)) = v := by
    intro v
    have hWu : IsUnit (WM x0).det := isUnit_iff_ne_zero.2 (hW hxG)
    have hUu : IsUnit (u1 x0).det := isUnit_iff_ne_zero.2 hu1
    refine ⟨((-(2 * Complex.I)) • ((WM x0)⁻¹ * v * u1 x0))ᴴ, ?_⟩
    rw [Z2, Matrix.mul_smul, map_smul, Matrix.mul_sub, map_sub, (hlow _).1, hsig, Matrix.conjTranspose_conjTranspose,
      zero_sub]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_neg, smul_smul]
    have : WM x0 * ((WM x0)⁻¹ * v * u1 x0) * (u1 x0)⁻¹ = v := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hWu, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hUu, Matrix.mul_one]
    rw [this]
    ext i j
    simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
    field_simp
  have hLC : ∀ v, L (Complex.I • v) = Complex.I * L v := by
    intro v
    obtain ⟨Q, hQ⟩ := hsurj v
    have := key Q
    rw [hQ] at this
    exact this
  have hC : HasFDerivAt H (toC L hLC) Z0 :=
    hasFDerivAt_of_restrictScalars ℝ hHd.hasFDerivAt (by ext; rfl)
  have hC' : DifferentiableAt ℂ H Z0 := hC.differentiableAt
  exact (hC'.comp Z0' (Matrix.ofLinearEquiv ℂ).toContinuousLinearEquiv.differentiableAt).differentiableWithinAt

end PositivityTheory.Rg.Sw.HSt.CR
end
end
