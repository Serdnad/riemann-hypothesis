module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle005
public import Formalism.SharpRestriction.CuspSpanNormBounds.AdmissibleBoundsFromSource
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle012
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle014
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle015
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle010

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.S

open Formalism.BasicNotions Formalism.MainNotions MeasureTheory

namespace AutInst

variable (I : AutInst)


open Classical in
def IsLevelCharIdem (μf : Measure I.Gf) (g₀ : ℕ) (e : I.Gf → ℂ) : Prop :=
  ∃ (K'' : Subgroup I.Gf) (χ : I.Gf → ℂ), IsOpen (K'' : Set I.Gf) ∧ IsCompact (K'' : Set I.Gf) ∧
    (K'' : Set I.Gf) ⊆ I.Kset ∧ (∀ k ∈ K'', I.UnipMod g₀ k) ∧
    (∀ k ∈ K'', ∀ k' ∈ K'', χ (k * k') = χ k * χ k') ∧ (∀ k ∈ K'', ‖χ k‖ = 1) ∧
    ∀ x, e x = if x ∈ K'' then (χ x)⁻¹ / ((μf (K'' : Set I.Gf)).toReal : ℂ) else 0

end AutInst

namespace CountE

open Formalism.MainNotions.PlaceDegreeData NumberField

variable (P : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop)

def CountIdempotentsClass (_D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ),
    HidaSetting I n₀ A b lam μf g g₀ e → P I μf g₀ e → CountData I lam σ w σs tens μf fund R e Re →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) →
    C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h →
    Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) →
    Real.log (Real.log b) ≤ cb * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) →
    |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (fdegAll I σ w) μf fund e| ≤
      Real.exp (-c * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (fdegAll I σ w) μf fund e

def RowsTieP (D : Formalism.BasicNotions.D7) (X : RowsAut) : Prop := RowsTie D X ∧ P X.I X.μf X.g₀ X.e

def CountRowsClass (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  ∀ (X : RowsAut) (b h : ℝ), RowsTieP P D X → HidaSetting X.I n₀ A b X.lam X.μf X.g X.g₀ X.e →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (X.I.ε v) (X.lam v) h) →
    C * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * Real.log (b * D.host.rdE) ≤ h →
    Real.log (D.R.f : ℝ) ≤ Real.sqrt (D.R.r : ℝ) →
    Real.log (Real.log b) ≤ cb * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ) →
    |(D.what₂.Dall : ℝ) - D.what₂.Dstar| ≤
      Real.exp (-(c * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ))) * D.what₂.Dstar

def CountAllPointsClass {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  0 < c ∧ 0 < cb ∧ ∀ x (i : Fm.Ix x), CountIdempotentsClass P (Fm.D x i) n₀ A C c cb

def CountRowsClassFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  0 < c ∧ 0 < cb ∧ ∀ x (i : Fm.Ix x), CountRowsClass P (Fm.D x i) n₀ A C c cb

theorem count_class_of_count {D : Formalism.BasicNotions.D7} {n₀ : ℕ} {A C c cb : ℝ} (h : PointsLemma D n₀ A C c cb) : CountIdempotentsClass P D n₀ A C c cb := by
  intro I b lam g g₀ e H _ _ _ σ w Hs _ _ _ σs tens μf _ fund R Re h' hS _ hc hg h1 h2 h3
  exact h I b lam g g₀ e H σ w Hs σs tens μf fund R Re h' hS hc hg h1 h2 h3

section Count

open Finset

variable {D : D7}

theorem admissibility_ten_of_rows_class (large₂ : SizeData₂ D) (X : RowsAut) (hX : RowsTieP P D X) (n0 : ℕ) (A C cb c : ℝ)
    (h : CountRowsClass P D n0 A C c cb) : AdmissibleBoundsFromSource.adm10 D large₂ n0 A C cb c := by
  intro hp
  obtain ⟨-, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := hp
  have hX' := hX.1
  obtain ⟨⟨pl, T⟩, t5, tsp⟩ := hX'
  have hn := T.n_eq
  have trd := T.rd_eq
  have tg0 := T.g0_eq
  have tg := T.g_eq
  have hq : ∀ v, X.I.pAt v = (univ.filter fun a : Fin D.R.r => epsS D.R a = true).card ∧
      X.I.qAt v = (univ.filter fun a : Fin D.R.r => epsS D.R a = false).card := by
    intro v
    have he := T.eps_eq v
    constructor
    · simp only [AutInst.pAt, he]
      exact card_cast hn (fun a => epsS D.R a = true)
    · simp only [AutInst.qAt, he]
      exact card_cast hn (fun a => epsS D.R a = false)
  have hS : PlaceDegreeData.HidaSetting X.I n0 A large₂.sc.b X.lam X.μf X.g X.g₀ X.e := by
    refine ⟨by rw [hn]; exact p2, ⟨_, _, hq, ?_⟩, p11, ?_, t5, ?_, X.e_adm, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hn]
      exact le_trans (Nat.pow_le_pow_left card_epsS_false 2) p3
    · rw [trd, hn]; exact p4
    · intro v a
      rw [T.lam_eq v a]; exact p5 _ _
    · rw [tg]
      exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
    · rw [tg]
      have : gg D = ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by unfold gg; push_cast; ring
      rw [← this]; exact p6
    · rw [tg0]; exact D.host.g_prime 0
    · rw [tg0, hn]; exact p7
    · exact tsp p8
  refine h X large₂.sc.b _ hX hS (fun v a c hac => ?_) le_rfl p10 p12
  rw [T.lam_eq v a, T.lam_eq v c]
  exact p9 _ _ _ (by rw [← T.eps_eq v a, ← T.eps_eq v c]; exact hac)

theorem count_rows_class_of_count_class (n₀ : ℕ) (A C c cb : ℝ) (hp : CountIdempotentsClass P D n₀ A C c cb) : CountRowsClass P D n₀ A C c cb := by
  intro X b h hT hS hg h1 h2 h3
  have hPX := hT.2
  obtain ⟨⟨pl, hA⟩, -, -⟩ := hT.1
  have hD := hA.D_eq
  have hDs : X.I.Dstar (PlaceDegreeData.fdegAll X.I X.σ X.w) X.μf X.fund X.e = D.what₂.Dstar := hA.Dstar_eq.symm
  have hf := hA.f_eq
  have hrd := hA.rd_eq
  have hn := hA.n_eq
  have hc : PlaceDegreeData.CountData X.I X.lam X.σ X.w X.σs X.tens X.μf X.fund X.R X.e X.Re :=
    ⟨hA.ds, hA.low, X.tens_spec, X.haar, X.fund_spec, X.R_spec, X.Re_spec⟩
  rw [← hn, ← hf, ← hrd] at h1
  rw [← hn, ← hf] at h2 h3
  have := hp X.I b X.lam X.g X.g₀ X.e X.H X.σ X.w X.Hs X.σs X.tens X.μf X.fund X.R X.Re h hS hPX hc hg h1 h2 h3
  have e1 : (X.I.Dcount X.σs X.μf X.fund X.R X.Re : ℝ) = (D.what₂.Dall : ℝ) := by exact_mod_cast hD
  rw [e1, hDs] at this
  rw [← hn, ← hf]
  convert this using 3
  ring

end Count

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Family

abbrev PLev : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop := fun I μf g₀ e => I.IsLevelCharIdem μf g₀ e

end CountE


open Classical in
def IsCharIdemFin {G : Type} [Group G] (f : MonoidAlgebra ℂ G) : Prop :=
  ∃ (U : Subgroup G) (χ : G → ℂ), (∀ a ∈ U, ∀ b ∈ U, χ (a * b) = χ a * χ b) ∧ (∀ a ∈ U, ‖χ a‖ = 1) ∧
    ∀ a, f.coeff a = if a ∈ U then (χ a)⁻¹ / (Nat.card U : ℂ) else 0

namespace AutInst

variable (I : AutInst)

structure RedDatum (g₁ g₂ : ℕ) : Type 1 where
  G₁ : Type
  G₂ : Type
  [grp₁ : Group G₁]
  [grp₂ : Group G₂]
  [fin₁ : Fintype G₁]
  [fin₂ : Fintype G₂]
  red : I.Gf → G₁ × G₂
  red_mul : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, red (x * y) = red x * red y
  red_surj : ∀ a : G₁ × G₂, ∃ x ∈ I.Kset, red x = a
  red_fib₁ : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, ((red x).1 = (red y).1 ↔ x⁻¹ * y ∈ I.Kg g₁)
  red_fib₂ : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, ((red x).2 = (red y).2 ↔ x⁻¹ * y ∈ I.Kg g₂)

attribute [instance] RedDatum.grp₁ RedDatum.grp₂ RedDatum.fin₁ RedDatum.fin₂


open Classical in
def IsCountIdem (μf : Measure I.Gf) (g₀ : ℕ) (e : I.Gf → ℂ) : Prop :=
  ∃ (a b p : ℕ) (R : I.RedDatum (g₀ ^ a) (p ^ b)) (f₀ : MonoidAlgebra ℂ R.G₁) (z ε₂ : MonoidAlgebra ℂ R.G₂),
    p.Prime ∧ p ≠ g₀ ∧ IsCharIdemFin f₀ ∧ (∀ x ∈ I.Kset, f₀.coeff (R.red x).1 ≠ 0 → I.UnipMod g₀ x) ∧
    IsCharIdemFin ε₂ ∧ z * z = z ∧ (∀ y : MonoidAlgebra ℂ R.G₂, z * y = y * z) ∧
    ∀ x, e x = if x ∈ I.Kset then
      f₀.coeff (R.red x).1 * (z * ε₂).coeff (R.red x).2 / ((μf (I.Kg (g₀ ^ a) ∩ I.Kg (p ^ b))).toReal : ℂ) else 0

end AutInst

namespace CountE

abbrev PCount : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop :=
  fun I μf g₀ e => I.IsLevelCharIdem μf g₀ e ∨ I.IsCountIdem μf g₀ e

end CountE

end Formalism.MainNotions.S
end
end

section

open MeasureTheory Matrix Finset

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def alphaPt {r : ℕ} (κ τ : ℝ) (γ : Point ℂ (r + 1)) : ℝ :=
  κ ^ (rootPat γ).card * ∏ p ∈ rootPat γ, (tF r κ τ p.2.val / tF r κ τ p.1.val) ^ 2

section Alg3

variable {k r : ℕ} {κ τ : ℝ}

theorem Hpk_mul_dMi (hκ : 0 < κ) (hτ : 0 < τ) : Hpk k r * dMi k r κ τ = dM k r κ τ * Hpk k r := by
  ext i j
  rw [dMi, dM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : Hpk k r i j = 0
  · rw [h]; simp
  · have e := tV_mul_of_Hpk hκ hτ i j h
    have : (tV k r κ τ j)⁻¹ = tV k r κ τ i := (eq_inv_of_mul_eq_one_left e).symm
    rw [this]; ring

theorem star_vecMul_dM (v : Fin (2 * r + k + 1) → ℂ) : star v ᵥ* dM k r κ τ = star (dM k r κ τ *ᵥ v) := by
  funext j
  rw [dM, Matrix.vecMul_diagonal, Pi.star_apply, Pi.star_apply, Matrix.mulVec_diagonal, star_mul',
    Complex.star_def, Complex.conj_ofReal, mul_comm]

theorem Zhat_cj (hκ : 0 < κ) (hτ : 0 < τ) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (hz' : inWb k r z') (g : Mx k r) (a b : Fin (r + 1)) :
    _root_.Formalism.QuantumDeterminants.Zhat k r ((τ : ℂ) • z) ((τ : ℂ) • z') (cj k r κ τ g) a b =
      ((tF r κ τ a.val * tF r κ τ b.val : ℝ) : ℂ) * _root_.Formalism.QuantumDeterminants.Zhat k r z z' g a b := by
  unfold _root_.Formalism.QuantumDeterminants.Zhat herm
  rw [cj_mulVec, dM_mulVec_fvec hz' b, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec (M := Hpk k r) (N := dMi k r κ τ), Hpk_mul_dMi hκ hτ, ← Matrix.mulVec_mulVec,
    dotProduct_smul, Matrix.dotProduct_mulVec, star_vecMul_dM, dM_mulVec_fvec hz a, star_smul,
    smul_dotProduct]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  push_cast; ring

theorem bigCell_cj (hκ : 0 < κ) (hτ : 0 < τ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    cj k r κ τ (bigCell k r c μ) = bigCell k r (fun a => ((tF r κ τ a.val ^ 2 : ℝ) : ℂ) * c a) μ := by
  ext i j
  rw [cj_apply]
  unfold bigCell
  by_cases hj : j.val < r
  · rw [dite_eq_left hj, dite_eq_left hj]
    by_cases hi : i = esI k r ⟨j.val, hj⟩
    · rw [if_pos hi, if_pos hi, hi, tV_esI]
      have : tV k r κ τ j = tF r κ τ j.val := by unfold tV; rw [if_pos hj]
      rw [this, inv_inv]; push_cast; ring
    · rw [if_neg hi, if_neg hi, mul_zero]
  · rw [dite_eq_right hj, dite_eq_right hj]
    by_cases hj2 : j.val ≤ r + k
    · rw [dite_eq_left hj2, dite_eq_left hj2]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · rw [dite_eq_left hi, tV_wb i hi.1 hi.2, tV_wb j (by omega) hj2]; simp
      · rw [dite_eq_right hi, mul_zero]
    · rw [dite_eq_right hj2, dite_eq_right hj2]
      by_cases hi : i.val = 2 * r + k - j.val
      · rw [if_pos hi, if_pos hi]
        have hti : tV k r κ τ i = tF r κ τ (2 * r + k - j.val) := by
          unfold tV; rw [if_pos (by omega), hi]
        have htj : tV k r κ τ j = (tF r κ τ (2 * r + k - j.val))⁻¹ := by
          unfold tV; rw [if_neg hj, if_neg hj2]
        have hp := tF_pos (r := r) hκ hτ (2 * r + k - j.val)
        rw [hti, htj]
        simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
        have hpc : ((tF r κ τ (2 * r + k - j.val) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
        push_cast
        rw [mul_inv]
        field_simp
      · rw [if_neg hi, if_neg hi, mul_zero]

theorem flagMat_cj (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (x : Mx k r)
    (i j : Fin (r + 1)) (hi : i.val < r) :
    flagMat k r ((τ : ℂ) • z) (cj k r κ τ x) i j =
      ((tF r κ τ j.val / tF r κ τ i.val : ℝ) : ℂ) * flagMat k r z x i j := by
  unfold flagMat
  rw [dite_eq_left hi, dite_eq_left hi, cj_mulVec, dM_mulVec_fvec hz j, Matrix.mulVec_smul, dMi_mulVec_apply, tV_eI,
    Pi.smul_apply, smul_eq_mul]
  push_cast; ring

theorem rootCoords_cjT (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (γ : Point ℂ (r + 1)) (x : Mt k r) (p : rootPat γ) :
    rootCoords k r ((τ : ℂ) • z) γ (cjT k r κ τ x) p =
      ((tF r κ τ p.1.2.val / tF r κ τ p.1.1.val : ℝ) : ℂ) * rootCoords k r z γ x p := by
  have hp := (Finset.mem_filter.mp p.2).2.1
  have hi : p.1.1.val < r := by
    have h1 : p.1.1.val < p.1.2.val := hp
    have h2 := p.1.2.isLt
    omega
  unfold rootCoords
  rw [of_cjT]
  exact flagMat_cj hκ hτ hz (Matrix.of x) p.1.1 p.1.2 hi

theorem Tz_smul (z : Fin (2 * r + k + 1) → ℂ) (t : ℝ) : Tz k r ((t : ℂ) • z) = t ^ 2 * Tz k r z := by
  unfold Tz herm
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem inWb_bvec_wI (j : Fin (k + 1)) : inWb k r (bvec (wI k r j)) := by
  intro i hi
  have : i ≠ wI k r j := by
    intro e; rw [e] at hi; unfold wI at hi; simp only at hi; omega
  simp [bvec, this]

theorem cj_blockW (hκ : 0 < κ) (hτ : 0 < τ) (h : Matrix (Fin k) (Fin k) ℂ) :
    cj k r κ τ (blockW k r h) = blockW k r h := by
  ext i j
  rw [cj_apply]
  unfold blockW
  by_cases hi : r ≤ i.val ∧ i.val < r + k
  · rw [dite_eq_left hi]
    by_cases hj : r ≤ j.val ∧ j.val < r + k
    · rw [dite_eq_left hj, tV_wb i hi.1 (by omega), tV_wb j hj.1 (by omega)]; simp
    · rw [dite_eq_right hj, mul_zero]
  · rw [dite_eq_right hi]
    by_cases e : i = j
    · rw [if_pos e, cj_fac_diag hκ hτ i j e, one_mul]
    · rw [if_neg e, mul_zero]

theorem isHCTypeW_cjI (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {u : Fin k → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {π : Mx k r → (H →L[ℂ] H)} (h : IsHCTypeW k r z u π) :
    IsHCTypeW k r ((τ : ℂ) • z) u (fun x => π (cjI k r κ τ x)) := by
  obtain ⟨g, ⟨hg1, hg2, hg3⟩, hU⟩ := h
  refine ⟨cj k r κ τ g, ⟨(cj_mem_UH_iff hκ hτ g).mpr hg1, fun a =>
    ⟨(cj_fix_bvec_iff hκ hτ g _).mpr (hg2 a).1, (cj_fix_bvec_iff hκ hτ g _).mpr (hg2 a).2⟩, ?_⟩, ?_⟩
  · rw [Tz_smul, Real.sqrt_mul (sq_nonneg τ), Real.sqrt_sq hτ.le, cj_mulVec, Matrix.mulVec_smul,
      dM_mulVec_wb (inWb_bvec_wI _), Complex.ofReal_mul, ← smul_smul, Matrix.mulVec_smul, hg3,
      Matrix.mulVec_smul, dMi_mulVec_wb hz]
  · have e : (fun h => π (cjI k r κ τ (cj k r κ τ g * blockW k r h * (cj k r κ τ g)⁻¹))) =
        fun h => π (g * blockW k r h * g⁻¹) := by
      funext h
      rw [← cj_inv hκ hτ, ← cj_blockW hκ hτ h, ← cj_mul hκ hτ, ← cj_mul hκ hτ, cjI_cj hκ hτ, cj_blockW hκ hτ]
    simp only at e ⊢
    rw [e]; exact hU

theorem isRelStab_iff (hκ : 0 < κ) (hτ : 0 < τ) (L L₁ : LocBessel k r) (hz : inWb k r L.z) (hz' : inWb k r L.z')
    (e1 : L₁.z = (τ : ℂ) • L.z) (e2 : L₁.z' = (τ : ℂ) • L.z') (e3 : L₁.c = (κ : ℂ) * L.c) (g : Mx k r) :
    IsRelStab L₁ (cj k r κ τ g) ↔ IsRelStab L g := by
  unfold IsRelStab
  rw [e1, e2, e3]
  constructor
  · intro h a ha
    have := h (cj k r κ τ a) ((cj_mem_RStab_iff hκ hτ g a).mpr ha)
    rwa [← cj_inv hκ hτ, ← cj_mul hκ hτ, ← cj_mul hκ hτ, psi_cj hκ hτ hz, psi_cj hκ hτ hz'] at this
  · intro h a₁ ha₁
    have ha : cjI k r κ τ a₁ ∈ RStab k r g := by
      rw [← cj_mem_RStab_iff hκ hτ g, cj_cjI hκ hτ]; exact ha₁
    have := h _ ha
    rw [← cj_cjI hκ hτ a₁, ← cj_inv hκ hτ, ← cj_mul hκ hτ, ← cj_mul hκ hτ, psi_cj hκ hτ hz, psi_cj hκ hτ hz']
    exact this

end Alg3

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

section

noncomputable section

namespace Formalism.MainNotions.PX

section GroupS0

open Formalism.BasicNotions Formalism.MainNotions.S NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Exp (D : D7) : Prop := ∀ u u' : D.what₂.Word, KExpansion D.s u u' ∧ KAbsConv D.s u u'

def GDr (D : D7) (X : TermTie D) : Prop :=
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), D.s.Gterm t ≠ 0 →
    Dl (X.fl t).fl (X.fl' t).fl (D.R.rS + 1) ≠ 0 ∧
    (Dl (X.fl t).fl (X.fl' t).fl D.R.rS ≠ 0 → ∀ τ, 0 < (embS D τ (Lat.Gval (X.fl t) (X.fl' t))).re)

section Family

variable {eps : ℝ} (Fm : FamP eps)

def RanksF (C0 Cg cb Cu cT CT : ℝ) : Prop := LocalBesselAndTopKernel.FamilyRanksHypothesis Fm C0 Cg cb Cu cT CT

end Family

end GroupS0

section GroupS1

open Formalism.MainNotions.S

end GroupS1

section GroupS5

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.UnitaryVolumeMass Formalism.MainNotions.S.Bridge

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def StdHypS (Cg cb Cu cT CT C0 Ch Cβ : ℝ) : Prop :=
  ∀ Cs Cs', OwnEv Fm fun C' Cl x i => StdOfHyp (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ

def TFrame (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
    ∀ w, 1 ≤ Tr (Fm.D x i) w * kaS (Fm.D x i) ^ (2 * (Fm.D x i).R.rS)

end GroupS5

end Formalism.MainNotions.PX

end
end
