module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CloseOfTarget
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.FlagUnipotentLattices.AlgebraicIdentityHigherDegree
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle002
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount

section Comp

variable {E : Type*} [Field E] {K : Type*} [CommRing K] (ψ : E →+* K) {r : ℕ}

def cP (cv : Fin (r + 1) → K) (L₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal cv * L₁.map ψ

def cP' (cv' : Fin (r + 1) → K) (L₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  L₁⁻¹.map ψ * Matrix.diagonal cv'

def cQ (cv : Fin (r + 1) → K) (U₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  U₁.map ψ * Matrix.diagonal cv

def cQ' (cv' : Fin (r + 1) → K) (U₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal cv' * U₁⁻¹.map ψ

theorem diag_one {cv cv' : Fin (r + 1) → K} (h : ∀ a, cv a * cv' a = 1) :
    Matrix.diagonal cv * Matrix.diagonal cv' = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  exact congrArg Matrix.diagonal (funext h)

theorem map_one' : (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E).map ψ = 1 := Matrix.map_one _ ψ.map_zero ψ.map_one

theorem map_inv_mul {L : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : L.det = 1) : L⁻¹.map ψ * L.map ψ = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (by rw [h]; exact isUnit_one), map_one']

theorem map_mul_inv {L : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : L.det = 1) : L.map ψ * L⁻¹.map ψ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (by rw [h]; exact isUnit_one), map_one']

theorem mono_map (σ : Fin (r + 1) → Fin (r + 1)) (ν : Fin (r + 1) → E) :
    (mono σ ν).map ψ = mono σ (fun a => ψ (ν a)) := by
  ext a b
  simp only [Matrix.map_apply, mono, Matrix.of_apply]
  split_ifs <;> simp

theorem inv_eq_map {x : E} (hx : x ≠ 0) : Ring.inverse (ψ x) = ψ x⁻¹ := by
  have h1 : ψ x * ψ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  calc Ring.inverse (ψ x) = Ring.inverse (ψ x) * (ψ x * ψ x⁻¹) := by rw [h1, mul_one]
    _ = ψ x⁻¹ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ ⟨⟨ψ x, ψ x⁻¹, h1, by rw [mul_comm]; exact h1⟩, rfl⟩, one_mul]

theorem hcv'_of {cv cv' : Fin (r + 1) → K} (hcv : ∀ a, cv a * cv' a = 1) : ∀ a, cv' a * cv a = 1 :=
  fun a => by rw [mul_comm]; exact hcv a

variable {cv cv' : Fin (r + 1) → K} (hcv : ∀ a, cv a * cv' a = 1) {L₁ U₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
include hcv hL₁ hU₁

theorem conjPrime_conjPrime₂ : cP ψ cv L₁ * cP' ψ cv' L₁ = 1 := by
  unfold cP cP'
  rw [show Matrix.diagonal cv * L₁.map ψ * (L₁⁻¹.map ψ * Matrix.diagonal cv') =
      Matrix.diagonal cv * (L₁.map ψ * L₁⁻¹.map ψ) * Matrix.diagonal cv' by simp only [Matrix.mul_assoc],
    map_mul_inv ψ (det_lo hL₁), Matrix.mul_one, diag_one hcv]

theorem cP'_cP : cP' ψ cv' L₁ * cP ψ cv L₁ = 1 := by
  unfold cP cP'
  rw [show L₁⁻¹.map ψ * Matrix.diagonal cv' * (Matrix.diagonal cv * L₁.map ψ) =
      L₁⁻¹.map ψ * (Matrix.diagonal cv' * Matrix.diagonal cv) * L₁.map ψ by simp only [Matrix.mul_assoc],
    diag_one (hcv'_of hcv), Matrix.mul_one, map_inv_mul ψ (det_lo hL₁)]

theorem cQ_cQ' : cQ ψ cv U₁ * cQ' ψ cv' U₁ = 1 := by
  unfold cQ cQ'
  rw [show U₁.map ψ * Matrix.diagonal cv * (Matrix.diagonal cv' * U₁⁻¹.map ψ) =
      U₁.map ψ * (Matrix.diagonal cv * Matrix.diagonal cv') * U₁⁻¹.map ψ by simp only [Matrix.mul_assoc],
    diag_one hcv, Matrix.mul_one, map_mul_inv ψ (det_up hU₁)]

theorem cQ'_cQ : cQ' ψ cv' U₁ * cQ ψ cv U₁ = 1 := by
  unfold cQ cQ'
  rw [show Matrix.diagonal cv' * U₁⁻¹.map ψ * (U₁.map ψ * Matrix.diagonal cv) =
      Matrix.diagonal cv' * (U₁⁻¹.map ψ * U₁.map ψ) * Matrix.diagonal cv by simp only [Matrix.mul_assoc],
    map_inv_mul ψ (det_up hU₁), Matrix.mul_one, diag_one (hcv'_of hcv)]

theorem cP_lo {k : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hk : IsLo k) : IsLo (cP' ψ cv' L₁ * k * cP ψ cv L₁) := by
  unfold cP cP'
  rw [show L₁⁻¹.map ψ * Matrix.diagonal cv' * k * (Matrix.diagonal cv * L₁.map ψ) =
      L₁⁻¹.map ψ * (Matrix.diagonal cv' * k * Matrix.diagonal cv) * L₁.map ψ by simp only [Matrix.mul_assoc]]
  exact isLo_mul (isLo_mul (isLo_map ψ (isLo_inv hL₁)) (isLo_conj hk cv' cv (hcv'_of hcv))) (isLo_map ψ hL₁)

theorem cQ_up {k : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hk : IsUp k) : IsUp (cQ ψ cv U₁ * k * cQ' ψ cv' U₁) := by
  unfold cQ cQ'
  rw [show U₁.map ψ * Matrix.diagonal cv * k * (Matrix.diagonal cv' * U₁⁻¹.map ψ) =
      U₁.map ψ * (Matrix.diagonal cv * k * Matrix.diagonal cv') * U₁⁻¹.map ψ by simp only [Matrix.mul_assoc]]
  exact isUp_mul (isUp_mul (isUp_map ψ hU₁) (isUp_conj hk cv cv' hcv)) (isUp_map ψ (isUp_inv hU₁))

theorem cW_eq (σ : Fin (r + 1) → Fin (r + 1)) (ν : Fin (r + 1) → E) (s e : K) :
    s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r =
      s • (cP ψ cv L₁ * mono σ (fun a => ψ (ν a)) * cQ ψ cv U₁) - e • Ecorner r := by
  unfold cP cQ
  rw [Matrix.map_mul, Matrix.map_mul, mono_map]
  simp only [Matrix.mul_assoc]

theorem cG_eq (X' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    cP' ψ cv' L₁ * (Matrix.diagonal cv * (L₁ * X' * L₁⁻¹).map ψ * Matrix.diagonal cv') * cP ψ cv L₁ = X'.map ψ := by
  have e : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Matrix.diagonal cv' * (Matrix.diagonal cv * M) = M :=
    fun M => by rw [← Matrix.mul_assoc, diag_one (hcv'_of hcv), Matrix.one_mul]
  have f : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) K, L₁⁻¹.map ψ * (L₁.map ψ * M) = M :=
    fun M => by rw [← Matrix.mul_assoc, map_inv_mul ψ (det_lo hL₁), Matrix.one_mul]
  unfold cP cP'
  rw [Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc, e, f, map_inv_mul ψ (det_lo hL₁), Matrix.mul_one]

theorem conj_mul {P P' A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hPP : P * P' = 1) :
    P' * (A * B) * P = (P' * A * P) * (P' * B * P) := by
  rw [show P' * A * P * (P' * B * P) = P' * A * (P * P') * B * P by simp only [Matrix.mul_assoc], hPP,
    Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem comp_target {σ : Fin (r + 1) → Fin (r + 1)} (hσ : ∀ a, σ (σ a) = a) {ν : Fin (r + 1) → E}
    (hν : ∀ a, ν a ≠ 0) {s e : K} (hs : IsUnit s) {kL kR : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hkL : IsLo kL)
    (hkR : IsUp kR)
    (hk : kL * (s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) * kR =
      s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) :
    IsLo (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹ ∧ (∀ i j, σ j < σ i → (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹ i j = 0) ∧
      (cP' ψ cv' L₁ * kL * cP ψ cv L₁) * (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹ = 1 := by
  have hν' : ∀ x, IsUnit (ψ (ν x)) := fun x => by
    have hu : ψ (ν x) * ψ (ν x)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ (hν x), map_one]
    exact ⟨⟨ψ (ν x), ψ (ν x)⁻¹, hu, by rw [mul_comm, hu]⟩, rfl⟩
  rw [cW_eq ψ hcv hL₁ hU₁] at hk
  have hfix := stab_core hs (cP'_cP ψ hcv hL₁ hU₁) (cQ_cQ' ψ hcv hL₁ hU₁) hkL hkR hk
  exact fix_inv hσ hν' (cP_lo ψ hcv hL₁ hU₁ hkL) (cQ_up ψ hcv hL₁ hU₁ hkR) hfix

theorem comp_main {σ : Fin (r + 1) → Fin (r + 1)} (hσ : ∀ a, σ (σ a) = a) {ν : Fin (r + 1) → E}
    (hν : ∀ a, ν a ≠ 0) {s e : K} (hs : IsUnit s) {I : Subring K} {kL kR a b : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hkL : IsLo kL) (hkR : IsUp kR)
    (hk : kL * (s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) * kR =
      s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r)
    (ha : IsLo a) (hb : IsUp b)
    (hab : a * (s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) * b =
      s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r)
    {X' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (haX : a = kL * (Matrix.diagonal cv * (L₁ * X' * L₁⁻¹).map ψ * Matrix.diagonal cv'))
    {t c : K} (ht : t ∈ I) (hc : c ∈ I) (hbν : ∀ a, t * ψ (ν a) ∈ I) (hbν' : ∀ a, t * ψ (ν a)⁻¹ ∈ I)
    (bP : ∀ i j, t * cP ψ cv L₁ i j ∈ I) (bP' : ∀ i j, t * cP' ψ cv' L₁ i j ∈ I)
    (bQ : ∀ i j, t * cQ ψ cv U₁ i j ∈ I) (bQ' : ∀ i j, t * cQ' ψ cv' U₁ i j ∈ I)
    (bx : ∀ i j, t * (cP' ψ cv' L₁ * kL * cP ψ cv L₁) i j ∈ I)
    (hG : EntIn (lat I (t * (t * (t * (t * (t * c)))))) (X'.map ψ - (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹)) :
    EntIn (lat I c) (a - 1) ∧ EntIn (lat I c) (b - 1) := by
  have hν' : ∀ x, IsUnit (ψ (ν x)) := fun x => by
    have hu : ψ (ν x) * ψ (ν x)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ (hν x), map_one]
    exact ⟨⟨ψ (ν x), ψ (ν x)⁻¹, hu, by rw [mul_comm, hu]⟩, rfl⟩
  have hinv : ∀ x, t * Ring.inverse (ψ (ν x)) ∈ I := fun x => by
    rw [inv_eq_map ψ (hν x)]
    exact hbν' x
  have hT := (comp_target ψ hcv hL₁ hU₁ hσ hν hs hkL hkR hk).2.2
  have hA : cP' ψ cv' L₁ * a * cP ψ cv L₁ = (cP' ψ cv' L₁ * kL * cP ψ cv L₁) * X'.map ψ := by
    rw [haX, conj_mul hcv hL₁ hU₁ (conjPrime_conjPrime₂ ψ hcv hL₁ hU₁), cG_eq ψ hcv hL₁ hU₁]
  have hE := close_of_target hT bx hG
  rw [← hA] at hE
  rw [cW_eq ψ hcv hL₁ hU₁] at hab
  exact close_pair hσ hν' ht hc hbν hinv (conjPrime_conjPrime₂ ψ hcv hL₁ hU₁) (cP'_cP ψ hcv hL₁ hU₁)
    (cQ_cQ' ψ hcv hL₁ hU₁) (cQ'_cQ ψ hcv hL₁ hU₁) bP bP' bQ bQ' hs ha hb hab (cP_lo ψ hcv hL₁ hU₁ ha)
    (cQ_up ψ hcv hL₁ hU₁ hb) hE

end Comp

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.MainNotions.S Formalism.L2.SG.Pf.AtPt

section LeadLemmas

variable {K K' : Type*} [CommRing K] [CommRing K']

theorem det_map' {m : ℕ} (f : K →+* K') (A : Matrix (Fin m) (Fin m) K) : (A.map f).det = f A.det :=
  (RingHom.map_det f A).symm

theorem leadM_top {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : leadM A (r + 1) = A.det := by
  unfold leadM; rw [dite_eq_left le_rfl]; rfl

theorem leadM_map {m : ℕ} (f : K →+* K') (A : Matrix (Fin m) (Fin m) K) (l : ℕ) :
    leadM (A.map f) l = f (leadM A l) := by
  unfold leadM
  split_ifs with hl
  · rw [RingHom.map_det]; rfl
  · simp

theorem leadM_smul {m : ℕ} (c : K) (A : Matrix (Fin m) (Fin m) K) (l : ℕ) :
    leadM (c • A) l = c ^ l * leadM A l := by
  unfold leadM
  split_ifs with hl
  · rw [show (c • A).submatrix (Fin.castLE hl) (Fin.castLE hl) = c • A.submatrix (Fin.castLE hl) (Fin.castLE hl)
      from rfl, Matrix.det_smul, Fintype.card_fin]
  · simp

theorem leadM_transpose {m : ℕ} (A : Matrix (Fin m) (Fin m) K) (l : ℕ) : leadM A.transpose l = leadM A l := by
  unfold leadM
  split_ifs with hl
  · rw [← Matrix.det_transpose]; rfl
  · rfl

theorem castLE_ne_last {r : ℕ} (a : Fin r) : Fin.castLE (Nat.le_succ r) a ≠ Fin.last r := by
  intro h
  have h1 := congrArg Fin.val h
  have h2 := a.isLt
  simp at h1
  omega

theorem leadM_add_corner {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    leadM (A + c • Ecorner r) r = leadM A r := by
  unfold leadM
  rw [dite_eq_left (Nat.le_succ r), dite_eq_left (Nat.le_succ r)]
  congr 1
  ext a b
  simp [Ecorner, castLE_ne_last a]

theorem det_add_corner {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    (A + c • Ecorner r).det = A.det + c * leadM A r := by
  have hE : A + c • Ecorner r =
      A.updateRow (Fin.last r) (A (Fin.last r) + c • Pi.single (Fin.last r) 1) := by
    ext a b
    by_cases ha : a = Fin.last r
    · subst ha
      by_cases hb : b = Fin.last r
      · subst hb; simp [Ecorner]
      · simp [Ecorner, hb]
    · simp [Ecorner, ha]
  rw [hE, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  congr 2
  rw [Matrix.det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
  have h0 : ∀ j : Fin r, (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)) (Fin.last r) j.castSucc = 0 := by
    intro j
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Matrix.updateRow_self,
    Pi.single_eq_same, mul_one, Fin.succAbove_last]
  have hs : (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix (Fin.castLE (Nat.le_succ r)) (Fin.castLE (Nat.le_succ r)) := by
    ext a b
    simp only [Matrix.submatrix_apply]
    rw [Matrix.updateRow_ne (Fin.castSucc_ne_last a)]
    rfl
  rw [hs, leadM, dite_eq_left (Nat.le_succ r)]
  have hpow : ((-1 : K) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := Even.neg_one_pow ⟨_, rfl⟩
  rw [hpow, one_mul]

end LeadLemmas

section Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem leadZZ_model (M : Loc.Model F E) {r : ℕ} (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (leadM Zh r = 0 ↔ leadM (Loc.HermSp.ZZplusOf M Zh T T') r = 0) ∧
    (IsUnit (leadM Zh r) ↔ IsUnit (leadM (Loc.HermSp.ZZplusOf M Zh T T') r)) ∧
    (leadM Zh r = 0 → IsUnit (leadM Zh (r + 1)) → IsUnit (Loc.HermSp.ZZplusOf M Zh T T').det) := by
  rcases hs : M.split with _ | g
  · have e : Loc.HermSp.ZZplusOf M Zh T T' = Zh := by unfold Loc.HermSp.ZZplusOf; rw [hs]
    rw [e, ← leadM_top]
    exact ⟨Iff.rfl, Iff.rfl, fun _ h => h⟩
  · set q : F := (g.q : F) with hq
    have hq0 : q ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
    let π₁ : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom
    let π₂ : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom
    have hzero : ∀ x : E, x = 0 ↔ π₁ x = 0 ∧ π₂ x = 0 := by
      intro x
      constructor
      · rintro rfl; simp
      · rintro ⟨h1, h2⟩
        have : g.e x = 0 := Prod.ext h1 h2
        exact (map_eq_zero_iff g.e g.e.injective).1 this
    have hunit : ∀ x : E, IsUnit x ↔ π₁ x ≠ 0 ∧ π₂ x ≠ 0 := by
      intro x
      rw [← MulEquiv.isUnit_map g.e.toMulEquiv, Prod.isUnit_iff, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
      rfl
    have e1 : (Loc.HermSp.ZZplusOf M Zh T T').map π₁ = q⁻¹ • Zh.map π₁ + (T / q) • Ecorner r := by
      ext a b
      unfold Loc.HermSp.ZZplusOf; rw [hs]
      by_cases hab : a = Fin.last r ∧ b = Fin.last r
      · simp [π₁, hab, Ecorner, q, div_eq_inv_mul] <;> ring
      · simp [π₁, hab, Ecorner, q, div_eq_inv_mul] <;> ring
    have e2 : (Loc.HermSp.ZZplusOf M Zh T T').map π₂ = (-q⁻¹) • (Zh.map π₂).transpose + (-(T' / q)) • Ecorner r := by
      ext a b
      unfold Loc.HermSp.ZZplusOf; rw [hs]
      by_cases hab : a = Fin.last r ∧ b = Fin.last r
      · simp [π₂, hab, Ecorner, q, div_eq_inv_mul] <;> ring
      · simp [π₂, hab, Ecorner, q, div_eq_inv_mul] <;> ring
    have l1 : π₁ (leadM (Loc.HermSp.ZZplusOf M Zh T T') r) = q⁻¹ ^ r * π₁ (leadM Zh r) := by
      rw [← leadM_map, e1, leadM_add_corner, leadM_smul, leadM_map]
    have l2 : π₂ (leadM (Loc.HermSp.ZZplusOf M Zh T T') r) = (-q⁻¹) ^ r * π₂ (leadM Zh r) := by
      rw [← leadM_map, e2, leadM_add_corner, leadM_smul, leadM_transpose, leadM_map]
    have hq1 : q⁻¹ ^ r ≠ 0 := pow_ne_zero _ (inv_ne_zero hq0)
    have hq2 : (-q⁻¹) ^ r ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq0))
    refine ⟨?_, ?_, ?_⟩
    · rw [hzero, hzero (leadM _ r), l1, l2, mul_eq_zero, mul_eq_zero]
      simp [hq0]
    · rw [hunit, hunit (leadM _ r), l1, l2]
      simp [hq0]
    · intro h0 hu
      rw [leadM_top] at hu
      rw [hunit] at hu ⊢
      have z := (hzero _).1 h0
      rw [← det_map', ← det_map', e1, e2, det_add_corner, det_add_corner, leadM_smul, leadM_smul,
        leadM_transpose, leadM_map, leadM_map, z.1, z.2, Matrix.det_smul, Matrix.det_smul,
        Matrix.det_transpose, det_map', det_map']
      simp only [mul_zero, add_zero, Fintype.card_fin]
      exact ⟨mul_ne_zero (pow_ne_zero _ (inv_ne_zero hq0)) hu.1,
        mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq0))) hu.2⟩

end Model

theorem leadZZ_holds {D : Formalism.BasicNotions.D7} (Zd : Formalism.L2.SG.TermLoc.LocDat D) : LeadZZ Zd :=
  fun p Zh T T' => leadZZ_model (Zd.M p) Zh T T'

end Formalism.L2.SG.Pf.PCount
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut

namespace Formalism.L2.SG.NGCut.PtPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frame_mem {D : D7} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (hz : F.fl.z ∈ Λ) (hX : XLam Λ F = XS D F.fl) (b : Fin (D.R.rS + 1)) : frame F b ∈ Λ := by
  induction b using Fin.lastCases with
  | last => rw [Formalism.MainNotions.LatticeGluingRadicals.a_frame_last]; exact hz
  | cast b =>
    rw [Formalism.MainNotions.LatticeGluingRadicals.a_frame_castSucc]
    have h : F.fl.e b ∈ XLam Λ F := by rw [hX]; exact Formalism.MainNotions.BridgeLemma₂.basis_vector_mem_span D F.fl b
    exact h.1

theorem zhatOM_isIntegral {D : D7} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    (hF : ∀ b, frame F b ∈ Λ) (hF' : ∀ b, frame F' b ∈ Λ) (i j : Fin (D.R.rS + 1)) :
    IsIntegral ℤ (ZhatOM (ZhatL F F') i j) := by
  obtain ⟨c, hc⟩ := Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int hun (hF i) (hF' j)
  have hZ : ZhatL F F' i j = (VS D).hT (frame F i) (frame F' j) := rfl
  have h1 : IsIntegral ℤ ((-1 : D.host.E) ^ (D.R.rS - j.val)) := (isIntegral_one.neg).pow _
  show IsIntegral ℤ ((-1 : D.host.E) ^ (D.R.rS - j.val) * ZhatL F F' i j)
  rw [hZ, ← hc]
  exact h1.mul (RingOfIntegers.isIntegral_coe c)


open Formalism.MainNotions.BesselShellMomentBounds Formalism.HermitianLatticeCounting.ExpansionTerms in
theorem blockEndMinors_of_cell {D : D7} (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hZ : ∀ i j, IsIntegral ℤ (Z i j)) (γ : Point D.host.E (D.R.rS + 1)) (hc : IsInCell Z γ) :
    BlockEndMinorsIntegral (toSig γ) := by
  obtain ⟨L, U, hL, hU, rfl⟩ := hc
  intro (a : Fin (toComp γ).length)
  have key := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.integral_evaluation_fourth D.host.E (integralClosure ℤ D.host.E).toSubring (D.R.rS + 1)
    (toComp γ) (toT γ) (toT_ne γ) L U
    ⟨fun i => (hL i i).2 rfl, fun i j hij => (hL i j).1 hij⟩
    ⟨fun i => (hU i i).2 rfl, fun i j hij => (hU i j).1 hij⟩
    (by intro i j; rw [← ptMat_eq]; exact hZ i j)
  have := key.1 ((a : ℕ) + 1)
  show IsIntegral ℤ (IndexedMinorEntry (toComp γ).blocksFun (toT γ) a) ∧ IndexedMinorEntry (toComp γ).blocksFun (toT γ) a ≠ 0
  rw [E5minor_eq]
  exact this

theorem stepPoints_of_ctx
    (hOV : ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepPoints := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hc νL νB ng γ hγ => ?_⟩
  obtain ⟨c, ν, t, ht, hv, -, hpt, -⟩ := hγ
  have hG : t.toTerm.G ≠ 0 := by
    intro h
    apply ht.1
    show Gt t = 0
    have h' : t.G = 0 := h
    simp [Gt, h']
  have hrel : t.toTerm.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := hOV Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc t hr
    show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨w, hw⟩ := hAt Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc t.toTerm hG hrel
  have hat := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hw, hrel⟩
  obtain ⟨F', ⟨hP, -⟩, -, hcell⟩ := hat
  have hrow := (Y.rowsOK u).1 t.toTerm.lam t.toTerm.mem
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ t.toTerm.lam := frame_mem _ hrow.2.1.2.2.1.1 hrow.2.2
  have hF' : ∀ b, frame F' b ∈ t.toTerm.lam := frame_mem _ hP.1.1 hP.2.2.2
  have hE := blockEndMinors_of_cell _ (zhatOM_isIntegral _ _ hrow.2.1.2.1 hF hF') _ hcell
  rw [← hpt]
  exact hE

theorem stepPoints_of
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepPoints :=
  stepPoints_of_ctx (fun _ _ _ _ _ _ _ _ D _ X Y u u' _ => hOV D X Y u u')
    (fun _ _ _ _ _ _ _ _ D _ X Y u u' _ => hAt D X Y u u')


end Formalism.L2.SG.NGCut.PtPf
end
end
