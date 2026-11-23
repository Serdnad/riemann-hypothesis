module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle123
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle125
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle126
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTie

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

def LevTransportU : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (Bs : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → Bs.z = z → Bs.z' = z' → Bs.π = π → Bs.π' = π' →
    ∀ (i : Fin (P.r + 1)),
    ∃ Tw : D.LevTower P.k P.r Wp Wq, D.TowerNormalised Tw ∧
      Tw.base.z = z ∧ Tw.base.z' = z' ∧ Tw.base.π = π ∧ Tw.base.π' = π' ∧
    ∃ (Di : B.RealPlaceData P.k (P.r - i) Wp Wq)
      (Xi : ActualOps (JC.parLev P i).k (JC.parLev P i).r Di.z Di.z' Di.π Di.π') (μi : Measure (Mt P.k (P.r - i)))
      (Li : R.LevelData (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')) (P.r - i))
      (sti : Fr.Start (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π'))) (κ : ℝ),
      Di = Tw.bs i ∧ 0 < κ ∧ IsData (JC.parLev P i) Di.z Di.z' Di.π Di.π' Xi μi Li sti l0 ∧
      ∀ (c : Fin P.r → ℂ), (∀ l : Fin P.r, l.val < i.val → c l ≠ 0) →
      ∃ T : RadSp P.k P.r z z' π π' →ₗ[ℂ] RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π',
        LevTrClauses P μ L st l0 i c Di μi Li sti T ∧
        ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (shiftCf i c''))

end Formalism.FourierDecayAlt.P.PTie
end
end

section

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature

theorem haarSmul {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hcT : c ≠ ∞) : B.IsHaarOn U (c • μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [smul_apply, h.conc, smul_zero]
  · intro a ha
    rw [Measure.map_smul c (B2x5.measurable_lmulM a).aemeasurable, h.left a ha]
  · intro a ha
    rw [Measure.map_smul c (B2x5.measurable_rmulF a).aemeasurable, h.right a ha]
  · intro K hK
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hcT) (h.finite_compact K hK)
  · intro h0
    apply h.ne_zero
    have := congrArg (fun ν : Measure (Mt k r) => c⁻¹ • ν) h0
    simpa [smul_smul, ENNReal.inv_mul_cancel hc0 hcT] using this

section norm

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem massW_ne_zero (Bs : B.RealPlaceData k r Wp Wq) : Bs.μW Set.univ ≠ 0 :=
  Measure.measure_univ_ne_zero.2 Bs.haarW.ne_zero

theorem massW'_ne_zero (Bs : B.RealPlaceData k r Wp Wq) : Bs.μW' Set.univ ≠ 0 :=
  Measure.measure_univ_ne_zero.2 Bs.haarW'.ne_zero

theorem massW_ne_top (Bs : B.RealPlaceData k r Wp Wq) : Bs.μW Set.univ ≠ ∞ := by
  have := Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.haar_finite Formalism.FourierDecayAlt.P.B2x3.compactW Bs.z_mem Bs.T_pos Bs.haarW
  exact measure_ne_top _ _

theorem massW'_ne_top (Bs : B.RealPlaceData k r Wp Wq) : Bs.μW' Set.univ ≠ ∞ := by
  have := Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.haar_finite Formalism.FourierDecayAlt.P.B2x3.compactW Bs.z'_mem Bs.T'_pos Bs.haarW'
  exact measure_ne_top _ _

def normS (Bs : B.RealPlaceData k r Wp Wq) : B.RealPlaceData k r Wp Wq :=
  { Bs with
    μW := (Bs.μW Set.univ)⁻¹ • Bs.μW
    μW' := (Bs.μW' Set.univ)⁻¹ • Bs.μW'
    μN := D.muN k r
    haarW := haarSmul Bs.haarW (ENNReal.inv_ne_zero.2 (massW_ne_top Bs)) (ENNReal.inv_ne_top.2 (massW_ne_zero Bs))
    haarN := Formalism.FourierDecayAlt.P.Dx2.MN.haar r
    haarW' := haarSmul Bs.haarW' (ENNReal.inv_ne_zero.2 (massW'_ne_top Bs))
      (ENNReal.inv_ne_top.2 (massW'_ne_zero Bs)) }

theorem normS_μW_univ_eq_one (Bs : B.RealPlaceData k r Wp Wq) : (normS Bs).μW Set.univ = 1 := by
  show ((Bs.μW Set.univ)⁻¹ • Bs.μW) Set.univ = 1
  rw [smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (massW_ne_zero Bs) (massW_ne_top Bs)]

theorem normS_μW'_univ_eq_one (Bs : B.RealPlaceData k r Wp Wq) : (normS Bs).μW' Set.univ = 1 := by
  show ((Bs.μW' Set.univ)⁻¹ • Bs.μW') Set.univ = 1
  rw [smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (massW'_ne_zero Bs) (massW'_ne_top Bs)]

end norm

theorem towerAt : Formalism.FourierDecayAlt.P.PTie.TowerAt := by
  intro k r Wp Wq _ _ _ _ Bs
  obtain ⟨T, hT, hN⟩ := Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq (normS Bs) (normS_μW_univ_eq_one Bs) (normS_μW'_univ_eq_one Bs) rfl
  exact ⟨T, by rw [hT]; rfl, by rw [hT]; rfl, by rw [hT]; rfl, by rw [hT]; rfl, hN⟩

section frame

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem herm_mulVec' {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg]

theorem frameVec_facts (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (hF : D.IsBaseFrame Bs ν' m₀) :
    inWb k r (m₀ *ᵥ ν') ∧ herm (Hpk k r) (m₀ *ᵥ ν') Bs.z = 0 ∧ herm (Hpk k r) (m₀ *ᵥ ν') (m₀ *ᵥ ν') = 1 := by
  obtain ⟨hw, hz, hn, hm, hmz⟩ := hF
  have hU : m₀ᴴ * Hpk k r * m₀ = Hpk k r := hm.1
  refine ⟨Formalism.FourierDecayAlt.P.Qx8.inWb_mulVec hm hw, ?_, by rw [herm_mulVec' hU]; exact hn⟩
  have h0 : herm (Hpk k r) (m₀ *ᵥ ν') (m₀ *ᵥ Bs.z') = 0 := by rw [herm_mulVec' hU]; exact hz
  rw [hmz] at h0
  set c : ℂ := ((√(Tz k r Bs.z' / Tz k r Bs.z) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact_mod_cast (Real.sqrt_pos.mpr (div_pos Bs.T'_pos Bs.T_pos)).ne'
  have e : herm (Hpk k r) (m₀ *ᵥ ν') (c • Bs.z) = star c * herm (Hpk k r) (m₀ *ᵥ ν') Bs.z := by
    unfold herm
    rw [star_smul, smul_dotProduct, smul_eq_mul]
  rw [e] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (star_eq_zero.mp h) hc0
  · exact h

theorem frame_of (Bs : B.RealPlaceData k r Wp Wq) : ∃ (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r),
    D.IsBaseFrame Bs ν' m₀ := by
  obtain ⟨Fb, hBw, hBo, hBz⟩ := Formalism.FourierDecayAlt.P.Qx8.frame_exists Bs.z'_mem Bs.T'_pos
  set T : ℝ := Tz k r Bs.z with hTdef
  set T' : ℝ := Tz k r Bs.z' with hT'def
  have hT : 0 < T := Bs.T_pos
  have hT' : 0 < T' := Bs.T'_pos
  set c : ℝ := √(T' / T) with hc
  have hcc : c * c = T' / T := Real.mul_self_sqrt (div_pos hT' hT).le
  have hcw : inWb k r ((c : ℂ) • Bs.z) := Formalism.FourierDecayAlt.P.Qx8.inWb_smul Bs.z_mem _
  have hz' : herm (Hpk k r) Bs.z' Bs.z' = ((-T' : ℝ) : ℂ) := by
    rw [Formalism.FourierDecayAlt.P.Qx8.herm_self']; push_cast; rfl
  have hcz : herm (Hpk k r) ((c : ℂ) • Bs.z) ((c : ℂ) • Bs.z) = ((-T' : ℝ) : ℂ) := by
    rw [Formalism.FourierDecayAlt.P.Qx8.herm_smul_left', Formalism.FourierDecayAlt.P.Qx8.herm_smul_right', Formalism.FourierDecayAlt.P.Qx8.herm_self']
    have hs : star (c : ℂ) = c := Complex.conj_ofReal c
    rw [hs, ← hTdef]
    have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have e1 : (c : ℂ) * (c : ℂ) = (T' : ℂ) / (T : ℂ) := by
      rw [← Complex.ofReal_mul, hcc]; push_cast; rfl
    rw [show (c : ℂ) * ((c : ℂ) * -(T : ℂ)) = -((c : ℂ) * (c : ℂ)) * (T : ℂ) by ring, e1]
    push_cast
    field_simp
  obtain ⟨m, hm, hmz, -⟩ := Formalism.FourierDecayAlt.P.Qx8.move Bs.z'_mem hcw (-T') (by linarith) hz' hcz
  refine ⟨Fb ⟨0, by have := Bs.k_pos; omega⟩, m, hBw _, hBz _ _ (List.mem_singleton_self _), ?_, hm, hmz⟩
  rw [hBo, ite_eq_left rfl]

end frame

end Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature

namespace Formalism.FourierDecayAlt.P

theorem exists_normalized_tower : Formalism.FourierDecayAlt.P.PTie.TowerAt := HaarMassHermitianCurvature.towerAt

end Formalism.FourierDecayAlt.P
end
end

section

open Matrix MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section defs

variable {k r : ℕ}

def zfull {j : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ :=
  U.blk2 Z 0 0 (Matrix.of fun _ _ => τ)

def x0 (k r j : ℕ) (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1))) : B.Mat k r :=
  D.castM (by omega : j + 1 + (r - (j + 1)) = r) (U.mMap k (j + 1) (r - (j + 1)) (zfull Z τ) γ)

def nL (k r j : ℕ) (hj : j + 1 ≤ r) (a : Fin j → ℂ) : B.Mat k r :=
  1 + ∑ b : Fin j, (a b • Matrix.single (esI k r ⟨j, by omega⟩) (esI k r ⟨b, by omega⟩) (1 : ℂ) -
    conj (a b) • Matrix.single (eI k r ⟨b, by omega⟩) (eI k r ⟨j, by omega⟩) (1 : ℂ))

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def RulesOn (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) :
    Prop :=
  Q.SmoothLev k r 0 Dm Φ ∧
    (∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ n ∈ QuantumDeterminants.Nset k r, g * n ∈ Dm ∧ Φ (g * n) = psi k r z' cStd n • Φ g) ∧
    ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ, nL k r j hj a * g ∈ Dm ∧
      Φ (nL k r j hj a * g) = psi k r z cStd (nL k r j hj a) • Φ g

def levelZeroKernel (k r j : ℕ) : ℂ := ((r - j : ℕ) : ℂ) + (k : ℂ) / 2

def domJ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Q.Mx k r) :=
  {g | Dmin k r z z' g ⟨j, by omega⟩ ≠ 0 ∧ Dmin k r z z' g ⟨j + 1, by omega⟩ ≠ 0 ∧ 0 < Gf k r z z' g}

def ParamComm {j : ℕ} (A : (Matrix (Fin j) (Fin j) ℂ → E) →ₗ[ℂ] (Matrix (Fin j) (Fin j) ℂ → E)) : Prop :=
  ∀ (U : Set (ℂ × (Fin j → Fin j → ℂ))) (κ : ℂ → Matrix (Fin j) (Fin j) ℂ → E), IsOpen U →
    U ⊆ {q | (Matrix.of q.2).det ≠ 0} →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => κ q.1 (Matrix.of q.2)) U →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => A (κ q.1) (Matrix.of q.2)) U ∧
    ∀ q ∈ U, PBP.dz (fun τ => A (κ τ) (Matrix.of q.2)) q.1 = A (fun Z => PBP.dz (fun τ => κ τ Z) q.1) (Matrix.of q.2) ∧
      PBP.dzb (fun τ => A (κ τ) (Matrix.of q.2)) q.1 = A (fun Z => PBP.dzb (fun τ => κ τ Z) q.1) (Matrix.of q.2)

end defs

def HeadLetter : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E), inWb k r z → inWb k r z' → IsOpen Dm →
    Dm ⊆ domJ k r j hj z z' → RulesOn k r j hj z z' Dm Φ →
    ∀ (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ), Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm → ∀ Y : ℝ,
      D.vLet k r z z' (j + 1) hj (true, Y) 0 Φ (x0 k r j hj Z τ γ) =
          ((Y : ℂ) + levelZeroKernel k r j) • D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ γ) +
            τ • PBP.dz (fun τ' => D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ' γ)) τ -
            τ • D.vLet k r z z' j (by omega) (true, Y) 1 Φ (x0 k r j hj Z τ γ) ∧
      D.vLet k r z z' (j + 1) hj (true, Y) 1 Φ (x0 k r j hj Z τ γ) =
          τ⁻¹ • D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ γ) ∧
      D.vLet k r z z' (j + 1) hj (false, Y) 0 Φ (x0 k r j hj Z τ γ) =
          ((Y : ℂ) - levelZeroKernel k r j) • D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ γ) -
            conj τ • PBP.dzb (fun τ' => D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ' γ)) τ -
            conj τ • D.vLet k r z z' j (by omega) (false, Y) 1 Φ (x0 k r j hj Z τ γ) ∧
      D.vLet k r z z' (j + 1) hj (false, Y) 1 Φ (x0 k r j hj Z τ γ) =
          (conj τ)⁻¹ • D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ γ)

def ZOnly : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (l : C.Letter) (e : Fin 2), inWb k r z → inWb k r z' →
    ∃ A : (Matrix (Fin j) (Fin j) ℂ → E) →ₗ[ℂ] (Matrix (Fin j) (Fin j) ℂ → E), ParamComm A ∧
      ∀ (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E), IsOpen Dm → Dm ⊆ domJ k r j hj z z' → Q.SmoothLev k r 0 Dm Φ →
      ∀ (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1))), Z.det ≠ 0 → τ ≠ 0 →
        γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
        D.vLet k r z z' j (by omega) l e Φ (x0 k r j hj Z τ γ) = A (fun Z' => Φ (x0 k r j hj Z' τ γ)) Z

def RulesClosed : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E), inWb k r z → inWb k r z' → IsOpen Dm →
    Dm ⊆ domJ k r j hj z z' → RulesOn k r j hj z z' Dm Φ →
    ∀ (i : ℕ) (hi : i ≤ j + 1), (i = j ∨ i = j + 1) → ∀ (l : C.Letter) (e : Fin 2),
      RulesOn k r j hj z z' Dm (D.vLet k r z z' i (by omega) l e Φ)

def WordInd : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E), inWb k r z → inWb k r z' → IsOpen Dm →
    Dm ⊆ domJ k r j hj z z' → RulesOn k r j hj z z' Dm Φ →
    ∀ (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))), Z.det ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    (∀ τ : ℂ, τ ≠ 0 → x0 k r j hj Z τ γ ∈ Dm) →
    ∀ (w : List C.Letter) (φ : Wd.Ix (Fin w.length) → V1 E),
    (∀ e τ, τ ≠ 0 → (φ e).1 τ = D.uwG k r z z' Φ j (by omega) w e (x0 k r j hj Z τ γ)) →
    ∀ (t : ℂ), t ≠ 0 → ∀ e, D.uwG k r z z' Φ (j + 1) hj w e (x0 k r j hj Z t γ) =
      (oneBT (levelZeroKernel k r j) (D.positionted w) φ e).1 t

def WordIndOfParts : Prop := HeadLetter → ZOnly → RulesClosed → WordInd

def HeadBridge : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ φ : Wd.Ix (Fin w.length) → V1 (Wq →L[ℂ] Wp),
    (∀ e τ, τ ≠ 0 → (φ e).1 τ = B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 e) (mLev P j hj τ γ)) →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)),
    ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X) (ℓ : X → (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))
      (Zx : X → Matrix (Fin j) (Fin j) ℂ) (Fx : X → Q.Mx P.k P.r → (Wq →L[ℂ] Wp)) (Dm : Set (Q.Mx P.k P.r))
      (φx : X → Wd.Ix (Fin w.length) → V1 (Wq →L[ℂ] Wp)),
      IsOpen Dm ∧ Dm ⊆ domJ P.k P.r j hj p.T.base.z p.T.base.z' ∧
      (∀ x, RulesOn P.k P.r j hj p.T.base.z p.T.base.z' Dm (Fx x)) ∧
      (∀ x, (Zx x).det ≠ 0 ∧ ∀ τ : ℂ, τ ≠ 0 → x0 P.k P.r j hj (Zx x) τ γ ∈ Dm) ∧
      (∀ x e' τ, τ ≠ 0 → (φx x e').1 τ =
        D.uwG P.k P.r p.T.base.z p.T.base.z' (Fx x) j (by omega) w e' (x0 P.k P.r j hj (Zx x) τ γ)) ∧
      B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
        ∫ x, ℓ x (D.uwG P.k P.r p.T.base.z p.T.base.z' (Fx x) (j + 1) hj w e (x0 P.k P.r j hj (Zx x) t γ)) ∂μ ∧
      (oneBT (kapJ P j) (D.positionted w) φ e).1 t = ∫ x, ℓ x ((oneBT (kapJ P j) (D.positionted w) (φx x) e).1 t) ∂μ

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

open Formalism.FourierDecayAlt.P.MAx3.G

section PolyTools

variable {R : Type} [Ring R] [Algebra ℂ R]

theorem curv_polyIn_congr {f g : ℂ → R} {d : ℕ} (h : PolyIn f d) (e : ∀ s, g s = f s) : PolyIn g d := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun s => by rw [e, ha]⟩

theorem curv_polyIn_csmul {f : ℂ → R} {d : ℕ} (c : ℂ) (hf : PolyIn f d) : PolyIn (fun s => c • f s) d := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨fun k => c • a k, fun s => by dsimp only; rw [ha, Finset.smul_sum]; simp only [smul_comm c]⟩

theorem curv_polyIn_sub {f g : ℂ → R} {d : ℕ} (hf : PolyIn f d) (hg : PolyIn g d) :
    PolyIn (fun s => f s - g s) d :=
  curv_polyIn_congr (polyIn_add hf (curv_polyIn_csmul (-1) hg)) fun s => by simp [sub_eq_add_neg]

theorem curv_polyIn_monomial (n : ℕ) (x : R) : PolyIn (fun s => s ^ n • x) n := by
  refine ⟨fun k => if k = n then x else 0, fun s => ?_⟩
  dsimp only
  rw [Finset.sum_eq_single n (fun b _ hb => by rw [if_neg hb, smul_zero])
    (fun h => absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h), if_pos rfl]

end PolyTools

theorem curv_top_zero {E : Type*} [AddCommGroup E] [Module ℂ E] (n : ℕ) (c : E) (a : ℕ → E)
    (h : ∀ u : ℂ, u ^ (n + 1) • c = ∑ i ∈ Finset.range (n + 1), u ^ i • a i) : c = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  set p : Polynomial ℂ := Polynomial.C (φ c) * Polynomial.X ^ (n + 1) -
    ∑ i ∈ Finset.range (n + 1), Polynomial.C (φ (a i)) * Polynomial.X ^ i with hpdef
  have hp : p = 0 := by
    apply Polynomial.funext
    intro u
    have hu := congrArg φ (h u)

    simp only [map_smul, map_sum, smul_eq_mul] at hu
    simp only [hpdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_finsetSum, Polynomial.eval_zero]
    rw [mul_comm (φ c), hu, sub_eq_zero]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hc := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q (n + 1)) hp
  simp only [hpdef, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_zero (fun i hi => by
    rw [if_neg (by have := Finset.mem_range.1 hi; omega)]), sub_zero] at hc
  exact hc

theorem curvature_radial_torus_holds : GTCCurvRTT := by
  intro A _ _ n f g Θ hn hrtt hF hg v
  set T := g v with hT
  set F : ℂ → A := fun u => f u - u ^ (n + 1) • (1 : A) - u ^ n • Θ with hFdef
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hG : PolyIn (fun u => F u * T - T * F u) (n - 1) :=
    curv_polyIn_sub (polyIn_mul_const hF T) (polyIn_const_mul T hF)
  have hSt : PolyIn (fun u => g u * f v - u ^ n • (T * Θ) - T * F u + v • (u ^ n • (Θ * T - T * Θ)) -
      u • (F u * T - T * F u) + v • (F u * T - T * F u)) n := by
    refine polyIn_add (curv_polyIn_sub (polyIn_add (curv_polyIn_sub (curv_polyIn_sub (polyIn_mul_const hg (f v))
      (curv_polyIn_monomial n (T * Θ))) (polyIn_mono (polyIn_const_mul T hF) (by omega)))
      (curv_polyIn_csmul v (curv_polyIn_monomial n (Θ * T - T * Θ)))) ?_) ?_
    · have := polyIn_smul_var hG
      rw [hn'] at this
      exact this
    · exact polyIn_mono (curv_polyIn_csmul v hG) (by omega)
  obtain ⟨s, hs⟩ := hSt
  have key : ∀ u : ℂ, u ^ (n + 1) • (Θ * T - T * Θ + T) = ∑ i ∈ Finset.range (n + 1), u ^ i • s i := by
    intro u
    rw [← hs u]
    have hfu : f u = F u + u ^ (n + 1) • (1 : A) + u ^ n • Θ := by simp only [hFdef]; abel
    have h := hrtt u v
    rw [← hT, hfu] at h
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at h
    linear_combination (norm := module) h
  have h0 := curv_top_zero n _ s key
  exact eq_neg_of_add_eq_zero_left h0

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem thetaC_eq_thetaNF {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A)
    (hTT : d.L.TT = (P.TT : ℂ)) : ThetaC d = ThetaNF P d := by
  unfold ThetaC ThetaNF
  rw [hTT]
  congr 3
  funext ρ
  rw [aC_eq]
  push_cast
  ring

theorem gTRTopNF_of_curvPoly (h : GTCCurvPoly) : GTRTopNF := by
  intro P A _ _ _ d _ hk _ hRel hTT
  obtain ⟨⟨a, ha⟩, -⟩ := h P A d hRel hk hTT
  have hk1 : P.k - 1 + 1 = P.k := by omega
  refine ⟨fun j => if j = P.k + 1 then 1 else if j = P.k then ThetaC d else if j < P.k then a j else 0,
    fun Y => ?_, 0, ?_⟩
  · have e := ha Y
    rw [hk1] at e
    dsimp only at e ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [show P.k ≠ P.k + 1 by omega, ↓reduceIte]
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [if_neg (by have := Finset.mem_range.1 hj; omega), if_neg (by have := Finset.mem_range.1 hj; omega),
        if_pos (Finset.mem_range.1 hj)]), ← e]
    abel
  · simp only [show P.k ≠ P.k + 1 by omega, if_false, if_true, Int.cast_zero, zero_smul, add_zero]
    exact thetaC_eq_thetaNF d hTT

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
