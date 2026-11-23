module

import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.MulVecApplyOfRow
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle036
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ExistsPowMulPredGe
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HpkMulVecEs
import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.FormalDegreeBessel.Bundle002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HaarOnSkOfB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMain
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle037
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ToTermAct
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubMemOfIndQ
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

section Model

variable {k r : ℕ}

theorem cont_of : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r =>
    (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := by
  exact continuous_id

theorem meas_rmul (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (Formalism.FourierDecayAlt.B.rmulF a : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) := by
  have hc : Continuous (Formalism.FourierDecayAlt.B.rmulF a : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) :=
    cont_of.matrix_mul continuous_const
  exact hc.measurable

theorem meas_conj (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (Formalism.QuantumDeterminants.conjM (k := k) (r := r) a) := by
  have hc : Continuous (Formalism.QuantumDeterminants.conjM (k := k) (r := r) a) :=
    (continuous_const.matrix_mul cont_of).matrix_mul continuous_const
  exact hc.measurable

theorem meas_mulP : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
    (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
  have hc : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) :=
    (cont_of.comp continuous_fst).matrix_mul (cont_of.comp continuous_snd)
  exact hc.measurable

theorem sigmaFinite_of_b {U : Set (Formalism.FourierDecayAlt.B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

theorem haarOn_sk_of_b' {U : Set (Formalism.FourierDecayAlt.B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ) : Formalism.MainNotions.S.IsHaarOn U μ := by
  exact ⟨sigmaFinite_of_b h, h.ne_zero, h.conc, h.left⟩

theorem det_unit_of_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : IsUnit g.det := by
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  rw [isUnit_iff_ne_zero]
  intro h0
  have h1 := congrArg Matrix.det hg'
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
  exact (Formalism.FourierDecayAlt.P.B2x5.isUnit_det_Hpk k r).ne_zero h1.symm

theorem inv_mem_UW {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UWset k r z) : g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z := by
  apply WlocSk.UnitaryGroupBasics.uw_inv <;> assumption

theorem muS_right {z : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, (Formalism.MainNotions.S.muS μW μN).map (Formalism.FourierDecayAlt.B.rmulF s) = Formalism.MainNotions.S.muS μW μN := by
  intro s hs
  obtain ⟨h0, hh0, n0, hn0, rfl⟩ := hs
  have := sigmaFinite_of_b hW
  have := sigmaFinite_of_b hN
  have hd := det_unit_of_UH hh0.1
  have hinv0 := inv_mem_UW hh0
  have hNc : μN.map (Formalism.QuantumDeterminants.conjM h0⁻¹) = μN :=
    Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μN hz hT hN h0⁻¹ hinv0
  have hW1 : μW.map (Formalism.FourierDecayAlt.B.rmulF h0) = μW := hW.right h0 hh0
  have hN1 : μN.map (Formalism.FourierDecayAlt.B.rmulF n0) = μN := hN.right n0 hn0
  let F : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r :=
    Prod.map (Formalism.FourierDecayAlt.B.rmulF h0) (Formalism.FourierDecayAlt.B.rmulF n0 ∘ Formalism.QuantumDeterminants.conjM h0⁻¹)
  have hFm : Measurable F := (meas_rmul h0).prodMap ((meas_rmul n0).comp (meas_conj _))
  have hF : (μW.prod μN).map F = μW.prod μN := by
    have h2 : μN.map (Formalism.FourierDecayAlt.B.rmulF n0 ∘ Formalism.QuantumDeterminants.conjM h0⁻¹) = μN := by
      rw [← Measure.map_map (meas_rmul n0) (meas_conj _), hNc, hN1]
    haveI : SigmaFinite (μW.map (Formalism.FourierDecayAlt.B.rmulF h0)) := by rw [hW1]; infer_instance
    haveI : SigmaFinite (μN.map (Formalism.FourierDecayAlt.B.rmulF n0 ∘ Formalism.QuantumDeterminants.conjM h0⁻¹)) := by rw [h2]; infer_instance
    rw [← Measure.map_prod_map _ _ (meas_rmul h0) ((meas_rmul n0).comp (meas_conj _)), hW1, h2]
  have hcomm : (Formalism.FourierDecayAlt.B.rmulF (h0 * n0)) ∘
      (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) =
      (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) ∘ F := by
    funext p
    have hi : h0 * h0⁻¹ = 1 := Matrix.mul_nonsing_inv h0 hd
    have hii : (h0⁻¹)⁻¹ = h0 := Matrix.nonsing_inv_nonsing_inv h0 hd
    show Matrix.of p.1 * Matrix.of p.2 * (h0 * n0) =
      (Matrix.of p.1 * h0) * (h0⁻¹ * Matrix.of p.2 * (h0⁻¹)⁻¹ * n0)
    rw [hii]
    calc Matrix.of p.1 * Matrix.of p.2 * (h0 * n0) = Matrix.of p.1 * (h0 * h0⁻¹) * Matrix.of p.2 * h0 * n0 := by
          rw [hi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  unfold Formalism.MainNotions.S.muS
  rw [Measure.map_map (meas_rmul _) meas_mulP, hcomm, ← Measure.map_map meas_mulP hFm, hF]

end Model

theorem psiP_mul {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : IsUnit P.det) (x s : Formalism.REAL.UJ ε) :
    psiP P (x * s) = Formalism.FourierDecayAlt.B.rmulF (P⁻¹ * Formalism.MainNotions.S.uMat s * P) (psiP P x) := by
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hm : Formalism.MainNotions.S.uMat (x * s) = Formalism.MainNotions.S.uMat x * Formalism.MainNotions.S.uMat s := by
    simp [Formalism.MainNotions.S.uMat]
  have key : P⁻¹ * Formalism.MainNotions.S.uMat (x * s) * P =
      (P⁻¹ * Formalism.MainNotions.S.uMat x * P) * (P⁻¹ * Formalism.MainNotions.S.uMat s * P) := by
    rw [hm, show P⁻¹ * Formalism.MainNotions.S.uMat x * P * (P⁻¹ * Formalism.MainNotions.S.uMat s * P) =
        P⁻¹ * Formalism.MainNotions.S.uMat x * (P * P⁻¹) * Formalism.MainNotions.S.uMat s * P by simp only [Matrix.mul_assoc], hPP,
      Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  funext i j
  exact congrFun (congrFun key i) j

theorem rightInvS_of (hSC : SetCorr) (hHC : HaarCorr) : RightInvS := by
  intro n r k ε e z z' T T' hF μ hμ s hs
  have hn : n = 2 * r + k + 1 := by have := hF.dim; omega
  subst hn
  obtain ⟨d, hGP⟩ := goodPos_shift hF
  have hF'' := frameLoc_shift hF d
  obtain ⟨P, hPJ, hPdet, hPe, zH, -, hzH, -, hPz, -, hTz, -⟩ :=
    pFrame_holds r k ε e z (z' + ∑ a, d a • e a) T T' hF'' hGP
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r zH := by rw [hTz]; exact hF.T_pos
  obtain ⟨μW0, hW0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r zH hzH hT
  obtain ⟨μN0, hN0⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
  obtain ⟨-, hC⟩ := hHC r k ε e z zH P hPJ hPdet hPe hzH hPz hT hF.k_pos
  obtain ⟨c, -, hm⟩ := hC μW0 μN0 (haarOn_sk_of_b' hW0) (haarOn_sk_of_b' hN0) μ hμ
  have hψs : P⁻¹ * Formalism.MainNotions.S.uMat s * P ∈ Formalism.QuantumDeterminants.Sset k r zH := (hSC r k ε e z zH P hPJ hPdet hPe hzH hPz hT s).1 hs
  have hme : MeasurableEmbedding (psiP (ε := ε) P) :=
    (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_closedEmbedding (ε := ε) (P := P) Formalism.REAL.uJEmb hPdet).measurableEmbedding
  have hms : Measurable (fun x : Formalism.REAL.UJ ε => x * s) := (continuous_mul_const s).measurable
  have hmap : (μ.map (fun x => x * s)).map (psiP P) = μ.map (psiP P) := by
    rw [Measure.map_map hme.measurable hms]
    have : psiP P ∘ (fun x : Formalism.REAL.UJ ε => x * s) = Formalism.FourierDecayAlt.B.rmulF (P⁻¹ * Formalism.MainNotions.S.uMat s * P) ∘ psiP P := by
      funext x; exact psiP_mul hPdet x s
    rw [this, ← Measure.map_map (meas_rmul _) hme.measurable, hm, Measure.map_smul,
      muS_right hzH hT hW0 hN0 _ hψs]
    exact (meas_rmul _).aemeasurable
  rw [← hme.comap_map (μ.map (fun x => x * s)), hmap, hme.comap_map]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

theorem rightInvS_of (hSC : SetCorr) (hHC : HaarCorr) : RightInvS := RI.rightInvS_of hSC hHC

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

theorem bigMem_holds : BigMem := Formalism.QuantumDeterminants.bigCellMem

theorem hJ_P {n : ℕ} {ε : Fin n → Bool} {P H : Matrix (Fin n) (Fin n) ℂ} (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = H)
    (x y : Fin n → ℂ) : hJ ε (P *ᵥ x) (P *ᵥ y) = Formalism.QuantumDeterminants.herm H y x := by
  unfold hJ Formalism.QuantumDeterminants.herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hPJ]

theorem hJ_smul_l {n : ℕ} (ε : Fin n → Bool) (a : ℂ) (x y : Fin n → ℂ) : hJ ε (a • x) y = conj a * hJ ε x y := by
  unfold hJ
  rw [star_smul, smul_dotProduct, smul_eq_mul, Complex.star_def]

theorem hJ_smul_r {n : ℕ} (ε : Fin n → Bool) (a : ℂ) (x y : Fin n → ℂ) : hJ ε x (a • y) = a * hJ ε x y := by
  unfold hJ
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem fam_eq {r k : ℕ} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {e : Fin r → Fin (2 * r + k + 1) → ℂ} {z zH : Fin (2 * r + k + 1) → ℂ}
    (hPe : ∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) (hPz : P *ᵥ zH = z) (a : Fin (r + 1)) :
    fam e z a = P *ᵥ Formalism.QuantumDeterminants.fvec k r zH a := by
  unfold fam Formalism.QuantumDeterminants.fvec
  split_ifs with h
  · have ha : a = Fin.castSucc ⟨a.val, h⟩ := Fin.ext rfl
    conv_lhs => rw [ha]
    rw [Fin.snoc_castSucc]
    exact (hPe _).symm
  · have ha : a = Fin.last r := Fin.ext (by have := a.2; simp only [Fin.val_last]; omega)
    subst ha
    rw [Fin.snoc_last]
    exact hPz.symm

theorem bigCell_mulVec_wb {k r : ℕ} (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    {w : Fin (2 * r + k + 1) → ℂ} (hw : Formalism.QuantumDeterminants.inWb k r w) :
    Formalism.QuantumDeterminants.bigCell k r c μ *ᵥ w = Formalism.FourierDecayAlt.B2.embWb k r μ *ᵥ w := by
  ext i
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · have hj1 : ¬ j.val < r := by omega
    unfold Formalism.QuantumDeterminants.bigCell Formalism.FourierDecayAlt.B2.embWb
    rw [dite_eq_right hj1, dite_eq_left hj.2]
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · rw [dite_eq_left hi, dite_eq_left ⟨hi, hj⟩]
    · rw [dite_eq_right hi, dite_eq_right (fun h => hi h.1),
        if_neg (fun (h : i = j ∧ ¬(r ≤ i.val ∧ i.val ≤ r + k)) => hi (by rw [h.1]; exact hj))]
  · rw [hw j (by omega)]
    simp

theorem conj_scinv (sc : ℝ) (m : ℕ) : conj (((sc : ℂ) ^ m)⁻¹) = ((sc : ℂ) ^ m)⁻¹ := by
  simp [map_inv₀, map_pow]

theorem zBig : ZBig := by
  intro r k ε e z z' zH zH' P sc hPJ hPdet hPe hzH hzH' hPz hPz' hsc μsec hsec q hq hζ
  have hU : (μsec q.2)ᴴ * Formalism.QuantumDeterminants.Hb k * μsec q.2 = Formalism.QuantumDeterminants.Hb k := (hsec.2 q.2 hζ).1
  refine ⟨inUJ_conj hPJ hPdet (bigMem_holds k r q.1 _ hq hU), ?_⟩
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hB : ∀ y, (P * Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) * P⁻¹) *ᵥ (P *ᵥ y) =
      P *ᵥ (Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) *ᵥ y) := by
    intro y
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  have hlast : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) *ᵥ zH') zH = q.2 := by
    have h1W : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Formalism.QuantumDeterminants.UWset k r zH := by
      refine ⟨by simp [Formalism.QuantumDeterminants.UH], fun a => by simp, by simp⟩
    have h1W' : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Formalism.QuantumDeterminants.UWset k r zH' := by
      refine ⟨by simp [Formalism.QuantumDeterminants.UH], fun a => by simp, by simp⟩
    have := (Formalism.FourierDecayAlt.P.b2_rank_one_mem k r zH zH' μsec hzH hzH' hsec q.2 hζ 1 h1W 1 h1W').2
    rw [inv_one, Matrix.one_mul, Matrix.mul_one] at this
    rw [bigCell_mulVec_wb q.1 _ hzH']
    exact this
  have hZ := Formalism.QuantumDeterminants.bigCellZhat k r zH zH' q.1 (μsec q.2) hzH hzH'
  ext a b
  simp only [Zhat, famSc]
  rw [Matrix.mulVec_smul, hJ_smul_l, hJ_smul_r, fam_eq hPe hPz a, fam_eq hPe hPz' b, hB, hJ_P hPJ]
  have hZab := congrFun (congrFun hZ a) b
  simp only [Formalism.QuantumDeterminants.Zhat] at hZab
  rw [hZab, conj_scinv]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    by_cases ha : a.val < r
    · rw [dite_eq_left ha]
      have ha' : a = Fin.castSucc ⟨a.val, ha⟩ := Fin.ext rfl
      conv_rhs => rw [ha']
      unfold coordSc
      rw [Fin.snoc_castSucc]
      ring
    · rw [dite_eq_right ha, hlast]
      have ha' : a = Fin.last r := Fin.ext (by have := a.2; simp only [Fin.val_last]; omega)
      subst ha'
      unfold coordSc
      rw [Fin.snoc_last]
      simp
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab]
    ring

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

section

namespace Formalism.L2.SG.Pf.RegroupPf

theorem foldReadyX_K2Level : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), X.LevelSubgroupNormalized →
    Formalism.L2.SG.PoincareInHH.Cut.FoldReadyX X :=
  fun _ X _ => Formalism.L2.SG.PoincareInHH.Cut.foldReadyX_holds X

theorem neatKu_K2Level : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X)
    (u : D.what₂.Word), X.LevelSubgroupNormalized → Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK :=
  fun _ X Y u _ => Formalism.L2.SG.PoincareInHH.Cut.neatKu_of_gamUnipKu X u Y.hK
    (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X u) (Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X u Y.hK)

theorem nDense_RG : NDense := Formalism.L2.SG.Pf.SlabNDensePf.nilradical_strong_approximation

theorem slabCoverC_holds : Formalism.L2.SG.Pf.Slab.SlabCoverC := Formalism.L2.SG.Pf.SlabCoverPf.slab_covering_of_strong_approx nDense_RG Formalism.L2.SG.Pf.nilradical_conj_level'
  (fun _ X u => Formalism.L2.SG.Pf.Level.ratLevi_holds X u) (fun _ X => Formalism.L2.SG.Pf.psiDd_holds X)

theorem regroupC_all : Formalism.L2.SG.Pf.Slab.RegroupC := regrouping_of_neatness (nStrongApproxC_of nDense_RG)
  (orbit_algebra_of_stabilizer term_carrier_holds (stabilizer_of_neat_level neatKu_K2Level)) slabCoverC_holds foldReadyX_K2Level neatKu_K2Level

end Formalism.L2.SG.Pf.RegroupPf
end

section

namespace Formalism.L2.SG.TermOp.Vanish

theorem rational_cocompact_holds : RCocompactC := rCocompactC_of ratApprox_holds ratMem_holds

end Formalism.L2.SG.TermOp.Vanish
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.NormCut Formalism.L2.SG.PackageTie2 Matrix

namespace Formalism.L2.SG.Pf.Act

section Row

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

theorem isoG_one {u : D.what₂.Word} : isoG (1 : Gam X u) = 1 := by
  apply LinearEquiv.ext
  intro y
  apply inclCrd_inj
  rw [isoG_spec]
  show X.B.I.fmat 1 *ᵥ incl X.B.I (X.crd y) = incl X.B.I (X.crd y)
  simp [Formalism.MainNotions.S.AutInst.fmat]

theorem one_mem_gamL {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)
    (q : {Λ // Λ ∈ what₂}) : colD (cs.h (cs.base q.1)) (iotaF X u 1 * cs.h (cs.base q.1)) ∈ X.B.I.Kset := by
  have e : colD (cs.h (cs.base q.1)) (iotaF X u 1 * cs.h (cs.base q.1)) =
      (((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u))⁻¹ * (((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u)) := by
    unfold colD; simp
  rw [e]
  exact Formalism.L2.SG.Pf.LatDictK.dict_K X _ _ {y | X.B.I.fmat (((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u))⁻¹ *ᵥ
    incl X.B.I (X.crd y) ∈ X.B.I.Lf} (fun _ => Iff.rfl) (fun _ => Iff.rfl)

theorem cmap_id {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {x : X.B.I.GA} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hN : SatGramActR.AutFConjN) (hx : RatLink X x β) (hx1 : x = 1) (hβ1 : β = 1)
    {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (c : GQ X u u' F0 F0' Λ Λ') :
    SatGramActR.cmap x β hN hx c = c := by
  subst hx1 hβ1
  by_cases hβ : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')
  · induction c using Quot.ind with
    | mk p =>
      rw [SatGramActR.cmap_pos _ _ _ _ hβ]
      congr 1
      apply Subtype.ext
      show (p.1.1 * (1 : X.B.I.GA)⁻¹, p.1.2 * (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V)⁻¹) = p.1
      simp
  · exact SatGramActR.cmap_neg _ _ _ _ hβ c

theorem tmap_id {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    {x : X.B.I.GA} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hN : SatGramActR.AutFConjN) (hx : RatLink X x β) (hx1 : x = 1) (hβ1 : β = 1)
    (t : GTerm X u u' F0 F0' what₂ rows') : SatGramActR.tmap x β hN hx t = t := by
  obtain ⟨Λ, hΛ, Λ', hΛ', c⟩ := t
  show (⟨Λ, hΛ, Λ', hΛ', SatGramActR.cmap x β hN hx c⟩ : GTerm X u u' F0 F0' what₂ rows') = ⟨Λ, hΛ, Λ', hΛ', c⟩
  rw [cmap_id hN hx hx1 hβ1]

variable {Y : Full X} {u u' : D.what₂.Word}

theorem act_one (q : {Λ // Λ ∈ Y.what₂ u'}) (t : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') :
    KernelOfEmbedding.act Y q ⟨1, one_mem_gamL (Y.cs u') q⟩ t = t :=
  tmap_id _ _ rfl isoG_one t

theorem rowFree_of (hN : ∀ u' : D.what₂.Word, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK)
    (hIR : SatGramRep.IotaRepC) : Formalism.L2.SG.Pf.FibreCounting.RowFree Y := by
  intro u u' s s' h hrow
  obtain ⟨γ, rfl⟩ := KernelOfEmbedding.fib_gam (hN u') h
  have hι := KernelOfEmbedding.iota_act hIR ⟨s.lam', s.mem'⟩ γ s rfl
  have hι2 : iotaOf Y.TR (Y.cs u) (Y.cs u') s =
      iotaOf Y.TR (Y.cs u) (Y.cs u') (KernelOfEmbedding.act Y ⟨s.lam', s.mem'⟩ γ s) := congrArg (fun r => r.2.2) hrow
  rw [hι] at hι2
  have hl : levi Y.TR (SatGramActL.kB (Y.cs u') s.lam' γ.1) = 1 := by
    have h3 : iotaOf Y.TR (Y.cs u) (Y.cs u') s * (levi Y.TR (SatGramActL.kB (Y.cs u') s.lam' γ.1))⁻¹ =
        iotaOf Y.TR (Y.cs u) (Y.cs u') s * 1 := by rw [mul_one]; exact hι2.symm
    exact inv_eq_one.1 (mul_left_cancel h3)
  have hg : gamL_levi (Y.cs u') Y.TR ⟨s.lam', s.mem'⟩ γ =
      gamL_levi (Y.cs u') Y.TR ⟨s.lam', s.mem'⟩ ⟨1, one_mem_gamL (Y.cs u') ⟨s.lam', s.mem'⟩⟩ := by
    apply Subtype.ext
    show levi Y.TR (colD _ _) = levi Y.TR (colD _ _)
    have e1 : colD ((Y.cs u').h ((Y.cs u').base s.lam')) (iotaF X u' γ.1 * (Y.cs u').h ((Y.cs u').base s.lam')) =
        SatGramActL.kB (Y.cs u') s.lam' γ.1 := (aK_eq _ _).symm
    have e2 : colD ((Y.cs u').h ((Y.cs u').base s.lam')) (iotaF X u' 1 * (Y.cs u').h ((Y.cs u').base s.lam')) = 1 := by
      unfold colD; simp
    rw [e1, e2, hl, levi_one]
  have h1 := (gamL_levi_bij (Y.cs u') Y.TR Y.hK (hN u') ⟨s.lam', s.mem'⟩).1 hg
  rw [h1, act_one]

theorem liftIotaFree (hN : ∀ u' : D.what₂.Word, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK)
    (hIR : SatGramRep.IotaRepC) (u u' : D.what₂.Word) (s₁ s₂ : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') (h : s₁.toTerm = s₂.toTerm)
    (hr : rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂) : s₁ = s₂ :=
  rowFree_of hN hIR u u' s₁ s₂ h hr

end Row

end Formalism.L2.SG.Pf.Act
end
end
