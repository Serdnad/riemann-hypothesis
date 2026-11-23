module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurePreservingProdPermThree
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerCoordinateProd
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle094
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlkUUMapMuPRn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
public import Formalism.HermitianCurvature.FrameExists2
import Formalism.FormalDegreeBessel.FinalG
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section pw

variable {k r : ℕ}

theorem hMat_monoP (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) : U.hMat σ d = C2.monoP σ.symm d := by
  ext i a
  simp only [U.hMat, U.wP, C2.monoP, Matrix.mul_diagonal, Matrix.of_apply]
  by_cases h : σ i = a
  · have h' : i = σ.symm a := by rw [← h, Equiv.symm_apply_apply]
    simp [h, h']
  · have h' : ¬ i = σ.symm a := fun hh => h (by rw [hh, Equiv.apply_symm_apply])
    simp [h, h']

theorem headH_eq (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (v : U.LW σ → ℂ) (u : G.UT r → ℂ) :
    U.headH σ d v u = StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)) * C2.monoP σ.symm d * G.upper u := by
  have h := StabilizerDisintegration.UC.permutationMatrix_mul_lowerUnipotent (σ := σ) (fun q => v (StabilizerDisintegration.UC.iota σ q))
  simp only [Equiv.apply_symm_apply] at h
  rw [U.headH, h, Matrix.mul_assoc (StabilizerDisintegration.lowP σ.symm _) (U.wP σ), ← U.hMat, hMat_monoP]

theorem psiC_add (c x y : ℂ) : C2.psiC c (x + y) = C2.psiC c x * C2.psiC c y := by
  unfold C2.psiC
  rw [← Complex.exp_add]
  congr 1
  simp only [mul_add, Complex.add_re, Complex.ofReal_add]

theorem psiC_star_mul (c x : ℂ) : C2.psiC c x * star (C2.psiC c x) = 1 := by
  have key : ∀ t : ℝ, Complex.exp (Complex.I * t) * star (Complex.exp (Complex.I * t)) = 1 := by
    intro t
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    rw [show Complex.I * (t : ℂ) + -Complex.I * (t : ℂ) = 0 by ring, Complex.exp_zero]
  exact key _

end pw

section pwmain

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def Amat (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (x0 : C2.Lstidx σ.symm → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  (C2.monoP σ.symm d)⁻¹ * StabilizerDisintegration.lowS σ.symm x0 * C2.monoP σ.symm d

private theorem mul_mem_utset_of_mem {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m)
    (hB : B ∈ C2.UTset m) : A * B ∈ C2.UTset m := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    rcases lt_or_ge l i with hl | hl
    · rw [hA.1 i l hl, zero_mul]
    · rw [hB.1 l j (lt_of_lt_of_le hji hl), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2 i, hB.2 i, mul_one]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with hl' | hl'
      · rw [hA.1 i l hl', zero_mul]
      · rw [hB.1 l i hl', mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

theorem integrand_pw (S : B.RealPlaceData k r Wp Wq) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (h h' : Mt k r) (hh : Matrix.of h ∈ UWset k r S.z) (hh' : Matrix.of h' ∈ UWset k r S.z')
    (p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ) :
    theta0 S.z σ.symm (TN k r ((h, (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).1),
        (h', (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).2))) •
      D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F
        (TN k r ((h, (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).1),
          (h', (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).2))) =
    chiL σ.symm p.1 • ((S.π (Matrix.of h)).comp
      ((U.psiStar k 0 σ S.z S.z' p.2 • F (U.gaXi k 0 σ d p.2 (fun a => a.elim0)
        ((midB r 0 (Matrix.of h))⁻¹ * γ0 * midB r 0 (Matrix.of h')))).comp (S.π' (Matrix.of h')⁻¹))) := by
  obtain ⟨x0, ⟨⟨y, y'⟩, ⟨⟨a, b⟩, ⟨v, u⟩⟩⟩⟩ := p
  have hhL : Matrix.of h ∈ UWset k (r + 0) (liftVec k r 0 z0) := hz ▸ hh
  have hhL' : Matrix.of h' ∈ UWset k (r + 0) (liftVec k r 0 z0') := hz' ▸ hh'
  have hY := uw_mid r 0 z0 _ hhL
  have hY' := uw_mid r 0 z0' _ hhL'
  have hYu : IsUnit (midB r 0 (Matrix.of h)).det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH hY.1
  have hY'u : IsUnit (midB r 0 (Matrix.of h')).det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH hY'.1
  have hAm : Amat σ d x0 ∈ C2.UTset r := conjS_UT hd x0
  have hAmi : (Amat σ d x0)⁻¹ ∈ C2.UTset r := ut_inv_mem hAm
  have hup : G.upper u ∈ C2.UTset r := StabilizerDisintegration.UC.upper_mem u
  have hprod : (Amat σ d x0)⁻¹ * G.upper u ∈ C2.UTset r := mul_mem_utset_of_mem hAmi hup
  have hV' : G.upper (StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)) = (Amat σ d x0)⁻¹ * G.upper u := ut_of_mem hprod
  have hAmu : IsUnit (Amat σ d x0).det := ut_det hAm
  have hZu : IsUnit (U.hMat σ d).det := by
    rw [U.hMat, Matrix.det_mul, Matrix.det_diagonal]
    exact (Formalism.FourierDecayAlt.P.Dx2.SL.isUnit_wP σ).mul
      (isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => hd a))
  have hγ0u : IsUnit γ0.det := gv_unit hγ0
  have hmat : (G.upper (StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q)))))ᴴ * U.hMat σ d * G.upper (StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)) = U.headH σ d v u := by
    rw [hMat_monoP, orbit_split hd, headH_eq, hV']
    show _ * _ * G.upper (StabilizerDisintegration.utc (Amat σ d x0 * ((Amat σ d x0)⁻¹ * G.upper u))) = _
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAmu, Matrix.one_mul, StabilizerDisintegration.UC.utc_upper]
  have hsgs : B.sgs ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) (U.mMap k r 0 (U.hMat σ d) γ0) =
      U.gaXi k 0 σ d ((y, y'), ((a, b), (v, u))) (fun a => a.elim0) ((midB r 0 (Matrix.of h))⁻¹ * γ0 * midB r 0 (Matrix.of h')) := by
    rw [sgs_formula z0 z0' h h' hhL hhL', rnAct_inv_rnAct hYu, rnAct_inv_rnAct hY'u, hmat, gaXi_zero]
  have hθ : theta0 S.z σ.symm ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) = chiL σ.symm x0 := by
    simp only [theta0, psiR, Equiv.apply_symm_apply, blkU_uMap_muP_Rn, x0c, StabilizerDisintegration.UC.utc_upper]
    show chiL σ.symm ((StabilizerDisintegration.UC.eSp σ.symm).symm (StabilizerDisintegration.UC.eSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))).1 = chiL σ.symm x0
    rw [MeasurableEquiv.symm_apply_apply]
  have hUU : ∀ w : G.UT r → ℂ, Formalism.DoubleCosetMeasures.IsUpUni (G.upper w) := fun w =>
    ⟨fun i j hij => (StabilizerDisintegration.UC.upper_mem w).1 i j hij, (StabilizerDisintegration.UC.upper_mem w).2⟩
  have hr1 : psi k r S.z cStd (U.Rn k r 0 (rnAct (midB r 0 (Matrix.of h)) y)) = psi k r S.z cStd (U.Rn k r 0 y) := by
    have e := psi_rnAct z0 cStd _ hY (rnAct (midB r 0 (Matrix.of h)) y)
    rw [rnAct_inv_rnAct hYu] at e
    rw [hz]
    exact e.symm
  have hr2 : psi k r S.z' cStd (U.Rn k r 0 (rnAct (midB r 0 (Matrix.of h')) y')) = psi k r S.z' cStd (U.Rn k r 0 y') := by
    have e := psi_rnAct z0' cStd _ hY' (rnAct (midB r 0 (Matrix.of h')) y')
    rw [rnAct_inv_rnAct hY'u] at e
    rw [hz']
    exact e.symm
  have hs1 : C2.simpleUp (G.upper (StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))) = C2.simpleUp (StabilizerDisintegration.lowS σ.symm x0)ᴴ +
      C2.simpleUp (StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)))ᴴ := by
    rw [StabilizerDisintegration.UC.upper_fSp]
    exact simpleUp_mul (StabilizerDisintegration.UC.LT_ct (StabilizerDisintegration.UC.lowS_mem σ.symm x0).1)
      (StabilizerDisintegration.UC.LT_ct (StabilizerDisintegration.UC.lowerUnipotent_mem σ.symm _).1)
  have hs2 : C2.simpleUp (G.upper (StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u))) = C2.simpleUp (Amat σ d x0)⁻¹ + C2.simpleUp (G.upper u) := by
    rw [hV']
    exact simpleUp_mul hAmi hup
  have hMu : IsUnit (C2.monoP σ.symm d).det := hMat_monoP σ d ▸ hZu
  have hinv : (U.hMat σ d)⁻¹ * ((StabilizerDisintegration.lowS σ.symm x0)ᴴᴴ)⁻¹ * U.hMat σ d = (Amat σ d x0)⁻¹ := by
    rw [Matrix.conjTranspose_conjTranspose, hMat_monoP]
    show _ = ((C2.monoP σ.symm d)⁻¹ * StabilizerDisintegration.lowS σ.symm x0 * C2.monoP σ.symm d)⁻¹
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hMu]
    simp only [Matrix.mul_assoc]
  have hrelU : C2.psiC cStd (C2.simpleUp (StabilizerDisintegration.lowS σ.symm x0)ᴴ) =
      C2.psiC cStd (C2.simpleUp (Amat σ d x0)⁻¹) := by
    have hQ : (StabilizerDisintegration.lowS σ.symm x0)ᴴ ∈ C2.UTset r := StabilizerDisintegration.UC.LT_ct (StabilizerDisintegration.UC.lowS_mem σ.symm x0).1
    have hQ' : (U.hMat σ d)⁻¹ * ((StabilizerDisintegration.lowS σ.symm x0)ᴴᴴ)⁻¹ * U.hMat σ d ∈ C2.UTset r := by
      rw [hinv]
      exact hAmi
    rw [relevance_U S (U.hMat σ d) hZu γ0 hγ0u hrel _ hQ hQ', hinv]
  have hw : U.wP σ * U.lowW σ v * (U.wP σ)⁻¹ = StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)) := by
    have e := StabilizerDisintegration.UC.conj_lowW σ (fun q => v (StabilizerDisintegration.UC.iota σ q))
    simp only [Equiv.apply_symm_apply] at e
    exact e
  have hright : G.psi U.betaU (U.subS (U.wP σ * U.lowW σ v * (U.wP σ)⁻¹) + U.supS (G.upper u)) =
      C2.psiC cStd (C2.simpleUp (StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)))ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper u))) := by
    rw [StabilizerDisintegration.UC.psi_conj, map_add (f := _), psiC_add, hw, ← StabilizerDisintegration.UC.subS_eq, ← StabilizerDisintegration.UC.psi_conj,
      StabilizerDisintegration.UC.psi_star, StabilizerDisintegration.UC.supS_eq]
  have hstar := psiC_star_mul cStd (C2.simpleUp (Amat σ d x0)⁻¹)
  have hxi : B.xiTau S (1, 1) ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) = U.psiStar k 0 σ S.z S.z' ((y, y'), ((a, b), (v, u))) := by
    rw [xiTau_one, psiStar_zero]
    simp only [psiR, Equiv.apply_symm_apply]
    rw [Formalism.FourierDecayAlt.P.PBG.psi_mul_nset S.z S.z_mem cStd (Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset _ (hUU _))
        (Formalism.FourierDecayAlt.P.Ux3.rn_nset _),
      Formalism.FourierDecayAlt.P.PBG.psi_mul_nset S.z' S.z'_mem cStd (Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset _ (hUU _))
        (Formalism.FourierDecayAlt.P.Ux3.rn_nset _),
      psi_muP S.z S.z_mem, psi_muP S.z' S.z'_mem, hr1, hr2, hs1, hs2, psiC_add, psiC_add, hrelU, hright,
      star_mul', star_mul']
    linear_combination (C2.psiC cStd (C2.simpleUp (StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)))ᴴ) *
      psi k r S.z cStd (U.Rn k r 0 y) * star (C2.psiC cStd (C2.simpleUp (G.upper u))) *
      star (psi k r S.z' cStd (U.Rn k r 0 y'))) * hstar
  have hphi : phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) (x0, ((y, y'), ((a, b), (v, u)))) =
      ((rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q)))), (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u))) := rfl
  rw [hphi]
  dsimp only
  rw [show TN k r ((h, (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) = ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) from rfl,
    D.orbIntegrand, B.rho]
  dsimp only
  rw [hθ, hxi, hsgs, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end pwmain

end Formalism.FourierDecayAlt.P.PBM
end
end

section

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.NFRadRedR

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def LocLog : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∃ O : Set (Q.Mx k r), IsOpen O ∧ (1 : Q.Mx k r) ∈ O ∧ ∃ Λ : Q.Mx k r → Q.Mx k r, ContDiffOn ℝ ∞ Λ O ∧
      ∀ g ∈ O, g ∈ UWset k r z → InLieW k r z (Λ g) ∧ NormedSpace.exp (Λ g) = g

variable {k r : ℕ}

def lieW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Submodule ℝ (Q.Mx k r) where
  carrier := {X | InLieW k r z X}
  zero_mem' := ⟨⟨by simp, fun a _ => ⟨by simp, by simp⟩⟩, by simp⟩
  add_mem' := by
    rintro X Y ⟨⟨hX1, hX2⟩, hX3⟩ ⟨⟨hY1, hY2⟩, hY3⟩
    refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
    · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
        show Xᴴ * Hpk k r + Yᴴ * Hpk k r + (Hpk k r * X + Hpk k r * Y) =
          (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) by abel, hX1, hY1, add_zero]
    · rw [Matrix.add_mulVec, (hX2 a ha).1, (hY2 a ha).1, add_zero]
    · rw [Matrix.add_mulVec, (hX2 a ha).2, (hY2 a ha).2, add_zero]
    · rw [Matrix.add_mulVec, hX3, hY3, add_zero]
  smul_mem' := by
    rintro c X ⟨⟨hX1, hX2⟩, hX3⟩
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
    · rw [Matrix.conjTranspose_smul]
      simp only [RCLike.star_def, RCLike.conj_ofReal]
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX1, smul_zero]
    · rw [Matrix.smul_mulVec, (hX2 a ha).1, smul_zero]
    · rw [Matrix.smul_mulVec, (hX2 a ha).2, smul_zero]
    · rw [Matrix.smul_mulVec, hX3, smul_zero]

def dOpL {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (hπ : Qr.IsRepW k r z π) :
    lieW k r z →ₗ[ℝ] (Wp →L[ℂ] Wp) where
  toFun X := dOp π (X : Q.Mx k r)
  map_add' X Y := (P.differential_operator_linear Wp k r z π hπ X Y X.2 Y.2).1
  map_smul' s X := by
    have h := (P.differential_operator_linear Wp k r z π hπ X X X.2 X.2).2 s
    show dOp π (s • (X : Q.Mx k r)) = s • dOp π (X : Q.Mx k r)
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact h

private lemma rep_exp_smul_eq_exp_dOp {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)} (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) {X : Q.Mx k r} (hX : InLieW k r z X) (t : ℝ) :
    π (NormedSpace.exp ((t : ℂ) • X)) = NormedSpace.exp (t • dOp π X) := by
  set A := dOp π X with hA
  set f : ℝ → (Wp →L[ℂ] Wp) := fun s => π (NormedSpace.exp ((s : ℂ) • X)) with hf
  have hmul : ∀ s u : ℝ, f (s + u) = f s * f u := by
    intro s u
    simp only [hf]
    rw [show ((s + u : ℝ) : ℂ) • X = (s : ℂ) • X + (u : ℂ) • X by push_cast; rw [add_smul],
      Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _),
      hπ.2 _ (exp_uw hX s) _ (exp_uw hX u), ContinuousLinearMap.mul_def]
  have h0 : HasDerivAt f A 0 := dOp_hasDeriv hπ hc hX
  have hd : ∀ s, HasDerivAt f (f s * A) s := by
    intro s
    have h2 : HasDerivAt (fun u => f s * f u) (f s * A) (s - s) := by
      rw [sub_self]
      exact h0.const_mul (f s)
    have h1 : HasDerivAt (fun u => f s * f (u - s)) (f s * A) s := HasDerivAt.comp_sub_const s s h2
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    show f u = f s * f (u - s)
    rw [← hmul]
    congr 1
    ring
  have hg : ∀ s, HasDerivAt (fun u => f u * NormedSpace.exp (u • -A)) 0 s := by
    intro s
    have := (hd s).mul (hasDerivAt_exp_smul_const (-A) s)
    have hcomm : Commute A (NormedSpace.exp (s • -A)) :=
      ((Commute.refl A).neg_right.smul_right s).exp_right
    have h0' : f s * A * NormedSpace.exp (s • -A) + f s * (NormedSpace.exp (s • -A) * -A) = 0 := by
      rw [mul_assoc, hcomm.eq, mul_neg, mul_neg, add_neg_cancel]
    exact this.congr_deriv h0'
  have hconst : ∀ s, f s * NormedSpace.exp (s • -A) = 1 := by
    intro s
    have hdiff : Differentiable ℝ (fun u => f u * NormedSpace.exp (u • -A)) := fun u => (hg u).differentiableAt
    have := is_const_of_deriv_eq_zero hdiff (fun u => (hg u).deriv) s 0
    rw [this]
    simp only [hf, zero_smul, Complex.ofReal_zero, NormedSpace.exp_zero, mul_one, hπ.1]
  have hk : ∀ s, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A)) 0 s := by
    intro s
    have := (hasDerivAt_exp_smul_const (-A) s).mul (hasDerivAt_exp_smul_const A s)
    have hcomm2 : Commute A (NormedSpace.exp (s • A)) := ((Commute.refl A).smul_right s).exp_right
    have h0' : NormedSpace.exp (s • -A) * -A * NormedSpace.exp (s • A) +
        NormedSpace.exp (s • -A) * (NormedSpace.exp (s • A) * A) = 0 := by
      rw [mul_assoc, neg_mul, hcomm2.eq, mul_neg, neg_add_cancel]
    exact this.congr_deriv h0'
  have hinv : NormedSpace.exp (t • -A) * NormedSpace.exp (t • A) = 1 := by
    have hdiff : Differentiable ℝ (fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A)) :=
      fun u => (hk u).differentiableAt
    have := is_const_of_deriv_eq_zero hdiff (fun u => (hk u).deriv) t 0
    rw [this]
    simp only [zero_smul, NormedSpace.exp_zero, mul_one]
  calc f t = f t * (NormedSpace.exp (t • -A) * NormedSpace.exp (t • A)) := by rw [hinv, mul_one]
    _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hconst t, one_mul]

private lemma contDiff_exp_hermitian_curvature {A : Type} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    ContDiff ℝ ∞ (NormedSpace.exp : A → A) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  exact (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt

theorem repSmooth_of (hLL : LocLog) : NFRadRedS.RepSmooth := by
  unfold NFRadRedS.RepSmooth
  intro Wp _ _ _ k r z π hz hTz hπ hc h₀ hh₀
  obtain ⟨O, hO, h1O, Λ, hΛ, hΛe⟩ := hLL k r z hz hTz
  have hrep : Qr.IsRepW k r z π := ⟨hπ, hc⟩
  have hdetH : IsUnit (Hpk k r).det := by
    have h := congrArg Matrix.det (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r)
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
  have hdet0 : IsUnit h₀.det := ((Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) hdetH).2.2 h₀ hh₀.1).1
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (lieW k r z)
  let T : Q.Mx k r →ₗ[ℝ] (Wp →L[ℂ] Wp) := (dOpL z π hrep).comp (Submodule.linearProjOfIsCompl _ q hq)
  have hT1 : ∀ Y, InLieW k r z Y → T Y = dOp π Y := by
    intro Y hY
    have hp := Submodule.linearProjOfIsCompl_apply_left hq ⟨Y, hY⟩
    show dOpL z π hrep (Submodule.linearProjOfIsCompl _ q hq Y) = dOp π Y
    rw [show Submodule.linearProjOfIsCompl _ q hq Y = ⟨Y, hY⟩ from hp]
    rfl
  let Tc := LinearMap.toContinuousLinearMap T
  let Lm : Q.Mx k r →ₗ[ℝ] Q.Mx k r :=
    { toFun := fun h => h₀⁻¹ * h
      map_add' := fun a b => Matrix.mul_add _ _ _
      map_smul' := fun c a => by simp [Matrix.mul_smul] }
  let Lc := LinearMap.toContinuousLinearMap Lm
  have hV : IsOpen {h : Q.Mx k r | h₀⁻¹ * h ∈ O} := hO.preimage Lc.continuous
  refine ⟨{h : Q.Mx k r | h₀⁻¹ * h ∈ O}, hV, ?_, fun h => π h₀ * NormedSpace.exp (Tc (Λ (h₀⁻¹ * h))), ?_, ?_⟩
  · show h₀⁻¹ * h₀ ∈ O
    rw [Matrix.nonsing_inv_mul h₀ hdet0]
    exact h1O
  · have h1 : ContDiffOn ℝ ∞ (fun h => Λ (Lc h)) {h : Q.Mx k r | h₀⁻¹ * h ∈ O} :=
      hΛ.comp Lc.contDiff.contDiffOn (fun h hh => hh)
    exact contDiffOn_const.mul (contDiff_exp_hermitian_curvature.comp_contDiffOn (Tc.contDiff.comp_contDiffOn h1))
  · intro h hV' hU
    have hg : h₀⁻¹ * h ∈ UWset k r z := Formalism.QuantumDeterminants.WeylGroupFacts.uw_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh₀) hU
    obtain ⟨hlie, hexp⟩ := hΛe _ hV' hg
    have hpi := rep_exp_smul_eq_exp_dOp hπ hc hlie 1
    simp only [Complex.ofReal_one, one_smul] at hpi
    rw [hexp] at hpi
    calc π h = π (h₀ * (h₀⁻¹ * h)) := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv h₀ hdet0, Matrix.one_mul]
      _ = (π h₀).comp (π (h₀⁻¹ * h)) := hπ.2 _ hh₀ _ hg
      _ = π h₀ * NormedSpace.exp (Tc (Λ (h₀⁻¹ * h))) := by
          rw [ContinuousLinearMap.mul_def, hpi,
            show Tc (Λ (h₀⁻¹ * h)) = dOp π (Λ (h₀⁻¹ * h)) from hT1 _ hlie]

end Formalism.FourierDecayAlt.P.NFRadRedR

namespace Formalism.FourierDecayAlt.P

theorem representation_smooth_of_log : NFRadRedR.LocLog → NFRadRedS.RepSmooth := fun h => NFRadRedR.repSmooth_of h

end Formalism.FourierDecayAlt.P
end
end
