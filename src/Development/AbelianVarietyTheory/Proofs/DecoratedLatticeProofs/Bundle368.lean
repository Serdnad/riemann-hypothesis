module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle284
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle346
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle271
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle021
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle205
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle313
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF

@[expose] public section

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnnAnnih

theorem blockMatrix_swap_mul_top_rows_eq_bottom_rows {n k : ℕ} (M : Matrix (Fin (n + n)) (Fin k) ℂ) :
    (blk4 (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0 * M).submatrix (fun i => finSumFinEquiv (Sum.inl i)) id =
      M.submatrix (fun i => finSumFinEquiv (Sum.inr i)) id := by
  have hM : M = (M.submatrix finSumFinEquiv id).submatrix finSumFinEquiv.symm id := by ext; simp
  rw [hM, blk4, Matrix.submatrix_mul_equiv]
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem row_sub_mul {a b k l : ℕ} (M : Matrix (Fin a) (Fin k) ℂ) (N : Matrix (Fin k) (Fin l) ℂ) (r : Fin b → Fin a) :
    M.submatrix r id * N = (M * N).submatrix r id := by
  ext i j
  simp [Matrix.mul_apply]

variable {D : D7}

theorem qX_mul_stdInv (A : HSp D) (μ : D.host.E) (hμ : IsSkew μ) (s : RealMat (dblSp A)) (hs : IsStdInv A μ s)
    (τ : D.what₂.Tau) :
    (dblDec A).qX.map (tauE D τ) * s τ = ((‖tauE D τ μ‖ : ℂ)⁻¹) • (dblDec A).qY.map (tauE D τ) := by
  obtain ⟨-, hdet, hinv⟩ := GlobalTheory.T.doubledBasisSkewColumnMatrix_gram_inverse D A μ hμ
  have hRT : (Tm A μ)⁻¹ * Tm A μ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hTR : Tm A μ * (Tm A μ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h1 : ((Tm A μ)⁻¹).map (tauE D τ) * (Tm A μ).map (tauE D τ) = 1 := by
    rw [← Matrix.map_mul, hRT, Matrix.map_one _ (tauE D τ).map_zero (tauE D τ).map_one]
  have h2 : (Tm A μ).map (tauE D τ) * ((Tm A μ)⁻¹).map (tauE D τ) = 1 := by
    rw [← Matrix.map_mul, hTR, Matrix.map_one _ (tauE D τ).map_zero (tauE D τ).map_one]
  have hqX : (dblDec A).qX.map (tauE D τ) =
      (((Tm A μ)⁻¹).map (tauE D τ)).submatrix (fun i => finSumFinEquiv (Sum.inl i)) id := by
    rw [hinv]; ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl]
  have hqY : (μ⁻¹ • (dblDec A).qY).map (tauE D τ) =
      (((Tm A μ)⁻¹).map (tauE D τ)).submatrix (fun i => finSumFinEquiv (Sum.inr i)) id := by
    rw [hinv]; ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inr]
  have hμ0 : tauE D τ μ ≠ 0 := (map_ne_zero (tauE D τ)).2 hμ.1
  have hn0 : (‖tauE D τ μ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hμ0)
  have hsτ : s τ * (Tm A μ).map (tauE D τ) = (Tm A μ).map (tauE D τ) * stdInv A.rank μ τ := hs τ
  have hsR : ((Tm A μ)⁻¹).map (tauE D τ) * s τ = stdInv A.rank μ τ * ((Tm A μ)⁻¹).map (tauE D τ) := by
    calc ((Tm A μ)⁻¹).map (tauE D τ) * s τ
          = ((Tm A μ)⁻¹).map (tauE D τ) * (s τ * ((Tm A μ).map (tauE D τ) * ((Tm A μ)⁻¹).map (tauE D τ))) := by
          rw [h2, Matrix.mul_one]
      _ = ((Tm A μ)⁻¹).map (tauE D τ) * ((Tm A μ).map (tauE D τ) * stdInv A.rank μ τ) *
            ((Tm A μ)⁻¹).map (tauE D τ) := by
          rw [← Matrix.mul_assoc (s τ), hsτ]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hqX, row_sub_mul, hsR, stdInv, Matrix.smul_mul]
  have hb := blockMatrix_swap_mul_top_rows_eq_bottom_rows (((Tm A μ)⁻¹).map (tauE D τ))
  rw [← hqY] at hb
  ext i j
  have hij := congrFun (congrFun hb i) j
  simp only [Matrix.submatrix_apply, Matrix.smul_apply, id] at hij ⊢
  rw [hij]
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
  field_simp

end GlobalTheory.StdUnnAnnih

namespace GlobalTheory.StdUnnAnnih

theorem re_imaginary_mul_neg_I_div_mul {a w : ℂ} (hre : a.re = 0) (him : 0 < a.im) (r : ℝ) :
    (a * (-(Complex.I / (r : ℂ))) * w).re = ‖a‖ / r * w.re := by
  have hn : ‖a‖ = a.im := by
    rw [Complex.norm_def, Complex.normSq_apply, hre, zero_mul, zero_add, Real.sqrt_mul_self him.le]
  have ha : a = (a.im : ℂ) * Complex.I := Complex.ext (by simp [hre]) (by simp)
  rw [hn, ha]
  have : (a.im : ℂ) * Complex.I * (-(Complex.I / (r : ℂ))) = ((a.im / r : ℝ) : ℂ) := by
    push_cast
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (-(a.im : ℂ) * (r : ℂ)⁻¹) * Complex.I_sq
  rw [this, Complex.re_ofReal_mul]
  simp

theorem annih_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ l : D.what₂.Tau → ℝ, (∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖) → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (X : Matrix (Fin B.rank) (Fin A.rank) ℂ), sch ψ A B ν 𝓨 (annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) (X * (dblDec A).qX.map (tauE D τ)) f) = annS B l sB θ τ X (sch ψ A B ν 𝓨 f) := by
  intro D ψ hψ θ hθ A B ν 𝓨 hcov μ hμ s' sB hs hsB l hl f hf τ X
  have hJ : cplxO (s' τ) (sB τ) (X * (dblDec A).qX.map (tauE D τ)) =
      ((Complex.I / (‖tauE D τ μ‖ : ℂ)) • (sB τ * X)) * (dblDec A).qY.map (tauE D τ) := by
    unfold cplxO
    rw [Matrix.mul_assoc (sB τ), Matrix.mul_assoc X, qX_mul_stdInv A μ hμ s' hs τ, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← Matrix.mul_assoc, div_eq_mul_inv]
  set Y := (Complex.I / (‖tauE D τ μ‖ : ℂ)) • (sB τ * X) with hY
  have hd1 := GlobalTheory.OrientedHeis.theta_dRho (S := dblSp A) (T := B) hθ hψ τ (X * (dblDec A).qX.map (tauE D τ)) hf
  have hd2 := GlobalTheory.OrientedHeis.theta_dRho (S := dblSp A) (T := B) hθ hψ τ (Y * (dblDec A).qY.map (tauE D τ)) hf
  obtain ⟨-, hsm, -, hsmul⟩ := GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hψ A B ν 𝓨 hcov _ _ hd2 hd2 Complex.I
  obtain ⟨-, -, hadd, -⟩ := GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hψ A B ν 𝓨 hcov _ _ hd1 hsm 0
  funext x
  rw [annih, hJ, hadd, hsmul, Pi.add_apply, Pi.smul_apply, GlobalTheory.T.heisenbergDerivative_diagonalHalf_eq_schrodingerDerivative D ψ hψ θ hθ A B ν 𝓨 hcov f hf τ X x,
    GlobalTheory.T.schrodinger_dualHalf_derivative_linear_form D ψ hψ θ hθ A B ν 𝓨 hcov f hf τ Y x]
  unfold annS linF
  congr 1
  obtain ⟨hss, hiso, -⟩ := hsB τ
  have hsG : (sB τ)ᴴ * gramAt D B τ = gramAt D B τ * sB τ := by
    calc (sB τ)ᴴ * gramAt D B τ = (sB τ)ᴴ * gramAt D B τ * (sB τ * sB τ) := by rw [hss, Matrix.mul_one]
      _ = gramAt D B τ * sB τ := by rw [← Matrix.mul_assoc, hiso]
  have htr : Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x) =
      -(Complex.I / (‖tauE D τ μ‖ : ℂ)) * Matrix.trace (Xᴴ * (gramAt D B τ * sB τ) * compAt θ τ x) := by
    rw [hY, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc Xᴴ, hsG]
    congr 1
    simp [Complex.conj_ofReal, div_eq_mul_inv]
  have key : (tauE D τ D.host.xi0 * Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x)).re =
      |l τ| * (Matrix.trace (Xᴴ * (gramAt D B τ * sB τ) * compAt θ τ x)).re := by
    rw [htr, ← mul_assoc, re_imaginary_mul_neg_I_div_mul (Formalism.IndefR.Fock.CCR.realPlace_imaginaryGenerator_re_eq_zero D τ) (Formalism.L2.Theta.xi_zero_im_pos D τ), hl τ]
  rw [key, smul_eq_mul]
  push_cast
  linear_combination (-(4 : ℂ) * Real.pi * ((|l τ| : ℝ) : ℂ) *
    ((Matrix.trace (Xᴴ * (gramAt D B τ * sB τ) * compAt θ τ x)).re : ℂ) * sch ψ A B ν 𝓨 f x) * Complex.I_sq

end GlobalTheory.StdUnnAnnih
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.AdForm GlobalTheory.AdForm.RdVal
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop.LComm

variable {D : D7}

theorem exists_finM (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (V.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ a : GA D V, GlobalTheory.AdForm.finM V hn a = y.1.1 := by
  subst hn
  obtain ⟨a, -, e⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V ⟨y.1, y.2⟩
  refine ⟨a, ?_⟩
  have e2 := congrArg Subtype.val e
  have e3 := congrArg Units.val e2
  exact e3



theorem rdS_inj (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
    (yc : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hbij : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (ψ ψ' : cl → Frames (gramC (V.gram.reindex (finCongr hn) (finCongr hn)) (embT D)) → ℂ)
    (h : ∀ y, rdS θ V hn S yc ψ y = rdS θ V hn S yc ψ' y) : ψ = ψ' := by
  funext c z
  obtain ⟨g, hg⟩ := exists_finM V hn (yc c)
  have hex : ∃ p, IsDec S yc (finM V hn g) p := by
    refine ⟨(c, 1, 1), Subgroup.one_mem _, ?_⟩
    simp [hg]
  have hp := hex.choose_spec
  have hc : hex.choose.1 = c := by
    apply hbij.1
    refine (@DoubleCoset.eq _ _ _ _ _ _).mpr ?_
    have hr : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) hex.choose.2.1 ∈
        ratPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
      Subgroup.mem_map.mpr ⟨_, hp.1, rfl⟩
    have hk : hex.choose.2.2.1 ∈ UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
      ((S.U_eq _).1 hex.choose.2.2.2).1
    have he : (yc c).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) hex.choose.2.1 * (yc hex.choose.1).1 *
        hex.choose.2.2.1 := Units.ext (hg.symm.trans hp.2)
    have hγ : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) hex.choose.2.1 ∈
        UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
      have : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) hex.choose.2.1 =
          (yc c).1 * (hex.choose.2.2.1)⁻¹ * ((yc hex.choose.1).1)⁻¹ := by rw [he]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (yc c).2 (Subgroup.inv_mem _ hk)) (Subgroup.inv_mem _ (yc _).2)
    exact ⟨⟨_, hγ⟩, Subgroup.mem_subgroupOf.mpr hr, ⟨_, hk⟩, Subgroup.mem_subgroupOf.mpr hex.choose.2.2.2, Subtype.ext he⟩
  set A : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := fun τ =>
    atInf (embT D) ((hex.choose.2.1)⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ with hA
  have hAu : ∀ τ, IsUnit (A τ).det := by
    intro τ
    rw [hA, Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse (atInf_mul_inv hex.choose.2.1 τ)).mul (infM_unit θ V hn g τ)
  have hy : ∀ τ, IsUnit ((A τ)⁻¹ * z.1 τ).det := by
    intro τ
    rw [Matrix.det_mul]
    exact (Matrix.isUnit_nonsing_inv_det _ (hAu τ)).mul (z.2 τ)
  have key := congrFun (h ⟨fun τ => (A τ)⁻¹ * z.1 τ, hy⟩) g
  have hz : (fun τ => atInf (embT D) ((hex.choose.2.1)⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ * ((A τ)⁻¹ * z.1 τ)) = z.1 := by
    funext τ
    show A τ * ((A τ)⁻¹ * z.1 τ) = _
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hAu τ), Matrix.one_mul]
  unfold rdS at key
  rw [dite_eq_left hex, dite_eq_left hex] at key
  dsimp only at key
  rw [hz, atFr, atFr, dite_eq_left z.2, dite_eq_left z.2, hc] at key
  exact mul_left_cancel₀ (Units.ne_zero _) key

theorem chart0_inj {u : D.what₂.Word} (F : Forms0 D u) (θ : InfFam D) (ψ ψ' : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)
    (h : ∀ y, (GlobalTheory.Core.Mi.chart0 F).rd θ ψ y = (GlobalTheory.Core.Mi.chart0 F).rd θ ψ' y) : ψ = ψ' := by
  have := rdS_inj θ (D.sp.X 0) (rankN D 0 (Nat.zero_le _)) F.cls0.lev F.cls0.y F.cls0.y_bij
    (fun c z => ψ c (F.val0.eY.symm z)) (fun c z => ψ' c (F.val0.eY.symm z)) (fun y => by
      have := h (F.val0.eY.symm y)
      unfold Chart.rd at this
      rw [show (GlobalTheory.Core.Mi.chart0 F).eY (F.val0.eY.symm y) = y from F.val0.eY.apply_symm_apply y] at this
      exact this)
  funext c y
  have h2 := congrFun (congrFun this c) (F.val0.eY y)
  simpa using h2

theorem iter_equiv {M β : Type} [NormedAddCommGroup M] [Module ℂ M] (S : β → M ≃ₗ[ℂ] M) (r : β → ℝ) (hr : ∀ b, 0 < r b)
    (hS : ∀ b φ, ‖S b φ‖ = r b * ‖φ‖) (ε : ℕ → β) (n : ℕ) :
    ∃ (A : M ≃ₗ[ℂ] M) (a : ℝ), 0 < a ∧ (∀ φ, ‖A φ‖ = a * ‖φ‖) ∧ ∀ φ, A φ = GlobalTheory.SeeSaw.iterS (fun b => S b) ε n φ := by
  induction n with
  | zero => exact ⟨LinearEquiv.refl ℂ M, 1, one_pos, fun φ => by simp, fun φ => rfl⟩
  | succ n ih =>
    obtain ⟨A, a, ha, h1, h2⟩ := ih
    refine ⟨A.trans (S (ε (2 * n))), r (ε (2 * n)) * a, mul_pos (hr _) ha, fun φ => ?_, fun φ => ?_⟩
    · rw [LinearEquiv.trans_apply, hS, h1, mul_assoc]
    · rw [LinearEquiv.trans_apply, h2]; rfl

theorem iterS_comm {α α' β : Type} (S : β → α → α) (S' : β → α' → α') (j : α → α') (h : ∀ b x, S' b (j x) = j (S b x))
    (ε : ℕ → β) (n : ℕ) (x : α) : GlobalTheory.SeeSaw.iterS S' ε n (j x) = j (GlobalTheory.SeeSaw.iterS S ε n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show S' _ (GlobalTheory.SeeSaw.iterS S' ε n (j x)) = j (S _ (GlobalTheory.SeeSaw.iterS S ε n x))
    rw [ih, h]

end GlobalTheory.MiTop.LComm
end

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.LatIndSB

theorem indicator_latO_mem_SB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M'), Set.indicator {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} (fun _ => (1 : ℂ)) ∈ SB (Matrix P.Y P.Y' P.k) := by
  intro D ψ S T M M' hM hM' P
  classical
  have hset : {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} =
      (((latO S T (M : Set _) (M' : Set _) fun _ => True).comap (GlobalTheory.LocMod.Witness.upH (ofSplit P.q) P.FS P.FT) : AddSubgroup _) : Set (Matrix P.Y P.Y' P.k)) := by
    obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem P.q
    ext x
    refine ⟨fun h => GlobalTheory.PlaceModel.latO_le_top _ h, fun h => ?_⟩
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε P.q.split.1 heε h).1
    have hh : (ofSplit P.q).up P.FS P.FT x ∈ GlobalTheory.PlaceModel.half S T P.q.e :=
      (GlobalTheory.PlaceModel.isHalf_iff S T).1 (GlobalTheory.LocMod.Witness.up_half (ofSplit P.q) P.FS P.FT x)
    have h3 : P.q.e • (ofSplit P.q).up P.FS P.FT x = (ofSplit P.q).up P.FS P.FT x := (GlobalTheory.PlaceModel.mem_half S T).1 hh
    change P.q.e • (ofSplit P.q).up P.FS P.FT x ∈ (latO S T (M : Set _) (M' : Set _) fun w => w = P.q.v) at h2
    rw [h3] at h2
    exact h2
  rw [hset]
  have ho := GlobalTheory.LocMod.Witness.lat_open (ofSplit P.q) P.FS P.FT hM hM'
  have hc := GlobalTheory.LocMod.Witness.lat_compact (ofSplit P.q) P.FS P.FT hM hM'
  have hcl := AddSubgroup.isClosed_of_isOpen _ ho
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · by_cases hx : x ∈ (((latO S T (M : Set _) (M' : Set _) fun _ => True).comap
        (GlobalTheory.LocMod.Witness.upH (ofSplit P.q) P.FS P.FT) : AddSubgroup _) : Set (Matrix P.Y P.Y' P.k))
    · exact ⟨_, ho, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
    · exact ⟨_, hcl.isOpen_compl, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  · exact HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _

end GlobalTheory.LatIndSB

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColsConj

theorem form_mulVec {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (A : Fin N → k)
    (G : Fin N → Fin N → k) (β : Matrix (Fin N) Y k) (m₁ : Y) (c₁ : k)
    (h1 : ∑ r, ∑ r', A r * G r r' * β r' m₁ = c₁) (h0 : ∀ m, m ≠ m₁ → ∑ r, ∑ r', A r * G r r' * β r' m = 0)
    (w : Y → k) : ∑ r, ∑ r', A r * G r r' * (β *ᵥ w) r' = c₁ * w m₁ := by
  have h : ∑ r, ∑ r', A r * G r r' * (β *ᵥ w) r' = ∑ m, (∑ r, ∑ r', A r * G r r' * β r' m) * w m := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (s := (Finset.univ : Finset Y))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset Y))]
    refine Finset.sum_congr rfl fun r' _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [h, Finset.sum_eq_single m₁ (fun m _ hm => by rw [h0 m hm, zero_mul]) (fun hm => absurd (Finset.mem_univ _) hm), h1]

theorem conj_part_mem_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (u u' : Fin S.rank → D.host.E) (m₁ : Y) (c₁ : k), IsSelfDualC S L → IntIn q S F L → valuation k c₁ = 1 → (∀ r, F.β r m₁ = c₁ * (ofSplit q).pr (u' r)) → (∑ r, ∑ r', star (u r) * S.gram r r' * u' r' = 1) → (∀ m, m ≠ m₁ → ∑ r, ∑ r', (ofSplit q).pr (star (u r)) * (ofSplit q).pr (S.gram r r') * F.β r' m = 0) → ∀ a : AE D, ((fun r => cA D q.e * (a * incA D (u r))) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ q.pr (cA D a) ∈ 𝒪[k]) := by
  intro D k _ _ _ _ q S L Y _ _ F u u' m₁ c₁ hL hI hc hb hd hp a
  have hpr : ∀ x : D.host.E, (ofSplit q).pr x = q.pr (incA D x) := fun _ => rfl
  simp only [hpr] at hb hp
  have hy : (fun r => cA D q.e * (a * incA D (u r))) =
      fun r => cA D (q.sec (q.pr (cA D a) * q.pr (incA D (star (u r))))) := by
    funext r
    rw [← RingHom.map_mul, q.sec_pr, RingHom.map_mul, RingHom.map_mul, GlobalTheory.LatVac.cA_cA,
      GlobalTheory.FinPl.FrameLat.cA_incA, star_star]
  have h1 : ∑ r, ∑ r', q.pr (incA D (star (u r))) * q.pr (incA D (S.gram r r')) * F.β r' m₁ = c₁ := by
    have h := congrArg (fun x => c₁ * q.pr (incA D x)) hd

    simp only [map_sum, RingHom.map_mul, RingHom.map_one, mul_one, Finset.mul_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
    rw [hb]; ring
  have key : ∀ w : Y → k, ∑ i, ∑ j, (F.β *ᵥ w) i * q.pr (cA D (incA D (S.gram i j))) *
      (q.pr (cA D a) * q.pr (incA D (star (u j)))) = q.pr (cA D a) * (c₁ * w m₁) := by
    intro w
    rw [← form_mulVec _ _ F.β m₁ c₁ h1 hp w, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.FinPl.FrameLat.cA_incA, GlobalTheory.LatVac.gram_star]; ring
  rw [hy, GlobalTheory.FinPl.FrameLat.csec_mem_iff hL]
  constructor
  · intro h
    have hw : ∀ i, (Pi.single m₁ (1 : k) : Y → k) i ∈ 𝒪[k] := fun i => by
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h2 := h _ ((hI _).1 hw)
    rw [key, Pi.single_eq_same, mul_one] at h2
    rw [Valuation.mem_integer_iff] at h2 ⊢
    rwa [map_mul, hc, mul_one] at h2
  · intro ha x hx
    have hxe : x = F.β *ᵥ (F.γ *ᵥ x) := by rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
    have hw : ∀ i, (F.γ *ᵥ x) i ∈ 𝒪[k] := (hI _).2 (by rw [← hxe]; exact hx)
    rw [hxe, key]
    exact mul_mem ha (mul_mem ((Valuation.mem_integer_iff _ _).2 hc.le) (hw m₁))

end GlobalTheory.ColsConj
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColsWPart

theorem wpart_mem_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (u : Fin S.rank → D.host.E) (m₀ : Y) (c₀ : k), IntIn q S F L → valuation k c₀ = 1 → (∀ r, F.β r m₀ = c₀ * (ofSplit q).pr (u r)) → ∀ a : AE D, ((fun r => q.e * (a * incA D (u r))) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ q.pr a ∈ 𝒪[k]) := by
  intro D k _ _ _ _ q S L Y _ _ F u m₀ c₀ hI hc hcol a
  have hc0 : c₀ ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact zero_ne_one hc
  have heq : (fun i => q.sec ((F.β *ᵥ Pi.single m₀ (q.pr a / c₀)) i)) = fun r => q.e * (a * incA D (u r)) := by
    funext r
    have h1 : (F.β *ᵥ Pi.single m₀ (q.pr a / c₀)) r = F.β r m₀ * (q.pr a / c₀) := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h1, hcol r, ← q.sec_pr, map_mul q.pr]
    congr 1
    show c₀ * q.pr (incA D (u r)) * (q.pr a / c₀) = q.pr a * q.pr (incA D (u r))
    field_simp
  rw [← heq, ← hI (Pi.single m₀ (q.pr a / c₀))]
  have hdiv : q.pr a / c₀ ∈ 𝒪[k] ↔ q.pr a ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, map_div₀, hc, div_one]
  constructor
  · intro h
    have := h m₀
    rw [Pi.single_eq_same] at this
    exact hdiv.1 this
  · intro h i
    by_cases hi : i = m₀
    · subst hi; rw [Pi.single_eq_same]; exact hdiv.2 h
    · rw [Pi.single_eq_of_ne hi]; exact zero_mem _

end GlobalTheory.ColsWPart
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.MovedDat

def RdAt {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (x : G.S.P.J)
    (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)) : Prop :=
  ∀ (a b : Fin D.R.k ⊕ Fin (G.s + 1)) (a' b' : Fin D.R.r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a →
    b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = g.val a' b' →
      valuation G.k ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E)) < 1

end GlobalTheory.MovedDat

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace

variable {D : D7} {c : Comm D} {v : VCom c}

def IsMatrixInFrameOfXZero (G : GLoc v) (κ : GA D (c.X 0)) (g : GL (XIx (Fin D.R.k) (Fin D.R.t) 0) G.k) : Prop :=
  (mt (c.X 0) κ).map G.q.pr = (G.FX 0 (Nat.zero_le _)).β * g.val * (G.FX 0 (Nat.zero_le _)).γ

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word}

end GlobalTheory.FamTrace

end
end
