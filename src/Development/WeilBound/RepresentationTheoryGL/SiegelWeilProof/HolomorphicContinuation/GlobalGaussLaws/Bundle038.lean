module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialSchwartzKilledByLongAnnihilation
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockMatrixTwoByTwoFinStandardSkewMap
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle238
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle262
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle095
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle242
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle018
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle024
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle026
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle025
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle020
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle037
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle033
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle031

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}




theorem dirAt_ne {m : ℕ} {τ τ' : D.what₂.Tau} (h : τ' ≠ τ) (Z : Matrix (Fin m) (Fin n) ℂ) :
    GlobalTheory.FockAnnKill.dirAt τ Z τ' = 0 := by
  exact if_neg h

theorem dirAt_self {m : ℕ} (τ : D.what₂.Tau) (Z : Matrix (Fin m) (Fin n) ℂ) : GlobalTheory.FockAnnKill.dirAt τ Z τ = Z := by
  exact if_pos rfl

theorem gAway_dirAt (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin n) ℂ) : gAway V l s τ (GlobalTheory.FockAnnKill.dirAt τ Z) = 1 := by
  classical
  show Complex.exp (-(2 * (Real.pi : ℂ)) * ∑ τ' with τ' ≠ τ, ((|l τ'| : ℝ) : ℂ) *
      ((GlobalTheory.FockAnnKill.dirAt τ Z τ').conjTranspose * (Formalism.BasicNotions.TH.gramAt D V τ' * s τ') *
        GlobalTheory.FockAnnKill.dirAt τ Z τ').trace) = 1
  rw [Finset.sum_eq_zero fun τ' hτ' => by rw [dirAt_ne (Finset.mem_filter.mp hτ').2 Z]; simp,
    mul_zero, Complex.exp_zero]

theorem trace_conjTranspose_mul_self {m : ℕ} (u : Matrix (Fin m) (Fin n) ℂ) :
    Matrix.trace (uᴴ * u) = ((∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.conj_mul']
  push_cast
  exact Finset.sum_comm

theorem gauss_dirAt {V : HSp D} {τ : D.what₂.Tau} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr)
    (l : D.what₂.Tau → ℝ) (u : Matrix (Fin V.rank) (Fin n) ℂ) :
    gauss V l s (GlobalTheory.FockAnnKill.dirAt τ (fr * u)) = gs (cLoc l τ) u := by
  show Complex.exp (-(2 * (Real.pi : ℂ)) * ∑ τ', ((|l τ'| : ℝ) : ℂ) *
      ((GlobalTheory.FockAnnKill.dirAt τ (fr * u) τ').conjTranspose * (Formalism.BasicNotions.TH.gramAt D V τ' * s τ') *
        GlobalTheory.FockAnnKill.dirAt τ (fr * u) τ').trace) =
    Complex.exp (-(((2 * Real.pi * |l τ|) * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ) : ℂ))
  have key : (fr * u)ᴴ * (Formalism.BasicNotions.TH.gramAt D V τ * s τ) * (fr * u) = uᴴ * u := by
    rw [Matrix.conjTranspose_mul,
      show uᴴ * frᴴ * (Formalism.BasicNotions.TH.gramAt D V τ * s τ) * (fr * u) =
        uᴴ * (frᴴ * (Formalism.BasicNotions.TH.gramAt D V τ * s τ) * fr) * u by simp only [Matrix.mul_assoc],
      hfr.2.2, Matrix.mul_one]
  rw [Finset.sum_eq_single τ (fun τ' _ h => by rw [dirAt_ne h]; simp)
      (fun h => absurd (Finset.mem_univ τ) h), dirAt_self, key, trace_conjTranspose_mul_self]
  congr 1
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace PositivityTheory.Rg.Sw.Glob.AW

variable {D : D7} {n : ℕ}

def cθ (θ : InfFam D) (τ : D.what₂.Tau) : AE D →+* ℂ := (θ τ).comp (infPart D)

theorem compAt_eq {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} (w : Mx D m k) : compAt θ τ w = w.map (cθ θ τ) := rfl

theorem compAt_mul' {θ : InfFam D} {τ : D.what₂.Tau} {m k l : ℕ} (x : Mx D m k) (y : Mx D k l) :
    compAt θ τ (x * y : Mx D m l) = compAt θ τ x * compAt θ τ y := by
  simp only [compAt_eq]; exact Matrix.map_mul

theorem compAt_one' {θ : InfFam D} {τ : D.what₂.Tau} {k : ℕ} : compAt θ τ (1 : Mx D k k) = 1 := by
  simp only [compAt_eq]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem compAt_zero' {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} : compAt θ τ (0 : Mx D m k) = 0 := by
  ext i j; simp [compAt_eq]

theorem compAt_add' {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} (x y : Mx D m k) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j; simp [compAt_eq]

theorem component_block_matrix {θ : InfFam D} {τ : D.what₂.Tau} (a b c d : Mx D n n) :
    compAt θ τ (blk4 a b c d : Mx D (n + n) (n + n)) = blk4 (compAt θ τ a) (compAt θ τ b) (compAt θ τ c) (compAt θ τ d) :=
  GlobalTheory.StdUnn.Frame.block_matrix_map _ a b c d

theorem ae_ext {θ : InfFam D} (hθ : IsInfFam θ) {z z' : AE D} (h1 : ∀ τ, cθ θ τ z = cθ θ τ z')
    (h2 : finPart D z = finPart D z') : z = z' := by
  have h := (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 (z - z') (fun τ => by
      have := h1 τ
      simp only [cθ, RingHom.comp_apply] at this
      rw [RingHom.map_sub, RingHom.map_sub, this, sub_self])
    (by rw [RingHom.map_sub, h2, sub_self])
  exact sub_eq_zero.mp h

theorem mx_ext {θ : InfFam D} (hθ : IsInfFam θ) {m k : ℕ} {x x' : Mx D m k} (h1 : ∀ τ, compAt θ τ x = compAt θ τ x')
    (h2 : x.map (finPart D) = x'.map (finPart D)) : x = x' := by
  ext i j
  exact ae_ext hθ (fun τ => congrFun (congrFun (h1 τ) i) j) (congrFun (congrFun h2 i) j)

theorem cθ_cA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : AE D) : cθ θ τ (cA D z) = conj (cθ θ τ z) :=
  (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.1 z τ

theorem finPart_cA (z : AE D) : finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      ((Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) z) =
    (Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F)) D.sp.cm.sig)
      ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) z)
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
  rfl

end PositivityTheory.Rg.Sw.Glob.AW
end
end

section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}




theorem compFin_eq_finPart (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (z : AE D) :
    compFin D.host.F D.host.E v z =
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)) (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem reidx_conjTranspose_mul (y : M2 n) : (reidx y)ᴴ * reidx y = reidx (yᴴ * y) := by
  simp only [reidx, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

theorem reidx_one : reidx (1 : M2 n) = 1 := by
  simp [reidx]

theorem compAt_cT_mul {θ : InfFam D} (hθ : IsInfFam θ) {m : ℕ} (M : Matrix (Fin m) (Fin m) (AE D)) (τ' : D.what₂.Tau) :
    compAt θ τ' (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M * M) =
      (compAt θ τ' M)ᴴ * compAt θ τ' M := by
  obtain ⟨-, hcA, -, -⟩ := GlobalTheory.T.extensionAdele_realComponents_cmType D θ hθ
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply,
    Matrix.conjTranspose_apply]

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_mul]
  congr 1
  exact hcA (M l i) τ'

theorem cT_one {m : ℕ} : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (1 : Matrix (Fin m) (Fin m) (AE D)) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Formalism.UG.cT]
  · simp [Formalism.UG.cT, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem iota_mem_K {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n} (hθ : IsInfFam θ) (hι : IsPlaceEmb θ τ ι)
    (k : GR n) (hk : InK (mR k)) : ι k ∈ K D n := by
  obtain ⟨hinf0, hcA, -, -⟩ := GlobalTheory.T.extensionAdele_realComponents_cmType D θ hθ
  obtain ⟨-, hcomp⟩ := hι
  obtain ⟨hτ, hτ', hfin⟩ := hcomp k
  rw [K, GlobalTheory.RegSch.EmbLevel.mem_levelAll_iff]
  set M : Matrix (Fin (n + n)) (Fin (n + n)) (AE D) := (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (ι k)).1 with hM
  have hMm : M = mat (ι k) := rfl
  refine ⟨fun v y => ?_, fun w => ?_⟩
  · have h1 : M.map (compFin D.host.F D.host.E v) = 1 := by
      ext i j
      simp only [Matrix.map_apply]
      rw [compFin_eq_finPart]
      have := congrFun (congrFun hfin i) j
      simp only [Matrix.map_apply] at this
      rw [← hMm] at this
      rw [this]
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    rw [h1, Matrix.one_mulVec]
  ·
    have key : ∀ i j, compInf D.host.F D.host.E w
        ((Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig) M * M) i j - (1 : Matrix (Fin (n + n)) (Fin (n + n)) (AE D)) i j) = 0 := by
      intro i j
      refine ((hinf0 _).2 ?_) w
      intro τ'
      have hc := compAt_cT_mul hθ M τ'
      have hrow : θ τ' (infPart D ((Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M * M) i j)) =
          ((compAt θ τ' M)ᴴ * compAt θ τ' M) i j := congrFun (congrFun hc i) j
      rw [map_sub, map_sub, hrow]
      by_cases hττ : τ' = τ
      · subst hττ
        have e : compAt θ τ' M = reidx (mR k) := hτ
        rw [e, reidx_conjTranspose_mul, hk.2, reidx_one]
        by_cases h : i = j
        · subst h; simp
        · simp [Matrix.one_apply_ne h]
      · have e : compAt θ τ' M = 1 := hτ' τ' hττ
        rw [e, Matrix.conjTranspose_one, Matrix.one_mul]
        by_cases h : i = j
        · subst h; simp
        · simp [Matrix.one_apply_ne h]
    simp only [inv_one, Units.val_one, cT_one, Matrix.mul_one]
    ext i j
    have := key i j
    rw [map_sub, sub_eq_zero] at this
    simpa only [Matrix.map_apply] using this

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open PositivityTheory.Rg.Sw.Glob.DecH

theorem decompAway : DecompAway := by
  intro D n θ τ ι hθ hι g
  obtain ⟨-, hιy⟩ := hι
  have hg : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mat g) * (Jst D n).map (incA D) * mat g =
      (Jst D n).map (incA D) := g.2
  set Y := compAt θ τ (mat g) with hYdef
  have hY : Yᴴ * reidx (JJ n) * Y = reidx (JJ n) := by
    have := congrArg (compAt θ τ) hg
    rwa [DA.compAt_mul, DA.compAt_mul, DA.compAt_conjT θ hθ, DA.compAt_Jst θ hθ] at this
  have hinv : compAt θ τ (mat g⁻¹) * Y = 1 := by
    rw [hYdef, ← DA.compAt_mul, ← DA.mat_mul, inv_mul_cancel, DA.mat_one, DA.compAt_one]
  have hYu : IsUnit Y.det := Matrix.isUnit_det_of_left_inverse hinv
  set M : M2 n := Y.submatrix finSumFinEquiv finSumFinEquiv with hMdef
  have hMY : reidx M = Y := by ext i j; simp [reidx, hMdef]
  have hMG : InG M := by
    have h2 : JJ n = (reidx (JJ n)).submatrix finSumFinEquiv finSumFinEquiv := by ext i j; simp [reidx]
    unfold InG
    rw [h2, hMdef, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hY]
  have hMu : IsUnit M.det := by rw [hMdef, det_submatrix_equiv_self]; exact hYu
  set y := mkGR M hMu hMG with hydef
  have hιY : compAt θ τ (mat (ι y)) = Y := by rw [(hιy y).1, hydef, mR_mkGR, hMY]
  have htriv : compAt θ τ (mat (g * (ι y)⁻¹)) = 1 := by
    have h3 : compAt θ τ (mat (g * (ι y)⁻¹)) * Y = Y := by
      calc compAt θ τ (mat (g * (ι y)⁻¹)) * Y = compAt θ τ (mat (g * (ι y)⁻¹)) * compAt θ τ (mat (ι y)) := by rw [hιY]
        _ = compAt θ τ (mat (g * (ι y)⁻¹ * ι y)) := by rw [DA.mat_mul (g * (ι y)⁻¹) (ι y), DA.compAt_mul]
        _ = Y := by rw [inv_mul_cancel_right]
    calc compAt θ τ (mat (g * (ι y)⁻¹)) = compAt θ τ (mat (g * (ι y)⁻¹)) * Y * Y⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hYu, Matrix.mul_one]
      _ = 1 := by rw [h3, Matrix.mul_nonsing_inv _ hYu]
  refine ⟨g * (ι y)⁻¹, y, htriv, by group, ?_⟩
  generalize g * (ι y)⁻¹ = x at htriv ⊢
  intro y'
  apply DA.mat_inj
  rw [DA.mat_mul, DA.mat_mul]
  apply GlobalTheory.StabAtPlace.mx_ext hθ
  · rw [DA.finMap_mul, DA.finMap_mul, (hιy y').2.2, Matrix.mul_one, Matrix.one_mul]
  · intro τ'
    rw [DA.compAt_mul, DA.compAt_mul]
    by_cases h : τ' = τ
    · subst h
      rw [htriv, Matrix.mul_one, Matrix.one_mul]
    · rw [(hιy y').2.1 τ' h, Matrix.mul_one, Matrix.one_mul]

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem weight_factor_eq_automorphy (p q : ℕ) (e : ℤ) (y : GR n) : F0 p q e y = jF e p q y (Complex.I • 1) := by
  simp only [F0, f0, jF, u1, u2, conj_I_smul_one, Matrix.mul_neg, mul_I_smul_one]
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.GaussH

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

theorem lawM_of : TensInj → LawM := by
  intro hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  obtain ⟨k, ⟨j, hj⟩, hk⟩ := LocLawH.chi_exp hC.hθ hC.hχ hC.hη τ
  refine ⟨k - j, fun y a ha hy f hf => ?_⟩
  set A : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero a ha.ne_zero with hAdef
  have hAv : A.1 = a := rfl
  have hAi : (A⁻¹).1 = a⁻¹ := by rw [Matrix.coe_units_inv, hAv]
  have hyA : y = LocLawH.mOf A := by
    apply GR_ext
    rw [hy, LocLawH.mR_mOf, hAv, hAi, Matrix.conjTranspose_nonsing_inv]
    rfl
  have hy0 : (mR (LocLawH.mOf A)).toBlocks₂₁ = 0 := by simp [LocLawH.mR_mOf]
  have haOf : LocLawH.aOf (LocLawH.mOf A) hy0 = A := Units.ext (by rw [LocLawH.aOf_val, LocLawH.mR_mOf]; simp)
  have hsc := LocLawH.scal hC.hθ hσ k j hk hj (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false)
    (cnt_add _) (LocLawH.mOf A) hy0
  rw [haOf] at hsc
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC _ _ fun Ψ hΨ => ?_
  rw [← hL.2 y Ψ hΨ f hf]
  funext x
  rw [hyA, hC.hω.levi _ (LocLawH.unitAt hσ τ A) (LocLawH.mat_mOf hσ hC.hι A), hsc, weight_factor_eq_automorphy,
    siegelP_jF _ hy0, cnt_add]
  have hbl : (mR (LocLawH.mOf A)).toBlocks₁₁ = a := by rw [LocLawH.mR_mOf]; simp [hAv]
  rw [hbl]
  have hΨx : Ψ (HMul.hMul x (LocLawH.unitAt hσ τ A).1 : Mx D V.rank n) = Ψ x := by
    refine hΨ.1 _ _ (fun τ' h => ?_) ?_
    · rw [LocLawH.unitAt_val, LocLawH.compAt_mulM, LocLawH.component_adelic_point_ne hσ h, Matrix.mul_one]
    · rw [LocLawH.unitAt_val, Matrix.map_mul, LocLawH.finite_part_adelic_point_matrix hσ, Matrix.mul_one]
  simp only [tens, hΨx, levF]
  rw [LocLawH.unitAt_val, LocLawH.compAt_mulM, LocLawH.component_adelic_point_matrix hσ, hAv, ← Matrix.mul_assoc]
  have hof : (Matrix.of (fr⁻¹ * compAt θ τ x) : Matrix (Fin V.rank) (Fin n) ℂ) = fr⁻¹ * compAt θ τ x := rfl
  rw [hof]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end
