module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle032
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Development.WeilBound.ThetaLifts.TowerModels.LeviAd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitP
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.Bundle002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle003
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle037
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle027
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle029
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle036
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Bundle002
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps

@[expose] public section

section

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def insW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (z : ℂ) : AE F E := (Place.exists_sec d.cm d.B.emb).choose (Pi.single w z)
section
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F)
theorem insW_self_k (z : ℂ) : piInf (d.B.emb w) (_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z) = z := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, h.2.1, Pi.single_eq_same]
theorem insW_ne_k {w' : InfinitePlace F} (hw : w' ≠ w) (z : ℂ) : piInf (d.B.emb w') (_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z) = 0 := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, h.2.1, Pi.single_eq_of_ne hw]
theorem insW_fin_k (z : ℂ) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z = 0 := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, h.2.2.1]
theorem insW_add_k (z z' : ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w (z + z') = _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z + _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z' := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, Pi.single_add, h.2.2.2.1]
end
def insL_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (v : Fin d.m → Fin d.n → ℂ) : Mx F E d.m d.n :=
  ((R.fr w).1 * (Matrix.of v).map star).map (_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w)
section
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
def Supp_k (Z : Mx F E d.m d.n) : Prop := (∀ w', w' ≠ w → d.cw w' Z = 0) ∧ finOne F • Z = 0
theorem cw_insL_k (v : Fin d.m → Fin d.n → ℂ) : d.cw w (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w v) = (R.fr w).1 * (Matrix.of v).map star := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_self_k]
theorem insL_supp_k (v : Fin d.m → Fin d.n → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KW.Supp_k w (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w v) := by
  refine ⟨fun w' hw' => ?_, ?_⟩
  · ext i j
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_ne_k d w hw', Matrix.zero_apply]
  · ext i j
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k, Matrix.smul_apply, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_fin_k, Matrix.zero_apply]
theorem insL_add_k (v v' : Fin d.m → Fin d.n → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (v + v') = _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w v + _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w v' := by
  have e : (R.fr w).1 * (Matrix.of (v + v')).map star =
      (R.fr w).1 * (Matrix.of v).map star + (R.fr w).1 * (Matrix.of v').map star := by
    rw [← Matrix.mul_add]
    congr 1
    ext i j
    simp
  unfold _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k
  rw [e]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_add_k]
theorem insL_zero_k : _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 = 0 := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.KW.insL_add_k R w 0 0
  rw [add_zero] at h
  calc _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 = _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 + _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 := by abel
    _ = _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 := by rw [← h]
    _ = 0 := sub_self _
theorem insL_loc_k {Z : Mx F E d.m d.n} (hZ : _root_.PositivityTheory.SiegelWeilFormula.KW.Supp_k w Z) : _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z) = Z := by
  refine Place.mat_ext d.cm d.B.emb (fun w' => ?_) ?_
  · by_cases hw : w' = w
    · rw [hw]
      change d.cw w (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)) = d.cw w Z
      rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_insL_k]
      have h2 : (Matrix.of (R.loc w Z)).map star = ((R.fr w)⁻¹).1 * d.cw w Z := by
        ext i j
        exact star_star _
      rw [h2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    · change d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)) = d.cw w' Z
      rw [(_root_.PositivityTheory.SiegelWeilFormula.KW.insL_supp_k R w _).1 w' hw, hZ.1 w' hw]
  · rw [(_root_.PositivityTheory.SiegelWeilFormula.KW.insL_supp_k R w _).2, hZ.2]
theorem rest_inv_k (X Z : Mx F E d.m d.n) (hZ : _root_.PositivityTheory.SiegelWeilFormula.KW.Supp_k w Z) :
    (X + Z) - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w (X + Z)) = X - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w X) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add'_k d R w X Z, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_add_k, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_loc_k R w hZ]
  abel
end
section
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem psi_add_right_k (ε : ℤˣ) (X Z Z' : Mx F E d.m d.n) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Z + Z'))) =
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z')) := by
  have e : d.gram X (Z + Z') = d.gram X Z + d.gram X Z' := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add]
  rw [e, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_add, map_add (f := _), mul_add, AddChar.map_add_eq_mul]
theorem psi_add_left_k (ε : ℤˣ) (X X' Z : Mx F E d.m d.n) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram (X + X') Z)) =
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X' Z)) := by
  have e : d.gram (X + X') Z = d.gram X Z + d.gram X' Z := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.add_mul]
  rw [e, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_add, map_add (f := _), mul_add, AddChar.map_add_eq_mul]
theorem cw_gram_k (w : InfinitePlace F) (X Z : Mx F E d.m d.n) :
    d.cw w (d.gram X Z) = (d.cw w X)ᵀ * d.A.J.map (d.B.emb w).1 * (d.cw w Z).map star := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw
  have hJ : (incM F d.A.J).map (piInf (d.B.emb w)) = d.A.J.map (d.B.emb w).1 := by
    ext i j
    simp [incM, PositivityTheory.ThKG.Tow.Levi.piInf_incl]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Place.map_cA d.cm (d.B.emb w) Z, hJ]
theorem gram_supp_cmp_k (w : InfinitePlace F) {Z' Z : Mx F E d.m d.n} (hZ' : _root_.PositivityTheory.SiegelWeilFormula.KW.Supp_k w Z') (hZ : d.cw w Z = 0) :
    d.gram Z' Z = 0 := by
  refine Place.mat_ext d.cm d.B.emb (fun w' => ?_) ?_
  · change d.cw w' (d.gram Z' Z) = d.cw w' 0
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_gram_k]
    by_cases hw : w' = w
    · subst hw
      rw [hZ, Matrix.map_zero _ (star_zero _), Matrix.mul_zero]
      ext i j
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
    · rw [hZ'.1 w' hw, Matrix.transpose_zero, Matrix.zero_mul, Matrix.zero_mul]
      ext i j
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
  · unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
    rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, hZ'.2]
    simp
theorem psi_zero_gram_k (ε : ℤˣ) : d.B.ψ (((ε : ℤ) : AF F) * d.tt (0 : Mx F E d.n d.n)) = 1 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt]
end
theorem zeta_ne_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.ζ ≠ 0 := by
  rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp
section
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem cw_loc_k (X : Mx F E d.m d.n) : d.cw w X = (R.fr w).1 * (Matrix.of (R.loc w X)).map star := by
  have h2 : (Matrix.of (R.loc w X)).map star = ((R.fr w)⁻¹).1 * d.cw w X := by
    ext i j
    exact star_star _
  rw [h2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
theorem frJ_k : (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by
  have h := R.hfr w
  calc (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star
      = R.ζ⁻¹ • (R.ζ • ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star)) := by
        rw [smul_smul, inv_mul_cancel₀ (_root_.PositivityTheory.SiegelWeilFormula.KW.zeta_ne_k R), one_smul]
    _ = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by rw [h, smul_smul]
end
theorem psi_at_w_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (ε : ℤˣ) (M : Mx F E d.n d.n)
    (hM1 : ∀ w', w' ≠ w → d.cw w' M = 0) (hM2 : finOne F • M = 0) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt M) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((2 * (((ε : ℤ) : ℂ) * (d.cw w M).trace).re : ℝ) : ℂ)) := by
  have hz : ((ε : ℤ) : AF F) * d.tt M = Algebra.trace (AF F) (AE F E) ((ε : ℤ) • M.trace) := by
    rw [map_zsmul, zsmul_eq_mul]
    rfl
  have ptr : ∀ u, piInf (d.B.emb u) M.trace = (d.cw u M).trace := fun u => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, map_sum]
  rw [hz, Place.psi_trace_at d.std d.cm d.B.emb w _ ?_ ?_, map_zsmul, ptr, zsmul_eq_mul]
  · rw [smul_comm, ← Matrix.trace_smul, hM2, Matrix.trace_zero, smul_zero]
  · intro u hu
    rw [map_zsmul, ptr, hM1 u hu, Matrix.trace_zero, smul_zero]
theorem kernel_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (ε : ℤˣ) (X : Mx F E d.m d.n) (u : Fin d.m → Fin d.n → ℂ) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u))) =
      Complex.exp (2 * Real.pi * Complex.I * (((-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) *
        Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u)).re : ℂ)) := by
  have hM1 : ∀ w', w' ≠ w → d.cw w' (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u)) = 0 := by
    intro w' hw
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_gram_k, (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_supp_k R w u).1 w' hw, Matrix.map_zero _ (star_zero _), Matrix.mul_zero]
  have hM2 : finOne F • d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u) = 0 := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
    rw [← Matrix.mul_smul]
    have : finOne F • (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u).map (cA σ) = (finOne F • _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u).map (cA σ) := by
      ext i j
      simp [map_smul]
    rw [this, (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_supp_k R w u).2]
    simp
  have e1 : d.cw w (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u)) =
      (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • ((Matrix.of (R.loc w X))ᴴ * Matrix.of u) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_gram_k, _root_.PositivityTheory.SiegelWeilFormula.KW.cw_loc_k R w X, _root_.PositivityTheory.SiegelWeilFormula.KW.cw_insL_k, Matrix.transpose_mul]
    have h3 : ((R.fr w).1 * (Matrix.of u).map star).map star = (R.fr w).1.map star * Matrix.of u := by
      ext i j
      simp [Matrix.mul_apply]
    have h4 : ((Matrix.of (R.loc w X)).map star)ᵀ = (Matrix.of (R.loc w X))ᴴ := rfl
    rw [h3, h4]
    calc (Matrix.of (R.loc w X))ᴴ * (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * ((R.fr w).1.map star * Matrix.of u)
        = (Matrix.of (R.loc w X))ᴴ * ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star) * Matrix.of u := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [_root_.PositivityTheory.SiegelWeilFormula.KW.frJ_k, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.psi_at_w_k d w ε _ hM1 hM2, e1, Matrix.trace_smul, smul_eq_mul]
  congr 1
  have e2 : -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ * Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u) =
      ((-2 : ℝ) : ℂ) * (((ε : ℤ) : ℂ) * (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ) *
        Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u))) := by
    push_cast
    ring
  rw [e2, Complex.re_ofReal_mul]
  push_cast
  ring
end PositivityTheory.SiegelWeilFormula.KW
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open GlobalTheory.Doubling (absE)
theorem isPar_of_frame_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (h21 : (inFrame d.b p).toBlocks₂₁ = 0) :
    ∃ t : GL (Fin d.n) (AE F E), IsPar p t ∧ (Matrix.GeneralLinearGroup.det t : AE F E) = (inFrame d.b p).toBlocks₁₁.det := by
  obtain ⟨-, tb, htb⟩ := d.ok.frame
  set M := inFrame d.b p with hM
  let E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := Matrix.fromRows 1 0
  let DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
  have htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1 := htb
  have hcol : ∀ N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), N * E1 = N.toCols₁ := by
    intro N
    ext i j
    simp [E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have h1 : incM F d.b.1 * E1 = incM F (d.b.1.toCols₁) := by
    rw [hcol]
    ext i j
    rfl
  have h2 : incM F ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1) = DC * incM F tb.1 := by
    rw [incM_mul'']
    congr 1
    ext i j
    cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all
  have hb : incM F d.b.1 * E1 = DC * incM F tb.1 := h1.trans ((congrArg (incM F) htb').trans h2)
  have hTb : incM F tb.1 * incM F (tb⁻¹).1 = 1 := by
    rw [← incM_mul'', Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hTb' : incM F (tb⁻¹).1 * incM F tb.1 = 1 := by
    rw [← incM_mul'', Units.inv_mul]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hdc : DC = incM F d.b.1 * E1 * incM F (tb⁻¹).1 := by
    rw [hb, Matrix.mul_assoc, hTb, Matrix.mul_one]
  have hME : M * E1 = E1 * M.toBlocks₁₁ := by
    rw [hcol]
    ext i j
    cases i with
    | inl i => simp [E1, Matrix.toCols₁, Matrix.toBlocks₁₁, Matrix.mul_apply, Matrix.one_apply]
    | inr i =>
      have := congrFun (congrFun h21 i) j
      simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at this
      simp [E1, Matrix.toCols₁, this, Matrix.mul_apply]
  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.det_one]⟩)
  have hug : IsUnit M := (hBi.mul (Units.isUnit p.1)).mul hBm
  have hgb : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← h21, Matrix.fromBlocks_toBlocks]
  have hdet : IsUnit (M.toBlocks₁₁.det * M.toBlocks₂₂.det) := by
    rw [← Matrix.det_fromBlocks_zero₂₁ M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₂, ← hgb]
    exact (Matrix.isUnit_iff_isUnit_det M).1 hug
  have hA : IsUnit M.toBlocks₁₁.det := isUnit_of_mul_isUnit_left hdet
  have hTbu : IsUnit (incM F tb.1).det :=
    isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, hTb, Matrix.det_one]⟩
  have hTbiu : IsUnit (incM F (tb⁻¹).1).det :=
    isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, hTb', Matrix.det_one]⟩
  have hu : IsUnit (incM F tb.1 * M.toBlocks₁₁ * incM F (tb⁻¹).1) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_mul]
    exact (hTbu.mul hA).mul hTbiu
  refine ⟨hu.unit, ?_, ?_⟩
  · show mat2 p * DC = DC * (hu.unit : Matrix (Fin d.n) (Fin d.n) (AE F E))
    rw [IsUnit.unit_spec, _root_.PositivityTheory.SiegelWeilFormula.KWhit.matrixRep_eq_frameConj_inFrame d p]
    change incM F d.b.1 * M * incM F (d.b⁻¹).1 * DC = DC * (incM F tb.1 * M.toBlocks₁₁ * incM F (tb⁻¹).1)
    rw [hdc]
    calc incM F d.b.1 * M * incM F (d.b⁻¹).1 * (incM F d.b.1 * E1 * incM F (tb⁻¹).1)
        = incM F d.b.1 * M * (incM F (d.b⁻¹).1 * incM F d.b.1) * E1 * incM F (tb⁻¹).1 := by
          simp only [Matrix.mul_assoc]
      _ = incM F d.b.1 * (M * E1) * incM F (tb⁻¹).1 := by
          rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = incM F d.b.1 * E1 * (incM F (tb⁻¹).1 * incM F tb.1) * M.toBlocks₁₁ * incM F (tb⁻¹).1 := by
          rw [hME, hTb', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  · rw [Matrix.GeneralLinearGroup.val_det_apply, IsUnit.unit_spec, Matrix.det_mul, Matrix.det_mul, mul_comm _ M.toBlocks₁₁.det,
      mul_assoc, ← Matrix.det_mul, hTb, Matrix.det_one, mul_one]
theorem a_mul_par_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {q : d.G} {t : GL (Fin d.n) (AE F E)} (hq : IsPar q t) (y : d.G) :
    d.a (q * y) = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) * d.a y := by
  obtain ⟨p, t', hp, k, hk, rfl⟩ := d.ok.hgt.iwa y
  rw [← mul_assoc, d.ok.hgt.val _ _ (KSplitP.isPar_mul hq hp) k hk, d.ok.hgt.val p t' hp k hk, map_mul, map_mul,
    NNReal.coe_mul]
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem rel_frame_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (y : d.G) :
    (inFrame d.b y)ᵀ * Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 * (inFrame d.b y).map (cA σ) =
      Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  have hF : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
      Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
    rw [e1, e2, ← key, hε]
    simp only [incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hM : (mat2 y)ᵀ * dbl (incM F d.Y.J) * (mat2 y).map (cA σ) = dbl (incM F d.Y.J) := y.2
  have := form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hM
  rw [← hF]
  exact this
theorem rel_nA_cond_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (β : nA σ d.Y d.b) :
    β.1ᵀ + ((ε : ℤ) : AE F E) • β.1.map (cA σ) = 0 := by
  obtain ⟨β, hβ⟩ := β
  show βᵀ + ((ε : ℤ) : AE F E) • β.map (cA σ) = 0
  induction hβ using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨y, hy⟩ := hx
    have h := _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_frame_k d ε hε y
    rw [hy] at h
    simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
      Matrix.transpose_one, Matrix.map_zero _ (map_zero (cA σ)), Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ)),
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
      Matrix.fromBlocks_inj] at h
    rw [add_comm]
    have h4 := h.2.2.2
    rw [Matrix.smul_mul, Matrix.one_mul] at h4
    exact h4
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.transpose_add, Matrix.map_add _ (map_add (cA σ)), smul_add]
    calc _ = (xᵀ + ((ε : ℤ) : AE F E) • x.map (cA σ)) + (yᵀ + ((ε : ℤ) : AE F E) • y.map (cA σ)) := by abel
      _ = 0 := by rw [hx, hy, add_zero]
  | neg x _ hx =>
    rw [Matrix.transpose_neg, Matrix.map_neg _ (map_neg (cA σ)), smul_neg, ← neg_add, hx, neg_zero]
theorem frameSign_eq_involution_scalar (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hσ : ∀ x, σ (σ x) = x) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (c : E)
    (hc : d.Y.J.map σ = c • d.Y.Jᵀ) (i : Fin d.n) : ((ε : ℤ) : E) = c := by
  have hD : (dbl d.Y.J).map σ = c • (dbl d.Y.J)ᵀ := by
    simp only [dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_smul, hc,
      Matrix.map_neg _ (map_neg σ), Matrix.map_zero _ (map_zero σ), Matrix.transpose_zero, Matrix.transpose_neg,
      smul_zero, smul_neg]
  have hbb : (d.b.1.map σ).map σ = d.b.1 := by
    ext i j
    simp [hσ]
  have h1 := congrArg σ.mapMatrix hε
  simp only [map_mul, AlgHom.mapMatrix_apply, hD, hbb] at h1
  have h2 := congrArg Matrix.transpose h1
  simp only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.transpose_map] at h2
  rw [← Matrix.mul_assoc, hε] at h2
  have := congrFun (congrFun h2 (Sum.inr i)) (Sum.inl i)
  simp [Matrix.fromBlocks_map] at this
  have hε2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  calc ((ε : ℤ) : E) = ((ε : ℤ) : E) * (c * ((ε : ℤ) : E)) := by rw [this, mul_one]
    _ = c * (((ε : ℤ) : E) * ((ε : ℤ) : E)) := by ring
    _ = c := by rw [hε2, mul_one]
theorem rel_sign_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    ((∀ i j, σ (d.Y.J j i) = -d.Y.J i j) → ε = -1) ∧ ((∀ i j, σ (d.Y.J j i) = d.Y.J i j) → ε = 1) := by
  have hσ := rel_sigma_sigma d.ok.good.cm
  have i : Fin d.n := ⟨0, d.ok.hn⟩
  constructor
  · intro h
    have := _root_.PositivityTheory.SiegelWeilFormula.KWhit.frameSign_eq_involution_scalar d hσ ε hε (-1) (by ext a b; simp [h b a]) i
    exact Units.ext (Int.cast_injective (α := E) (by simpa using this))
  · intro h
    have := _root_.PositivityTheory.SiegelWeilFormula.KWhit.frameSign_eq_involution_scalar d hσ ε hε 1 (by ext a b; simp [h b a]) i
    exact Units.ext (Int.cast_injective (α := E) (by simpa using this))
theorem rel_eta_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    ∃ η : E, η ≠ 0 ∧ σ η = -(((ε : ℤ) : E) * η) ∧ ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j := by
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · have he := (_root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_sign_k d ε hε).1 hY
    subst he
    refine ⟨1, one_ne_zero, by simp, fun i j => by simp [hA.herm i j]⟩
  · have he := (_root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_sign_k d ε hε).2 hY
    subst he
    obtain ⟨η, hη, hση⟩ := rel_anti d.ok.good.cm
    refine ⟨η, hη, by simp [hση], fun i j => ?_⟩
    rw [map_mul, hση, hA.skew i j, neg_mul_neg]
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
def RelRealP_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Φ : d.Fn) P gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf →
  ∀ (x : d.G) (t u : GL (Fin d.n) (AE F E)), inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1 →
  ∀ η : E, η ≠ 0 → (∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) →
  ∃ (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (g : InfinitePlace F → GL (Fin d.n) ℂ) (l : InfinitePlace F → ℝ) (εs : InfinitePlace F → Fin d.m → Bool)
    (Φg : (Fin d.n → Fin d.m → AF F ⊗[F] E) → ℂ) (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ),
    (∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y)) ∧
    (∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star) ∧
    (∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1) ∧
    (∀ Y, Φg Y = d.T Φ (toMx Y * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ)) ∧
    (∃ e : InfinitePlace F → Bool, εs = fun i _ => e i) ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F d.B.ψ ∧ Gen.IsPlaces σ d.B.ψ θ l ∧ Gen.IsFrames (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) θ εs fr ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin d.bs Φf Φv ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsProdInfFin Φg (Gen.phiInf θ l fr g P) Φf
theorem relReal_k : _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.RelRealP_k := by
  intro F E _ _ _ _ _ σ d R Φ P gf hP x t u _ η hη herm
  obtain ⟨Φf, Φv, hpf, hpr⟩ := _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.pure_prod_of'_k R Φ P gf hP u η (thW d.B) (thW_th' d.B) (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_k R η hη) (fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_frc_k R η hη w)
    (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_k d u η hη) (fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_gc_k d u η hη w) (fun _ => -1) (fun _ => by norm_num)
  refine ⟨thW d.B, _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_k R η hη, _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_k d u η hη, fun _ => -1, _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.εsW_k R η, _, Φf, Φv, thW_th' d.B, fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_frc_k R η hη w,
    fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_gc_k d u η hη w, fun _ => rfl, ⟨fun w => decide (0 < (((d.B.emb w).1 η / R.ζ) * ((R.sg w : ℤ) : ℂ)).re), rfl⟩,
    _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.isCharAF_of_good_k d.B d.ok.good, _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.isPlaces_thW'_k d.B d.ok.good,
    _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.isFrames_of'_k R η hη d.ok.good.cm herm (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.eta_zeta'_k R hη herm) (thW d.B) (thW_th' d.B) (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_k R η hη)
      (fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_frc_k R η hη w), hpf, hpr⟩
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
end
