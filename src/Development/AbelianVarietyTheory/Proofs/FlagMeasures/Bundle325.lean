module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Aesop.Main
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.NatSmulMulEq
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace

@[expose] public section

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QuotTransport

lemma jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; split_ifs <;> norm_num

lemma exists_unit {n m : ℕ} (ε : Fin n → Bool) (H : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ)
    (Qi : Matrix (Fin m) (Fin n) ℂ) (h1 : Qi * Q = 1) (h2 : Q * Qi = 1) (h3 : Qᴴ * Formalism.REAL.Jm ε * Q = H)
    (y : Matrix (Fin m) (Fin m) ℂ) (hy : yᴴ * H * y = H) :
    ∃ g : Formalism.REAL.UJ ε, ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = Q * y⁻¹ * Qi := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := jm_mul_self ε
  have hHi : (Qi * Formalism.REAL.Jm ε * Qiᴴ) * H = 1 := by
    have : H * (Qi * Formalism.REAL.Jm ε * Qiᴴ) = 1 := by
      rw [← h3]
      calc Qᴴ * Formalism.REAL.Jm ε * Q * (Qi * Formalism.REAL.Jm ε * Qiᴴ)
          = Qᴴ * Formalism.REAL.Jm ε * (Q * Qi) * Formalism.REAL.Jm ε * Qiᴴ := by simp only [Matrix.mul_assoc]
        _ = Qᴴ * Qiᴴ := by
          rw [h2, Matrix.mul_one, Matrix.mul_assoc Qᴴ (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJ, Matrix.mul_one]
        _ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    exact mul_eq_one_comm.mp this
  have hl : (Qi * Formalism.REAL.Jm ε * Qiᴴ * yᴴ * H) * y = 1 := by
    calc (Qi * Formalism.REAL.Jm ε * Qiᴴ * yᴴ * H) * y = (Qi * Formalism.REAL.Jm ε * Qiᴴ) * (yᴴ * H * y) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hy, hHi]
  have hdet : IsUnit y.det := Matrix.isUnit_det_of_left_inverse hl
  have hyr : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv y hdet
  have hyl : y⁻¹ * y = 1 := Matrix.nonsing_inv_mul y hdet
  have hy' : (y⁻¹)ᴴ * H * y⁻¹ = H := by
    calc (y⁻¹)ᴴ * H * y⁻¹ = (y⁻¹)ᴴ * (yᴴ * H * y) * y⁻¹ := by rw [hy]
      _ = (y * y⁻¹)ᴴ * H * (y * y⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hyr, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    ⟨Q * y⁻¹ * Qi, Q * y * Qi, by
      calc Q * y⁻¹ * Qi * (Q * y * Qi) = Q * (y⁻¹ * (Qi * Q) * y) * Qi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.mul_one, hyl, Matrix.mul_one, h2],
     by
      calc Q * y * Qi * (Q * y⁻¹ * Qi) = Q * (y * (Qi * Q) * y⁻¹) * Qi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.mul_one, hyr, Matrix.mul_one, h2]⟩
  have hu : u ∈ Formalism.REAL.UJ ε := by
    show Formalism.REAL.inUJ ε (Q * y⁻¹ * Qi)
    unfold Formalism.REAL.inUJ
    calc (Q * y⁻¹ * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * y⁻¹ * Qi)
        = Qiᴴ * ((y⁻¹)ᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * y⁻¹) * Qi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Qiᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qi := by rw [h3, hy']
      _ = (Q * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * Qi) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  exact ⟨⟨u, hu⟩, rfl⟩

end GlobalTheory.QuotTransport

namespace GlobalTheory


open GlobalTheory.QuotTransport in
theorem quotMeas_besselModel_of_quotLoc : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μ ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))), SFinite μ → Formalism.L2.SG.RealObj.IsQuotLoc μ ν → IsQuotMeas (muGB X (C.Q τ) (C.Qi τ) τ) (μ.map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ⁻¹ * y * γ)))) (ν.map (fun z => Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹))) := by
  intro D X θ C τ γ μ ν hμ hq f hf
  haveI : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).IsMulRightInvariant :=
    ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  obtain ⟨h1, h2, h3, -⟩ := C.isT τ
  obtain ⟨g, hg⟩ := exists_unit _ _ (C.Q τ) (C.Qi τ) h1 h2 h3 (C.y τ) (C.y_mem τ)
  have h2' : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, C.Q τ * (C.Qi τ * M) = M := by
    intro M; rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hγ : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      ((γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
        ((((γ⁻¹ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one,
      Matrix.one_mul]
  have hc : Continuous (fun w : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => uMat w) :=
    Units.continuous_val.comp continuous_subtype_val
  have hcM : ∀ {h : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.REAL.UJ (X.B.I.ε (vOf X τ))}, Continuous h →
      ∀ (A : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ)
        (B : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ),
      Continuous (fun w => (Matrix.of.symm (A * uMat (h w) * B) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    fun hh A B => (continuous_const.matrix_mul (hc.comp hh)).matrix_mul continuous_const
  have hcβ : Continuous (fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      (Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    (hcM (continuous_const_mul γ⁻¹) (C.Qi τ) (C.Q τ)).matrix_mul (continuous_const (y := (C.y τ)⁻¹))
  set φ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun w => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) w) with hφ
  set α : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ⁻¹ * y * γ)) with hα
  set β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun z => Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) with hβ
  have hφm : Measurable φ := (hcM continuous_id _ _).measurable
  have hαm : Measurable α := (hcM ((continuous_const.mul continuous_id).mul continuous_const) _ _).measurable
  have hβm : Measurable β := hcβ.measurable
  have hpc : Continuous (fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      ((fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))) :=
    Continuous.matrix_mul continuous_snd continuous_fst
  have hj : Measurable (fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      f (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j)) :=
    hf.comp hpc.measurable
  have hA : ∀ w, φ (w * g) = β (γ * w) := by
    intro w
    show Matrix.of.symm (C.Qi τ * uMat (w * g) * C.Q τ) =
      Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * (γ * w)) * C.Q τ * (C.y τ)⁻¹)
    rw [inv_mul_cancel_left]
    congr 1
    simp only [uMat, Subgroup.coe_mul, Units.val_mul, hg, Matrix.mul_assoc, h1, Matrix.mul_one]
  have hB : ∀ y z, β (y * z) = fun i j => (Matrix.of (α y) * Matrix.of (β z)) i j := by
    intro y z
    simp only [hα, hβ, Formalism.L2.SG.RealObj.trG, Equiv.apply_symm_apply, uMat, Subgroup.coe_mul, Units.val_mul,
      Matrix.mul_assoc, h2', hγ]
    rfl
  show ∫⁻ x, f x ∂((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map φ) = ∫⁻ x, ∫⁻ s,
    f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(μ.map α) ∂(ν.map β)
  rw [lintegral_map (hj.lintegral_prod_right' (ν := μ.map α)) hβm]
  calc ∫⁻ x, f x ∂((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map φ)
      = ∫⁻ w, f (φ w) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := lintegral_map hf hφm
    _ = ∫⁻ w, f (φ (w * g)) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) :=
        (lintegral_mul_right_eq_self (fun w => f (φ w)) g).symm
    _ = ∫⁻ w, f (β (γ * w)) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := by simp only [hA]
    _ = ∫⁻ w, f (β w) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := lintegral_mul_left_eq_self (fun w => f (β w)) γ
    _ = ∫⁻ z, ∫⁻ y, f (β (y * z)) ∂μ ∂ν := hq _ (hf.comp hβm)
    _ = ∫⁻ z, ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of (β z)) i j) ∂(μ.map α) ∂ν := by
        refine lintegral_congr fun z => ?_
        have hmz : Measurable (fun s : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
            f (fun i j => (Matrix.of s * Matrix.of (β z)) i j)) := hj.comp measurable_prodMk_left
        rw [lintegral_map hmz hαm]
        simp only [hB]

end GlobalTheory
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.SRe.ConvStep
variable {D : D7}

theorem kset_one (X : HidaSetting D) : (1 : X.B.I.Gf) ∈ X.B.I.Kset := by
  show ((1 : X.B.I.Gf) : GL _ _) ∈ Formalism.UG.stabGL X.B.I.Lf
  rw [OneMemClass.coe_one]
  exact (Formalism.UG.stabGL X.B.I.Lf).one_mem

theorem kset_mul (X : HidaSetting D) {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hy : y ∈ X.B.I.Kset) :
    x * y ∈ X.B.I.Kset := by
  show ((x * y : X.B.I.Gf) : GL _ _) ∈ Formalism.UG.stabGL X.B.I.Lf
  rw [Subgroup.coe_mul]
  exact mul_mem hx hy

theorem kset_inv (X : HidaSetting D) {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) : x⁻¹ ∈ X.B.I.Kset := by
  show ((x⁻¹ : X.B.I.Gf) : GL _ _) ∈ Formalism.UG.stabGL X.B.I.Lf
  rw [Subgroup.coe_inv]
  exact inv_mem hx

theorem red_one (X : HidaSetting D) {red : X.B.I.Gf → G0g D.nd} (hr : IsRedHom X red) : red 1 = 1 := by
  have h := hr.2.1 1 (kset_one X) 1 (kset_one X)
  rw [one_mul] at h
  exact mul_left_cancel (a := red 1) (by rw [mul_one]; exact h.symm)

theorem fibre_iff (X : HidaSetting D) {red : X.B.I.Gf → G0g D.nd} (hr : IsRedHom X red) {s : X.B.I.Gf}
    (hs : s ∈ X.B.I.Kset) (x : X.B.I.Gf) :
    (x ∈ X.B.I.Kset ∧ red x = red s) ↔ s⁻¹ * x ∈ X.B.I.Kg X.B.g := by
  have hsi : s⁻¹ ∈ X.B.I.Kset := kset_inv X hs
  have hinv : red s⁻¹ = (red s)⁻¹ := by
    have h1 := hr.2.1 s⁻¹ hsi s hs
    rw [inv_mul_cancel, red_one X hr] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  constructor
  · rintro ⟨hx, hrx⟩
    have hk : s⁻¹ * x ∈ X.B.I.Kset := kset_mul X hsi hx
    refine (hr.2.2.2 _ hk).1 ?_
    rw [hr.2.1 _ hsi _ hx, hinv, hrx, inv_mul_cancel]
  · intro hk
    have hkK : s⁻¹ * x ∈ X.B.I.Kset := hk.1
    have hr1 : red (s⁻¹ * x) = 1 := (hr.2.2.2 _ hkK).2 hk
    have h2 := kset_mul X hs hkK
    rw [mul_inv_cancel_left] at h2
    refine ⟨h2, ?_⟩
    have h3 := hr.2.1 _ hs _ hkK
    rw [mul_inv_cancel_left, hr1, mul_one] at h3
    exact h3

theorem one_le_g (X : HidaSetting D) : 1 ≤ X.B.g := by
  rw [X.g_eq]
  exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)

theorem kg_open (X : HidaSetting D) : IsOpen (X.B.I.Kg X.B.g) := X.B.I.topf_open X.B.g (one_le_g X)

theorem kg_pos_fin (X : HidaSetting D) : 0 < X.B.μf (X.B.I.Kg X.B.g) ∧ X.B.μf (X.B.I.Kg X.B.g) < ⊤ := by
  have hne : (X.B.I.Kg X.B.g).Nonempty := ⟨1, by
    refine ⟨kset_one X, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
    simp [Formalism.MainNotions.S.AutInst.fmat]⟩
  refine ⟨(kg_open X).measure_pos X.B.μf hne, ?_⟩
  exact lt_of_le_of_lt (measure_mono fun x hx => hx.1) (PI.WAU.Cpt.isCompact_Kset X.B.I).measure_lt_top

theorem fibre_meas (X : HidaSetting D) {red : X.B.I.Gf → G0g D.nd} (hr : IsRedHom X red) {s : X.B.I.Gf}
    (hs : s ∈ X.B.I.Kset) :
    MeasurableSet {x | x ∈ X.B.I.Kset ∧ red x = red s} ∧
      X.B.μf {x | x ∈ X.B.I.Kset ∧ red x = red s} = X.B.μf (X.B.I.Kg X.B.g) := by
  have e : {x | x ∈ X.B.I.Kset ∧ red x = red s} = (fun x => s⁻¹ * x) ⁻¹' (X.B.I.Kg X.B.g) := by
    ext x; exact fibre_iff X hr hs x
  rw [e]
  refine ⟨((kg_open X).preimage (continuous_const_mul s⁻¹)).measurableSet, ?_⟩
  exact measure_preimage_mul X.B.μf s⁻¹ _

open scoped InnerProductSpace in
theorem top_expand [Fintype (G0g D.nd)] (X : HidaSetting D) {red : X.B.I.Gf → G0g D.nd} (hr : IsRedHom X red)
    (s0 : G0g D.nd → X.B.I.Gf) (hs0 : ∀ γ, s0 γ ∈ X.B.I.Kset ∧ red (s0 γ) = γ) (a : G0g D.nd → ℂ)
    (Top : L2X X →L[ℂ] L2X X)
    (hT : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R
      (fun x => if x ∈ X.B.I.Kset then a (red x) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0) Top)
    (y : L2X X) (hy : ∀ k ∈ X.B.I.Kset, X.B.R (1, k) y = X.B.R (1, s0 (red k)) y) :
    Top y = ∑ γ, a γ • X.B.R (1, s0 γ) y := by
  apply ext_inner_left ℂ
  intro x
  rw [hT.2 x y, inner_sum]
  simp only [inner_smul_right]
  set V : ℝ := (X.B.μf (X.B.I.Kg X.B.g)).toReal with hV
  have hVpos : 0 < V := ENNReal.toReal_pos (kg_pos_fin X).1.ne' (kg_pos_fin X).2.ne
  have hV0 : (V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hVpos.ne'
  let Fb : G0g D.nd → Set X.B.I.Gf := fun γ => {z | z ∈ X.B.I.Kset ∧ red z = γ}
  have hFb : ∀ γ, MeasurableSet (Fb γ) ∧ X.B.μf (Fb γ) = X.B.μf (X.B.I.Kg X.B.g) := by
    intro γ
    have := fibre_meas X hr (hs0 γ).1
    rw [(hs0 γ).2] at this
    exact this
  let cf : G0g D.nd → ℂ := fun γ => a γ / (V : ℂ) * ⟪x, X.B.R (1, s0 γ) y⟫_ℂ
  have hpt : ∀ g : X.B.I.Gf,
      (if g ∈ X.B.I.Kset then a (red g) / (V : ℂ) else 0) * ⟪x, X.B.R (1, g) y⟫_ℂ =
        ∑ γ, (Fb γ).indicator (fun _ => cf γ) g := by
    intro g
    by_cases hg : g ∈ X.B.I.Kset
    · rw [if_pos hg, Finset.sum_eq_single (red g)]
      · rw [Set.indicator_of_mem (show g ∈ Fb (red g) from ⟨hg, rfl⟩), hy g hg]
      · intro b _ hb
        exact Set.indicator_of_notMem (by exact fun hm => hb hm.2.symm) _
      · intro h1; exact absurd (Finset.mem_univ _) h1
    · rw [if_neg hg, zero_mul]
      symm
      refine Finset.sum_eq_zero fun b _ => ?_
      exact Set.indicator_of_notMem (by exact fun hm => hg hm.1) _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun γ _ => ?_
    rw [integral_indicator_const _ (hFb γ).1, measureReal_def, (hFb γ).2, ← hV]
    simp only [cf, Complex.real_smul]
    field_simp
  · intro γ _
    refine (integrable_indicator_iff (hFb γ).1).2 ?_
    refine integrableOn_const ?_
    rw [(hFb γ).2]; exact (kg_pos_fin X).2.ne

end GlobalTheory.Mem.SRe.ConvStep

namespace GlobalTheory.Mem.SRe

end GlobalTheory.Mem.SRe
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.StdCharTotReal

section Local

variable {F : Type} [Field F] [NumberField F]

theorem trace_int_iff (a : F) : (∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k) ↔
    ∀ d ∈ differentIdeal ℤ (𝓞 F), ∃ r : 𝓞 F, (r : F) = a * d := by
  apply _root_.GlobalTheory.SnMass.Inhab.trace_int_iff <;> assumption

theorem integral_iff (x : F) : (∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (Af F) x v ∈ v.adicCompletionIntegers F) ↔
    ∃ r : 𝓞 F, (r : F) = x := by
  constructor
  · intro h
    have hx := (GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral F _).2 h
    rwa [GlobalTheory.Idele.algebraMap_mem_adelicIdeal (GlobalTheory.AdLat.one_ne_zero_fracIdeal F),
      FractionalIdeal.mem_one_iff] at hx
  · rintro ⟨r, rfl⟩ v
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v r

theorem fin_conductor (χ : Af F → ℂ) (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y)
    (hrat : ∀ a : F, χ (algebraMap F (Af F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (-a) : ℚ) : ℂ))) (z : Af F) :
    (∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = 1) ↔
      ∀ d ∈ differentIdeal ℤ (𝓞 F), ∀ v : HeightOneSpectrum (𝓞 F), (z * algebraMap F (Af F) (d : F)) v ∈ v.adicCompletionIntegers F := by
  apply _root_.GlobalTheory.SnMass.Inhab.fin_conductor <;> assumption

theorem single_same (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : singleV F v y v = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem single_ne (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    singleV F v y w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

theorem single_mul (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) (t : Af F) :
    singleV F v y * t = singleV F v (y * t v) := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change singleV F v y w * t w = singleV F v (y * t v) w
  by_cases hw : w = v
  · subst hw; rw [single_same, single_same]
  · rw [single_ne v _ hw, single_ne v _ hw, zero_mul]

theorem psiV_ne_one_of_trace {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ)
    (hinf : ∀ a : F, psiInf F ψ (algebraMap F (Ainf F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F a : ℚ) : ℂ))) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y, psiV F ψ v y ≠ 1 := by
  by_contra hn
  push Not at hn
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  have hd1 : algebraMap F (Fv F v) (d : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact_mod_cast hd0
  obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)
  have key := (fin_conductor (fun y => ψ (pairA F 0 y))
    (h.1.comp (Continuous.prodMk continuous_const continuous_id))
    (fun a b => by
      rw [← AddChar.map_add_eq_mul]
      exact congrArg ψ (Prod.ext (add_zero _).symm rfl))
    (fun a => by rw [GlobalTheory.StdRat.char_fin_rat ψ h, hinf]) (singleV F v (z * (algebraMap F (Fv F v) (d : F))⁻¹))).1
    (fun t _ => by rw [single_mul]; exact hn _) d hd v
  have h1 : (singleV F v (z * (algebraMap F (Fv F v) (d : F))⁻¹) * algebraMap F (Af F) (d : F)) v = z := by
    rw [single_mul, single_same]
    show z * (algebraMap F (Fv F v) (d : F))⁻¹ * algebraMap F (Fv F v) (d : F) = z
    rw [inv_mul_cancel_right₀ hd1]
  rw [h1, HeightOneSpectrum.mem_adicCompletionIntegers, hz, ← WithZero.exp_zero, WithZero.exp_le_exp] at key
  omega

theorem sum_places_eq_trace [IsTotallyReal F] (x : F) :
    (((∑ w : InfinitePlace F, (w.embedding x).re : ℝ)) : ℂ) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  apply _root_.GlobalTheory.SnMass.Inhab.sum_places_eq_trace <;> assumption

end Local

theorem exists_psiV_ne_one : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ x : Ainf F, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))) → ∀ v : HeightOneSpectrum (𝓞 F), ∃ r, psiV F ψ v r ≠ 1 := by
  intro F _ _ hF ψ hψ hinf v
  refine psiV_ne_one_of_trace hψ (fun a => ?_) v
  rw [hinf, ← sum_places_eq_trace]
  refine congrArg (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))
    (Finset.sum_congr rfl fun w _ => congrArg Complex.re ?_)
  rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe]
  simp

end GlobalTheory.StdCharTotReal
end
