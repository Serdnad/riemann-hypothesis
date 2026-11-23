module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle256
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle316
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle026
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle002

@[expose] public section

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom

theorem measPolish_UJ (n : ℕ) (ε : Fin n → Bool) : PolishSpace (Formalism.REAL.UJ ε) := by
  haveI : PolishSpace (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (PolishSpace (Fin n → Fin n → ℂ))
  exact (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.polishSpace

variable {D : D7}

theorem measCont_trX (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) : Continuous (trX X C) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun x : X.B.I.Ginf => C.Qi τ * Formalism.MainNotions.S.uMat (x (vOf X τ)) * C.Q τ
  refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
  exact (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply _)

theorem measInj_trX (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) : Function.Injective (trX X C) := by
  intro x y h
  funext v
  obtain ⟨τ, rfl⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, by simp [vOf]⟩
  have h2 : C.Qi τ * Formalism.MainNotions.S.uMat (x (vOf X τ)) * C.Q τ =
      C.Qi τ * Formalism.MainNotions.S.uMat (y (vOf X τ)) * C.Q τ := congrFun h τ
  obtain ⟨-, h1, -⟩ := C.isT τ
  have h3 := congrArg (fun M => C.Q τ * M * C.Qi τ) h2
  simp only [Matrix.mul_assoc, h1, Matrix.mul_one] at h3
  simp only [← Matrix.mul_assoc, h1, Matrix.one_mul] at h3
  exact Subtype.ext (Units.ext h3)

theorem measTauOf_mk (D : D7) (τ : D.what₂.Tau) : tauOf D (InfinitePlace.mk (embS D τ)) = τ :=
  (GlobalTheory.RealPlaces.existsUnique_place D _).unique
    (GlobalTheory.RealPlaces.existsUnique_place D _).exists.choose_spec rfl

theorem measInj_cjw (D : D7) (w : InfinitePlace D.host.E) : Function.Injective (cjw D w) := by
  intro M N h
  by_cases hw : Direct D w
  · simpa [cjw, hw] using h
  · simp only [cjw, hw, if_false] at h
    funext i j
    simpa using congrArg star (congrFun (congrFun h i) j)

theorem measCont_Gm (D : D7) : Continuous (Gm D) := by
  refine continuous_pi fun w => ?_
  by_cases hw : Direct D w
  · simp only [Gm, cjw, hw, if_true]
    exact continuous_apply _
  · simp only [Gm, cjw, hw, if_false]
    exact continuous_pi fun i => continuous_pi fun j =>
      continuous_star.comp ((continuous_apply j).comp ((continuous_apply i).comp (continuous_apply _)))

theorem measInj_Gm (D : D7) : Function.Injective (Gm D) := by
  intro y z h
  funext τ
  have := congrFun h (InfinitePlace.mk (embS D τ))
  simp only [Gm, measTauOf_mk] at this
  exact measInj_cjw D _ this

theorem measurableSet_Gm_trX_image : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (S : Set X.B.I.Ginf),
    MeasurableSet S → MeasurableSet (Gm D '' (trX X C '' S)) := by
  intro D X θ C S hS
  haveI : ∀ v, PolishSpace (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => measPolish_UJ _ _
  rw [Set.image_image]
  exact hS.image_of_continuousOn_injOn ((measCont_Gm D).comp (measCont_trX X C)).continuousOn
    ((measInj_Gm D).comp (measInj_trX X C)).injOn

end GlobalTheory.CovDom
end
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom.RealPts

theorem jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

def mkUJc {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨⟨A, Formalism.REAL.Jm ε * Aᴴ * Formalism.REAL.Jm ε,
    by
      rw [mul_eq_one_comm]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, h, jm_mul_self],
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, h, jm_mul_self]⟩, h⟩

theorem uMat_mkUJc {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε) : Formalism.MainNotions.S.uMat (mkUJc ε A h) = A := rfl

theorem hpk_star (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r).map star = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  simp only [Matrix.map_apply]
  unfold Formalism.QuantumDeterminants.Hpk
  split_ifs <;> simp

theorem tauOf_spec (D : D7) (w : InfinitePlace D.host.E) : InfinitePlace.mk (embS D (tauOf D w)) = w := by
  unfold tauOf
  exact (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose_spec

theorem tauOf_mk (D : D7) (τ : D.what₂.Tau) : tauOf D (InfinitePlace.mk (embS D τ)) = τ :=
  (GlobalTheory.RealPlaces.existsUnique_place D _).unique (tauOf_spec D _) rfl

theorem cjw_cjw (D : D7) (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    cjw D w (cjw D w M) = M := by
  unfold cjw
  split_ifs with h
  · rfl
  · funext i j
    simp

theorem cjw_injective (D : D7) (w : InfinitePlace D.host.E) : Function.Injective (cjw D w) := by
  intro M N hMN
  rw [← cjw_cjw D w M, hMN, cjw_cjw]

theorem of_cjw_mul (D : D7) (w : InfinitePlace D.host.E) (A B : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    Matrix.of (cjw D w (Matrix.of.symm (Matrix.of A * Matrix.of B))) =
      Matrix.of (cjw D w A) * Matrix.of (cjw D w B) := by
  unfold cjw
  split_ifs with h
  · ext i j
    rfl
  · ext i j
    simp [Matrix.mul_apply, star_sum]

private theorem hpk_apply_of_outer_index (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    star (Formalism.QuantumDeterminants.Hpk k r i j) = Formalism.QuantumDeterminants.Hpk k r i j := by
  have e := congrFun (congrFun (hpk_star k r) i) j
  simpa only [Matrix.map_apply] using e

theorem cjw_mem (D : D7) (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
    (hM : Matrix.of M ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    Matrix.of (cjw D w M) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  unfold cjw
  split_ifs with h
  · exact hM
  · simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at hM ⊢
    have e : (Matrix.of fun i j => star (M i j))ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (Matrix.of fun i j => star (M i j))
        = ((Matrix.of M)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of M).map star := by
      ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, star_sum,
        star_mul', star_star, hpk_apply_of_outer_index]
    rw [e, hM, hpk_star]

end GlobalTheory.CovDom.RealPts

namespace GlobalTheory.CovDom.RealPts

theorem trX_of {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (g : X.B.I.Ginf) (τ : D.what₂.Tau) :
    Matrix.of (trX X C g τ) = C.Qi τ * Formalism.MainNotions.S.uMat (g (vOf X τ)) * C.Q τ := rfl

private theorem of_trX_mul_eq_mul {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (s g : X.B.I.Ginf)
    (τ : D.what₂.Tau) :
    Matrix.of (trX X C (s * g) τ) = Matrix.of (trX X C s τ) * Matrix.of (trX X C g τ) := by
  have hQ : C.Q τ * C.Qi τ = 1 := (C.isT τ).2.1
  rw [trX_of, trX_of, trX_of]
  simp only [Pi.mul_apply, Formalism.MainNotions.S.uMat, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQ, Matrix.one_mul]

private theorem eq_of_mul_mul_eq_of_det_ne_zero {n m : ℕ} (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (hQ : Q * Qi = 1) (A : Matrix (Fin n) (Fin n) ℂ) : Q * (Qi * A * Q) * Qi = A := by
  simp only [← Matrix.mul_assoc, hQ, Matrix.one_mul]
  rw [Matrix.mul_assoc, hQ, Matrix.mul_one]

private theorem hcompl_unit_property_of_isPrime {n m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (H N : Matrix (Fin m) (Fin m) ℂ)
    (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (hQ : Q * Qi = 1) (hJ : Qᴴ * J * Q = H) (hN : Nᴴ * H * N = H) :
    (Q * N * Qi)ᴴ * J * (Q * N * Qi) = J := by
  have e : (Q * N * Qi)ᴴ * J * (Q * N * Qi) = Qiᴴ * (Nᴴ * (Qᴴ * J * Q) * N) * Qi := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e' : (Q * Qi)ᴴ * J * (Q * Qi) = Qiᴴ * (Qᴴ * J * Q) * Qi := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hJ, hN, ← hJ, ← e', hQ]
  simp

end GlobalTheory.CovDom.RealPts

namespace GlobalTheory.CovDom

open GlobalTheory.CovDom.RealPts

theorem transport_real_points : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ),
    (∀ x : InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS, (∀ w, Matrix.of (x w) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) →
      ∃ g : X.B.I.Ginf, Gm D (trX X C g) = x) ∧
    Function.Injective (fun g : X.B.I.Ginf => Gm D (trX X C g)) ∧
    ∀ (s g : X.B.I.Ginf) (w : InfinitePlace D.host.E),
      Matrix.of (Gm D (trX X C (s * g)) w) = Matrix.of (Gm D (trX X C s) w) * Matrix.of (Gm D (trX X C g) w) := by
  intro D X θ C
  refine ⟨?_, ?_, ?_⟩
  ·
    intro x hx
    have hM : ∀ τ, Matrix.of (cjw D (InfinitePlace.mk (embS D τ)) (x (InfinitePlace.mk (embS D τ)))) ∈
        Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
      fun τ => cjw_mem D _ _ (hx _).1
    have hU : ∀ v, (C.Q (X.pl v) * Matrix.of (cjw D (InfinitePlace.mk (embS D (X.pl v)))
          (x (InfinitePlace.mk (embS D (X.pl v))))) * C.Qi (X.pl v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) *
        (C.Q (X.pl v) * Matrix.of (cjw D (InfinitePlace.mk (embS D (X.pl v)))
          (x (InfinitePlace.mk (embS D (X.pl v))))) * C.Qi (X.pl v)) = Formalism.REAL.Jm (X.B.I.ε v) := by
      intro v
      have hT := C.isT (X.pl v)
      simp only [IsTranspC, vOf, Equiv.symm_apply_apply] at hT
      exact hcompl_unit_property_of_isPrime _ _ _ _ _ hT.2.1 hT.2.2.1 (hM _)
    refine ⟨fun v => mkUJc (X.B.I.ε v) _ (hU v), ?_⟩
    have key : ∀ τ, trX X C (fun v => mkUJc (X.B.I.ε v) _ (hU v)) τ =
        cjw D (InfinitePlace.mk (embS D τ)) (x (InfinitePlace.mk (embS D τ))) := by
      intro τ
      apply Matrix.of.injective
      have hQi : C.Qi τ * C.Q τ = 1 := (C.isT τ).1
      simp only [trX_of, uMat_mkUJc, vOf, Equiv.apply_symm_apply]
      exact eq_of_mul_mul_eq_of_det_ne_zero (C.Qi τ) (C.Q τ) hQi _
    funext w
    simp only [Gm, key, tauOf_spec, cjw_cjw]
  ·
    intro s g hsg
    funext v
    obtain ⟨τ, rfl⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, X.pl.symm_apply_apply v⟩
    have hw := congrFun hsg (InfinitePlace.mk (embS D τ))
    simp only [Gm, tauOf_mk] at hw
    have h2 := congrArg Matrix.of (cjw_injective D _ hw)
    rw [trX_of, trX_of] at h2
    have h3 := congrArg (fun N => C.Q τ * N * C.Qi τ) h2
    simp only [eq_of_mul_mul_eq_of_det_ne_zero (C.Q τ) (C.Qi τ) (C.isT τ).2.1] at h3
    exact Subtype.ext (Units.ext h3)
  ·
    intro s g w
    simp only [Gm]
    rw [← of_cjw_mul, ← of_trX_mul_eq_mul, Equiv.symm_apply_apply]

end GlobalTheory.CovDom
end
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDomGrp

variable {D : D7} (X : HidaSetting D)

theorem vecOf_apply (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    vecOf X c = ∑ i, c i • X.bas (ci X i) := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.funCongrLeft_apply, Module.Basis.equivFun_symm_apply]
  rw [← (ci X).sum_comp]
  simp

theorem crdH_vecOf (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) : crdH X (vecOf X c) = c := by
  funext i
  simp only [crdH, vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, LinearEquiv.funCongrLeft_apply]
  simp

theorem vecOf_crdH (y : (VS D).V) : vecOf X (crdH X y) = y := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  conv_rhs => rw [← X.bas.equivFun.symm_apply_apply y]
  congr 1

variable {X} in
theorem n_vecOf {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E}
    (hγ : ∀ y, crdH X (n y) = γ *ᵥ crdH X y) (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    n (vecOf X c) = vecOf X (γ *ᵥ c) := by
  conv_lhs => rw [← vecOf_crdH X (n (vecOf X c)), hγ, crdH_vecOf]

theorem crdH_eq_crd (y : (VS D).V) (i : Fin (2 * D.R.rS + D.R.k + 1)) :
    crdH X y i = X.ιE (X.crd y (ci X i)) := by
  simp [crdH, HidaSetting.crd, crdOf]

theorem sig_apply (a : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) a = star a := rfl

theorem hT_vecOf (a b : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    (VS D).hT (vecOf X a) (vecOf X b) = GlobalTheory.SgAlg.form (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) b a := by
  rw [vecOf_apply, vecOf_apply]

  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
  GlobalTheory.SgAlg.form, dotProduct, Matrix.mulVec, sig_apply, Jc, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply]
  ring

theorem Jc_det_ne_zero : (Jc X).det ≠ 0 := by
  have h : Jc X = (X.B.I.J.map X.ιE).submatrix (ci X) (ci X) := by
    ext i j
    simp [Jc, X.J_eq]
  rw [h, Matrix.det_submatrix_equiv_self]
  intro h0
  apply X.B.I.J_det
  apply X.ιE.injective
  rw [map_zero]
  exact (RingHom.map_det X.ιE.toRingHom X.B.I.J).trans h0

def coordEquiv : (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) ≃ₗ[D.host.E] (VS D).V :=
  (LinearEquiv.funCongrLeft D.host.E D.host.E (ci X).symm).trans X.bas.equivFun.symm

theorem coordEquiv_apply (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) : coordEquiv X c = vecOf X c := rfl

theorem coordEquiv_symm_apply (y : (VS D).V) : (coordEquiv X).symm y = crdH X y := by
  apply (coordEquiv X).injective
  rw [LinearEquiv.apply_symm_apply, coordEquiv_apply, vecOf_crdH]

theorem exists_mat (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    ∃ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, ∀ y, crdH X (n y) = γ *ᵥ crdH X y := by
  refine ⟨LinearMap.toMatrix' (((coordEquiv X).symm.toLinearMap ∘ₗ n.toLinearMap) ∘ₗ (coordEquiv X).toLinearMap), fun y => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  simp [coordEquiv_symm_apply, coordEquiv_apply, vecOf_crdH]

theorem exists_equiv (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E) (hU : GlobalTheory.SgAlg.IsUn (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) γ) :
    ∃ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, ∀ y, crdH X (n y) = γ *ᵥ crdH X y := by
  have hdet : IsUnit γ.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply Jc_det_ne_zero X
    have := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  have h1 : γ⁻¹ * γ = 1 := Matrix.nonsing_inv_mul γ hdet
  have h2 : γ * γ⁻¹ = 1 := Matrix.mul_nonsing_inv γ hdet
  refine ⟨(coordEquiv X).symm.trans ((Matrix.toLin'OfInv h1 h2).trans (coordEquiv X)), fun y => ?_⟩
  simp only [LinearEquiv.trans_apply, coordEquiv_symm_apply, coordEquiv_apply, Matrix.toLin'OfInv_apply,
    Matrix.toLin'_apply, crdH_vecOf]
  rfl

end GlobalTheory.CovDomGrp
end
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDom

variable {D : D7} (X : HidaSetting D)

theorem vecOf_apply (x : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    vecOf X x = ∑ i, x i • X.bas (ci X i) := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Module.Basis.equivFun_symm_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  exact Fintype.sum_equiv (ci X).symm _ _ fun j => by simp

theorem vecOf_bijective : Function.Bijective (vecOf X) := by
  unfold vecOf
  rw [LinearMap.coe_comp]
  exact X.bas.equivFun.symm.bijective.comp (LinearEquiv.funCongrLeft _ _ _).bijective

private theorem sig_eq_star' (a : D.host.E) : D.sp.cm.sig a = star a := by rfl

theorem form_Jc (x y : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    GlobalTheory.SgAlg.form (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) x y = (VS D).hT (vecOf X y) (vecOf X x) := by
  rw [vecOf_apply, vecOf_apply]

  simp only [GlobalTheory.SgAlg.form, dotProduct, Matrix.mulVec, Jc, map_sum, map_smulₛₗ,
  LinearMap.sum_apply, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [AlgHom.coe_toRingHom, sig_eq_star', starRingEnd_apply]
  ring

end GlobalTheory.CovDom

theorem GlobalTheory.CovDom.herm_selfDual : ∀ (D : D7) (X : HidaSetting D), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND D.sp.cm.sig (Jc X) ∧ GlobalTheory.SgGlob.SelfDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Lc X) := by
  intro D X
  have hform := form_Jc X
  have hinj := (vecOf_bijective X).1
  have hsurj := (vecOf_bijective X).2
  unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND GlobalTheory.SgGlob.SelfDual
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_, fun v => ?_⟩
  · simp only [Jc]
    rw [sig_eq_star']
    exact (VS D).herm.eq _ _
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    apply hv0
    apply hinj
    rw [map_zero]
    apply (VS D).nondeg.2
    intro w
    obtain ⟨y, rfl⟩ := hsurj w
    rw [← hform v y]
    simp [GlobalTheory.SgAlg.form, hv]
  · let e : (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) ≃ₗ[𝓞 D.host.E] (VS D).V :=
      (LinearEquiv.ofBijective (vecOf X) (vecOf_bijective X)).restrictScalars (𝓞 D.host.E)
    have hc : Lc X = (VS D).L0.comap (e : _ →ₗ[𝓞 D.host.E] (VS D).V) := rfl
    rw [hc, Submodule.comap_equiv_eq_map_symm]
    exact (VS D).standardTuple_isLattice.fg.map _
  · show vecOf X v ∈ (VS D).L0 ↔ _
    conv_lhs => rw [← (VS D).baseLattice_isUnimodular]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply]
    constructor
    · intro h w hw
      rw [hform v w]
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp (h _ hw)
      exact ⟨a, ha⟩
    · intro h y hy
      obtain ⟨w, rfl⟩ := hsurj y
      have hw := h w hy
      rw [hform v w] at hw
      obtain ⟨a, ha⟩ := hw
      exact Submodule.mem_one.mpr ⟨a, ha⟩
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isometry_transports_discriminantModule : ∀ (K V V' : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (e : V ≃ₗ[K] V'), (∀ x y, h' (e x) (e y) = h x y) → ∀ (L : Submodule (𝓞 K) V) (I : Ideal (𝓞 K)), GlobalTheory.Mass.IsIntLat h' (GlobalTheory.Mass.Transp.img e L) → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L)) ⧸ (GlobalTheory.Mass.Transp.img e L).comap (Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L)).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ I)) → GlobalTheory.Mass.IsIntLat h L ∧ Nonempty ((↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ I)) := by
  first | exact @GlobalTheory.Mass.Transp.discModule_transport | exact GlobalTheory.Mass.Transp.discModule_transport | (intros; apply GlobalTheory.Mass.Transp.discModule_transport <;> assumption)
end
