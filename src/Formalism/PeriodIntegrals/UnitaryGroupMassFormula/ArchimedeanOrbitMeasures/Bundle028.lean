module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle027
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle023
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceAll
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def gramH {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) D.host.E :=
  Matrix.of fun i j => (VS D).hT (wF X u' i) (wF X u' j)

theorem gram_sq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) :
    gramH X u' * gramH X u' =
    Matrix.diagonal (Fin.append (Fin.snoc (fun _ : Fin D.R.rS => (1 : D.host.E))
      ((((D.mem u').A.T : ℕ) : D.host.E) * (((D.mem u').A.T : ℕ) : D.host.E))) (fun _ : Fin D.R.rS => 1)) := by
  have h1 : ∀ b : Fin D.R.rS, Fin.last D.R.rS ≠ b.castSucc := fun b h => (Fin.castSucc_lt_last b).ne' h
  have h1' : ∀ b : Fin D.R.rS, b.castSucc ≠ Fin.last D.R.rS := fun b h => (Fin.castSucc_lt_last b).ne h
  have h2 : ∀ (x : Fin (D.R.rS + 1)) (y : Fin D.R.rS), Fin.castAdd D.R.rS x ≠ Fin.natAdd (D.R.rS + 1) y := by
    intro x y h
    have := congrArg Fin.val h
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
    omega
  have h2' : ∀ (x : Fin (D.R.rS + 1)) (y : Fin D.R.rS), Fin.natAdd (D.R.rS + 1) y ≠ Fin.castAdd D.R.rS x :=
    fun x y h => h2 x y h.symm
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_add, Fin.sum_univ_castSucc]
  refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i <;> refine Fin.addCases (fun j1 => ?_) (fun j2 => ?_) j
  · refine Fin.lastCases ?_ (fun a => ?_) i1 <;> refine Fin.lastCases ?_ (fun b => ?_) j1 <;>
      simp [gramH, wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ff, X.ef,
        hT_fe, hT_ze, hT_zf, (X.zu_orth u' _).1, (X.zu_orth u' _).2, X.zu_norm, Matrix.diagonal_apply, h1, h1', h2, h2', eq_comm]
  · refine Fin.lastCases ?_ (fun a => ?_) i1 <;>
      simp [gramH, wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ff, X.ef,
        hT_fe, hT_ze, hT_zf, (X.zu_orth u' _).1, (X.zu_orth u' _).2, X.zu_norm, Matrix.diagonal_apply, h1, h1', h2, h2', eq_comm]
  · refine Fin.lastCases ?_ (fun b => ?_) j1 <;>
      simp [gramH, wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ff, X.ef,
        hT_fe, hT_ze, hT_zf, (X.zu_orth u' _).1, (X.zu_orth u' _).2, X.zu_norm, Matrix.diagonal_apply, h1, h1', h2, h2', eq_comm]
  · simp [gramH, wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ff, X.ef,
      hT_fe, hT_ze, hT_zf, (X.zu_orth u' _).1, (X.zu_orth u' _).2, X.zu_norm, Matrix.diagonal_apply, h1, h1', h2, h2', eq_comm]

theorem detT_holds : DetT := by
  intro D X u' ψ hT μinf νinf fibInf hP v
  have hGH : gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) = (gramH X u').map X.ιE.symm := by
    ext i j
    rw [gram_eq]
    rfl
  have hdet : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det = X.ιE.symm (gramH X u').det := by
    rw [hGH]
    exact (RingHom.map_det (X.ιE.symm : D.host.E →+* X.B.I.E) _).symm
  have hsq : (gramH X u').det ^ 2 = (((D.mem u').A.T : ℕ) : D.host.E) ^ 2 := by
    have h := congrArg Matrix.det (gram_sq X u')
    rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_add, Fin.prod_univ_castSucc] at h
    simp only [Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, Finset.prod_const_one,
      one_mul, mul_one] at h
    rw [sq, sq]
    exact h
  have hz : (X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det) ^ 2 =
      ((((D.mem u').A.T : ℕ) : ℂ)) ^ 2 := by
    rw [hdet, ← map_pow, ← map_pow, hsq, map_pow, map_pow, map_natCast, map_natCast]
  have hn : ‖X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det‖ ^ 2 = (Tw u') ^ 2 := by
    rw [← norm_pow, hz, norm_pow, Complex.norm_natCast]
    rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (by unfold Tw; positivity)).1 hn

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

theorem hasFDerivAt_conj_exp {ι : Type} [Fintype ι] {n : ℕ}
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    ∃ D : EuclideanSpace ℝ ι →L[ℝ] (Fin n → ℂ),
      HasFDerivAt (fun y => (A * NormedSpace.exp (L y) * B) *ᵥ w) D 0 ∧ ∀ y, D y = (A * L y * B) *ᵥ w := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  let Lc : EuclideanSpace ℝ ι →L[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap L
  let h : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin n → ℂ) :=
    { toFun := fun M => (A * M * B) *ᵥ w
      map_add' := fun M N => by simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec]
      map_smul' := fun r M => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
        ext i
        simp [Matrix.mulVec, dotProduct, Finset.smul_sum, mul_assoc] }
  let hc : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap h
  have hexp : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (Lc 0) := by
    rw [map_zero]; exact hasFDerivAt_exp_zero
  have h1 := hc.hasFDerivAt.comp (0 : EuclideanSpace ℝ ι) (hexp.comp (0 : EuclideanSpace ℝ ι) Lc.hasFDerivAt)
  refine ⟨hc.comp ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ).comp Lc), h1, fun y => rfl⟩

theorem dKForm_holds : DKForm := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S ι _ L hc hL x v
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  let Φ : TupI X →+ (InfinitePlace X.B.I.F → Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → ℂ) :=
    { toFun := fun Y v b i => PI.AprimeInfU.thetaInf X v (Y b i)
      map_zero' := by funext v b i; exact map_zero _
      map_add' := by intro Y Z; funext v b i; exact map_add _ _ _ }
  have hsa : ∀ z z', (tupCoord X).symm (z + z') = (tupCoord X).symm z + (tupCoord X).symm z' := by
    intro z z'; apply (tupCoord X).injective; rw [tupCoord_add]; simp
  let T0 : EuclideanSpace ℝ (KapI X) →+ TupI X :=
    { toFun := (tupCoord X).symm
      map_zero' := by
        have h := hsa 0 0
        rw [add_zero] at h
        simpa using h
      map_add' := hsa }
  let Ψ0 := Φ.comp T0
  have hc0 : Continuous Ψ0 := by
    refine continuous_pi fun v => continuous_pi fun b => continuous_pi fun i => ?_
    exact (continuous_thetaInf X v).comp ((continuous_apply i).comp ((continuous_apply b).comp
      (tupCoord X).symm.continuous))
  let Ψ := Ψ0.toRealLinearMap hc0
  have hΨ : ∀ z v b i, Ψ z v b i = PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z b i) := fun _ _ _ _ => rfl
  have hinj : Function.Injective Ψ := by
    intro z z' h
    apply (tupCoord X).symm.injective
    funext b i
    have key : ∀ v, PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z b i) =
        PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z' b i) := by
      intro v
      rw [← hΨ, ← hΨ, h]
    exact sub_eq_zero.1 (thetaInf_inj X _ fun v => by rw [map_sub, key v, sub_self])
  have hcbi : Fintype.card (Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex,
      Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (Ainf X.B.I.F)
        (Module.finBasisOfFinrankEq X.B.I.F X.B.I.E X.B.I.cm.deg2)), Fintype.card_fin]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (KapI X)) =
      Module.finrank ℝ (InfinitePlace X.B.I.F → Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → ℂ) := by
    simp only [finrank_euclideanSpace, Fintype.card_prod, hcbi, Module.finrank_pi_fintype,
      Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin]
    ring
  let Ψe := LinearMap.linearEquivOfInjective (Ψ : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] _) hinj hdim
  have hΨe : ∀ Z : TupI X, tupCoord X Z = Ψe.symm (Φ Z) := by
    intro Z
    apply Ψe.injective
    rw [LinearEquiv.apply_symm_apply, LinearMap.linearEquivOfInjective_apply]
    show Φ (T0 (tupCoord X Z)) = Φ Z
    simp [T0]
  have hG : ∀ x v b, (fun i => Φ (kap0 X hb c L x • Y0 X u') v b i) =
      ((X.B.I.P v * uMat (c v)) * NormedSpace.exp (L x v) * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
        fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
    intro x v b
    funext i
    show PI.AprimeInfU.thetaInf X v ((X.toInf hb (c * (fun w => expU (X.B.I.ε w) (L x w)) * c⁻¹) • Y0 X u') b i) = _
    rw [theta_act]
    have hu : uMat ((c * (fun w => expU (X.B.I.ε w) (L x w)) * c⁻¹) v) =
        uMat (c v) * NormedSpace.exp (L x v) * uMat (c v)⁻¹ := by
      have e := expU_val (X.B.I.ε v) (L x v) (hL.1 x v).1
      simp only [uMat, Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] at e ⊢
      rw [e]
    rw [hu]
    simp only [Matrix.mul_assoc]

  have hD : ∀ v b, ∃ Dvb : EuclideanSpace ℝ ι →L[ℝ] (Fin X.B.I.n → ℂ),
      HasFDerivAt (fun x => Φ (kap0 X hb c L x • Y0 X u') v b) Dvb 0 ∧
        ∀ y, Dvb y = ((X.B.I.P v * uMat (c v)) * L y v * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
          fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
    intro v b
    obtain ⟨Dvb, h1, h2⟩ := hasFDerivAt_conj_exp ((LinearMap.proj v : (InfinitePlace X.B.I.F →
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) →ₗ[ℝ] _) ∘ₗ L) (X.B.I.P v * uMat (c v)) (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)
      (fun j => X.B.I.φ v (tupH (frameOf X u') b j))
    refine ⟨Dvb, ?_, fun y => h2 y⟩
    have e : (fun x => Φ (kap0 X hb c L x • Y0 X u') v b) = fun x =>
        ((X.B.I.P v * uMat (c v)) * NormedSpace.exp (((LinearMap.proj v : (InfinitePlace X.B.I.F →
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) →ₗ[ℝ] _) ∘ₗ L) x) * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
          fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
      funext x
      exact hG x v b
    rw [e]
    exact h1
  choose Dv hDv1 hDv2 using hD
  let DD : EuclideanSpace ℝ ι →L[ℝ] (InfinitePlace X.B.I.F → Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → ℂ) :=
    ContinuousLinearMap.pi fun v => ContinuousLinearMap.pi fun b => Dv v b
  have hGd : HasFDerivAt (fun x => Φ (kap0 X hb c L x • Y0 X u')) DD 0 :=
    hasFDerivAt_pi.2 fun v => hasFDerivAt_pi.2 fun b => hDv1 v b
  have hK : KapOrb X u' (kap0 X hb c L) = fun x => Ψe.symm (Φ (kap0 X hb c L x • Y0 X u')) := by
    funext x
    exact hΨe _
  have hKd : HasFDerivAt (KapOrb X u' (kap0 X hb c L))
      (Ψe.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp DD) 0 := by
    rw [hK]
    exact Ψe.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp (0 : EuclideanSpace ℝ ι) hGd
  rw [hKd.fderiv]
  have hΦ : Φ ((tupCoord X).symm (Ψe.symm (DD x))) = DD x := by
    have h1 : Ψe (Ψe.symm (DD x)) = DD x := Ψe.apply_symm_apply (DD x)
    rw [LinearMap.linearEquivOfInjective_apply] at h1
    exact h1
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  ext i b
  have e1 : (fun j => PI.AprimeInfU.thetaInf X v ((tupCoord X).symm (Ψe.symm (DD x)) b j)) = DD x v b :=
    funext fun j => congrFun (congrFun (congrFun hΦ v) b) j
  have hY0 : (fun j => PI.AprimeInfU.thetaInf X v (Y0 X u' b j)) = fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
    funext j
    rw [show Y0 X u' b j = inclR (Ainf X.B.I.F) (tupH (frameOf X u') b j) from rfl, thetaInf_inclR]
  show ((X.B.I.P v)⁻¹ *ᵥ fun j => PI.AprimeInfU.thetaInf X v ((tupCoord X).symm (Ψe.symm (DD x)) b j)) i =
    (uMat (c v) * L x v * uMat (c v)⁻¹ * betaV X v (Y0 X u')) i b
  rw [e1, show DD x v b = Dv v b x from rfl, hDv2]
  have eR : (uMat (c v) * L x v * uMat (c v)⁻¹ * betaV X v (Y0 X u')) i b =
      ((uMat (c v) * L x v * uMat (c v)⁻¹) *ᵥ ((X.B.I.P v)⁻¹ *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j))) i := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    show ((X.B.I.P v)⁻¹ *ᵥ fun j => PI.AprimeInfU.thetaInf X v (Y0 X u' b j)) k = _
    rw [hY0]
    rfl
  have hM : (X.B.I.P v)⁻¹ * (X.B.I.P v * uMat (c v) * L x v * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) =
      uMat (c v) * L x v * uMat (c v)⁻¹ * (X.B.I.P v)⁻¹ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu,
      Matrix.one_mul, Matrix.mul_assoc (uMat (c v) * L x v)]
  rw [eR, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix
open scoped ENNReal NNReal

section Lin

variable {n m : ℕ} {α β : Type} [Fintype α] [Fintype β]

def jacM (w : Matrix (Fin n) (Fin m) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (Lv : EuclideanSpace ℝ α →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (Hv : EuclideanSpace ℝ β →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) :
    (EuclideanSpace ℝ α × EuclideanSpace ℝ β) →ₗ[ℝ] (Fin n → Fin m → ℂ) where
  toFun z := (Lv z.1 * w + (1 / 2 : ℂ) • (B * Hv z.2) : Matrix (Fin n) (Fin m) ℂ)
  map_add' z z' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add (f := _), Matrix.add_mul, Matrix.mul_add, smul_add]
    abel
  map_smul' r z := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Matrix.smul_mul, Matrix.mul_smul, RingHom.id_apply]
    rw [smul_comm]
    exact (smul_add _ _ _).symm

def mulCR (c : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℝ (Fin n × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin m × Bool) :=
  (reimE (r := n) (m := m)).toLinearMap ∘ₗ ((mulLC (c := m) c).restrictScalars ℝ) ∘ₗ
    (reimE (r := n) (m := m)).symm.toLinearMap

theorem mulCR_apply (c : Matrix (Fin n) (Fin n) ℂ) (y : EuclideanSpace ℝ (Fin n × Fin m × Bool)) :
    mulCR c y = reim (c * Matrix.of ((reimE (r := n) (m := m)).symm y)) := by
  unfold mulCR
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars, mulLC_apply]
  rfl

end Lin

def flatL (V β : Type) [Fintype V] [Fintype β] :
    (∀ _ : V, EuclideanSpace ℝ β) →ₗ[ℝ] EuclideanSpace ℝ (V × β) where
  toFun z := WithLp.toLp 2 (fun p : V × β => z p.1 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flatL_pres (V β : Type) [Fintype V] [Fintype β] :
    (Measure.pi fun _ : V => (volume : Measure (EuclideanSpace ℝ β))).map (flatL V β) = volume := by
  classical
  have hmeas : Measurable (fun z : V → β → ℝ => Function.uncurry z) := by
    have h := (MeasurableEquiv.curry V β ℝ).symm.measurable
    rw [MeasurableEquiv.coe_curry_symm] at h
    exact h
  have hU : MeasurePreserving (fun z : V → β → ℝ => Function.uncurry z) volume volume := by
    refine ⟨hmeas, ?_⟩
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
    have hpre : (fun z : V → β → ℝ => Function.uncurry z) ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ (fun v => Set.pi Set.univ (fun b => s (v, b))) := by
      ext z
      simp [Function.uncurry]
    rw [hpre, volume_pi, Measure.pi_pi]
    simp only [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  have hP := volume_preserving_pi (fun _ : V => PiLp.volume_preserving_ofLp β)
  have hT := PiLp.volume_preserving_toLp (V × β)
  have h := (hT.comp hU).comp hP
  have hf : (⇑(flatL V β)) = (WithLp.toLp 2 ∘ fun z : V → β → ℝ => Function.uncurry z) ∘
      (fun z : V → EuclideanSpace ℝ β => fun v => WithLp.ofLp (z v)) := by
    funext z
    rfl
  rw [hf]
  exact h.map_eq

theorem detJm_ne {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε).det ≠ 0 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 (fun a _ => by split_ifs <;> norm_num)

theorem normSq_det_of_unitary {n : ℕ} (ε : Fin n → Bool) (c : Matrix (Fin n) (Fin n) ℂ)
    (hc : cᴴ * Formalism.REAL.Jm ε * c = Formalism.REAL.Jm ε) : Complex.normSq c.det = 1 := by
  have h := congrArg Matrix.det hc
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ := detJm_ne ε
  have h2 : star c.det * c.det = 1 := by
    have e : (star c.det * c.det) * (Formalism.REAL.Jm ε).det = 1 * (Formalism.REAL.Jm ε).det := by
      rw [one_mul]
      nth_rewrite 2 [← h]
      ring
    exact mul_right_cancel₀ hJ e
  have h3 : ((Complex.normSq c.det : ℝ) : ℂ) = 1 := by
    rw [← Complex.mul_conj, mul_comm]
    exact h2
  exact_mod_cast h3

theorem placeJacAll_of (h : PlaceJac) : PlaceJacAll := by
  set_option synthInstance.maxHeartbeats 200000 in
    classical
    intro V _ n m ε S w c ι κ _ _ L H hn hw hG hc hL1 hL2 hL3 hH1 hH2 hH3
    obtain ⟨ιv, _, Lv, T, hLQ, hLn, hLs, hLT, hTb, hTn⟩ := place_split L
      (fun v M => Mᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M = 0 ∧ ∀ i ∈ S v, ∀ j ∈ S v, M i j = 0)
      hL1 (fun v => ⟨by simp, fun i _ j _ => rfl⟩) hL2 hL3
    obtain ⟨κv, _, Hv, T', hHQ, hHn, hHs, hHT, hT'b, hT'n⟩ := place_split H (fun v M => Mᴴ = M)
      hH1 (fun v => by simp) hH2 hH3
    let G : V → Matrix (Fin m) (Fin m) ℂ := fun v => (w v)ᴴ * Formalism.REAL.Jm (ε v) * w v
    let cst : V → ℝ := fun v => 2 ^ (n * m) / ‖(G v).det‖ ^ (S v).card
    have hcst : ∀ v, 0 < cst v := fun v => div_pos (by positivity) (pow_pos (norm_pos_iff.2 (hG v)) _)
    let Φ : ∀ v, (EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v)) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin n × Fin m × Bool) :=
      fun v => mulCR (c v) ∘ₗ (reimE (r := n) (m := m)).toLinearMap ∘ₗ jacM (w v) (w v * (G v)⁻¹) (Lv v) (Hv v)
    have hΦ : ∀ v z, Φ v z = reim (c v * (Lv v z.1 * w v + (1 / 2 : ℂ) • (w v * (G v)⁻¹ * Hv v z.2))) := by
      intro v z
      simp only [Φ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, mulCR_apply]
      congr 2
    have hPJ : ∀ v, (volume : Measure (EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v))).map
        (fun z => reim (Lv v z.1 * w v + (1 / 2 : ℂ) • (w v * (G v)⁻¹ * Hv v z.2))) =
        ENNReal.ofReal (cst v) • volume :=
      fun v => h n m (ε v) (S v) (w v) (Lv v) (Hv v) (hn v) (hw v) (hG v) (hLQ v) (hLn v)
        (fun M h1 h2 => hLs v M ⟨h1, h2⟩) (hHQ v) (hHn v) (hHs v)
    have hd : ∀ v, (c v).det ≠ 0 := fun v h0 => by
      have := normSq_det_of_unitary (ε v) (c v) (hc v)
      rw [h0] at this
      simp at this
    have hΦm : ∀ v, (volume : Measure (EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v))).map (Φ v) =
        ((cst v).toNNReal : ℝ≥0∞) • volume := by
      intro v
      have e : (Φ v : _ → _) = (mulCR (m := m) (c v)) ∘
          (fun z => reim (Lv v z.1 * w v + (1 / 2 : ℂ) • (w v * (G v)⁻¹ * Hv v z.2))) := rfl
      have hm1 : Measurable (fun z : EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v) =>
          reim (Lv v z.1 * w v + (1 / 2 : ℂ) • (w v * (G v)⁻¹ * Hv v z.2))) :=
        ((reimE (r := n) (m := m)).toLinearMap ∘ₗ
          jacM (w v) (w v * (G v)⁻¹) (Lv v) (Hv v)).continuous_of_finiteDimensional.measurable
      rw [e, ← Measure.map_map (mulCR (m := m) (c v)).continuous_of_finiteDimensional.measurable hm1, hPJ v,
        Measure.map_smul]
      have hC : (volume : Measure (EuclideanSpace ℝ (Fin n × Fin m × Bool))).map (mulCR (m := m) (c v)) = volume := by
        have e2 : (mulCR (m := m) (c v) : _ → _) =
            fun y => reim (c v * Matrix.of ((reimE (r := n) (m := m)).symm y)) := funext (mulCR_apply (c v))
        rw [e2, map_mulL (c v) (hd v), normSq_det_of_unitary (ε v) (c v) (hc v)]
        simp
      rw [hC]
      rfl
      exact (mulCR (m := m) (c v)).continuous_of_finiteDimensional.measurable.aemeasurable
    let F : (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) →ₗ[ℝ] EuclideanSpace ℝ (V × Fin n × Fin m × Bool) :=
      flatL V (Fin n × Fin m × Bool) ∘ₗ
        (LinearMap.pi fun v => Φ v ∘ₗ LinearMap.prodMap (LinearMap.proj v ∘ₗ T) (LinearMap.proj v ∘ₗ T'))
    have hF : ∀ z, F z = reimV (fun v => c v * (L z.1 v * w v +
        (1 / 2 : ℂ) • (w v * ((w v)ᴴ * Formalism.REAL.Jm (ε v) * w v)⁻¹ * H z.2 v))) := by
      intro z
      have e1 : F z = flatL V (Fin n × Fin m × Bool) (fun v => Φ v (T z.1 v, T' z.2 v)) := rfl
      rw [e1]
      simp only [hΦ, hLT, hHT]
      rfl
    have hmT := PI.AprimeInfG.measurePreserving_of_normSq T hTb hTn
    have hmT' := PI.AprimeInfG.measurePreserving_of_normSq T' hT'b hT'n
    have h12 := hmT.prod hmT'
    have h3 := MeasurePreserving.symm (PI.AprimeInfG.piProdEquiv (fun v => EuclideanSpace ℝ (ιv v))
      (fun v => EuclideanSpace ℝ (κv v))) (PI.AprimeInfG.measurePreserving_piProdEquiv
      (fun v => EuclideanSpace ℝ (ιv v)) (fun v => EuclideanSpace ℝ (κv v)) (fun v => volume) (fun v => volume))
    have h123 := h3.comp h12
    have hPm : Measurable (fun x : ∀ v, EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v) => fun v => Φ v (x v)) :=
      Measurable.of_eval fun v => (Φ v).continuous_of_finiteDimensional.measurable.comp (measurable_pi_apply v)
    have h4 := pi_map_smul (fun v => (volume : Measure (EuclideanSpace ℝ (ιv v))).prod volume)
      (fun v => (volume : Measure (EuclideanSpace ℝ (Fin n × Fin m × Bool)))) (fun v => Φ v)
      (fun v => (Φ v).continuous_of_finiteDimensional.measurable) (fun v => (cst v).toNNReal)
      (fun v => by rw [ENNReal.smul_def]; exact hΦm v)
    have hfun : (F : _ → _) = flatL V (Fin n × Fin m × Bool) ∘ ((fun x v => Φ v (x v)) ∘
        ((PI.AprimeInfG.piProdEquiv (fun v => EuclideanSpace ℝ (ιv v)) (fun v => EuclideanSpace ℝ (κv v))).symm ∘
          Prod.map T T')) := rfl
    have hmap : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)).map F =
        ENNReal.ofReal (∏ v, cst v) • volume := by
      rw [hfun, ← Measure.map_map (flatL V (Fin n × Fin m × Bool)).continuous_of_finiteDimensional.measurable
        (hPm.comp h123.measurable), ← Measure.map_map hPm h123.measurable,
        show (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) = volume.prod volume from rfl,
        h123.map_eq, h4, Measure.map_smul, flatL_pres, ENNReal.ofReal_prod_of_nonneg (fun v _ => (hcst v).le)]
      rfl
      exact (flatL V (Fin n × Fin m × Bool)).continuous_of_finiteDimensional.measurable.aemeasurable
    have hpos : ENNReal.ofReal (∏ v, cst v) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Finset.prod_pos fun v _ => hcst v
    have : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)).IsAddHaarMeasure := by
      rw [show (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) = volume.prod volume from rfl]
      infer_instance
    have hbij := bij_of_map (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) volume F _ hpos
      ENNReal.ofReal_ne_top hmap
    exact ⟨(LinearEquiv.ofBijective F hbij).toContinuousLinearEquiv, fun z => hF z, hmap⟩

end PI.AprimeInfW
end
end
