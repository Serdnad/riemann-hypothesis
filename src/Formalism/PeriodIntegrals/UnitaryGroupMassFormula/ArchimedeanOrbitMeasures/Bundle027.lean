module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle024
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarMapContDiffAtBase
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.EqOneOfToHAFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle023
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

def reimV {V : Type} {n m : ℕ} (M : V → Matrix (Fin n) (Fin m) ℂ) : EuclideanSpace ℝ (V × Fin n × Fin m × Bool) :=
  (WithLp.equiv 2 (V × Fin n × Fin m × Bool → ℝ)).symm fun p =>
    if p.2.2.2 then (M p.1 p.2.1 p.2.2.1).re else (M p.1 p.2.1 p.2.2.1).im

def BetaIso : Prop := ∀ {D : D7} (X : HidaSetting D),
    ∃ Bc : EuclideanSpace ℝ (KapI X) ≃L[ℝ]
        EuclideanSpace ℝ (InfinitePlace X.B.I.F × Fin X.B.I.n × Fin (D.R.rS + 1 + D.R.rS) × Bool),
      ∀ Y : TupI X, Bc (tupCoord X Y) = reimV (fun v => betaV X v Y)

def MuBridge : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    μinf.map (fun Y => reimV (fun v => betaV X v Y)) =
      ENNReal.ofReal (2 ^ (X.B.I.n * (D.R.rS + 1 + D.R.rS) * Fintype.card (InfinitePlace X.B.I.F))) • volume

def NuBridge : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∃ (κ : Type) (_ : Fintype κ) (Hh : EuclideanSpace ℝ κ →ₗ[ℝ]
        (InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) ℂ))
      (Tc : HmI X ≃ₜ EuclideanSpace ℝ κ),
      (∀ s v, (Hh s v)ᴴ = Hh s v) ∧ (∀ s, ∑ v, ∑ i, ∑ j, ‖Hh s v i j‖ ^ 2 = ‖s‖ ^ 2) ∧
      (∀ M : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) ℂ,
        (∀ v, (M v)ᴴ = M v) → ∃ s, Hh s = M) ∧
      (∀ S T, Tc (S + T) = Tc S + Tc T) ∧
      (∀ S v, Hh (Tc S) v = (S : Matrix _ _ _).map (PI.AprimeInfU.thetaInf X v)) ∧
      νinf.map Tc = volume

def DKForm : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L →
    ∀ x v, betaV X v ((tupCoord X).symm (fderiv ℝ (KapOrb X u' (kap0 X hb c L)) 0 x)) =
      uMat (c v) * L x v * uMat (c v)⁻¹ * betaV X v (Y0 X u')

def RowsZ : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)), StdConj X hb u' c S →
    ∀ v, ∀ i ∈ S v, ∀ b, (uMat (c v)⁻¹ * betaV X v (Y0 X u')) i b = 0

def DetT : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ v : InfinitePlace X.B.I.F, ‖X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det‖ = Tw u'

def PlaceJacAll : Prop := ∀ (V : Type) [Fintype V] (n m : ℕ) (ε : V → Fin n → Bool) (S : V → Finset (Fin n))
    (w : V → Matrix (Fin n) (Fin m) ℂ) (c : V → Matrix (Fin n) (Fin n) ℂ) {ι κ : Type} [Fintype ι] [Fintype κ]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ))
    (H : EuclideanSpace ℝ κ →ₗ[ℝ] (V → Matrix (Fin m) (Fin m) ℂ)),
    (∀ v, n = m + (S v).card) → (∀ v, ∀ i ∈ S v, ∀ b, w v i b = 0) →
    (∀ v, ((w v)ᴴ * Formalism.REAL.Jm (ε v) * w v).det ≠ 0) →
    (∀ v, (c v)ᴴ * Formalism.REAL.Jm (ε v) * c v = Formalism.REAL.Jm (ε v)) →
    (∀ x v, (L x v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * L x v = 0 ∧ ∀ i ∈ S v, ∀ j ∈ S v, L x v i j = 0) →
    (∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2) →
    (∀ M : V → Matrix (Fin n) (Fin n) ℂ, (∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧
      ∀ i ∈ S v, ∀ j ∈ S v, M v i j = 0) → ∃ x, L x = M) →
    (∀ t v, (H t v)ᴴ = H t v) → (∀ t, ∑ v, ∑ i, ∑ j, ‖H t v i j‖ ^ 2 = ‖t‖ ^ 2) →
    (∀ M : V → Matrix (Fin m) (Fin m) ℂ, (∀ v, (M v)ᴴ = M v) → ∃ t, H t = M) →
    ∃ Fe : (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) ≃L[ℝ] EuclideanSpace ℝ (V × Fin n × Fin m × Bool),
      (∀ z, Fe z = reimV (fun v => c v * (L z.1 v * w v +
        (1 / 2 : ℂ) • (w v * ((w v)ᴴ * Formalism.REAL.Jm (ε v) * w v)⁻¹ * H z.2 v)))) ∧
      (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)).map Fe =
        ENNReal.ofReal (∏ v, 2 ^ (n * m) / ‖((w v)ᴴ * Formalism.REAL.Jm (ε v) * w v).det‖ ^ (S v).card) • volume

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

theorem contDiff_conj_exp {ι : Type} [Fintype ι] {n : ℕ}
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    ContDiff ℝ 1 (fun x => (A * NormedSpace.exp (L x) * B) *ᵥ y) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  let Lc : EuclideanSpace ℝ ι →L[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap L
  let H : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin n → ℂ) :=
    { toFun := fun M => (A * M * B) *ᵥ y
      map_add' := fun M M' => by simp [Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec]
      map_smul' := fun c M => by
        simp only [RingHom.id_apply]
        rw [Matrix.mul_smul, Matrix.smul_mul]
        funext i
        simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply, Finset.smul_sum, smul_mul_assoc] }
  let Hc : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap H
  have he : ContDiff ℝ 1 (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
    contDiff_iff_contDiffAt.2 fun M => (NormedSpace.exp_analytic (𝕂 := ℝ) M).contDiffAt
  exact Hc.contDiff.comp (he.comp Lc.contDiff)

theorem theta_act {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (hb : AdBridgeIso X.B.I) (s : X.B.I.Ginf)
    (v : InfinitePlace X.B.I.F) (b : Fin (D.R.rS + 1 + D.R.rS)) (i : Fin X.B.I.n) :
    PI.AprimeInfU.thetaInf X v ((X.toInf hb s • Y0 X u') b i) =
      ((X.B.I.P v * uMat (s v) * (X.B.I.P v)⁻¹) *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j)) i := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  set Mm : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :=
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (X.toInf hb s) : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) with hMm
  have hmap : Mm.map (PI.AprimeInfU.thetaInf X v) = X.B.I.P v * uMat (s v) * (X.B.I.P v)⁻¹ := by
    rw [uMat_toInf X hb s v, ← hMm]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]
  rw [← hmap]
  show PI.AprimeInfU.thetaInf X v ((Mm *ᵥ Y0 X u' b) i) = _

  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Y0 X u' b j = inclR (Ainf X.B.I.F) (tupH (frameOf X u') b j) from rfl, thetaInf_inclR]

theorem continuous_thetaInf {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) :
    Continuous (PI.AprimeInfU.thetaInf X v) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  let σ : Ainf X.B.I.F →+* ℂ := PI.AprimeInfU.evInf X v
  have hσ : Continuous σ :=
    (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)
  let φl : (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) →ₛₗ[σ] ℂ :=
    { toFun := PI.AprimeInfU.thetaInf X v
      map_add' := map_add _
      map_smul' := fun a y => by
        rw [Algebra.smul_def, map_mul, smul_eq_mul]
        congr 1
        show PI.AprimeInfU.thetaInf X v (a ⊗ₜ[X.B.I.F] (1 : X.B.I.E)) = _
        rw [thetaInf_tmul, map_one, mul_one] }
  exact IsModuleTopology.continuous_of_linearMapₛₗ hσ φl

theorem kapSm_holds : KapSm := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S ι _ L hc hL
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
  have hGc : ContDiff ℝ 1 (fun x => Φ (kap0 X hb c L x • Y0 X u')) := by
    refine contDiff_pi.2 fun v => contDiff_pi.2 fun b => ?_
    have e : (fun x => Φ (kap0 X hb c L x • Y0 X u') v b) = fun x =>
        ((X.B.I.P v * uMat (c v)) * NormedSpace.exp (((LinearMap.proj v : (InfinitePlace X.B.I.F →
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) →ₗ[ℝ] _) ∘ₗ L) x) * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
          fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
      funext x
      exact hG x v b
    rw [e]
    exact contDiff_conj_exp _ _ _ _
  have hK : KapOrb X u' (kap0 X hb c L) = fun x => Ψe.symm (Φ (kap0 X hb c L x • Y0 X u')) := by
    funext x
    exact hΨe _
  rw [hK]
  have h1 : ContDiff ℝ 1 (fun y => Ψe.symm y) := Ψe.toContinuousLinearEquiv.symm.contDiff
  exact (h1.comp hGc).contDiffAt

end PI.AprimeInfW
end
end
