module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
import GroundTheory.AutomorphicForms.Bundle012
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
public import GroundTheory.AutomorphicForms.GL2.AdelicFourier2TensorCosetIndicatorAlgebraMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle063
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle059
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle202
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.MapUgCToUg
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle227
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.LtrFourier

noncomputable section

theorem map_mulVec_fin {k : Type} [Field k] [NumberField k] {n : ℕ} (A : GL (Fin n) 𝔸[k]) :
    (adeleMeasurePi k).map (fun x : Fin n → 𝔸[k] => (A : Matrix (Fin n) (Fin n) 𝔸[k]) *ᵥ x) =
      ENNReal.ofReal ((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ •
        adeleMeasurePi k (ι := Fin n) := by
  have hmap := GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi (tInv (A⁻¹))
  have hdet : Matrix.GeneralLinearGroup.det (tInv (A⁻¹)) = Matrix.GeneralLinearGroup.det A := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    change (((A⁻¹)⁻¹ : GL (Fin n) 𝔸[k]) : Matrix (Fin n) (Fin n) 𝔸[k])ᵀ.det = _
    rw [Matrix.det_transpose, inv_inv]
  have hfun : (fun x : Fin n → 𝔸[k] =>
      x ᵥ* ((tInv (A⁻¹) : GL (Fin n) 𝔸[k]) : Matrix (Fin n) (Fin n) 𝔸[k])) =
      fun x => (A : Matrix (Fin n) (Fin n) 𝔸[k]) *ᵥ x := by
    funext x
    change x ᵥ* (((A⁻¹)⁻¹ : GL (Fin n) 𝔸[k]) : Matrix (Fin n) (Fin n) 𝔸[k])ᵀ = _
    rw [inv_inv]
    exact Matrix.vecMul_transpose _ x
  rwa [hdet, hfun] at hmap

theorem map_mulVec {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : GL ι 𝔸[k]) :
    (adeleMeasurePi k).map (fun x : ι → 𝔸[k] => (A : Matrix ι ι 𝔸[k]) *ᵥ x) =
      ENNReal.ofReal ((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ •
        adeleMeasurePi k (ι := ι) := by
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let P : GL (Fin (Fintype.card ι)) 𝔸[k] :=
    ⟨(A : Matrix ι ι 𝔸[k]).submatrix e.symm e.symm,
      ((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).submatrix e.symm e.symm,
      by rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv]⟩
  have hdet : Matrix.GeneralLinearGroup.det P = Matrix.GeneralLinearGroup.det A := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    exact Matrix.det_submatrix_equiv_self _ _
  have h1 : MeasurePreserving (fun x : ι → 𝔸[k] => x ∘ e.symm) (adeleMeasurePi k)
      (adeleMeasurePi k) := GroundTheory.Heights₂.Theta.measurePreserving_comp_equiv (adeleMeasure k) e.symm
  have h3 : MeasurePreserving (fun x : Fin (Fintype.card ι) → 𝔸[k] => x ∘ e) (adeleMeasurePi k)
      (adeleMeasurePi k) := GroundTheory.Heights₂.Theta.measurePreserving_comp_equiv (adeleMeasure k) e
  have hP : Measurable fun x : Fin (Fintype.card ι) → 𝔸[k] =>
      (P : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝔸[k]) *ᵥ x :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hfun : (fun x : ι → 𝔸[k] => (A : Matrix ι ι 𝔸[k]) *ᵥ x) =
      (fun x => x ∘ e) ∘
        (fun x => (P : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝔸[k]) *ᵥ x) ∘
          (fun x => x ∘ e.symm) := by
    funext x
    simp only [Function.comp_apply]
    change _ = ((A : Matrix ι ι 𝔸[k]).submatrix e.symm e.symm *ᵥ (x ∘ e.symm)) ∘ e
    have hx : (x ∘ e.symm) ∘ e = x := by
      funext j
      simp
    rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, hx]
    funext i
    simp
  rw [hfun, ← Measure.map_map h3.measurable (hP.comp h1.measurable),
    ← Measure.map_map hP h1.measurable, h1.map_eq, map_mulVec_fin P, hdet, Measure.map_smul,
    h3.map_eq]
  exact h3.measurable.aemeasurable

def mulVecHomeo {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : GL ι 𝔸[k]) : (ι → 𝔸[k]) ≃ₜ (ι → 𝔸[k]) where
  toFun x := (A : Matrix ι ι 𝔸[k]) *ᵥ x
  invFun x := ((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ x
  left_inv x := by
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  right_inv x := by
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem integral_comp_mulVec {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι]
    [DecidableEq ι] (A : GL ι 𝔸[k]) (f : (ι → 𝔸[k]) → ℂ) :
    ∫ x, f ((A : Matrix ι ι 𝔸[k]) *ᵥ x) ∂adeleMeasurePi k =
      (((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ : ℂ) *
        ∫ x, f x ∂adeleMeasurePi k := by
  have hemb : MeasurableEmbedding (fun x : ι → 𝔸[k] => (A : Matrix ι ι 𝔸[k]) *ᵥ x) :=
    (mulVecHomeo A).measurableEmbedding
  rw [← hemb.integral_map, map_mulVec, integral_smul_measure, ENNReal.toReal_ofReal
      (inv_nonneg.2 (ideleModule k (Matrix.GeneralLinearGroup.det A)).2.le),
    Complex.real_smul, Complex.ofReal_inv]

theorem adelicFourierPi_ltr : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ), adelicFourierPi k (ltr A F) =
      (((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ : ℂ) •
        ltr (tInv A) (adelicFourierPi k F) := by
  intro k _ _ ι _ _ A F
  funext y
  have h := integral_comp_mulVec A (fun z => F z *
    (adelicChar k (∑ i, (((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ z) i * y i) : ℂ))
  simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h
  have hp : ∀ z : ι → 𝔸[k], ∑ i, (((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ z) i * y i =
      ∑ i, z i * (((tInv A : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ y) i := by
    intro z
    change (((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ z) ⬝ᵥ y =
      z ⬝ᵥ ((((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]))ᵀ *ᵥ y)
    rw [Matrix.mulVec_transpose, dotProduct_comm _ y, Matrix.dotProduct_mulVec,
      dotProduct_comm]
  simp only [hp] at h
  simpa only [adelicFourierPi, ltr, Pi.smul_apply, smul_eq_mul] using h

end

end GlobalTheory.CompanionTheory.LtrFourier
end

section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

open scoped SchwartzMap Classical

set_option synthInstance.maxSize 1000

noncomputable section

namespace GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat

open GroundTheory.Automorphic.Adele2 NumberField.mixedEmbedding

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

def mulVecCLE (M : GL ι (mixedSpace k)) : (ι → mixedSpace k) ≃L[ℝ] (ι → mixedSpace k) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u ↦ (M : Matrix ι ι (mixedSpace k)) *ᵥ u
      invFun := fun u ↦ ((M⁻¹ : GL ι (mixedSpace k)) : Matrix ι ι (mixedSpace k)) *ᵥ u
      map_add' := fun u v ↦ mulVec_add _ u v
      map_smul' := fun c u ↦ mulVec_smul _ c u
      left_inv := fun u ↦ by
        simp only [mulVec_mulVec, Units.inv_mul, one_mulVec]
      right_inv := fun u ↦ by
        simp only [mulVec_mulVec, Units.mul_inv, one_mulVec] }

theorem mulVecCLE_apply (M : GL ι (mixedSpace k)) (u : ι → mixedSpace k) :
    mulVecCLE M u = (M : Matrix ι ι (mixedSpace k)) *ᵥ u := rfl

def mulVecHomeo (M : GL ι 𝔸ᶠ[k]) : (ι → 𝔸ᶠ[k]) ≃ₜ (ι → 𝔸ᶠ[k]) where
  toFun u := (M : Matrix ι ι 𝔸ᶠ[k]) *ᵥ u
  invFun u := ((M⁻¹ : GL ι 𝔸ᶠ[k]) : Matrix ι ι 𝔸ᶠ[k]) *ᵥ u
  left_inv u := by simp only [mulVec_mulVec, Units.inv_mul, one_mulVec]
  right_inv u := by simp only [mulVec_mulVec, Units.mul_inv, one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem comp_mulVec_mem_finiteSchwartzBruhatPi (M : GL ι 𝔸ᶠ[k]) {g : (ι → 𝔸ᶠ[k]) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi k) :
    (fun z ↦ g ((M : Matrix ι ι 𝔸ᶠ[k]) *ᵥ z)) ∈ finiteSchwartzBruhatPi k := by
  obtain ⟨h1, h2⟩ := (mem_finiteSchwartzBruhatPi k).1 hg
  exact (mem_finiteSchwartzBruhatPi k).2
    ⟨h1.comp_continuous (mulVecHomeo M).continuous,
      h2.comp_isClosedEmbedding (mulVecHomeo M).isClosedEmbedding⟩

theorem infPartPi_mulVec (A : Matrix ι ι 𝔸[k]) (x : ι → 𝔸[k]) :
    infPartPi (A *ᵥ x) = A.map infRingHom *ᵥ infPartPi x := by
  funext i
  exact RingHom.map_mulVec infRingHom A x i

theorem finPartPi_mulVec (A : Matrix ι ι 𝔸[k]) (x : ι → 𝔸[k]) :
    finPartPi (A *ᵥ x) = A.map finRingHom *ᵥ finPartPi x := by
  funext i
  exact RingHom.map_mulVec finRingHom A x i

theorem ltr_schwartzBruhatTensorPi (A : GL ι 𝔸[k]) (φ : 𝓢(ι → mixedSpace k, ℂ))
    (g : (ι → 𝔸ᶠ[k]) → ℂ) :
    ltr A (schwartzBruhatTensorPi φ g) =
      schwartzBruhatTensorPi
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (mulVecCLE (Matrix.GeneralLinearGroup.map infRingHom A)) φ)
        (fun z ↦ g ((Matrix.GeneralLinearGroup.map finRingHom A : GL ι 𝔸ᶠ[k]) *ᵥ z)) := by
  funext x
  have h1 : ((Matrix.GeneralLinearGroup.map infRingHom A : GL ι (mixedSpace k)) :
      Matrix ι ι (mixedSpace k)) = (A : Matrix ι ι 𝔸[k]).map infRingHom := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  have h2 : ((Matrix.GeneralLinearGroup.map finRingHom A : GL ι 𝔸ᶠ[k]) :
      Matrix ι ι 𝔸ᶠ[k]) = (A : Matrix ι ι 𝔸[k]).map finRingHom := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  simp only [ltr, schwartzBruhatTensorPi, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, mulVecCLE_apply, h1, h2, infPartPi_mulVec, finPartPi_mulVec]

theorem ltr_mem {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) (A : GL ι 𝔸[k]) :
    ltr A F ∈ schwartzBruhatPi (K := k) (ι := ι) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    rw [ltr_schwartzBruhatTensorPi]
    exact schwartzBruhatTensorPi_mem _ (comp_mulVec_mem_finiteSchwartzBruhatPi _ hg)
  | zero => exact zero_mem _
  | add G H _ _ ihG ihH => exact add_mem ihG ihH
  | smul a G _ ih => exact Submodule.smul_mem _ a ih

end GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

section Adic

variable {R : Type*} [CommRing R]

theorem smodEq_span_pow_iff (π x y : R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {π} ^ n • (⊤ : Submodule R R))] ↔ π ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem eq_zero_of_forall_pow_dvd {π x : R} (h : IsHausdorff (Ideal.span {π}) R)
    (hx : ∀ n : ℕ, π ^ n ∣ x) : x = 0 :=
  h.haus x fun n => (smodEq_span_pow_iff π x 0 n).2 (by simpa using hx n)

theorem exists_limit_of_pow_dvd {π : R} (h : IsPrecomplete (Ideal.span {π}) R) (f : ℕ → R)
    (hf : ∀ n : ℕ, π ^ n ∣ f (n + 1) - f n) : ∃ L, ∀ n : ℕ, π ^ n ∣ f n - L :=
  _root_.UpperTheory.Reformulated.B.Yra6.main h f hf

theorem pow_pow_of_compatible {M : Type*} [Monoid M] {l : ℕ} {v : ℕ → M}
    (hv : ∀ i, v (i + 1) ^ l = v i) (i j : ℕ) : v (i + j) ^ l ^ j = v i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', pow_mul, ← add_assoc, hv, ih]

end Adic

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem sub_pow_pow (x y : A.A) (j : ℕ) : (x - y) ^ l ^ j = x ^ l ^ j - y ^ l ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, ih, pow_mul, pow_mul]
    exact map_sub A.frob _ _

theorem exists_limit_pow (b : ℕ → A.A) (hb : ∀ j, A.pi ∣ b (j + 1) ^ l - b j) (i : ℕ) :
    ∃ L, ∀ n : ℕ, A.pi ^ n ∣ b (i + n) ^ l ^ n - L := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  refine exists_limit_of_pow_dvd (π := A.pi) A.compl.toIsPrecomplete
    (fun n => b (i + n) ^ l ^ n) fun n => ?_
  have e : b (i + (n + 1)) ^ l ^ (n + 1) - b (i + n) ^ l ^ n
      = (b (i + n + 1) ^ l - b (i + n)) ^ l ^ n := by
    rw [sub_pow_pow, ← pow_mul, ← pow_succ', add_assoc]
  change A.pi ^ n ∣ b (i + (n + 1)) ^ l ^ (n + 1) - b (i + n) ^ l ^ n
  rw [e]
  exact (pow_dvd_pow _ (Nat.lt_pow_self hl).le).trans (pow_dvd_pow_of_dvd (hb _) _)

theorem exists_compatible_roots_of_sharp : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (u : ℕ → A.U),
    (∀ i, u (i + 1) ^ l = u i) →
    ∃ a : ℕ → A.A, (∀ i, a (i + 1) ^ l = a i) ∧ ∀ i, A.sharp (a i) = u i := by
  intro l _ A u hu
  obtain ⟨hsurj, hker⟩ := sharp_map_surjective_ker A
  choose b hb using fun j => hsurj (Ideal.Quotient.mk _ (u j))
  have hbd : ∀ j, A.pi ∣ b (j + 1) ^ l - b j := fun j => by
    rw [← Ideal.mem_span_singleton]
    rw [← hker, RingHom.mem_ker, map_sub, map_pow, hb, hb, ← map_pow, hu, sub_self]
  choose a ha using exists_limit_pow A b hbd
  have hA : IsHausdorff (Ideal.span {A.pi}) A.A := A.compl.toIsHausdorff
  have hroot : ∀ i, a (i + 1) ^ l = a i := fun i => by
    refine sub_eq_zero.1 (eq_zero_of_forall_pow_dvd hA fun n => ?_)
    have h1 : A.pi ^ n ∣ b (i + 1 + n) ^ l ^ (n + 1) - a (i + 1) ^ l := by
      rw [pow_succ, pow_mul]
      exact (ha (i + 1) n).trans (sub_dvd_pow_sub_pow _ _ l)
    have h2 : A.pi ^ n ∣ b (i + 1 + n) ^ l ^ (n + 1) - a i := by
      have := ha i (n + 1)
      rw [show i + (n + 1) = i + 1 + n by ring] at this
      exact (pow_dvd_pow _ (Nat.le_succ n)).trans this
    have := dvd_sub h2 h1
    simpa using this
  have hmod : ∀ i, A.pi ∣ a i - b i := fun i => by
    have h1 := ha i 1
    rw [pow_one, pow_one] at h1
    have := dvd_sub (hbd i) h1
    simpa using this
  have hl1 : ∀ i, (l : A.U) ∣ A.sharp (a i) - u i := fun i => by
    have h0 : A.aToU1 (a i) = A.aToU1 (b i) := by
      rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hker, Ideal.mem_span_singleton]
      exact hmod i
    rw [hb, sharpMap_eq] at h0
    have := Ideal.Quotient.eq.1 h0
    rwa [pow_one, Ideal.mem_span_singleton] at this
  refine ⟨a, hroot, fun i => sub_eq_zero.1 ?_⟩
  refine eq_zero_of_forall_pow_dvd (π := (l : A.U)) (GlobalTheory.T.untilt_adic_complete A).toIsHausdorff fun n => ?_
  have h1 := dvd_sub_pow_of_dvd_sub (hl1 (i + n)) n
  rw [← map_pow, pow_pow_of_compatible hroot, pow_pow_of_compatible hu] at h1
  exact (pow_dvd_pow _ (Nat.le_succ n)).trans h1

end GlobalTheory.CompanionTheory.Untilt
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem existsUnique_idempotent_sharp {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.U)
    (he : IsIdempotentElem e) : ∃! e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = e := by
  obtain ⟨hsurj, hker⟩ := sharp_map_surjective_ker A
  haveI hcA : IsAdicComplete (Ideal.span {A.pi ^ 1}) A.A := by
    rw [pow_one]; exact A.compl
  haveI hcA' : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl
  haveI hcU : IsAdicComplete (Ideal.span {(l : A.U)}) A.U := GlobalTheory.T.untilt_adic_complete A
  have hmemker : ∀ x y : A.A, A.aToU1 x = A.aToU1 y →
      Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) x = Ideal.Quotient.mk _ y := by
    intro x y h
    apply Ideal.Quotient.eq.2
    rw [pow_one, ← hker, RingHom.mem_ker, map_sub, h, sub_self]
  have hsharp_idem : ∀ x : A.A, IsIdempotentElem x → IsIdempotentElem (A.sharp x) := fun x hx =>
    hx.map A.sharp
  have hU := GlobalTheory.CompanionTheory.IdemLift.existsUnique_idempotent_lift (l : A.U) 1 one_ne_zero
    (Ideal.Quotient.mk _ e) (he.map (Ideal.Quotient.mk _))
  obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk _ e)
  have haid : IsIdempotentElem (Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) a) := by
    have : A.aToU1 (a * a) = A.aToU1 a := by
      rw [map_mul, ha]
      exact congrArg _ he |>.trans rfl
    have h2 := hmemker _ _ this
    rw [map_mul] at h2
    exact h2
  obtain ⟨e₀, ⟨he₀, hmk⟩, huniq⟩ := GlobalTheory.CompanionTheory.IdemLift.existsUnique_idempotent_lift A.pi 1 one_ne_zero
    (Ideal.Quotient.mk _ a) haid
  have hcong : ∀ x y : A.A, Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) x = Ideal.Quotient.mk _ y →
      A.aToU1 x = A.aToU1 y := by
    intro x y h
    have h3 := Ideal.Quotient.eq.1 h
    rw [pow_one, ← hker, RingHom.mem_ker, map_sub] at h3
    exact sub_eq_zero.1 h3
  refine ⟨e₀, ⟨he₀, ?_⟩, ?_⟩
  · refine hU.unique ⟨hsharp_idem _ he₀, ?_⟩ ⟨he, rfl⟩
    rw [← A.sharpMap_eq, hcong _ _ hmk, ha]
  · rintro e₁ ⟨he₁, hs₁⟩
    refine huniq e₁ ⟨he₁, ?_⟩
    rw [← hmk]
    apply hmemker
    have hs₀ : A.sharp e₀ = e := hU.unique ⟨hsharp_idem _ he₀, by
      rw [← A.sharpMap_eq, hcong _ _ hmk, ha]⟩ ⟨he, rfl⟩
    rw [A.sharpMap_eq, A.sharpMap_eq, hs₁, hs₀]

end GlobalTheory.CompanionTheory.Untilt
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.RootsC

variable {l : ℕ} [hl : Fact l.Prime]

theorem seq_add_pow (m d : ℕ) : rootSeq l (m + d) ^ l ^ d = rootSeq l m := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, pow_succ', pow_mul, GroundTheory.PAdicHodge.rootSeq_succ_pow, ih]

theorem seq_primitive (n : ℕ) : IsPrimitiveRoot (rootSeq l n) (l ^ n) := by
  cases n with
  | zero =>
    rw [pow_zero, IsPrimitiveRoot.one_right_iff]
    simpa using (GroundTheory.PAdicHodge.rootSeq_pow (p := l) 0)
  | succ k =>
    have h1 : ¬ rootSeq l (k + 1) ^ l ^ k = 1 := by
      rw [Nat.add_comm, seq_add_pow]
      exact GroundTheory.PAdicHodge.rootSeq_one_ne_one
    have h2 := orderOf_eq_prime_pow h1 (GroundTheory.PAdicHodge.rootSeq_pow (p := l) (k + 1))
    rw [← h2]
    exact IsPrimitiveRoot.orderOf _

theorem exists_primitive_cl (n : ℕ) : ∃ η : PadicAlgCl l, IsPrimitiveRoot η (l ^ n) := by
  have hq : (l ^ n : ℕ) ≠ 0 := pow_ne_zero n hl.out.ne_zero
  haveI : NeZero ((l ^ n : ℕ) : PadicAlgCl l) := ⟨by exact_mod_cast hq⟩
  have hdeg : (Polynomial.cyclotomic (l ^ n) (PadicAlgCl l)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    have ht : 0 < Nat.totient (l ^ n) := Nat.totient_pos.2 (Nat.pos_of_ne_zero hq)
    exact_mod_cast ht.ne'
  obtain ⟨η, hη⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨η, Polynomial.isRoot_cyclotomic_iff.1 hη⟩

theorem exists_lift (n : ℕ) :
    ∃ ρ : PadicAlgCl l, IsPrimitiveRoot ρ (l ^ n) ∧ clToC l ρ = rootSeq l n := by
  obtain ⟨η, hη⟩ := exists_primitive_cl (l := l) n
  have hinj : Function.Injective (clToC l) := (clToC l).injective
  have hη' : IsPrimitiveRoot (clToC l η) (l ^ n) :=
    (IsPrimitiveRoot.map_iff_of_injective hinj).2 hη
  obtain ⟨i, -, hi⟩ := hη'.eq_pow_of_pow_eq_one (GroundTheory.PAdicHodge.rootSeq_pow (p := l) n)
  refine ⟨η ^ i, ?_, by rw [map_pow, hi]⟩
  rw [← IsPrimitiveRoot.map_iff_of_injective hinj, map_pow, hi]
  exact seq_primitive n

theorem prim_of_primitive {q : ℕ} (hq : q ≠ 0) {F : Type} [Field F] [CharZero F] {ρ : F}
    (h : IsPrimitiveRoot ρ q) :
    IsUnit ((q : ℕ) : F) ∧ Polynomial.aeval ρ (Polynomial.cyclotomic q ℤ) = 0 := by
  refine ⟨isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hq), ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact h.isRoot_cyclotomic (Nat.pos_of_ne_zero hq)

theorem rootsEx : CrystallineSemistableComparison.E.RootsEx := by
  intro l _
  choose ρ hρ using fun n => exists_lift (l := l) n
  exact ⟨⟨fun n => Subtype.mk (ρ n)
      (prim_of_primitive (pow_ne_zero n (Fact.out : l.Prime).ne_zero) (hρ n).1),
    fun n => (hρ n).2⟩⟩

end GlobalTheory.CompanionTheory.RootsC
end
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_galois_fixes_integers : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g (a : OK l K), (lev h k).σA g (algebraMap (OK l K) (lev h k).A a) = algebraMap (OK l K) (lev h k).A a := by
  first | exact @GlobalTheory.CompanionTheory.LatC.sigA_fix | exact GlobalTheory.CompanionTheory.LatC.sigA_fix | (intros; apply GlobalTheory.CompanionTheory.LatC.sigA_fix <;> assumption)
end
