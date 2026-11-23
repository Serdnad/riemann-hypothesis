module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfLoc
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle008
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KbBase
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KbCurve
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle002

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Ker

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc
  PositivityTheory.RgBcC.LfSt.ChainPf.DCc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem int_of_cpt (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (K : Mat n → (V →L[ℂ] V)) (f : Mat n → V)
    (hK : ContinuousOn K (GLs n)) (hf : ContinuousOn f (GLs n)) (hc : Cpt f) :
    Integrable (fun y : G n => K y.val (f y.val)) μ := by
  refine integrable_cpt hL μ (fun y => K y (f y)) (hK.clm_apply hf) ?_
  obtain ⟨R, hR⟩ := hc
  exact ⟨R, fun y hy h => by simp [hR y hy h]⟩

theorem act_one [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V))
    (F : Mat n → E.V) : act μ E k F 1 = ∫ y : G n, k y.val (F y.val) ∂μ := by
  simp only [act, one_mul]

theorem gamma_of_comm (hKZ : KerZero) (hL : LgFacts) {E : KMod n} (Γ : E.V →L[ℂ] E.V)
    (hΓρ : ∀ k, Γ * E.ρ k = E.ρ k * Γ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V)) (hkc : ContinuousOn k (GLs n))
    (hke : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂)
    (hΓ : ∀ f ∈ CE E, act μ E k (fun x => Γ (f x)) 1 = Γ (act μ E k f 1)) :
    ∀ y ∈ GLs n, Γ * k y = k y * Γ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have hz := hKZ n μ E (fun y => k y * Γ - Γ * k y) ((hkc.clm_comp continuousOn_const).sub
      (continuousOn_const.clm_comp hkc)) (fun y hy k₂ => by
        simp only [hke y hy k₂, mul_assoc, ← hΓρ, sub_mul]) (fun f hf hfc => by
      have hfcont : ContinuousOn f (GLs n) := hf.1.continuousOn
      have i1 := int_of_cpt hL μ (fun y => k y * Γ) f (hkc.clm_comp continuousOn_const) hfcont hfc
      have i2 := int_of_cpt hL μ (fun y => Γ * k y) f (continuousOn_const.clm_comp hkc) hfcont hfc
      simp only [ContinuousLinearMap.sub_apply]
      rw [integral_sub i1 i2]
      have e1 : ∫ y : G n, (k y.val * Γ) (f y.val) ∂μ = act μ E k (fun x => Γ (f x)) 1 := by
        rw [act_one]; rfl
      have e2 : ∫ y : G n, (Γ * k y.val) (f y.val) ∂μ = Γ (act μ E k f 1) := by
        rw [act_one]
        exact ContinuousLinearMap.integral_comp_comm Γ
          (int_of_cpt hL μ k f hkc hfcont hfc)
      rw [e1, e2, hΓ f hf, sub_self])
  intro y hy
  have := hz y hy
  exact (sub_eq_zero.1 this).symm

theorem rd_cont {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (X : Mat n) : ContinuousOn (Rd X f) (GLs n) :=
  (hf.continuousOn_fderiv_of_isOpen (isOpen_GLs n) (by simp)).clm_apply
    (continuous_id.matrix_mul continuous_const).continuousOn

theorem ld_cont {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (X : Mat n) : ContinuousOn (Ld X f) (GLs n) :=
  ((hf.continuousOn_fderiv_of_isOpen (isOpen_GLs n) (by simp)).clm_apply
    (continuous_const.matrix_mul continuous_id).continuousOn).neg

def mr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V →L[ℂ] V) : (V →L[ℂ] V) →L[ℂ] (V →L[ℂ] V) :=
  (ContinuousLinearMap.mul ℂ (V →L[ℂ] V)).flip A

theorem rd_mr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (k : Mat n → (V →L[ℂ] V))
    (hk : ContDiffOn ℝ ∞ k (GLs n)) (A : V →L[ℂ] V) (X : Mat n) (y : Mat n) (hy : y ∈ GLs n) :
    Rd X (fun y => k y * A) y = Rd X k y * A := by
  have hd : DifferentiableAt ℝ k y := (hk.differentiableOn (by simp)).differentiableAt ((isOpen_GLs n).mem_nhds hy)
  have e : (fun y => k y * A) = ⇑((mr A).restrictScalars ℝ) ∘ k := rfl
  have hd2 := (((mr A).restrictScalars ℝ).hasFDerivAt.comp y hd.hasFDerivAt).fderiv
  simp only [Rd]
  rw [e]
  exact congrArg (fun L => L (y * X)) hd2

theorem kapL_int (hA : ActDer) (hU : Unimod) (hL : LgFacts) {E : KMod n} (Fr : Mat n → (E.V →L[ℂ] E.V))
    (ε : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V)) (hks : ContDiffOn ℝ ∞ k (GLs n)) (hkc : Cpt k)
    (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hfc : Cpt f) :
    DC ε Fr (act μ E k f) 1 = ∫ y : G n, kapL ε Fr k y.val (f y.val) ∂μ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hD := (hA hU n μ E k f hks hkc hf).2
  have hfc' : ContinuousOn f (GLs n) := hf.continuousOn
  have iL : ∀ p, Integrable (fun y : G n => Ld (hb p) k y.val (f y.val)) μ := fun p =>
    int_of_cpt hL μ _ f (ld_cont k hks _) hfc' hfc
  have iK : Integrable (fun y : G n => k y.val (f y.val)) μ := int_of_cpt hL μ _ f hks.continuousOn hfc' hfc
  have iP : ∀ p, Integrable (fun y : G n => (ε (hb p)) (Ld (hb p) k y.val (f y.val) +
      ((fderiv ℝ Fr 1) (hb p)) (k y.val (f y.val)))) μ := fun p =>
    ContinuousLinearMap.integrable_comp _ ((iL p).add (ContinuousLinearMap.integrable_comp _ iK))
  have ek : ∀ y : G n, kapL ε Fr k y.val (f y.val) = ∑ p, (ε (hb p)) (Ld (hb p) k y.val (f y.val) +
      ((fderiv ℝ Fr 1) (hb p)) (k y.val (f y.val))) := by
    intro y
    simp [kapL]
  simp_rw [ek]
  rw [integral_finsetSum _ fun p _ => iP p]
  simp only [DC]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e1 : ∫ a : G n, (ε (hb p)) ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ =
      (ε (hb p)) (∫ a : G n, ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ) :=
    ContinuousLinearMap.integral_comp_comm _ ((iL p).add (ContinuousLinearMap.integrable_comp _ iK))
  have e2 : ∫ a : G n, ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ =
      (∫ a : G n, (Ld (hb p) k a.val) (f a.val) ∂μ) + ∫ a : G n, ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val)) ∂μ :=
    integral_add (iL p) (ContinuousLinearMap.integrable_comp _ iK)
  have e3 : ∫ a : G n, ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val)) ∂μ =
      ((fderiv ℝ Fr 1) (hb p)) (∫ a : G n, (k a.val) (f a.val) ∂μ) :=
    ContinuousLinearMap.integral_comp_comm _ iK
  rw [e1, e2, e3, hD _ 1 h1, act_one]
  simp only [one_mul]

theorem int_of_cptK (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (K : Mat n → (V →L[ℂ] V)) (f : Mat n → V)
    (hK : ContinuousOn K (GLs n)) (hf : ContinuousOn f (GLs n)) (hc : Cpt K) :
    Integrable (fun y : G n => K y.val (f y.val)) μ := by
  refine integrable_cpt hL μ (fun y => K y (f y)) (hK.clm_apply hf) ?_
  obtain ⟨R, hR⟩ := hc
  exact ⟨R, fun y hy h => by simp [hR y hy h]⟩

theorem kapR_int (hI : IBPAct) (hU : Unimod) (hR : RCalc) (hL : LgFacts) {E : KMod n} (Fr : Mat n → (E.V →L[ℂ] E.V))
    (ε : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V)) (hks : ContDiffOn ℝ ∞ k (GLs n)) (hkc : Cpt k)
    (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hfc : Cpt f) :
    act μ E k (DC ε Fr f) 1 = ∫ y : G n, kapR ε Fr k y.val (f y.val) ∂μ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hfc' : ContinuousOn f (GLs n) := hf.continuousOn
  have hk' : ∀ p, ContDiffOn ℝ ∞ (fun y => k y * ε (hb p)) (GLs n) := fun p => by
    have e : (fun y => k y * ε (hb p)) = ⇑((mr (ε (hb p))).restrictScalars ℝ) ∘ k := rfl
    rw [e]
    exact ((mr (ε (hb p))).restrictScalars ℝ).contDiff.comp_contDiffOn hks
  have hkc' : ∀ p, Cpt fun y => k y * ε (hb p) := fun p => by
    obtain ⟨R, hR⟩ := hkc
    exact ⟨R, fun y hy h => by simp [hR y hy h]⟩
  have iA : ∀ p, Integrable (fun y : G n => (k y.val * ε (hb p)) (Rd (hb p) f y.val)) μ := fun p =>
    int_of_cptK hL μ _ _ ((hk' p).continuousOn) (rd_cont f hf _) (hkc' p)
  have iB : ∀ p, Integrable (fun y : G n => (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) μ := fun p =>
    int_of_cpt hL μ _ f ((hk' p).continuousOn.clm_comp continuousOn_const) hfc' hfc
  have iC : ∀ p, Integrable (fun y : G n => (Rd (hb p) k y.val * ε (hb p)) (f y.val)) μ := fun p =>
    int_of_cpt hL μ _ f ((rd_cont k hks _).clm_comp continuousOn_const) hfc' hfc
  have eL : ∀ y : G n, k y.val (DC ε Fr f y.val) = ∑ p, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) := by
    intro y

    simp [DC, map_sum, map_add (f := _)]
  have eR : ∀ y : G n, kapR ε Fr k y.val (f y.val) = ∑ p, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) := by
    intro y
    simp [kapR]
  rw [act_one]
  simp_rw [eL, eR]
  have sL : ∫ y : G n, ∑ p, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = ∑ p, ∫ y : G n, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ :=
    integral_finsetSum _ fun p _ => (iA p).add (iB p)
  have sR : ∫ y : G n, ∑ p, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = ∑ p, ∫ y : G n, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ :=
    integral_finsetSum _ fun p _ => (iC p).neg.add (iB p)
  rw [sL, sR]
  refine Finset.sum_congr rfl fun p _ => ?_
  have a1 : ∫ y : G n, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = (∫ y : G n, (k y.val * ε (hb p)) (Rd (hb p) f y.val) ∂μ) +
      ∫ y : G n, (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val) ∂μ := integral_add (iA p) (iB p)
  have a2 : ∫ y : G n, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = (∫ y : G n, -((Rd (hb p) k y.val * ε (hb p)) (f y.val)) ∂μ) +
      ∫ y : G n, (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val) ∂μ := integral_add (iC p).neg (iB p)
  rw [a1, a2, integral_neg]
  congr 1
  have hibp := hI hU hR n μ E (fun y => k y * ε (hb p)) f (hk' p) (hkc' p) hf (hb p) 1 h1
  simp only [one_mul] at hibp
  rw [hibp]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show (Rd (hb p) (fun y => k y * ε (hb p)) y.val) (f y.val) = (Rd (hb p) k y.val * ε (hb p)) (f y.val)
  rw [rd_mr k hks _ _ _ (mem_GLs_of y)]

end PositivityTheory.RgBcC.LfSt.ChainPf.Ker
end
end

section

noncomputable section

open Matrix Finset Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbDer

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain PositivityTheory.RgBcC.LfSt.Kchain.KbBase
  PositivityTheory.RgBcC.LfSt.Kchain.KbCurve PositivityTheory.RgBcC.LfSt.Kchain.KbFr
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiffAt_mat {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : E → Mat n} {x : E}
    (h : ContDiffAt ℝ ∞ A x) (a b : Fin n) : ContDiffAt ℝ ∞ (fun z => A z a b) x :=
  (entL a b).contDiff.contDiffAt.comp x h

theorem contDiffAt_matmul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A B : E → Mat n} {x : E}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x) : ContDiffAt ℝ ∞ (fun z => A z * B z) x := by
  refine contDiffAt_of_entries fun a b => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun c _ => (contDiffAt_mat hA a c).mul (contDiffAt_mat hB c b)

theorem contDiff_conjT : ContDiff ℝ ∞ (fun y : Mat n => yᴴ) := by
  refine contDiff_iff_contDiffAt.2 fun x => contDiffAt_of_entries fun a b => ?_
  simp only [Matrix.conjTranspose_apply]
  exact (Complex.conjCLE.contDiff.comp (contDiff_entry b a)).contDiffAt

theorem inv_mem {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n := by
  show (x⁻¹).det ≠ 0
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hx

theorem conjT_mem {x : Mat n} (hx : x ∈ GLs n) : xᴴ ∈ GLs n := by
  show (xᴴ).det ≠ 0
  rw [Matrix.det_conjTranspose]
  exact star_ne_zero.2 hx

theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  show (x * y).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hx hy

section

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

theorem derOne_at (h : CxData lam E Fr ε ι S Γ T) {k : Mat n → (E.V →L[ℂ] E.V)} (hk : ContDiffOn ℝ ∞ k (GLs n))
    {d y : Mat n} (hd : d ∈ GLs n) (hy : y ∈ GLs n) {x : Mat n} (hx : x ∈ GLs n) (X : Mat n) :
    fderiv ℝ (fun x' => Kf Fr k Γ T d x' y) x (x * X) =
      Fr x * (fderiv ℝ Fr 1 X * k (x⁻¹ * d * yᴴ⁻¹) + Ld X k (x⁻¹ * d * yᴴ⁻¹)) * Γ * T * Fr y⁻¹ := by
  set w := x⁻¹ * d * yᴴ⁻¹ with hwdef
  have hw : w ∈ GLs n := mul_mem (mul_mem (inv_mem hx) hd) (inv_mem (conjT_mem hy))
  have hkw : DifferentiableAt ℝ k w := diffAt_of hk hw
  have hg : ContDiffAt ℝ ∞ (fun x' : Mat n => x'⁻¹ * d * yᴴ⁻¹) x :=
    contDiffAt_matmul (contDiffAt_matmul (contDiffAt_inv hx) contDiffAt_const) contDiffAt_const
  have hdiff : DifferentiableAt ℝ (fun x' => Kf Fr k Γ T d x' y) x := by
    unfold Kf
    have h1 : DifferentiableAt ℝ (fun x' : Mat n => k (x'⁻¹ * d * yᴴ⁻¹)) x :=
      hkw.comp x (hg.differentiableAt (by simp))
    exact ((((diffAt_of h.smooth hx).mul h1).mul_const Γ).mul_const T).mul_const (Fr y⁻¹)
  have h1 := hasDerivAt_fderiv_line hdiff (x * X)
  have hF : HasDerivAt (fun t : ℝ => Fr (x * (1 + t • X))) (Fr x * fderiv ℝ Fr 1 X) 0 := by
    refine ((hasDerivAt_Fr_line h X).const_mul (Fr x)).congr_of_eventuallyEq ?_
    filter_upwards [line_mem X] with t ht
    exact h.mul x hx _ ht
  have hc : HasDerivAt (fun t : ℝ => (1 + t • X)⁻¹ * w) ((-X) * w) 0 :=
    (hasDerivAt_matmul (hasDerivAt_lineInv X) (hasDerivAt_const (0 : ℝ) w)).congr_deriv (by simp)
  have hK : HasDerivAt (fun t : ℝ => k ((1 + t • X)⁻¹ * w)) (fderiv ℝ k w ((-X) * w)) 0 :=
    hkw.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  have h2 := (((hF.fun_mul hK).mul_const Γ).mul_const T).mul_const (Fr y⁻¹)
  have e : (fun t : ℝ => Kf Fr k Γ T d (x + t • (x * X)) y) =
      fun t : ℝ => Fr (x * (1 + t • X)) * k ((1 + t • X)⁻¹ * w) * Γ * T * Fr y⁻¹ := by
    funext t
    have e1 : x + t • (x * X) = x * (1 + t • X) := by rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    simp only [Kf, e1, Matrix.mul_inv_rev, hwdef, Matrix.mul_assoc]
  rw [e] at h1
  rw [h1.unique h2]
  simp only [zero_smul, add_zero, inv_one, Matrix.one_mul, Matrix.mul_one, Ld, neg_mul, map_neg]
  noncomm_ring

theorem derOne : DerOne := fun _ _ _ _ _ _ _ _ _ h _ hk _ _ hd hy _ hx X => derOne_at h hk hd hy hx X

end

end PositivityTheory.RgBcC.LfSt.Kchain.KbDer
end
end
