module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContDiffOnSecondCayleyBlockEntries
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DpDual
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseSecondBlockEqNegConjTranspose
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle010
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.FL

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt
open PositivityTheory.Rg.Sw.LVs.II (cE cE_hasDerivAt0 cE_add cE_zero cE_continuous mulL mulL_apply)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem cd_det_lemma {ι : Type} [Fintype ι] [DecidableEq ι] :
    ContDiff ℂ ∞ (fun x : Matrix ι ι ℂ => x.det) := by
  have he : ∀ i j : ι, ContDiff ℂ ∞ (fun x : Matrix ι ι ℂ => x i j) := fun i j =>
    contDiff_apply_apply ℂ i j
  simp_rw [Matrix.det_apply']
  exact ContDiff.sum (fun σ _ => contDiff_const.mul (contDiff_prod (fun i _ => he _ _)))

theorem cd_det : ContDiff ℂ ∞ (fun x : M2 n => x.det) := by
  exact cd_det_lemma

theorem cd_detu1 : ContDiff ℂ ∞ (fun x : M2 n => (u1 x).det) := by
  exact cd_det_lemma.comp contDiff_first_cayley_block

theorem curve_hasDerivAt (X x : M2 n) : HasDerivAt (fun s : ℝ => x * cE X s) (x * X) 0 := by
  have h := (mulL x).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (cE_hasDerivAt0 X)
  simp only [Function.comp_def, mulL_apply] at h
  exact h

theorem curve_deriv (Ψ : M2 n → ℂ) (hΨ : ContDiff ℂ ∞ Ψ) (X x : M2 n) :
    HasDerivAt (fun s : ℝ => Ψ (x * cE X s)) (fderiv ℂ Ψ x (x * X)) 0 := by
  have hd : HasFDerivAt Ψ (fderiv ℂ Ψ x) (x * cE X 0) := by
    rw [cE_zero, Matrix.mul_one]
    exact (hΨ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h := (hd.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) (curve_hasDerivAt X x)
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars'] at h
  exact h

theorem continuous_mR' : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem det_mR_ne' (g : GR n) : (mR g).det ≠ 0 := by
  show ((g : GL (Fin n ⊕ Fin n) ℂ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ).det ≠ 0
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (g : GL (Fin n ⊕ Fin n) ℂ).isUnit).ne_zero

def rD (X x : M2 n) : ℂ := fderiv ℂ (fun x : M2 n => x.det) x (x * X) / x.det

def rA (X x : M2 n) : ℂ := fderiv ℂ (fun x : M2 n => (u1 x).det) x (x * X) / (u1 x).det

private theorem rD_mul_left_eq_of_det_ne_zero (P A X : M2 n) (hP : P.det ≠ 0) : rD X (P * A) = rD X A := by
  unfold rD
  let L : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ P)
  have hL : ∀ y, L y = P * y := fun y => rfl
  have hdet : ∀ B : M2 n, HasFDerivAt (fun x : M2 n => x.det) (fderiv ℂ (fun x : M2 n => x.det) B) B :=
    fun B => ((cd_det (n := n)).differentiable (by simp) B).hasFDerivAt
  have h1 : HasFDerivAt (fun y : M2 n => (P * y).det)
      ((fderiv ℂ (fun x : M2 n => x.det) (P * A)).comp L) A := by
    have := (hdet (P * A)).comp A (L.hasFDerivAt (x := A))
    simp only [Function.comp_def, hL] at this
    exact this
  have h2 : HasFDerivAt (fun y : M2 n => (P * y).det)
      (P.det • fderiv ℂ (fun x : M2 n => x.det) A) A := by
    simp_rw [Matrix.det_mul]
    exact (hdet A).const_mul P.det
  have h4 := congrArg (fun T => T (A * X)) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hL] at h4
  rw [Matrix.mul_assoc, h4, Matrix.det_mul, mul_div_mul_left _ _ hP]

theorem rD_up (X : M2 n) (p k : GR n) : rD X (mR p * mR k) = rD X (mR k) := by
  exact rD_mul_left_eq_of_det_ne_zero _ _ X (det_mR_ne' p)

private theorem rA_mul_left_eq_of_u1_mul (D : Matrix (Fin n) (Fin n) ℂ) (P A X : M2 n) (hD : D.det ≠ 0)
    (hu : ∀ y, u1 (P * y) = D * u1 y) : rA X (P * A) = rA X A := by
  unfold rA
  let L : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ P)
  have hL : ∀ y, L y = P * y := fun y => rfl
  have hdet : ∀ B : M2 n, HasFDerivAt (fun x : M2 n => (u1 x).det) (fderiv ℂ (fun x : M2 n => (u1 x).det) B) B :=
    fun B => ((cd_detu1 (n := n)).differentiable (by simp) B).hasFDerivAt
  have h1 : HasFDerivAt (fun y : M2 n => (u1 (P * y)).det)
      ((fderiv ℂ (fun x : M2 n => (u1 x).det) (P * A)).comp L) A := by
    have := (hdet (P * A)).comp A (L.hasFDerivAt (x := A))
    simp only [Function.comp_def, hL] at this
    exact this
  have h2 : HasFDerivAt (fun y : M2 n => (u1 (P * y)).det)
      (D.det • fderiv ℂ (fun x : M2 n => (u1 x).det) A) A := by
    simp_rw [hu, Matrix.det_mul]
    exact (hdet A).const_mul D.det
  have h4 := congrArg (fun T => T (A * X)) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hL] at h4
  rw [Matrix.mul_assoc, h4, hu, Matrix.det_mul, mul_div_mul_left _ _ hD]

theorem rA_up (X : M2 n) (p k : GR n) (hp : IsUp p) : rA X (mR p * mR k) = rA X (mR k) := by
  have hD : (toBlocks₂₂ (mR p)).det ≠ 0 := by
    rw [← first_block_of_upper p hp]
    exact det_first_cayley_block_ne_zero p.2
  exact rA_mul_left_eq_of_u1_mul _ _ _ X hD (fun y => first_block_upper_mul p y hp)

theorem continuous_rD (X : M2 n) : Continuous fun k : GR n => rD X (mR k) := by
  unfold rD
  refine Continuous.div ?_ (cd_det.continuous.comp continuous_mR') (fun k => det_mR_ne' k)
  exact ((cd_det.continuous_fderiv (by simp)).comp continuous_mR').clm_apply
    (continuous_mR'.mul continuous_const)

theorem continuous_rA (X : M2 n) : Continuous fun k : GR n => rA X (mR k) := by
  unfold rA
  refine Continuous.div ?_ (cd_detu1.continuous.comp continuous_mR')
    (fun k => (det_u_ne (x := mR k) k.2).1)
  exact ((cd_detu1.continuous_fderiv (by simp)).comp continuous_mR').clm_apply
    (continuous_mR'.mul continuous_const)

end PositivityTheory.Rg.Sw.HSt.FL
end
end

section

noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Hf (m : ℕ) (e : ℤ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n) (z : ℂ) (y : M2 n) : ℂ :=
  ∫ t, fz m e z (y * a * nU (herm t) * b) * ψ t

theorem isClosed_G : IsClosed {x : M2 n | InG x} := by
  show IsClosed {x : M2 n | xᴴ * JJ n * x = JJ n}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

instance instLC : LocallyCompactSpace (M2 n) :=
  inferInstanceAs (LocallyCompactSpace (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))

instance instFC : FirstCountableTopology (M2 n) :=
  inferInstanceAs (FirstCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))

def Gs (n : ℕ) : Set (M2 n) := {x | InG x}

theorem continuousAt_fz {x : M2 n} (hx : InG x) (m : ℕ) (e : ℤ) (z : ℂ) :
    ContinuousAt (fun p : M2 n × ℂ => fz m e p.2 p.1) (x, z) := by
  have hdx : x.det ≠ 0 := (LoweringDerivative.isUnit_det_of_inG hx).ne_zero
  have hdet : Continuous (fun y : M2 n => y.det) := continuous_id.matrix_det
  have hdetn : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => M.det) := continuous_id.matrix_det
  have hu1 : Continuous (fun y : M2 n => u1 y) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply,
      smul_eq_mul]
    fun_prop
  have hub : ContinuousAt (fun y : M2 n => ub1 y) x :=
    continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
      (contDiffOn_inverse_first_block i j).continuousOn.continuousAt (isOpen_det_ne.mem_nhds hdx)
  have hw : (u1 x).det * (ub1 x).det = ((Complex.normSq (u1 x).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_conjTranspose hx, Matrix.det_conjTranspose, Complex.star_def, Complex.normSq_eq_conj_mul_self]
    ring
  have hslit : (u1 x).det * (ub1 x).det ∈ Complex.slitPlane := by
    rw [hw, Complex.ofReal_mem_slitPlane]
    exact Complex.normSq_pos.2 (det_first_block_ne_zero_group hx)
  show ContinuousAt (fun p : M2 n × ℂ =>
    p.1.det ^ e * (u1 p.1).det ^ (-(m : ℤ)) * ((u1 p.1).det * (ub1 p.1).det) ^ (-p.2)) (x, z)
  have hA : ContinuousAt (fun p : M2 n × ℂ => p.1.det) (x, z) := (hdet.comp continuous_fst).continuousAt
  have hB : ContinuousAt (fun p : M2 n × ℂ => (u1 p.1).det) (x, z) :=
    ((hu1.comp continuous_fst).matrix_det).continuousAt
  have hub' : ContinuousAt (fun y : M2 n => (ub1 y).det) x := hdetn.continuousAt.comp hub
  have hC : ContinuousAt (fun p : M2 n × ℂ => (ub1 p.1).det) (x, z) :=
    ContinuousAt.comp (g := fun y : M2 n => (ub1 y).det) (f := Prod.fst) (x := (x, z)) hub'
      continuous_fst.continuousAt
  refine ((hA.zpow₀ e (Or.inl hdx)).mul (hB.zpow₀ _ (Or.inl (det_first_block_ne_zero_group hx)))).mul ?_
  exact (hB.mul hC).cpow continuous_snd.neg.continuousAt hslit

theorem inG_path {y a b : M2 n} (hy : InG y) (ha : InG a) (hb : InG b) (t : Fin n → Fin n → ℝ) :
    InG (y * a * nU (herm t) * b) := by
  have hH : (herm t)ᴴ = herm t := by
    ext i j
    simp only [herm, Matrix.conjTranspose_apply, Complex.star_def, map_add (f := _), map_div₀, map_mul,
      Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  have hN : InG (nU (herm t)) := by
    show (nU (herm t))ᴴ * JJ n * nU (herm t) = JJ n
    simp [nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hH]
  exact inG_mul (inG_mul (inG_mul hy ha) hN) hb

private theorem continuous_nU_herm : Continuous (fun t : Fin n → Fin n → ℝ => nU (herm t)) := by
  have hherm : Continuous (fun t : Fin n → Fin n → ℝ => herm t) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [herm]
    fun_prop
  unfold nU
  exact continuous_const.matrix_fromBlocks hherm continuous_const continuous_const

private theorem continuous_fz_mul_nU_herm_mul {X : Type} [TopologicalSpace X] (m : ℕ) (e : ℤ)
    {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) {a b : M2 n} (ha : InG a) (hb : InG b)
    (Y : X → M2 n) (hY : Continuous Y) (hYG : ∀ x, InG (Y x)) (Z : X → ℂ) (hZ : Continuous Z)
    (T : X → (Fin n → Fin n → ℝ)) (hT : Continuous T) :
    Continuous fun x => fz m e (Z x) (Y x * a * nU (herm (T x)) * b) * ψ (T x) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine ContinuousAt.mul ?_ (hψ.comp hT).continuousAt
  have hG := inG_path (hYG x) ha hb (T x)
  have hP : Continuous fun x => (Y x * a * nU (herm (T x)) * b, Z x) :=
    (((hY.matrix_mul continuous_const).matrix_mul (continuous_nU_herm.comp hT)).matrix_mul
      continuous_const).prodMk hZ
  exact ContinuousAt.comp (g := fun p : M2 n × ℂ => fz m e p.2 p.1)
    (f := fun x => (Y x * a * nU (herm (T x)) * b, Z x)) (x := x)
    (continuousAt_fz hG m e (Z x)) hP.continuousAt

theorem continuous_Hf (m : ℕ) (e : ℤ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {a b : M2 n} (ha : InG a) (hb : InG b) :
    Continuous fun q : ↥(Gs n) × ℂ => Hf m e ψ a b q.2 q.1.1 := by
  haveI : LocallyCompactSpace ↥(Gs n) := (isClosed_G (n := n)).locallyCompactSpace
  have hF := continuous_fz_mul_nU_herm_mul (X := (↥(Gs n) × ℂ) × (Fin n → Fin n → ℝ)) m e hψ ha hb
    (fun p => p.1.1.1) (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
    (fun p => p.1.1.2) (fun p => p.1.2) (continuous_snd.comp continuous_fst) (fun p => p.2) continuous_snd
  have key := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Fin n → Fin n → ℝ)))
    (f := fun (q : ↥(Gs n) × ℂ) t => fz m e q.2 (q.1.1 * a * nU (herm t) * b) * ψ t) hF hψc
  refine key.congr fun q => ?_
  unfold Hf
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
    rw [image_eq_zero_of_notMem_tsupport ht, mul_zero]

theorem differentiable_Hf (m : ℕ) (e : ℤ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {a b y : M2 n} (ha : InG a) (hb : InG b) (hy : InG y) : Differentiable ℂ fun z => Hf m e ψ a b z y := by
  have hC : IsCompact (tsupport ψ) := hψc
  haveI : IsFiniteMeasure ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ)) :=
    isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  have hnull : ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ)) (tsupport ψ)ᶜ = 0 := by
    rw [Measure.restrict_apply' (isClosed_tsupport ψ).measurableSet, Set.compl_inter_self, measure_empty]
  have hF := continuous_fz_mul_nU_herm_mul (X := (Fin n → Fin n → ℝ) × ℂ) m e hψ ha hb (fun _ => y) continuous_const
    (fun _ => hy) (fun p => p.2) continuous_snd (fun p => p.1) continuous_fst
  have hdiff : ∀ t ∈ tsupport ψ,
      DifferentiableOn ℂ (fun z => fz m e z (y * a * nU (herm t) * b) * ψ t) Set.univ := by
    intro t _ z _
    have hG := inG_path hy ha hb t
    have hc : (u1 (y * a * nU (herm t) * b)).det * (ub1 (y * a * nU (herm t) * b)).det ≠ 0 := by
      refine mul_ne_zero (det_first_block_ne_zero_group hG) ?_
      rw [inverse_first_block_eq_conjTranspose hG, Matrix.det_conjTranspose]
      exact star_ne_zero.2 (det_first_block_ne_zero_group hG)
    simp only [fz]
    exact (((differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hc))).mul_const
      _).differentiableWithinAt
  have main := (AbsSt.holParam (Fin n → Fin n → ℝ) ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ))
    (tsupport ψ) hC hnull Set.univ (fun t z => fz m e z (y * a * nU (herm t) * b) * ψ t) isOpen_univ
    hF.continuousOn hdiff).1
  rw [differentiableOn_univ] at main
  have hEq : ∀ z, Hf m e ψ a b z y = ∫ t in tsupport ψ, fz m e z (y * a * nU (herm t) * b) * ψ t := by
    intro z
    unfold Hf
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
      rw [image_eq_zero_of_notMem_tsupport ht, mul_zero]).symm
  simp only [hEq]
  exact main

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
end
end

section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem toBlocks₁₁_mul' (A B : M2 n) :
    (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem mul_cm₁₁ (x : M2 n) : (x * Cm n).toBlocks₁₁ = Complex.I • x.toBlocks₁₁ + x.toBlocks₁₂ := by
  simp [toBlocks₁₁_mul', Cm, Matrix.mul_smul]

theorem cmS : (Cm n)ᴴ * JJ n * Cm n = fromBlocks ((-2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) 0 0
    ((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  simp only [Cm, JJ, fromBlocks_conjTranspose, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem cmiH_cmi : (Cmi n)ᴴ * Cmi n = (1 / 2 : ℂ) • (1 : M2 n) := by
  rw [← fromBlocks_one, fromBlocks_smul]
  simp only [Cmi, fromBlocks_conjTranspose, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem cmi_mul_cm : Cmi n * Cm n = 1 := mul_eq_one_comm.1 cm_mul_cmi

theorem mR_inv_mul (y y' : GR n) : mR (y⁻¹ * y') = (mR y)⁻¹ * mR y' := by
  simp [mR, Matrix.coe_units_inv]

theorem isUnit_mR (y : GR n) : IsUnit (mR y) := (y.1).isUnit

theorem fib : Fib := by
  intro n y y' hz
  have hGk : InG (mR (y⁻¹ * y')) := (y⁻¹ * y').2
  refine ⟨hGk, ?_⟩
  set x := mR y with hxdef
  set x' := mR y' with hx'def
  set k := mR (y⁻¹ * y') with hkdef
  have hkxx : k = x⁻¹ * x' := mR_inv_mul y y'
  have hxu : IsUnit x := isUnit_mR y
  have hxdet : IsUnit x.det := (Matrix.isUnit_iff_isUnit_det x).1 hxu
  have hu1 : (u1 x).det ≠ 0 := (detU1 n y).1
  have hu1' : (u1 x').det ≠ 0 := (detU1 n y').1
  have hu1u : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 hu1
  have hu1u' : IsUnit (u1 x').det := isUnit_iff_ne_zero.2 hu1'
  set c := (u1 x)⁻¹ * u1 x' with hc

  have h21 : (x' * Cm n).toBlocks₂₁ = (x * Cm n).toBlocks₂₁ * c := by
    rw [mul_cm₂₁, mul_cm₂₁, hc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1u, Matrix.one_mul]
  have h11 : (x' * Cm n).toBlocks₁₁ = (x * Cm n).toBlocks₁₁ * c := by
    rw [mul_cm₁₁, mul_cm₁₁]
    have hz' : (Complex.I • x.toBlocks₁₁ + x.toBlocks₁₂) * (u1 x)⁻¹ =
        (Complex.I • x'.toBlocks₁₁ + x'.toBlocks₁₂) * (u1 x')⁻¹ := hz
    have := congrArg (· * u1 x') hz'
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu1u', Matrix.mul_one] at this
    rw [hc]; exact this.symm

  set D := Cmi n * k * Cm n with hD
  have hDE : D * fromBlocks 1 0 0 0 = fromBlocks c 0 0 0 := by
    have e1 : x' * Cm n * fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 0 0 =
        x * Cm n * fromBlocks c 0 0 0 := by
      conv_lhs => rw [← fromBlocks_toBlocks (x' * Cm n), fromBlocks_multiply]
      conv_rhs => rw [← fromBlocks_toBlocks (x * Cm n), fromBlocks_multiply]
      rw [h11, h21]; simp
    calc D * fromBlocks 1 0 0 0 = Cmi n * x⁻¹ * (x' * Cm n * fromBlocks 1 0 0 0) := by
          rw [hD, hkxx]; simp only [Matrix.mul_assoc]
      _ = Cmi n * x⁻¹ * (x * Cm n * fromBlocks c 0 0 0) := by rw [e1]
      _ = Cmi n * (x⁻¹ * x) * Cm n * fromBlocks c 0 0 0 := by simp only [Matrix.mul_assoc]
      _ = fromBlocks c 0 0 0 := by
          rw [Matrix.nonsing_inv_mul _ hxdet, Matrix.mul_one, cmi_mul_cm, Matrix.one_mul]
  have hD0 : D = fromBlocks c D.toBlocks₁₂ 0 D.toBlocks₂₂ := by
    have := hDE
    conv_lhs at this => rw [← fromBlocks_toBlocks D, fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero] at this
    obtain ⟨e11, -, e21, -⟩ := Matrix.fromBlocks_inj.1 this
    conv_lhs => rw [← fromBlocks_toBlocks D]
    rw [e11, e21]

  have hk : kᴴ * JJ n * k = JJ n := hGk
  have hS : Dᴴ * ((Cm n)ᴴ * JJ n * Cm n) * D = (Cm n)ᴴ * JJ n * Cm n := by
    have hcc : (Cmi n)ᴴ * (Cm n)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, cm_mul_cmi, Matrix.conjTranspose_one]
    calc Dᴴ * ((Cm n)ᴴ * JJ n * Cm n) * D
        = (Cm n)ᴴ * kᴴ * ((Cmi n)ᴴ * (Cm n)ᴴ) * JJ n * (Cm n * Cmi n) * k * Cm n := by
          rw [hD]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Cm n)ᴴ * (kᴴ * JJ n * k) * Cm n := by
          rw [hcc, cm_mul_cmi]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (Cm n)ᴴ * JJ n * Cm n := by rw [hk]
  rw [cmS, hD0] at hS
  simp only [fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.conjTranspose_zero,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at hS
  obtain ⟨s11, s12, -, s22⟩ := Matrix.fromBlocks_inj.1 hS
  have hI : (-2 * Complex.I) ≠ 0 := by simp [Complex.ext_iff]
  have hI' : (2 * Complex.I) ≠ 0 := by simp [Complex.ext_iff]
  have hcc : cᴴ * c = 1 := by
    have := congrArg (fun M => (-2 * Complex.I)⁻¹ • M) s11
    simpa [smul_smul, inv_mul_cancel₀ hI] using this
  have hcc' : c * cᴴ = 1 := mul_eq_one_comm.1 hcc
  have hB : D.toBlocks₁₂ = 0 := by
    have h1 : cᴴ * D.toBlocks₁₂ = 0 := by
      have := congrArg (fun M => (-2 * Complex.I)⁻¹ • M) s12
      simpa [smul_smul, inv_mul_cancel₀ hI] using this
    calc D.toBlocks₁₂ = c * cᴴ * D.toBlocks₁₂ := by rw [hcc', Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, h1, Matrix.mul_zero]
  have hc' : (D.toBlocks₂₂)ᴴ * D.toBlocks₂₂ = 1 := by
    rw [hB] at s22
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, smul_zero] at s22
    have := congrArg (fun M => (2 * Complex.I)⁻¹ • M) s22
    simpa [smul_smul, inv_mul_cancel₀ hI'] using this
  have hDD : Dᴴ * D = 1 := by
    rw [hD0, hB, fromBlocks_conjTranspose, fromBlocks_multiply, hcc, hc', ← fromBlocks_one]
    simp

  have hkD : k = Cm n * D * Cmi n := by
    rw [hD]; simp only [← Matrix.mul_assoc]
    rw [cm_mul_cmi, Matrix.one_mul, Matrix.mul_assoc, cm_mul_cmi, Matrix.mul_one]
  have hcm2 : (Cm n)ᴴ * Cm n = (2 : ℂ) • (1 : M2 n) := by
    rw [← fromBlocks_one, fromBlocks_smul]
    simp only [Cm, fromBlocks_conjTranspose, fromBlocks_multiply]
    congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  calc kᴴ * k = (Cmi n)ᴴ * (Dᴴ * ((Cm n)ᴴ * Cm n) * D) * Cmi n := by
        rw [hkD]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (2 : ℂ) • ((Cmi n)ᴴ * Cmi n) := by
        rw [hcm2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hDD, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one]
    _ = 1 := by rw [cmiH_cmi, smul_smul]; norm_num

end PositivityTheory.Rg.Sw.HSt
end
end
