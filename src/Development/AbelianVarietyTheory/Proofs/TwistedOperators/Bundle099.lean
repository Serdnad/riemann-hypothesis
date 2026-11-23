module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleOf
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FractionalBaseInclusion
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Mathlib.MeasureTheory.Function.L2Space
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle627
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CommuteRowOpRightMixedOp
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumRowDegreeEqOfHarmonicHighestCasimir
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle090
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerKTypesPTensorStableUnderK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Lemma
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
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

@[expose] public section

section

namespace GlobalTheory.RegSSObj

theorem regularSemisimple : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple :=
  GlobalTheory.RegSS.regularSemisimple

end GlobalTheory.RegSSObj
end

section

noncomputable section

namespace GlobalTheory.Proof.FractionFieldEmbeddingCompat

open Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion

theorem fracExt_fracBase_algebraMap {D : D7} (c : NChoice D) (w : D.what₂.places.Pl) (y : D.ntw.O0 (c.twI w)) :
    fracExt c w (fracBase D (c.twI w) (algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y)) =
      algebraMap (c.Oe w) (FractionRing (c.Oe w)) (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
        (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w))
          (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y))) := by
  rw [← IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)]
  simp [fracExt, fracBase, IsFractionRing.map]

theorem embW_eq_of_tie {D : D7} {c : NChoice D} (h : NChTie D c) (w : D.what₂.places.Pl) (x : D.LL0) :
    c.embW w (x : D.what₂.LL) = fracExt c w (fracBase D (c.twI w) (embSide D (c.twI w) (c.sd w) x)) := by
  obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 (c.twI w)) (embSide D (c.twI w) (c.sd w) x)
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz1 : algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) z ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hz0
  have hmul : embSide D (c.twI w) (c.sd w) x * algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) z =
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y := by
    rw [← hyz, div_mul_cancel₀ _ hz1]
  have e := h.embedding_baseField_condition w x y z hz0 hmul
  rw [← fracExt_fracBase_algebraMap, ← fracExt_fracBase_algebraMap, ← hmul, map_mul, map_mul] at e
  exact mul_right_cancel₀ ((map_ne_zero _).2 ((map_ne_zero _).2 hz1)) e

theorem embCompat : EmbCompat := by
  intro D c h K _ _ _ κ hκ w ιK hι
  subst hι
  ext x
  have e := embW_eq_of_tie h w (κ x)
  rw [hκ x] at e
  exact e

end GlobalTheory.Proof.FractionFieldEmbeddingCompat

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HSAbs

theorem coeFn_finsum {X : Type} [MeasurableSpace X] {ν : Measure X} {κ : Type} (s : Finset κ)
    (f : κ → Lp ℂ 2 ν) : (⇑(∑ i ∈ s, f i) : X → ℂ) =ᵐ[ν] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 ν
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

theorem pointwise {X : Type} [MeasurableSpace X] {ν : Measure X}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type} (e : ι → H) (he : Orthonormal ℂ e) (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ)
    (hT : ∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) (s : Finset ι) :
    ∀ᵐ x ∂ν, ∑ i ∈ s, ‖T (e i) x‖ ^ 2 ≤ C ^ 2 := by
  classical

  let w : (s → ℂ) → H := fun c => ∑ j : s, c j • e j
  have hon : Orthonormal ℂ (fun j : s => e j) := he.comp _ Subtype.val_injective
  have hw2 : ∀ c, ‖w c‖ ^ 2 = ∑ j : s, ‖c j‖ ^ 2 := by
    intro c
    have h := hon.inner_sum c c Finset.univ

    rw [@norm_sq_eq_re_inner ℂ, h, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (s → ℂ)
  have hD : ∀ c ∈ D, ∀ᵐ x ∂ν, ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖ := by
    intro c _
    have hlin : T (w c) = ∑ j : s, c j • T (e j) := by

      simp only [w, map_sum, map_smul]
    have hsm : ∀ᵐ x ∂ν, ∀ j : s, (c j • T (e j) : Lp ℂ 2 ν) x = c j * T (e j) x := by
      rw [ae_all_iff]
      intro j
      filter_upwards [Lp.coeFn_smul (c j) (T (e j))] with x hx
      rw [hx]; rfl
    filter_upwards [hT (w c), coeFn_finsum (ν := ν) Finset.univ (fun j : s => c j • T (e j)), hsm]
      with x hx hsum hj
    rw [hlin, hsum] at hx
    simpa only [hj] using hx
  filter_upwards [(ae_ball_iff hDc).2 hD] with x hx

  have hall : ∀ c : s → ℂ, ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖ := by
    have hcl : IsClosed {c : s → ℂ | ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have hsub : closure D ⊆ {c : s → ℂ | ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖} :=
      hcl.closure_subset_iff.2 fun c hc => hx c hc
    intro c
    exact hsub (hDd.closure_eq ▸ Set.mem_univ c)

  set S := ∑ j : s, ‖T (e j) x‖ ^ 2 with hS
  have key := hall fun j => (starRingEnd ℂ) (T (e j) x)
  have hL : ‖∑ j : s, (starRingEnd ℂ) (T (e j) x) * T (e j) x‖ = S := by
    have : ∑ j : s, (starRingEnd ℂ) (T (e j) x) * T (e j) x = ((S : ℝ) : ℂ) := by
      rw [hS]; push_cast
      exact Finset.sum_congr rfl fun j _ => RCLike.conj_mul _
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hR : ‖w (fun j => (starRingEnd ℂ) (T (e j) x))‖ ^ 2 = S := by
    rw [hw2]
    exact Finset.sum_congr rfl fun j _ => by rw [RCLike.norm_conj]
  rw [hL] at key
  have hnn := norm_nonneg (w fun j => (starRingEnd ℂ) (T (e j) x))
  have hfin : S ≤ C ^ 2 := by
    nlinarith [sq_nonneg (C - ‖w fun j => (starRingEnd ℂ) (T (e j) x)‖)]
  rw [← Finset.sum_coe_sort s (fun i => ‖T (e i) x‖ ^ 2)]
  exact hfin

theorem sum_le {X : Type} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type} (e : ι → H) (he : Orthonormal ℂ e) (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ)
    (hT : ∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) (s : Finset ι) :
    ∑ i ∈ s, ‖T (e i)‖ ^ 2 ≤ C ^ 2 * ν.real univ := by
  have hn : ∀ f : Lp ℂ 2 ν, ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
    intro f
    rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
    simp_rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
    rw [integral_ofReal, RCLike.ofReal_re]
  have hint : ∀ f : Lp ℂ 2 ν, Integrable (fun x => ‖f x‖ ^ 2) ν := by
    intro f
    have hm : MemLp f ((2 : ℕ) : ENNReal) ν := by simpa using Lp.memLp f
    exact hm.integrable_norm_pow (by norm_num)
  calc ∑ i ∈ s, ‖T (e i)‖ ^ 2 = ∫ x, ∑ i ∈ s, ‖T (e i) x‖ ^ 2 ∂ν := by
        rw [integral_finsetSum s fun i _ => hint (T (e i))]
        exact Finset.sum_congr rfl fun i _ => hn _
    _ ≤ ∫ _x, C ^ 2 ∂ν :=
        integral_mono_ae (integrable_finsetSum s fun i _ => hint (T (e i)))
          (integrable_const _) (pointwise e he T C hT s)
    _ = C ^ 2 * ν.real univ := by rw [integral_const, smul_eq_mul, mul_comm]

end GlobalTheory.HSAbs


open GlobalTheory.HSAbs in
theorem GlobalTheory.isHilbertSchmidt_of_ae_bounded : ∀ {X : Type} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ), (∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) → GlobalTheory.OpTrace.IsHilbertSchmidt T := by
  intro X _ ν _ H _ _ _ T C hT
  unfold GlobalTheory.OpTrace.IsHilbertSchmidt
  refine summable_of_sum_le (c := C ^ 2 * ν.real univ) (fun i => sq_nonneg _) fun u => ?_
  exact GlobalTheory.HSAbs.sum_le _ (GlobalTheory.OpTrace.stdBasis (H := H)).orthonormal T C hT u
end

section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.FlagMeas.DetAdj

lemma mul_basisMat_eq {n : ℕ} (V : Submodule ℂ (Fin n → ℂ)) {d : Type} [Fintype d] [DecidableEq d]
    (b : Module.Basis d ℂ V) (g : Matrix (Fin n) (Fin n) ℂ) (f : V →ₗ[ℂ] V)
    (hf : ∀ v : V, ((f v : V) : Fin n → ℂ) = g *ᵥ (v : Fin n → ℂ)) :
    g * Matrix.of (fun i j => (b j : Fin n → ℂ) i) =
      Matrix.of (fun i j => (b j : Fin n → ℂ) i) * LinearMap.toMatrix b b f := by
  ext i j
  have h1 : (g * Matrix.of (fun i j => (b j : Fin n → ℂ) i)) i j = (g *ᵥ (b j : Fin n → ℂ)) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, ← hf]
  have h2 : ((f (b j) : V) : Fin n → ℂ) = ∑ k, b.repr (f (b j)) k • (b k : Fin n → ℂ) := by
    conv_lhs => rw [← b.sum_repr (f (b j))]
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  rw [h2]
  simp [Matrix.mul_apply, LinearMap.toMatrix_apply, Finset.sum_apply, mul_comm]

theorem detOn_conjTranspose : ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)),
    (∀ y ∈ V, g *ᵥ y ∈ V) → (∀ y ∈ V, gᴴ *ᵥ y ∈ V) →
      GlobalTheory.FlagMeas.detOn gᴴ V = GlobalTheory.FlagMeas.detOn g V := by
  intro n g V hg hgh
  have hg' : ∀ y ∈ V, Matrix.toLin' g y ∈ V := by simpa [Matrix.toLin'_apply] using hg
  have hgh' : ∀ y ∈ V, Matrix.toLin' gᴴ y ∈ V := by simpa [Matrix.toLin'_apply] using hgh
  unfold GlobalTheory.FlagMeas.detOn
  rw [dite_eq_left hgh', dite_eq_left hg']
  set f := (Matrix.toLin' g).restrict hg'
  set f' := (Matrix.toLin' gᴴ).restrict hgh'
  let b := Module.finBasis ℂ V
  set B : Matrix (Fin n) (Fin (Module.finrank ℂ V)) ℂ := Matrix.of (fun i j => (b j : Fin n → ℂ) i) with hB
  set A := LinearMap.toMatrix b b f
  set A' := LinearMap.toMatrix b b f'
  have h1 : g * B = B * A := mul_basisMat_eq V b g f (fun v => by simp [f, Matrix.toLin'_apply])
  have h2 : gᴴ * B = B * A' := mul_basisMat_eq V b gᴴ f' (fun v => by simp [f', Matrix.toLin'_apply])
  have hinj : Function.Injective B.mulVec := by
    rw [Matrix.mulVec_injective_iff]
    have : B.col = fun j => (b j : Fin n → ℂ) := by ext j i; rfl
    rw [this]
    exact b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hG : (Bᴴ * B).det ≠ 0 := (Matrix.PosDef.conjTranspose_mul_self B hinj).det_pos.ne'
  have key : (Bᴴ * B) * A = A'ᴴ * (Bᴴ * B) := by
    calc (Bᴴ * B) * A = Bᴴ * (g * B) := by rw [h1, Matrix.mul_assoc]
      _ = (gᴴ * B)ᴴ * B := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = A'ᴴ * (Bᴴ * B) := by rw [h2, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hdet : A.det = star A'.det := by
    have := congrArg Matrix.det key
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, mul_comm (star _)] at this
    exact mul_left_cancel₀ hG this
  rw [← LinearMap.det_toMatrix b f, ← LinearMap.det_toMatrix b f']
  change ‖A'.det‖ = ‖A.det‖
  rw [hdet, norm_star]

end GlobalTheory.FlagMeas.DetAdj
end

section

open Matrix

namespace GlobalTheory.FlagMeas

theorem detOn_exp_smul : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)),
    (∀ y ∈ V, A *ᵥ y ∈ V) → ∃ c : ℝ, ∀ t : ℝ,
      GlobalTheory.FlagMeas.detOn (NormedSpace.exp (t • A)) V = Real.exp (t * c) := by
  intro n A V hA
  have hA' : ∀ y ∈ V, Matrix.toLin' A y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply]; exact hA y hy
  set f : V →ₗ[ℂ] V := (Matrix.toLin' A).restrict hA' with hf
  set b := Module.finBasis ℂ V with hb
  set B := LinearMap.toMatrixAlgEquiv b f with hB
  refine ⟨(B.trace).re, fun t => ?_⟩
  have hts : t • A = (t : ℂ) • A := by ext i j; simp [Complex.real_smul]
  rw [hts]
  set s : ℂ := (t : ℂ) with hs
  have hpowA : ∀ (k : ℕ) (v : V), (s • A) ^ k *ᵥ (v : Fin n → ℂ) = (((s • f) ^ k) v : Fin n → ℂ) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ih, Module.End.mul_apply]
      simp [hf, LinearMap.restrict_apply, Matrix.toLin'_apply, Matrix.smul_mulVec]
  have hpowB : ∀ k : ℕ, Matrix.toLinAlgEquiv b ((s • B) ^ k) = (s • f) ^ k := by
    intro k
    rw [map_pow, map_smul, hB, Matrix.toLinAlgEquiv_toMatrixAlgEquiv]
  have key : ∀ v : V, NormedSpace.exp (s • A) *ᵥ (v : Fin n → ℂ) =
      ((Matrix.toLinAlgEquiv b (NormedSpace.exp (s • B))) v : Fin n → ℂ) := by
    intro v
    open scoped Matrix.Norms.Operator in
    have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (s • A)
    open scoped Matrix.Norms.Operator in
    have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (s • B)
    let g1 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (Fin n → ℂ) :=
      LinearMap.applyₗ (v : Fin n → ℂ) ∘ₗ Matrix.toLin'.toLinearMap
    let g2 : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ →ₗ[ℂ] (Fin n → ℂ) :=
      V.subtype ∘ₗ LinearMap.applyₗ v ∘ₗ (Matrix.toLinAlgEquiv b).toLinearMap
    have h1' := h1.map g1 (LinearMap.continuous_of_finiteDimensional g1)
    have h2' := h2.map g2 (LinearMap.continuous_of_finiteDimensional g2)
    have heq : (g1 ∘ fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (s • A) ^ k) =
        (g2 ∘ fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (s • B) ^ k) := by
      funext k
      simp only [Function.comp_apply, map_smul, g1, g2, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
        LinearEquiv.coe_coe, Matrix.toLin'_apply, AlgEquiv.toLinearMap_apply, Submodule.subtype_apply]
      rw [hpowA, hpowB]
    rw [heq] at h1'
    exact h1'.unique h2'
  have hstab : ∀ y ∈ V, Matrix.toLin' (NormedSpace.exp (s • A)) y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply, key ⟨y, hy⟩]; exact Submodule.coe_mem _
  have hres : (Matrix.toLin' (NormedSpace.exp (s • A))).restrict hstab =
      Matrix.toLinAlgEquiv b (NormedSpace.exp (s • B)) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp only [LinearMap.restrict_coe_apply, Matrix.toLin'_apply]
    exact key v
  rw [detOn, dite_eq_left hstab, hres]
  show ‖LinearMap.det (Matrix.toLin b b (NormedSpace.exp (s • B)))‖ = _
  rw [LinearMap.det_toLin, GlobalTheory.SUVol.det_exp, Matrix.trace_smul, smul_eq_mul, Complex.norm_exp, hs,
    Complex.re_ofReal_mul]

end GlobalTheory.FlagMeas
end

section

open Formalism.REAL Finset Polynomial

theorem _root_.GlobalTheory.T.scalar_capelli_truncated_perelomov_popov : ∀ (m N : ℕ) (χ : Fin (m + 1) → ℂ), ∃ r : ℂ[X], r.natDegree ≤ m ∧ ∀ u : ℂ, (u - m) ^ (N + 1) * (∏ s, (u + 1 - (m : ℂ) / 2 + χ s) - ∏ s, (u - (m : ℂ) / 2 + χ s)) - (∏ s, (u - (m : ℂ) / 2 + χ s)) * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * GlobalTheory.Dec.gelfVal χ k = r.eval u := by
  first | exact @GlobalTheory.ScalarNewton.scalar_newton | exact GlobalTheory.ScalarNewton.scalar_newton | (intros; apply GlobalTheory.ScalarNewton.scalar_newton <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.PackLoc

def embOpt {m N : ℕ} (e : Option (Fin m) ≃ Fin N) (h : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => match e.symm a, e.symm b with
    | some i, some j => h i j
    | none, none => 1
    | _, _ => 0

def embOptL {m N : ℕ} (e : Option (Fin m) ≃ Fin N) (X : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => match e.symm a, e.symm b with
    | some i, some j => X i j
    | _, _ => 0

theorem embH_eq_embOpt {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) (h : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.SepReal.embH e h = embOpt e h := rfl

theorem embL_eq_embOptL {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) (X : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.SepReal.embL e X = embOptL e X := rfl

theorem embOpt_one {m N : ℕ} (e : Option (Fin m) ≃ Fin N) : embOpt e 1 = 1 := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embOpt, Matrix.one_apply]

end GlobalTheory.PackLoc

end
end

section

namespace GlobalTheory.SepReal

theorem interlaced_sub_single : ∀ {n : ℕ} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ},
    GlobalTheory.SepReal.Interlaced ε lam ε' mu → (∀ a c, a ≠ c → 2 ≤ |lam a - lam c|) → (∀ a i, mu i < lam a → mu i + 1 < lam a) →
      (∀ a i, lam a ≠ mu i) → ∀ s, GlobalTheory.SepReal.Interlaced ε (lam - Pi.single s 1) ε' mu := by
  intro n ε lam ε' mu hI hw hm hne s
  have h01 : ∀ a, (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = 0 ∨ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = 1 := by
    intro a
    by_cases h : a = s
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hb : ∀ a, 0 ≤ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a ∧ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a ≤ 1 := by
    intro a
    rcases h01 a with h | h <;> rw [h] <;> norm_num
  have key : ∀ x y : Fin (n + 1) ⊕ Fin n, Sum.elim (lam - Pi.single s 1) mu y < Sum.elim (lam - Pi.single s 1) mu x ↔
      Sum.elim lam mu y < Sum.elim lam mu x := by
    rintro (a | i) (c | j)
    · simp only [Sum.elim_inl, Pi.sub_apply]
      by_cases hac : a = c
      · subst hac; simp
      · have hw' := hw a c hac
        have ha := h01 a
        have hc := h01 c
        generalize (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = da at ha
        generalize (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) c = dc at hc
        rcases le_abs.1 hw' with h | h <;> rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;>
          constructor <;> intro h' <;> linarith
    · simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]
      have hba := hb a
      constructor
      · intro h; linarith
      · intro h; have := hm a j h; linarith
    · simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]
      have hbc := hb c
      constructor
      · intro h
        by_contra h'
        have hlt : mu i < lam c := lt_of_le_of_ne (not_lt.1 h') (fun e => hne c i e.symm)
        have := hm c i hlt
        linarith
      · intro h; linarith
    · simp
  intro x y h hz
  rw [key] at h
  exact hI x y h (fun z hz' => hz z ⟨(key z y).2 hz'.1, (key x z).2 hz'.2⟩)

end GlobalTheory.SepReal
end

section

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

theorem _root_.GlobalTheory.T.sum_row_degree_eq_of_harmonic_highest_casimir : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (k l n : ℕ) (z : Fin k × Fin n → σ) (y : Fin l × Fin n → σ), Function.Injective z → Function.Injective y → (∀ u w, z u ≠ y w) → ∀ (P : MvPolynomial σ ℂ) (a : Fin k → ℕ) (b : Fin l → ℕ) (κ : Fin n → ℤ), P ≠ 0 → Antitone a → Antitone b → Antitone κ → (∀ i j, i < j → rowOp ℂ z i j P = 0) → (∀ i, rowOp ℂ z i i P = (a i : ℂ) • P) → (∀ i j, i < j → rowOp ℂ y i j P = 0) → (∀ i, rowOp ℂ y i i P = (b i : ℂ) • P) → (∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) P) = 0) → (∀ i j, i < j → mixedOp ℂ z y i j P = 0) → (∀ t, mixedOp ℂ z y t t P = (κ t : ℂ) • P) → ∑ i, (a i : ℤ) = ∑ t, max (κ t) 0 := by
  first | exact @GlobalTheory.HarmRowDegree.sum_row_degree_eq | exact GlobalTheory.HarmRowDegree.sum_row_degree_eq | (intros; apply GlobalTheory.HarmRowDegree.sum_row_degree_eq <;> assumption)
end

section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

theorem _root_.GlobalTheory.T.lowerKTypes_pTensor_stable_under_K : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), LowData ε E Λ u j → IsTau ε Λ τ w → TauTie ε E j τ → ∀ G : Fin n × Fin n → W, arr1 j G ∈ Vminus ε E Λ u → ∀ k ∈ Kset ε, ∃ G' : Fin n × Fin n → W, arr1 j G' ∈ Vminus ε E Λ u ∧ ∑ p, ⟪τ k w, G p⟫_ℂ • (k⁻¹ * thE ε p * k) = ∑ p, ⟪w, G' p⟫_ℂ • thE ε p := by
  first | exact @GlobalTheory.SphJet.vminus_stable_under_K | exact GlobalTheory.SphJet.vminus_stable_under_K | (intros; apply GlobalTheory.SphJet.vminus_stable_under_K <;> assumption)
end
