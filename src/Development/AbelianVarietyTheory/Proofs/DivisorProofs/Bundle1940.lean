module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319

@[expose] public section

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

noncomputable section

namespace GlobalTheory.Cusp.SmoothParam

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ N : Subgroup G} [DiscreteTopology Γ] [LocallyCompactSpace N]


omit [SecondCountableTopology G] [DiscreteTopology Γ] [LocallyCompactSpace N] in
theorem aestronglyMeasurable_out {E : Type} [NormedAddCommGroup E] [SecondCountableTopology E]
    {Φ : G → E} (hΦ : Continuous Φ) (hinv : ∀ γ ∈ Γ, ∀ x, Φ (γ * x) = Φ x) (g : G)
    (μ : Measure (Quot (Γ.subgroupOf N))) :
    AEStronglyMeasurable (fun q : Quot (Γ.subgroupOf N) => Φ ((q.out : N) * g)) μ := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have hl : LeftInv (Γ.subgroupOf N) (fun n : N => Φ (n * g)) := fun γ hγ n => by
    simp only [Subgroup.coe_mul, mul_assoc]; exact hinv _ hγ _
  have hm : Measurable (fun n : N => Φ (n * g)) :=
    (hΦ.comp ((continuous_subtype_val).mul continuous_const)).measurable
  have hq : Measurable (descend (Γ.subgroupOf N) (fun n : N => Φ (n * g))) := by
    refine measurable_from_quotient.2 ?_
    have e : (descend (Γ.subgroupOf N) (fun n : N => Φ (n * g))) ∘ Quotient.mk'' = fun n : N => Φ (n * g) :=
      hl.lift_descend
    rw [e]; exact hm
  exact hq.aestronglyMeasurable


omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ] [LocallyCompactSpace N] in
theorem exists_bound {T E : Type} [TopologicalSpace T] [NormedAddCommGroup E] (hc : Cocompact Γ N)
    {Ψ : G → T → E} (hΨ : Continuous fun p : G × T => Ψ p.1 p.2) (hinv : ∀ γ ∈ Γ, ∀ x t, Ψ (γ * x) t = Ψ x t)
    (g : G) {S : Set T} (hS : IsCompact S) : ∃ C, ∀ (n : N) t, t ∈ S → ‖Ψ (n * g) t‖ ≤ C := by
  obtain ⟨K, hK, hs⟩ := hc
  obtain ⟨C, hC⟩ := (hK.prod hS).exists_bound_of_continuousOn (f := fun p : N × T => Ψ (p.1 * g) p.2)
    (hΨ.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)).continuousOn
  refine ⟨C, fun n t ht => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hs n
  have e : Ψ (((γ * n : N) : G) * g) t = Ψ (n * g) t := by
    simp only [Subgroup.coe_mul, mul_assoc]; exact hinv _ hγ _ _
  exact e ▸ hC (γ * n, t) ⟨hk, ht⟩

theorem hasFDerivAt_param {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hc : Cocompact Γ N) (H : G → (Fin k → ℝ) → E)
    (hinv : ∀ γ ∈ Γ, ∀ x t, H (γ * x) t = H x t) (hd : ∀ x, Differentiable ℝ (H x))
    (h0 : Continuous fun p : G × (Fin k → ℝ) => H p.1 p.2)
    (h1 : Continuous fun p : G × (Fin k → ℝ) => fderiv ℝ (H p.1) p.2) (g : G) (t₀ : Fin k → ℝ) :
    HasFDerivAt (fun t => ∫ q, H ((q.out : N) * g) t ∂probMeasure Γ N)
      (∫ q, fderiv ℝ (H ((q.out : N) * g)) t₀ ∂probMeasure Γ N) t₀ := by
  have := hc.isProbabilityMeasure
  have hinv' : ∀ γ ∈ Γ, ∀ x t, fderiv ℝ (H (γ * x)) t = fderiv ℝ (H x) t := fun γ hγ x t => by
    rw [show H (γ * x) = H x from funext (hinv γ hγ x)]
  obtain ⟨C, hC⟩ := exists_bound (Ψ := fun x t => fderiv ℝ (H x) t) hc h1 hinv' g (isCompact_closedBall t₀ 1)
  obtain ⟨C0, hC0⟩ := exists_bound (Ψ := H) hc h0 hinv g (isCompact_closedBall t₀ 1)
  have hm : ∀ t, AEStronglyMeasurable (fun q : Quot (Γ.subgroupOf N) => H ((q.out : N) * g) t) (probMeasure Γ N) :=
    fun t => aestronglyMeasurable_out (Φ := fun x => H x t) (h0.comp (continuous_id.prodMk continuous_const))
      (fun γ hγ x => hinv γ hγ x t) g _
  have hm' : AEStronglyMeasurable (fun q : Quot (Γ.subgroupOf N) => fderiv ℝ (H ((q.out : N) * g)) t₀)
      (probMeasure Γ N) :=
    aestronglyMeasurable_out (Φ := fun x => fderiv ℝ (H x) t₀) (h1.comp (continuous_id.prodMk continuous_const))
      (fun γ hγ x => hinv' γ hγ x t₀) g _
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (Metric.ball_mem_nhds t₀ one_pos) (.of_forall hm)
    (Integrable.of_bound (hm t₀) C0 (.of_forall fun q => hC0 _ t₀ (Metric.mem_closedBall_self zero_le_one))) hm'
    (.of_forall fun q t ht => hC _ t (Metric.ball_subset_closedBall ht)) (integrable_const C)
    (.of_forall fun q t _ => (hd _ t).hasFDerivAt)


omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem iteratedFDeriv_fderiv_eq {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin k → ℝ) → E) (m : ℕ) (t : Fin k → ℝ) :
    iteratedFDeriv ℝ m (fderiv ℝ f) t =
      (continuousMultilinearCurryRightEquiv' ℝ m (Fin k → ℝ) E) (iteratedFDeriv ℝ (m + 1) f t) := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp


omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem continuous_of_iteratedFDeriv_zero {X : Type} [TopologicalSpace X] {k : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : X → (Fin k → ℝ) → E}
    (h : Continuous fun p : X × (Fin k → ℝ) => iteratedFDeriv ℝ 0 (H p.1) p.2) :
    Continuous fun p : X × (Fin k → ℝ) => H p.1 p.2 := by
  have e : (fun p : X × (Fin k → ℝ) => H p.1 p.2) =
      fun p => continuousMultilinearCurryFin0 ℝ (Fin k → ℝ) E (iteratedFDeriv ℝ 0 (H p.1) p.2) := by
    funext p; simp [continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply]
  rw [e]; exact (continuousMultilinearCurryFin0 ℝ (Fin k → ℝ) E).continuous.comp h

theorem contDiff_param (hc : Cocompact Γ N) (g : G) {k : ℕ} (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (H : G → (Fin k → ℝ) → E),
      (∀ γ ∈ Γ, ∀ x t, H (γ * x) t = H x t) → (∀ x, ContDiff ℝ ∞ (H x)) →
      (∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (H p.1) p.2) →
      ContDiff ℝ n fun t => ∫ q, H ((q.out : N) * g) t ∂probMeasure Γ N := by
  induction n with
  | zero =>
    intro E _ _ _ H hinv hs hm
    have h1 : Continuous fun p : G × (Fin k → ℝ) => fderiv ℝ (H p.1) p.2 := by
      refine continuous_of_iteratedFDeriv_zero (H := fun x => fderiv ℝ (H x)) ?_
      simp only [iteratedFDeriv_fderiv_eq]
      exact (continuousMultilinearCurryRightEquiv' ℝ 0 (Fin k → ℝ) E).continuous.comp (hm 1)
    refine contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => ?_)
    exact (hasFDerivAt_param hc H hinv (fun x => (hs x).differentiable (by simp))
      (continuous_of_iteratedFDeriv_zero (hm 0)) h1 g t).continuousAt
  | succ n ih =>
    intro E _ _ _ H hinv hs hm
    have hm' : ∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (fderiv ℝ (H p.1)) p.2 := by
      intro m
      simp only [iteratedFDeriv_fderiv_eq]
      exact (continuousMultilinearCurryRightEquiv' ℝ m (Fin k → ℝ) E).continuous.comp (hm (m + 1))
    have hinv' : ∀ γ ∈ Γ, ∀ x t, fderiv ℝ (H (γ * x)) t = fderiv ℝ (H x) t := fun γ hγ x t => by
      rw [show H (γ * x) = H x from funext (hinv γ hγ x)]
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨_, ih (fun x => fderiv ℝ (H x)) hinv'
      (fun x => (contDiff_infty_iff_fderiv.1 (hs x)).2) hm', fun t => ?_⟩
    exact hasFDerivAt_param hc H hinv (fun x => (contDiff_infty_iff_fderiv.1 (hs x)).1)
      (continuous_of_iteratedFDeriv_zero (hm 0))
      (continuous_of_iteratedFDeriv_zero (H := fun x => fderiv ℝ (H x)) (hm' 0)) g t

end GlobalTheory.Cusp.SmoothParam

theorem GlobalTheory.Cusp.contDiff_constTermOn_param : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ N : Subgroup G} [DiscreteTopology Γ]
    [LocallyCompactSpace N], GlobalTheory.Cusp.Cocompact Γ N → ∀ {k : ℕ} (F : G → (Fin k → ℝ) → ℂ),
    (∀ γ ∈ Γ, ∀ x t, F (γ * x) t = F x t) → (∀ x, ContDiff ℝ ∞ (F x)) →
    (∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (F p.1) p.2) →
    ∀ g : G, ContDiff ℝ ∞ fun t => GlobalTheory.Cusp.constTermOn Γ N (fun x => F x t) g := by
  intro G _ _ _ _ _ _ Γ N _ _ hc k F hinv hs hm g
  exact contDiff_infty.2 fun n => GlobalTheory.Cusp.SmoothParam.contDiff_param hc g n F hinv hs hm
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open scoped TensorProduct

noncomputable section
open Matrix
namespace GlobalTheory.StdPar.UnipArch

section Lin

variable {A : Type} [CommRing A] {n r : ℕ}

theorem mem_span_cols_iff (C : Matrix (Fin n) (Fin r) A) (I : Set (Fin r)) (y : Fin n → A) :
    y ∈ Submodule.span A ((fun i => Cᵀ i) '' I) ↔ ∃ a : Fin r → A, (∀ l, l ∉ I → a l = 0) ∧ C *ᵥ a = y := by
  first
  | exact @_root_.GlobalTheory.ColumnSumLemma.main
  | exact _root_.GlobalTheory.ColumnSumLemma.main
  | (apply _root_.GlobalTheory.ColumnSumLemma.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ColumnSumLemma.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ColumnSumLemma.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ColumnSumLemma.main ..)

variable (P : Fin r → Fin r → Prop) (hPt : ∀ i l j, P i l → P l j → P i j) (hPlt : ∀ i l, P i l → i < l)
include hPt



end Lin

section Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open GlobalTheory.AutFunCompare (evW sgW)


variable (F) in
def inlA : Ainf F →ₗ[F] AF F := LinearMap.inl F (Ainf F) (Af F)


variable (F) in
def inrA : Af F →ₗ[F] AF F := LinearMap.inr F (Ainf F) (Af F)


variable (F E) in
def glueInf (c : ∀ w : InfinitePlace F, w.Completion ⊗[F] E) : AF F ⊗[F] E :=
  (inlA F).rTensor E (∑ w, (sgW w).rTensor E (c w))

theorem map_evW_sum_sgW (c : ∀ w : InfinitePlace F, w.Completion ⊗[F] E) (w : InfinitePlace F) :
    Algebra.TensorProduct.map (evW w) (AlgHom.id F E) (∑ w', (sgW w').rTensor E (c w')) = c w := by
  classical

  rw [map_sum, Finset.sum_eq_single w]
  · induction c w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show (evW w (sgW w a)) ⊗ₜ[F] x = a ⊗ₜ[F] x
      congr 1
      exact Pi.single_eq_same w a
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  · intro w' _ hw'
    induction c w' using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show (evW w (sgW w' a)) ⊗ₜ[F] x = 0
      rw [show evW w (sgW w' a) = 0 from Pi.single_eq_of_ne (Ne.symm hw') a, TensorProduct.zero_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
  · simp

theorem compInf_rTensor_inlA (z : Ainf F ⊗[F] E) (w : InfinitePlace F) :
    compInf F E w ((inlA F).rTensor E z) = Algebra.TensorProduct.map (evW w) (AlgHom.id F E) z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem compInf_glueInf (c : ∀ w : InfinitePlace F, w.Completion ⊗[F] E) (w : InfinitePlace F) :
    compInf F E w (glueInf F E c) = c w := by
  rw [glueInf, compInf_rTensor_inlA, map_evW_sum_sgW]

theorem sndA_rTensor_inlA (z : Ainf F ⊗[F] E) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((inlA F).rTensor E z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x =>
    show (sndA F (inlA F a)) ⊗ₜ[F] x = 0
    rw [show sndA F (inlA F a) = 0 from rfl, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

theorem sndA_glueInf (c : ∀ w : InfinitePlace F, w.Completion ⊗[F] E) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (glueInf F E c) = 0 :=
  sndA_rTensor_inlA _

@[simp] theorem glueInf_zero : glueInf F E (fun _ => 0) = 0 := by
  simp only [glueInf, map_zero, Finset.sum_const_zero]

theorem tens_ext {z z' : AF F ⊗[F] E} (h1 : ∀ w, compInf F E w z = compInf F E w z')
    (h2 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z = Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z') :
    z = z' := by
  have hz : ∀ z : AF F ⊗[F] E, z = (inlA F).rTensor E (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) +
      (inrA F).rTensor E (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero, add_zero]
    | tmul x y =>
      show x ⊗ₜ[F] y = (inlA F (fstA F x)) ⊗ₜ[F] y + (inrA F (sndA F x)) ⊗ₜ[F] y
      rw [← TensorProduct.add_tmul]
      congr 1
      exact Prod.ext (add_zero _).symm (zero_add _).symm
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  have hc : ∀ (w : InfinitePlace F) (z : AF F ⊗[F] E), compInf F E w z =
      Algebra.TensorProduct.map (evW w) (AlgHom.id F E) (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) := by
    intro w z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul x y => rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  rw [hz z, hz z', h2, GlobalTheory.AutFunCompare.infTens_ext (fun w => (hc w z).symm.trans ((h1 w).trans (hc w z')))]

end Glue

section Main

end Main

end GlobalTheory.StdPar.UnipArch
end
end

section

noncomputable section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG)

namespace GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ}

structure Frame (P : Pair D cc δ t0 Q) where

  A : HSp D

  B : HSp D
  rkA : A.rank = P.a
  rkB : B.rank = P.d

  ιA : Formalism.MainNotions.StandardLatticesGL3.GA D P.a →* GA D A

  ιB : Formalism.MainNotions.StandardLatticesGL3.GA D P.d →* GA D B

  KA : Subgroup (GL (Fin A.rank) (Lev.EAf D))

  KB : Subgroup (GL (Fin B.rank) (Lev.EAf D))

  m : Measure (GA D A)

  mH : Measure (GA D B)

structure IsFrame (P : Pair D cc δ t0 Q) (Y : Frame P) : Prop where
  gramA : Y.A.gram = 1
  gramB : Y.B.gram = 1
  defA : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace Y.A
  defB : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace Y.B
  injA : Function.Injective Y.ιA
  injB : Function.Injective Y.ιB
  rangeA : Y.ιA.range = GfC Y.A
  rangeB : Y.ιB.range = GfC Y.B
  ratA : ∀ x, (∃ γ ∈ GQ Y.A, finHom Y.A γ = finHom Y.A (Y.ιA x)) ↔ x ∈ ratG D P.a
  ratB : ∀ h, (∃ γ ∈ GQ Y.B, finHom Y.B γ = finHom Y.B (Y.ιB h)) ↔ h ∈ ratG D P.d
  levA : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel Y.A Y.KA
  levB : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel Y.B Y.KB
  levA_iff : ∀ x, Lev.finE Y.A (Y.ιA x) ∈ Y.KA ↔ x ∈ intG D P.a
  levB_iff : ∀ h, Lev.finE Y.B (Y.ιB h) ∈ Y.KB ↔ h ∈ P.J
  haarA : Y.m.IsHaarMeasure
  haarB : Y.mH.IsHaarMeasure
  measA : ∃ 𝓕, Links.IsMeasDef Y.A Y.KA Y.m 𝓕
  measB : ∃ 𝓕, Links.IsMeasDef Y.B Y.KB Y.mH 𝓕

structure Data (P : Pair D cc δ t0 Q) extends Frame P where

  ψ : AddChar (AF D.host.F) ℂ

  θ : InfFam D

  χA : (AE D)ˣ →* Circle

  χB : (AE D)ˣ →* Circle

  om : GlobalTheory.Core.Rk.IP.WRep A B

  vac : WO A B → ℂ

  c₁ : ℂ

namespace Data

variable {P : Pair D cc δ t0 Q} (X : Data P)

def var (k : Formalism.MainNotions.GL3Theta.Idx D P.a P.d) : FVar D X.B.rank X.A.rank :=
  (k.1, Fin.cast X.rkB.symm k.2.1, Fin.cast X.rkA.symm k.2.2)

def fock (T : Tup D P.a P.d P.n) : WO X.A X.B → ℂ :=
  pureTensorL (aPlusAll (heisO X.ψ X.A X.B) X.θ (fun _ => cplxO 1 1) (fun _ => 1) (fun _ => 1)) X.vac
    (MvPolynomial.rename X.var (minorPol D T))

def lift (T : Tup D P.a P.d P.n) : GA D X.B → ℂ := GlobalTheory.Core.Rk.IP.up X.om X.m (X.fock T) 1

end Data

structure IsWeilOf (P : Pair D cc δ t0 Q) (X : Data P) : Prop where
  inf : IsInfFam X.θ
  weil : IsWeilDatumO X.ψ X.A X.B X.χA X.χB X.om
  vac_theta : IsThetaFunO X.ψ X.A X.B X.vac
  vac_fock : ∀ τ, IsFockVacAt (heisO X.ψ X.A X.B) X.θ τ (cplxO 1 1) X.vac
  c₁_ne : X.c₁ ≠ 0
  ker : ∀ x h T, thetaKO X.om (X.ιA x) (X.ιB h) (X.fock T) = X.c₁ * P.term x h T

  fixA : ∀ k ∈ intG D P.a, ∀ T, X.om (X.ιA k, 1) (X.fock T) = X.fock T

  eigB : ∀ j ∈ P.J, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ T, X.om (1, X.ιB j) (X.fock T) = c • X.fock T

  infB : ∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))

def IsDict (P : Pair D cc δ t0 Q) (X : Data P) : Prop := IsFrame P X.toFrame ∧ IsWeilOf P X

end GlobalTheory.NormDict
end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RallisBottom

open GlobalTheory.Core.Rk.IP

variable {D : D7}

def HeckeFormAniso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → wittIndex B = 0 →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ),
    IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : LFun.Fam D.host.E,
    LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ →
    (∃ s₁ : ℝ, s₁ < (t : ℝ) / 2 ∧ IntegrableOn (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s₁) (openOff A LA Sf) m) →
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m ∧
    ∀ l, HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) ((t : ℂ) / 2) l →
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) =
        volQ B mH * (l / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank ((t : ℂ) / 2)) *
          ∫ g in openOff A LA Sf, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m

end GlobalTheory.RallisBottom

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.exists_traceZero_adele_unit_lattice_at_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ β b up um : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) β ∧ cA σ β = -β ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      β • z ∈ GlobalTheory.InertSph.latAt W v ∧ b • z ∈ GlobalTheory.InertSph.latAt W v ∧ up • z ∈ GlobalTheory.InertSph.latAt W v ∧
      um • z ∈ GlobalTheory.InertSph.latAt W v ∧ (β * b) • z = z ∧ ((1 + β) * up) • z = z ∧ ((1 - β) * um) • z = z := by
  first | exact @GlobalTheory.InertSph.exists_traceZero_unit | exact GlobalTheory.InertSph.exists_traceZero_unit | (intros; apply GlobalTheory.InertSph.exists_traceZero_unit <;> assumption)
end
