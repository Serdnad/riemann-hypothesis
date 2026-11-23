module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Mathlib.Topology.Separation.CompletelyRegular
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle147
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.FormalDegreeBessel.FinalG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsLinearIndependentNormLeSuccMin
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagBase.PoissonV

variable (ι κ : Type) [Fintype ι] [Fintype κ]


open MeasureTheory NumberField Matrix Finset in
variable (ι κ : Type) [Fintype ι] [Fintype κ] in
theorem _root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_curry :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by
  have h : MeasurePreserving (MeasurableEquiv.curry ι κ ℂ).symm volume volume := by
    refine ⟨(MeasurableEquiv.curry ι κ ℂ).symm.measurable, ?_⟩
    have hv : (volume : Measure (ι × κ → ℂ)) = Measure.pi fun _ => volume := rfl
    rw [hv]
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have hpre : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => Set.univ.pi fun k => s (i, k) := by
      ext x
      simp [MeasurableEquiv.curry, Set.mem_pi, Prod.forall]
    rw [hpre, volume_pi_pi]
    simp_rw [volume_pi_pi]
    rw [Fintype.prod_prod_type]
  simpa using h.symm

def coords : EuclideanSpace ℂ (ι × κ) ≃L[ℝ] (ι → κ → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x w a => x (w, a)
      invFun := fun y => WithLp.toLp 2 fun p => y p.1 p.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

open MeasureTheory NumberField Matrix Finset in
variable (ι κ : Type) [Fintype ι] [Fintype κ] in
theorem _root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_coords :
    MeasurePreserving (_root_.GlobalTheory.FlagBase.PoissonV.coords ι κ) volume volume :=
  (_root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_curry ι κ).comp (_root_.GlobalTheory.volume_preserving_ofLp_complex _)

open MeasureTheory NumberField Matrix Finset in
variable (ι κ : Type) [Fintype ι] [Fintype κ] in
theorem _root_.GlobalTheory.FlagBase.PoissonV.norm_sq_coords (x : EuclideanSpace ℂ (ι × κ)) :
    ∑ w, ∑ a, ‖_root_.GlobalTheory.FlagBase.PoissonV.coords ι κ x w a‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

end GlobalTheory.FlagBase.PoissonV

namespace GlobalTheory.FlagBase

open PoissonV

open MeasureTheory NumberField Matrix Finset in
variable (ι κ : Type) [Fintype ι] [Fintype κ] in
private theorem inner_toLp_conj_eq_sum_re_dotProduct (u : EuclideanSpace ℂ (ι × κ))
    (y : ι → κ → ℂ) :
    inner ℝ u (WithLp.toLp 2 fun p => starRingEnd ℂ (y p.1 p.2) : EuclideanSpace ℂ (ι × κ)) =
      ∑ w, (_root_.GlobalTheory.FlagBase.PoissonV.coords ι κ u w ⬝ᵥ y w).re := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp [_root_.GlobalTheory.FlagBase.PoissonV.coords, dotProduct, Complex.re_sum, Complex.mul_re]
  congr 1 <;> exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => mul_comm _ _


open MeasureTheory NumberField Matrix Finset in
theorem _root_.GlobalTheory.FlagBase.poisson_gaussV (E : Type) [Field E] [NumberField E] (j : ℕ)
    (L : Submodule ℤ (_root_.GlobalTheory.FlagBase.VecInf E j))
    [DiscreteTopology L] (hL : IsZLattice ℝ L) :
    Summable (fun x : L => _root_.GlobalTheory.FlagBase.gaussV E j x) ∧
      Summable (fun y : _root_.GlobalTheory.FlagBase.dualAt E j L => _root_.GlobalTheory.FlagBase.gaussV E j y) ∧
      ∑' x : L, _root_.GlobalTheory.FlagBase.gaussV E j x =
        (_root_.GlobalTheory.FlagBase.covAt E j L)⁻¹ *
          ∑' y : _root_.GlobalTheory.FlagBase.dualAt E j L, _root_.GlobalTheory.FlagBase.gaussV E j y ∧
      ∫ x, _root_.GlobalTheory.FlagBase.gaussV E j x = 1 := by
  classical
  haveI := hL
  let e := _root_.GlobalTheory.FlagBase.PoissonV.coords (InfinitePlace E) (Fin j)
  let L' := ZLattice.comap ℝ L
    (e : EuclideanSpace ℂ (InfinitePlace E × Fin j) →ₗ[ℝ] _root_.GlobalTheory.FlagBase.VecInf E j)
  have hmemL : ∀ u, u ∈ L' ↔ e u ∈ L := fun u => Iff.rfl
  have hg : ∀ u, _root_.GlobalTheory.FlagBase.gaussV E j (e u) = Real.exp (-Real.pi * ‖u‖ ^ 2) := by
    intro u
    show Real.exp (-Real.pi * ∑ w, ∑ a, ‖e u w a‖ ^ 2) = _
    rw [_root_.GlobalTheory.FlagBase.PoissonV.norm_sq_coords]
  have hg' : ∀ x, _root_.GlobalTheory.FlagBase.gaussV E j x = Real.exp (-Real.pi * ‖e.symm x‖ ^ 2) := by
    intro x
    rw [← hg, ContinuousLinearEquiv.apply_symm_apply]
  let eL : L ≃ L' :=
    { toFun := fun y => ⟨e.symm y, by rw [hmemL, ContinuousLinearEquiv.apply_symm_apply]; exact y.2⟩
      invFun := fun x => ⟨e x, (hmemL x).1 x.2⟩
      left_inv := fun y => by ext; simp
      right_inv := fun x => by ext; simp }
  let ψ : _root_.GlobalTheory.FlagBase.VecInf E j ≃ EuclideanSpace ℂ (InfinitePlace E × Fin j) :=
    { toFun := fun y => WithLp.toLp 2 fun p => starRingEnd ℂ (y p.1 p.2)
      invFun := fun z w a => starRingEnd ℂ (z (w, a))
      left_inv := fun y => by funext w a; simp
      right_inv := fun z => by ext p; simp }
  have hψ : ∀ y, _root_.GlobalTheory.FlagBase.gaussV E j y = Real.exp (-Real.pi * ‖ψ y‖ ^ 2) := by
    intro y
    show Real.exp (-Real.pi * ∑ w, ∑ a, ‖y w a‖ ^ 2) = _
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp [ψ]
  have hinner : ∀ u y, inner ℝ u (ψ y) = ∑ w, (e u w ⬝ᵥ y w).re :=
    fun u y => inner_toLp_conj_eq_sum_re_dotProduct _ _ u y
  have hdual : ∀ y, y ∈ _root_.GlobalTheory.FlagBase.dualAt E j L ↔
      ∀ x ∈ L, ∃ z : ℤ, ∑ w, (x w ⬝ᵥ y w).re = z := by
    intro y
    unfold _root_.GlobalTheory.FlagBase.dualAt
    constructor
    · intro hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact hy
      | zero => intro x _; exact ⟨0, by simp⟩
      | add y y' _ _ h h' =>
        intro x hx
        obtain ⟨z, hz⟩ := h x hx
        obtain ⟨z', hz'⟩ := h' x hx
        refine ⟨z + z', ?_⟩
        simp only [Pi.add_apply, dotProduct_add, Complex.add_re, Finset.sum_add_distrib, hz, hz']
        push_cast
        ring
      | smul n y _ h =>
        intro x hx
        obtain ⟨z, hz⟩ := h x hx
        refine ⟨n * z, ?_⟩
        simp only [Pi.smul_apply, dotProduct_smul, Complex.smul_re]
        rw [← Finset.smul_sum, hz, zsmul_eq_mul]
        push_cast
        ring
    · intro hy
      exact Submodule.subset_span hy
  have hmem : ∀ y, y ∈ _root_.GlobalTheory.FlagBase.dualAt E j L ↔ ψ y ∈ _root_.GlobalTheory.dualLattice L' := by
    intro y
    rw [hdual, _root_.GlobalTheory.mem_dualLattice]
    constructor
    · intro h u hu
      obtain ⟨z, hz⟩ := h (e u) ((hmemL u).1 hu)
      exact ⟨z, by rw [hinner, hz]⟩
    · intro h x hx
      obtain ⟨m, hm⟩ := h (e.symm x) (by rw [hmemL, ContinuousLinearEquiv.apply_symm_apply]; exact hx)
      refine ⟨m, ?_⟩
      rw [hm, hinner, ContinuousLinearEquiv.apply_symm_apply]
  let dL : _root_.GlobalTheory.FlagBase.dualAt E j L ≃ _root_.GlobalTheory.dualLattice L' := ψ.subtypeEquiv hmem
  let f : EuclideanSpace ℂ (InfinitePlace E × Fin j) → ℝ := fun u => Real.exp (-Real.pi * ‖u‖ ^ 2)
  have hsL : Summable (fun x : L => _root_.GlobalTheory.FlagBase.gaussV E j x) :=
    ((eL.summable_iff (f := fun x : L' => f x)).2
      (_root_.GlobalTheory.summable_lattice_exp_neg_mul_norm_sq L' Real.pi_pos)).congr fun x => by rw [hg']; rfl
  have hsD : Summable (fun y : _root_.GlobalTheory.FlagBase.dualAt E j L => _root_.GlobalTheory.FlagBase.gaussV E j y) :=
    ((dL.summable_iff (f := fun z : _root_.GlobalTheory.dualLattice L' => f z)).2
      (_root_.GlobalTheory.summable_lattice_exp_neg_mul_norm_sq _ Real.pi_pos)).congr fun y => by rw [hψ]; rfl
  have hT1 : ∑' x : L, _root_.GlobalTheory.FlagBase.gaussV E j x = ∑' x : L', f x :=
    calc ∑' x : L, _root_.GlobalTheory.FlagBase.gaussV E j x = ∑' x : L, f (eL x) :=
          tsum_congr fun x => by rw [hg']; rfl
      _ = ∑' x : L', f x := eL.tsum_eq (fun x : L' => f x)
  have hT2 : ∑' y : _root_.GlobalTheory.FlagBase.dualAt E j L, _root_.GlobalTheory.FlagBase.gaussV E j y =
      ∑' z : _root_.GlobalTheory.dualLattice L', f z :=
    calc ∑' y : _root_.GlobalTheory.FlagBase.dualAt E j L, _root_.GlobalTheory.FlagBase.gaussV E j y =
          ∑' y : _root_.GlobalTheory.FlagBase.dualAt E j L, f (dL y) :=
          tsum_congr fun y => by rw [hψ]; rfl
      _ = ∑' z : _root_.GlobalTheory.dualLattice L', f z := dL.tsum_eq (fun z : _root_.GlobalTheory.dualLattice L' => f z)
  haveI : (volume : Measure (_root_.GlobalTheory.FlagBase.VecInf E j)).IsAddHaarMeasure := by
    rw [← (_root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_coords (InfinitePlace E) (Fin j)).map_eq]
    exact e.isAddHaarMeasure_map volume
  have hcov : _root_.GlobalTheory.FlagBase.covAt E j L = ZLattice.covolume L' volume := by
    show ZLattice.covolume L volume = _
    exact (ZLattice.covolume_comap L volume volume
      (_root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_coords _ _)).symm
  have hP := _root_.GlobalTheory.tsum_gaussian_lattice_eq_dualLattice L' one_pos
  simp only [mul_one, Real.one_rpow, div_one] at hP
  refine ⟨hsL, hsD, ?_, ?_⟩
  · rw [hT1, hT2, hcov]
    exact hP
  · have hI : ∫ x, _root_.GlobalTheory.FlagBase.gaussV E j x = ∫ u, f u :=
      ((_root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_coords (InfinitePlace E) (Fin j)).integral_comp
        e.toHomeomorph.measurableEmbedding (_root_.GlobalTheory.FlagBase.gaussV E j)).symm.trans
        (integral_congr_ae (Filter.Eventually.of_forall fun u => hg u))
    rw [hI]
    show ∫ u, Real.exp (-Real.pi * ‖u‖ ^ 2) = 1
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm Real.pi_pos, div_self Real.pi_ne_zero,
      Real.one_rpow]

end GlobalTheory.FlagBase
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff Pointwise

namespace GlobalTheory.RadVol

private theorem measure_slice_le_measure_mul_inv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] {N : Set G} {ν : Measure G} (hnull : ν Nᶜ = 0)
    (hleft : ∀ m ∈ N, Measure.map (fun x => m * x) ν = ν) {K S : Set G} (hK : IsCompact K) (g : G) :
    ν {s | s ∈ S ∧ s⁻¹ * g ∈ K} ≤ ν (K * K⁻¹) := by
  by_cases h0 : ∃ s₀ ∈ N, s₀⁻¹ * g ∈ K
  · obtain ⟨s₀, hs₀, hk₀⟩ := h0
    have hKK : MeasurableSet (K * K⁻¹) := (hK.mul hK.inv).isClosed.measurableSet
    have hpre : MeasurableSet ((fun x => s₀⁻¹ * x) ⁻¹' (K * K⁻¹)) := hKK.preimage (measurable_const_mul _)
    calc ν {s | s ∈ S ∧ s⁻¹ * g ∈ K} ≤ ν ((fun x => s₀⁻¹ * x) ⁻¹' (K * K⁻¹)) := by
          apply measure_mono
          intro s hs
          simp only [Set.mem_preimage]
          rw [show s₀⁻¹ * s = (s₀⁻¹ * g) * (s⁻¹ * g)⁻¹ by group]
          exact Set.mul_mem_mul hk₀ (Set.inv_mem_inv.mpr hs.2)
      _ = Measure.map (fun x => s₀ * x) ν ((fun x => s₀⁻¹ * x) ⁻¹' (K * K⁻¹)) := by
          rw [hleft s₀ hs₀]
      _ = ν ((fun x => s₀ * x) ⁻¹' ((fun x => s₀⁻¹ * x) ⁻¹' (K * K⁻¹))) :=
          Measure.map_apply (measurable_const_mul _) hpre
      _ = ν (K * K⁻¹) := by
          congr 1
          ext x
          simp
  · push_neg at h0
    have hsub : {s | s ∈ S ∧ s⁻¹ * g ∈ K} ⊆ Nᶜ := fun s hs hsN => h0 s hsN hs.2
    calc ν {s | s ∈ S ∧ s⁻¹ * g ∈ K} ≤ ν Nᶜ := measure_mono hsub
      _ = 0 := hnull
      _ ≤ ν (K * K⁻¹) := bot_le

theorem measure_mul_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    {N : Set G} {ν : Measure G} (hν : IsHaarSub N ν) {K S T : Set G} (hK : IsCompact K) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (h : ∀ s ∈ S, ∀ k ∈ K, s * k ∈ T) : ν S * μ K ≤ ν (K * K⁻¹) * μ T := by
  classical
  obtain ⟨-, hfc, hnull, hleft⟩ := hν
  haveI : IsFiniteMeasureOnCompacts ν := hfc
  haveI : SigmaFinite ν := inferInstance
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set E : Set (G × G) := {p | p.1 ∈ S ∧ p.1⁻¹ * p.2 ∈ K} with hEd
  have hE : MeasurableSet E :=
    (measurable_fst hS).inter ((measurable_fst.inv.mul measurable_snd) hKm)

  have h1 : ν.prod μ E = ν S * μ K := by
    rw [Measure.prod_apply hE]
    have hsl : ∀ s, μ (Prod.mk s ⁻¹' E) = S.indicator (fun _ => μ K) s := by
      intro s
      by_cases hs : s ∈ S
      · rw [Set.indicator_apply, if_pos hs, ← measure_preimage_mul μ s⁻¹ K]
        congr 1
        ext x
        simp [hEd, hs]
      · rw [Set.indicator_apply, if_neg hs]
        have h0 : Prod.mk s ⁻¹' E = ∅ := by
          ext x
          simp [hEd, hs]
        rw [h0, measure_empty]
    simp_rw [hsl]
    rw [lintegral_indicator_const hS, mul_comm]

  have h2 : ν.prod μ E ≤ ν (K * K⁻¹) * μ T := by
    rw [Measure.prod_apply_symm hE]
    calc ∫⁻ g, ν ((fun s => (s, g)) ⁻¹' E) ∂μ
        ≤ ∫⁻ g, T.indicator (fun _ => ν (K * K⁻¹)) g ∂μ := by
          apply lintegral_mono
          intro g
          by_cases hg : g ∈ T
          · rw [Set.indicator_apply, if_pos hg]
            exact (le_of_eq (by rw [hEd]; rfl)).trans
              (measure_slice_le_measure_mul_inv (S := S) hnull hleft hK g)
          · rw [Set.indicator_apply, if_neg hg]
            have h0 : (fun s => (s, g)) ⁻¹' E = ∅ := by
              ext s
              simp only [hEd, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
                not_and]
              intro hs hk
              apply hg
              simpa using h s hs _ hk
            exact le_of_eq (by show ν ((fun s => (s, g)) ⁻¹' E) = 0; rw [h0, measure_empty])
      _ = ν (K * K⁻¹) * μ T := lintegral_indicator_const hT _
  calc ν S * μ K = ν.prod μ E := h1.symm
    _ ≤ ν (K * K⁻¹) * μ T := h2

private theorem dOp_nonneg_subadditive_continuous {n : ℕ} (ε : Fin n → Bool) :
    (∀ g : UJ ε, 0 ≤ dOp (umat g)) ∧
      (∀ g g' : UJ ε, dOp (umat (g * g')) ≤ dOp (umat g) + dOp (umat g')) ∧
      Continuous (fun g : UJ ε => dOp (umat g)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : ∀ g : Matrix (Fin 0) (Fin 0) ℂ, dOp g = 0 := by
      intro g
      have hz : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)‖ = 0 := by
        refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ le_rfl fun x => ?_) (norm_nonneg _)
        rw [zero_mul, EuclideanSpace.norm_eq]
        simp
      simp only [dOp, hz, Real.log_zero]
    simp only [h0]
    exact ⟨fun _ => le_rfl, fun _ _ => by norm_num, continuous_const⟩
  · obtain ⟨-, h2, -, -, h5⟩ := GlobalTheory.Count.Cartan.cartan_distances n ε
    exact ⟨fun g => (h2 g 1 hn).1, fun g g' => (h2 g g' hn).2.2.1, h5⟩

theorem radical_volume_growth : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)),
    IsIsoC ε W → IsHaarSub (NW ε W) ν →
    (∃ C : ℝ, ∀ r : ℝ, 0 ≤ r →
      ν {m | dOp (umat m) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r))) ∧
    ∀ b : ℝ, 4 * n * rkR ε < b → Integrable (fun m : UJ ε => Real.exp (-(b * dOp (umat m)))) ν := by
  intro n ε W ν _ hν
  obtain ⟨hP, hM, hD⟩ := dOp_nonneg_subadditive_continuous ε
  haveI : (muG ε).IsHaarMeasure := by
    first
    | infer_instance
    | (unfold muG; infer_instance)
  have hgrowth : ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r →
      ν {m | dOp (umat m) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r)) := by
    obtain ⟨C, -, hball⟩ := GlobalTheory.BallVol.ballVol n ε
    obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : UJ ε)
    have hμK : 0 < muG ε K := by
      first
      | exact measure_pos_of_mem_nhds (μ := muG ε) hK1
      | exact (muG ε).measure_pos_of_mem_nhds hK1
      | exact Measure.measure_pos_of_mem_nhds (muG ε) hK1
    have hμKt : muG ε K < ⊤ := by
      first
      | exact hKc.measure_lt_top (μ := muG ε)
      | exact IsCompact.measure_lt_top hKc
    have hνKK : ν (K * K⁻¹) < ⊤ := by
      haveI : IsFiniteMeasureOnCompacts ν := hν.2.1
      exact (hKc.mul hKc.inv).measure_lt_top
    obtain ⟨B, hB⟩ := hKc.bddAbove_image hD.continuousOn
    refine ⟨(ν (K * K⁻¹)).toReal * C * Real.exp (4 * n * rkR ε * max B 0) / (muG ε K).toReal,
      fun r hr => ?_⟩

    have hmul : ∀ s ∈ {m : UJ ε | dOp (umat m) ≤ r}, ∀ k ∈ K,
        s * k ∈ {m : UJ ε | dOp (umat m) ≤ r + max B 0} := by
      intro s hs k hk
      have hkB : dOp (umat k) ≤ B := hB (Set.mem_image_of_mem _ hk)
      have hs' : dOp (umat s) ≤ r := hs
      show dOp (umat (s * k)) ≤ r + max B 0
      linarith [hM s k, le_max_left B 0]
    have key := measure_mul_le (muG ε) hν (S := {m : UJ ε | dOp (umat m) ≤ r})
      (T := {m : UJ ε | dOp (umat m) ≤ r + max B 0}) hKc (measurableSet_le hD.measurable measurable_const)
      (measurableSet_le hD.measurable measurable_const) hmul
    have hT : muG ε {m : UJ ε | dOp (umat m) ≤ r + max B 0} ≤
        ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * (r + max B 0))) :=
      hball _ (add_nonneg hr (le_max_right B 0))
    have hm : 0 < (muG ε K).toReal := ENNReal.toReal_pos hμK.ne' hμKt.ne
    have key2 : ν {m : UJ ε | dOp (umat m) ≤ r} * ENNReal.ofReal (muG ε K).toReal ≤
        ENNReal.ofReal ((ν (K * K⁻¹)).toReal * (C * Real.exp (4 * n * rkR ε * (r + max B 0)))) := by
      rw [ENNReal.ofReal_toReal hμKt.ne, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hνKK.ne]
      exact key.trans (by gcongr)
    have key3 := (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hm).ne')
      (Or.inl ENNReal.ofReal_ne_top)).mpr key2
    rw [← ENNReal.ofReal_div_of_pos hm] at key3
    refine key3.trans (le_of_eq (congrArg ENNReal.ofReal ?_))
    rw [mul_add, Real.exp_add]
    ring
  refine ⟨hgrowth, fun b hb => ?_⟩
  obtain ⟨C, hC⟩ := hgrowth
  exact GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth (UJ ε) ν (fun m => dOp (umat m)) (4 * n * rkR ε) b C
    hD.measurable hP hC hb

end GlobalTheory.RadVol
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.AeqCont

theorem null_preimage_lmulM {k r : ℕ} {μG : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μG)
    {s : Mat k r} (hs : s ∈ GG k r) {N : Set (Mt k r)} (hN : μG N = 0) :
    μG (lmulM s ⁻¹' N) = 0 := by
  have hm : Measurable (lmulM s : Mt k r → Mt k r) :=
    Continuous.measurable (α := Mt k r) (γ := Mt k r)
      (continuous_const.matrix_mul (continuous_id (X := Mat k r)))
  refine le_antisymm ?_ bot_le
  calc μG (lmulM s ⁻¹' N) ≤ μG (lmulM s ⁻¹' toMeasurable μG N) :=
        measure_mono (Set.preimage_mono (subset_toMeasurable μG N))
    _ = (μG.map (lmulM s)) (toMeasurable μG N) :=
        (Measure.map_apply hm (measurableSet_toMeasurable μG N)).symm
    _ = μG (toMeasurable μG N) := by rw [hμ.2.2.2 s hs]
    _ = 0 := by rw [measure_toMeasurable, hN]

theorem eqOn_of_ae (k r : ℕ) {B : Type} [NormedAddCommGroup B] (μG : Measure (Mt k r))
    (f g : Mat k r → B) (hμ : IsHaarOn (GG k r) μG) (hf : ContinuousOn f (GG k r))
    (hg : ContinuousOn g (GG k r))
    (hfg : (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] (fun x => g (Matrix.of x))) :
    ∀ x ∈ GG k r, f x = g x := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hgrp := uHGroup _ _ hH
  intro x0 hx0
  by_contra hne
  obtain ⟨U, hUo, hU⟩ := (continuousOn_iff'.1 (hf.sub hg)) ({0}ᶜ : Set B) isOpen_compl_singleton
  have hmemU : ∀ y ∈ GG k r, y ∈ U → f y ≠ g y := by
    intro y hy hyU h
    have : y ∈ (f - g) ⁻¹' ({0}ᶜ : Set B) ∩ GG k r := by rw [hU]; exact ⟨hyU, hy⟩
    exact this.1 (by simp [h])
  have hx0U : x0 ∈ U := by
    have : x0 ∈ (f - g) ⁻¹' ({0}ᶜ : Set B) ∩ GG k r :=
      ⟨by simpa [sub_eq_zero] using hne, hx0⟩
    rw [hU] at this; exact this.1
  set N : Set (Mt k r) := {x | (Matrix.of x : Mat k r) ∈ U ∧ (Matrix.of x : Mat k r) ∈ GG k r} with hNdef
  have hN : μG N = 0 := by
    have h0 : μG {x | ¬ f (Matrix.of x) = g (Matrix.of x)} = 0 := ae_iff.1 hfg
    exact measure_mono_null (fun x hx => hmemU _ hx.2 hx.1) h0
  let O : GG k r → Set (Mt k r) := fun s => {x | (s.1 * Matrix.of x : Mat k r) ∈ U}
  have hO : ∀ s, IsOpen (O s) := fun s =>
    hUo.preimage (continuous_const.matrix_mul (continuous_id (X := Mat k r)))
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable O hO
  have hcov : {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} ⊆ ⋃ s ∈ T, lmulM s.1 ⁻¹' N := by
    intro x hx
    have hdet : IsUnit (Matrix.of x : Mat k r).det := (hgrp.2.2 _ hx).1
    have hxinv : (Matrix.of x : Mat k r)⁻¹ ∈ GG k r := (hgrp.2.2 _ hx).2
    let s : GG k r := ⟨x0 * (Matrix.of x : Mat k r)⁻¹, hgrp.2.1 _ hx0 _ hxinv⟩
    have hxO : x ∈ ⋃ i, O i := Set.mem_iUnion.2 ⟨s, by
      show x0 * (Matrix.of x : Mat k r)⁻¹ * Matrix.of x ∈ U
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]; exact hx0U⟩
    rw [← hT] at hxO
    obtain ⟨t, htT, hxt⟩ := Set.mem_iUnion₂.1 hxO
    exact Set.mem_iUnion₂.2 ⟨t, htT, hxt, hgrp.2.1 _ t.2 _ hx⟩
  have hG0 : μG {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} = 0 :=
    measure_mono_null hcov ((measure_biUnion_null_iff hTc).2 fun s _ => null_preimage_lmulM hμ s.2 hN)
  have huniv : μG Set.univ = 0 := by
    have : (Set.univ : Set (Mt k r)) =
        {x | (Matrix.of x : Mat k r) ∈ GG k r} ∪ {x | (Matrix.of x : Mat k r) ∉ GG k r} := by
      ext x; by_cases h : (Matrix.of x : Mat k r) ∈ GG k r <;> simp [h]
    rw [this]; exact measure_union_null hG0 hμ.2.2.1
  exact hμ.2.1 (Measure.measure_univ_eq_zero.1 huniv)

end GlobalTheory.SgInf.AeqCont
end
end
