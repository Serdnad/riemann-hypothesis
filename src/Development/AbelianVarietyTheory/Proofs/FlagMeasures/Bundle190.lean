module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle170
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle171
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIsotropicFlagSelfAdjointLeviIffBlock
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeSublevelAsymptoticsProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle127
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieEntriesUnipotentBesselNCharacterization
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
public import Formalism.PeriodIntegrals.UpqRep
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle173
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle162
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Complex
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN

theorem hasDom_ideLat_dInv_div : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * (dInv E t')⁻¹) c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  intro F E _ _ _ _ _ σ hσ hu t t' c hc
  have hE : IsTotallyComplex E := hσ.2.1
  have hdE : (discr E : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero E
  have hdF : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
  have hd : |(discr E : ℝ)| = |(discr F : ℝ)| ^ 2 := by
    have h1 := congrArg (Nat.cast : ℕ → ℤ) (FrameDual.natAbs_discr_sq (F := F) (E := E) hσ.2.2.1)
    rw [Nat.cast_pow, Int.natCast_natAbs, Int.natCast_natAbs] at h1
    rw [sq_abs]
    have h2 : ((|discr E| : ℤ) : ℝ) = ((|discr F| ^ 2 : ℤ) : ℝ) := by rw [h1]
    push_cast at h2
    rw [h2, sq_abs]
  set I := dInv E t * (dInv E t')⁻¹ with hIdef
  have hNI : ((FractionalIdeal.absNorm I : ℚ) : ℝ) = (|(discr E : ℝ)|⁻¹ ^ t) * (|(discr E : ℝ)|⁻¹ ^ t')⁻¹ := by
    rw [hIdef, map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, FrameDual.absNorm_dInv, FrameDual.absNorm_dInv]
  have hI : I ≠ 0 := by
    intro h0
    have h1 : ((FractionalIdeal.absNorm I : ℚ) : ℝ) = 0 := by rw [h0, map_zero, Rat.cast_zero]
    rw [hNI] at h1
    have : |(discr E : ℝ)| ≠ 0 := abs_ne_zero.2 hdE
    simp_all
  obtain ⟨L₀, hL₀, hcov⟩ := HomCovolume.exists_idealLat E hE I hI
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  let f : (InfinitePlace E → ℂ) →ₗ[ℝ] (InfinitePlace E → ℂ) :=
    LinearMap.pi fun w => (Algebra.lmul ℝ ℂ ((c : ℂ))⁻¹).comp (LinearMap.proj w)
  have hf : ∀ z w, f z w = ((c : ℂ))⁻¹ * z w := fun _ _ => rfl
  have hdet : LinearMap.det f = (∏ _w : InfinitePlace E, ‖(c : ℂ)‖ ^ 2)⁻¹ := by
    rw [LinearMap.det_pi, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, norm_inv, inv_pow]
  have hpos : 0 < ∏ _w : InfinitePlace E, ‖(c : ℂ)‖ ^ 2 :=
    Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 hc0) _
  let L : Submodule ℤ (InfinitePlace E → ℂ) := L₀.comap (f.restrictScalars ℤ)
  obtain ⟨_, _, h⟩ := HomCovolume.HasCov.of_det f (L := L) (by rw [hdet]; exact (inv_pos.2 hpos).ne')
    (fun _ => Iff.rfl) hcov
  have hL : ∀ z, z ∈ L ↔ z ∈ (ideLat I c : Set (InfinitePlace E → ℂ)) := by
    intro z
    change f z ∈ L₀ ↔ ∃ y ∈ I, ∀ w, z w = (c : ℂ) * w.embedding y
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h w => ?_, fun h w => ?_⟩
    · rw [← h w, hf, mul_inv_cancel_left₀ hc0]
    · rw [hf, h w, inv_mul_cancel_left₀ hc0]
  refine ⟨latticeDomain L, measurableSet_latticeDomain L, fun a => ?_, ?_⟩
  · obtain ⟨z, hz, hu'⟩ := existsUnique_add_mem_latticeDomain L a
    refine ⟨z, ⟨(hL z).1 z.2, hz⟩, ?_⟩
    rintro l ⟨hl, hl'⟩
    exact congrArg Subtype.val (hu' ⟨l, (hL l).2 hl⟩ hl')
  · rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (isAddFundamentalDomain_latticeDomain _ _), measureReal_def, hdet, abs_of_pos (inv_pos.2 hpos),
      div_inv_eq_mul] at h
    have hfin : volume (latticeDomain L) ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, h]
    congr 1
    have hn : InfinitePlace.nrComplexPlaces E = Fintype.card (InfinitePlace E) := by
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    have hDpos : 0 < |(discr F : ℝ)| := abs_pos.2 hdF
    have hr : |(discr F : ℝ)| ^ (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) =
        |(discr F : ℝ)| ^ (1 + 2 * t') / |(discr F : ℝ)| ^ (2 * t) := by
      rw [show (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) = ((1 + 2 * t' : ℕ) : ℝ) - ((2 * t : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_sub hDpos, Real.rpow_natCast, Real.rpow_natCast]
    rw [hNI, HomCovolume.vInv_pow E hE, hn, hd, Real.sqrt_sq hDpos.le, hr, Finset.prod_const, Finset.card_univ,
      Complex.norm_real, Real.norm_of_nonneg hc.le]
    generalize |(discr F : ℝ)| = D at hDpos
    generalize Fintype.card (InfinitePlace E) = n
    rw [inv_pow, inv_pow, inv_inv, ← pow_mul, ← pow_mul, ← pow_mul, pow_add, pow_one, div_eq_mul_inv]
    ring

end GlobalTheory.SnMass.VolN
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.columnBlocksSpanFlag_of_block_triangular : ∀ (n a : ℕ) (j : Fin a → ℕ) (A B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (p q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ k i, i < k → p k i = 0 ∧ q k i = 0) → (∀ i, A i = ∑ k, B k * p k i) → (∀ i, B i = ∑ k, A k * q k i) → SpansFlag A W → SpansFlag B W := by
  first | exact @GlobalTheory.LeviIso.spansFlag_of_triangular | exact GlobalTheory.LeviIso.spansFlag_of_triangular | (intros; apply GlobalTheory.LeviIso.spansFlag_of_triangular <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.exists_measurable_unitaryLeviBlockMap : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∃ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ ∧ ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) := by
  first | exact @GlobalTheory.LeviIso.exists_measurable_levMap | exact GlobalTheory.LeviIso.exists_measurable_levMap | (intros; apply GlobalTheory.LeviIso.exists_measurable_levMap <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.haarComplexGLMatrices_conj_and_singular_null : ∀ j : ℕ, MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => starRingEnd ℂ (x r s)) (haarLoc j) (haarLoc j) ∧ haarLoc j {x | (Matrix.of x).det = 0} = 0 := by
  first | exact @GlobalTheory.LeviIso.haarLoc_conj_and_null | exact GlobalTheory.LeviIso.haarLoc_conj_and_null | (intros; apply GlobalTheory.LeviIso.haarLoc_conj_and_null <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem isClosed_flagM {n a : ℕ} (ε : Fin n → Bool) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) :
    IsClosed (flagM ε W) := by
  have hc : Continuous fun g : Formalism.REAL.UJ ε => uMat g := Units.continuous_val.comp continuous_subtype_val
  have hc' : Continuous fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ := hc.matrix_conjTranspose
  have hset : flagM ε W = ⋂ i, ⋂ y ∈ W i,
      ((fun g : Formalism.REAL.UJ ε => uMat g *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)) ∩
        (fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ))) := by
    ext g
    simp [flagM]
  rw [hset]
  refine isClosed_iInter fun i => isClosed_biInter fun y _ => ?_
  have hW : IsClosed (W i : Set (Fin n → ℂ)) := (W i).closed_of_finiteDimensional
  exact (hW.preimage (hc.matrix_mulVec continuous_const)).inter (hW.preimage (hc'.matrix_mulVec continuous_const))

theorem ae_det_ne_zero {a : ℕ} (j : Fin a → ℕ) (d : Fin a → ℝ) {Y : Type} [MeasurableSpace Y] (ν : Measure Y)
    [SFinite ν] :
    ∀ᵐ z ∂((Measure.pi fun i => ENNReal.ofReal (d i) • haarLoc (j i)).prod ν), ∀ i, (Matrix.of (z.1 i)).det ≠ 0 := by
  have h1 : ∀ᵐ x ∂(Measure.pi fun i => ENNReal.ofReal (d i) • haarLoc (j i)), ∀ i, (Matrix.of (x i)).det ≠ 0 := by
    rw [ae_all_iff]
    intro i
    have h0 : ∀ᵐ y ∂(ENNReal.ofReal (d i) • haarLoc (j i)), (Matrix.of y).det ≠ 0 := by
      have hn := (haarLoc_conj_and_null (j i)).2
      rw [ae_iff, Measure.smul_apply]
      simp [hn]
    exact (Measure.tendsto_eval_ae_ae (μ := fun i => ENNReal.ofReal (d i) • haarLoc (j i)) (i := i)).eventually
      (p := fun y => (Matrix.of y).det ≠ 0) h0
  exact Measure.quasiMeasurePreserving_fst.ae h1

private theorem measurePreserving_smul_measure {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → X}
    (hf : MeasurePreserving f μ μ) (c : ENNReal) : MeasurePreserving f (c • μ) (c • μ) :=
  ⟨hf.measurable, by rw [Measure.map_smul c hf.measurable.aemeasurable, hf.map_eq]⟩

theorem map_chart_carried_and_invariant : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ), SpansFlag B W → ∀ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ → (∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) → ∀ c : ℝ, (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) (flagM ε W)ᶜ = 0 ∧ ∀ s ∈ flagM ε W, (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ).map (fun g => s * g) = (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) := by
  intro n n₀ a j ε ε₀ B B₀ hB W hW θ hθ hθl c
  set P := Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i) with hP
  set ν := ENNReal.ofReal c • Formalism.REAL.muG ε₀ with hν
  have hdet : ∀ᵐ z ∂(P.prod ν), ∀ i, (Matrix.of (z.1 i)).det ≠ 0 :=
    ae_det_ne_zero j (fun i => 2 ^ (j i ^ 2)) ν
  have hmem : ∀ z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀,
      (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → θ z ∈ flagM ε W := fun z hz =>
    (Range.mem_flagM_iff n n₀ a j ε ε₀ B B₀ hB W hW (θ z)).2 ⟨fun i => Matrix.of (z.1 i), z.2, hz, hθl z hz⟩
  have hM : MeasurableSet (flagM ε W) := (isClosed_flagM ε W).measurableSet
  refine ⟨?_, fun s hs => ?_⟩
  · have h : ∀ᵐ m ∂((P.prod ν).map θ), m ∈ flagM ε W :=
      (ae_map_iff hθ.aemeasurable hM).2 (hdet.mono hmem)
    exact measure_mono_null (fun m hm => hm) (ae_iff.1 h)
  · obtain ⟨x, g, hx, hs'⟩ := (Range.mem_flagM_iff n n₀ a j ε ε₀ B B₀ hB W hW s).1 hs
    let T : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ :=
      Prod.map (fun (y : ∀ i, Fin (j i) → Fin (j i) → ℂ) (i : Fin a) (r t : Fin (j i)) =>
        (x i * Matrix.of (y i) * (1 : Matrix (Fin (j i)) (Fin (j i)) ℂ)) r t) (fun u => g * u)
    have hT : MeasurePreserving T (P.prod ν) (P.prod ν) := by
      refine MeasurePreserving.prod ?_ ?_
      · exact measurePreserving_pi _ _ fun i =>
          measurePreserving_smul_measure (GlobalTheory.HaarMul.measurePreserving_mul_mul (j i) (x i) 1 (hx i) (by simp)) _
      · exact measurePreserving_smul_measure (measurePreserving_mul_left (Formalism.REAL.muG ε₀) g) _
    have hcomm : ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → s * θ z = θ (T z) := by
      intro z hz
      have hz' : ∀ i, (Matrix.of ((T z).1 i)).det ≠ 0 := by
        intro i
        have : Matrix.of ((T z).1 i) = x i * Matrix.of (z.1 i) := by
          ext r t
          simp [T]
        rw [this, Matrix.det_mul]
        exact mul_ne_zero (hx i) (hz i)
      apply Subtype.ext
      apply Units.ext
      change uMat s * uMat (θ z) = uMat (θ (T z))
      rw [hs', hθl z hz, hθl (T z) hz', ← hB.lev_mul]
      congr 1
      · funext i
        ext r t
        simp [T]
    have hmul : Measurable fun m : Formalism.REAL.UJ ε => s * m := measurable_const_mul s
    calc ((P.prod ν).map θ).map (fun m => s * m)
        = (P.prod ν).map (fun z => s * θ z) := by rw [Measure.map_map hmul hθ]; rfl
      _ = (P.prod ν).map (fun z => θ (T z)) := Measure.map_congr (hdet.mono fun z hz => hcomm z hz)
      _ = ((P.prod ν).map T).map θ := by rw [Measure.map_map hθ hT.measurable]; rfl
      _ = (P.prod ν).map θ := by rw [hT.map_eq]

end GlobalTheory.LeviIso
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.flagStabilizer_mul_inv_leviComponent_mem_unipotent : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (A₀ : Matrix (Fin n) (Fin n₀) ℂ) (p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (d : ∀ k, Matrix (Fin (j k)) (Fin n₀) ℂ) (s h : Formalism.REAL.UJ ε₀) (y : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g m : Formalism.REAL.UJ ε), SpansFlag A W → SpansFlag B W → (∀ k i, i < k → p k i = 0) → (∀ i, (p i i).det ≠ 0) → (∀ i, A i = ∑ k, B k * p k i) → A₀ = B₀ * uMat s + ∑ k, B k * d k → (∀ i, (y i).det ≠ 0) → (∀ i, uMat g * A i = A i * y i) → uMat g * A₀ = A₀ * uMat h → uMat m = lev ε B B₀ (fun i => p i i * y i * (p i i)⁻¹) (uMat (s * h * s⁻¹)) → g * m⁻¹ ∈ flagN ε W := by
  first | exact @GlobalTheory.LeviUnip.mul_inv_mem_flagN | exact GlobalTheory.LeviUnip.mul_inv_mem_flagN | (intros; apply GlobalTheory.LeviUnip.mul_inv_mem_flagN <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.infiniteGLHaarMeasure_eq_pi_local : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ), haarGL E j = (Measure.pi fun _ : InfinitePlace E => haarLoc j : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) := by
  first | exact @GlobalTheory.HaarPi.haarGL_eq_pi | exact GlobalTheory.HaarPi.haarGL_eq_pi | (intros; apply GlobalTheory.HaarPi.haarGL_eq_pi <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.hasEuclideanBallVolumeSublevelAsymptotics_prod : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (q : X → ℝ) (p : Y → ℝ) (d e : ℕ), Measurable q → Measurable p → (∀ x, 0 ≤ q x) → (∀ y, 0 ≤ p y) → IsRadial μ q d → IsRadial ν p e → IsRadial (μ.prod ν) (fun z => q z.1 + p z.2) (d + e) := by
  first | exact @GlobalTheory.LeviIso.isRadial_prod | exact GlobalTheory.LeviIso.isRadial_prod | (intros; apply GlobalTheory.LeviIso.isRadial_prod <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.mem_isotropicFlagSelfAdjointLevi_iff_block : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ), SpansFlag B W → ∀ m : Formalism.REAL.UJ ε, m ∈ flagM ε W ↔ ∃ (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g : Formalism.REAL.UJ ε₀), (∀ i, (x i).det ≠ 0) ∧ uMat m = lev ε B B₀ x (uMat g) := by
  first | exact @GlobalTheory.LeviIso.Range.mem_flagM_iff | exact GlobalTheory.LeviIso.Range.mem_flagM_iff | (intros; apply GlobalTheory.LeviIso.Range.mem_flagM_iff <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.lieEntries_unipotentBesselN_characterization : ∀ (k r : ℕ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)), (x ∈ lieE (Nset k r) ↔ ((unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0 ∧ ∀ i j : Fin (2 * r + k + 1), lev k r j ≤ lev k r i → unrealify x i j = 0)) ∧ (x ∈ lieE (Nset k r) → NormedSpace.exp (unrealify x) ∈ Nset k r) := by
  first | exact @GlobalTheory.CellDens.LieN.lieE_Nset | exact GlobalTheory.CellDens.LieN.lieE_Nset | (intros; apply GlobalTheory.CellDens.LieN.lieE_Nset <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology

theorem _root_.GlobalTheory.T.integral_translate_family_isKFinite_hermitian : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ → GlobalTheory.KFinAvg.IsHaarKH k r μ → ∀ (N : ℕ) (b : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ), (∀ j, Continuous (b j)) → (∀ (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g) → ∀ (c : Fin N → ℂ) (v : H), PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (∫ g, (∑ j, c j * b j g) • σ g v ∂μ) := by
  first | exact @GlobalTheory.KFinAvg.isKFinHpk_integral_translates | exact GlobalTheory.KFinAvg.isKFinHpk_integral_translates | (intros; apply GlobalTheory.KFinAvg.isKFinHpk_integral_translates <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual

noncomputable section

namespace GlobalTheory.MeanDual.Alg

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def halfTraceForm : LinearMap.BilinForm ℚ (Fin j → E) :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ E (x ⬝ᵥ y) / 2)
    (fun x x' y => by rw [add_dotProduct, map_add (f := _), add_div])
    (fun c x y => by rw [smul_dotProduct, map_smul, smul_eq_mul, smul_eq_mul, mul_div_assoc])
    (fun x y y' => by rw [dotProduct_add, map_add (f := _), add_div])
    (fun c x y => by rw [dotProduct_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_div_assoc])

theorem halfTraceForm_apply (x y : Fin j → E) :
    halfTraceForm E j x y = Algebra.trace ℚ E (x ⬝ᵥ y) / 2 := rfl

theorem halfTraceForm_symm : (halfTraceForm E j).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [halfTraceForm_apply, halfTraceForm_apply, dotProduct_comm]

theorem halfTraceForm_left (x : Fin j → E) (h : ∀ y, halfTraceForm E j x y = 0) : x = 0 := by
  ext i
  rw [Pi.zero_apply]
  by_contra hx

  have h1 := h (Pi.single i (x i)⁻¹)
  rw [halfTraceForm_apply, dotProduct_single, mul_inv_cancel₀ hx, ← map_one (algebraMap ℚ E),
    Algebra.trace_algebraMap, nsmul_eq_mul, mul_one] at h1
  have h2 : (0 : ℚ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  linarith

theorem halfTraceForm_nondegenerate : (halfTraceForm E j).Nondegenerate := by
  refine ⟨halfTraceForm_left E j, fun y hy => halfTraceForm_left E j y fun x => ?_⟩
  rw [(halfTraceForm_symm E j).eq]
  exact hy x

theorem restrict_trDual (Λ : Submodule (𝓞 E) (Fin j → E)) :
    (trDual E j Λ).restrictScalars ℤ =
      (halfTraceForm E j).dualSubmodule (Λ.restrictScalars ℤ) := by
  ext y
  simp only [Submodule.restrictScalars_mem, mem_trDual, LinearMap.BilinForm.mem_dualSubmodule,
    Submodule.mem_one, halfTraceForm_apply, eq_intCast]
  constructor
  · intro hy x hx
    obtain ⟨z, hz⟩ := hy x hx
    refine ⟨z, ?_⟩
    rw [dotProduct_comm, hz]
    ring
  · intro hy x hx
    obtain ⟨z, hz⟩ := hy x hx
    refine ⟨z, ?_⟩
    rw [dotProduct_comm]
    linarith

private theorem smul_mem_span_rat_restrictScalars (Λ : Submodule (𝓞 E) (Fin j → E)) (a : E) {x : Fin j → E}
    (hx : x ∈ Submodule.span ℚ ((Λ.restrictScalars ℤ : Submodule ℤ (Fin j → E)) : Set (Fin j → E))) :
    a • x ∈ Submodule.span ℚ ((Λ.restrictScalars ℤ : Submodule ℤ (Fin j → E)) : Set (Fin j → E)) := by
  obtain ⟨m, s, hm, hms⟩ :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ a)).exists_nsmul_eq (𝓞 E)
  induction hx using Submodule.span_induction with
  | mem y hy =>
    have hsy : s • y ∈ Λ := Λ.smul_mem s hy
    have key : a • y = (m : ℚ)⁻¹ • (s • y) := by
      rw [← algebraMap_smul E s y, ← hms, smul_assoc, ← Nat.cast_smul_eq_nsmul ℚ,
        inv_smul_smul₀ (by exact_mod_cast hm)]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsy)
  | zero => simp
  | add y z _ _ hy hz =>
    rw [smul_add]
    exact add_mem hy hz
  | smul q y _ hy =>
    rw [smul_comm]
    exact Submodule.smul_mem _ _ hy

theorem isLattice_restrict (Λ : Submodule (𝓞 E) (Fin j → E)) (h : Submodule.IsFullLattice E Λ) :
    Submodule.IsFullLattice ℚ (Λ.restrictScalars ℤ) := by
  refine { toIsLattice := Submodule.IsLattice.of_fg ℚ
             (Submodule.FG.restrictScalars (Submodule.IsLattice.fg E Λ)),
           span_eq_top := ?_ }
  refine Submodule.eq_top_iff'.mpr fun v => ?_
  have hv : v ∈ Submodule.span E (Λ : Set (Fin j → E)) := by
    rw [h.span_eq_top]
    trivial
  induction hv using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul a y _ hy => exact smul_mem_span_rat_restrictScalars E j Λ a hy

theorem exists_basis (Λ : Submodule (𝓞 E) (Fin j → E)) (h : Submodule.IsFullLattice E Λ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ (Fin j → E)),
      Λ.restrictScalars ℤ = Submodule.span ℤ (Set.range b) := by

  have := isLattice_restrict E j Λ h
  have := Submodule.IsLattice.free ℚ (Λ.restrictScalars ℤ)
  have := Submodule.IsLattice.finite ℚ (Λ.restrictScalars ℤ)
  let bF := Module.finBasis ℤ (Λ.restrictScalars ℤ)
  refine ⟨_, bF.extendOfIsFullLattice ℚ, ?_⟩
  have hb : ⇑(bF.extendOfIsFullLattice ℚ) = (Λ.restrictScalars ℤ).subtype ∘ bF :=
    funext fun k => bF.extendOfIsFullLattice_apply ℚ k
  rw [hb, Set.range_comp, ← Submodule.map_span, bF.span_eq, Submodule.map_top,
    Submodule.range_subtype]

theorem isLattice_trDual_and_trDual_trDual :
    ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)),
      Submodule.IsFullLattice E Λ →
        Submodule.IsFullLattice E (trDual E j Λ) ∧ trDual E j (trDual E j Λ) = Λ := by
  intro E _ _ j Λ h
  obtain ⟨n, b, hb⟩ := exists_basis E j Λ h
  have hB := halfTraceForm_nondegenerate E j
  have hS := halfTraceForm_symm E j

  have hD : (trDual E j Λ).restrictScalars ℤ =
      Submodule.span ℤ (Set.range ((halfTraceForm E j).dualBasis hB b)) := by
    rw [restrict_trDual, hb, LinearMap.BilinForm.dualSubmodule_span_of_basis _ hB]
  refine ⟨{ toIsLattice := ?_, span_eq_top := ?_ }, ?_⟩
  · apply Submodule.IsLattice.of_fg E
    apply Submodule.FG.of_restrictScalars ℤ
    rw [hD]
    exact Submodule.fg_span (Set.finite_range _)
  · refine eq_top_iff.mpr fun v _ => ?_
    have hv : v ∈ Submodule.span ℚ (Set.range ((halfTraceForm E j).dualBasis hB b)) := by
      rw [((halfTraceForm E j).dualBasis hB b).span_eq]
      trivial
    have h1 : Set.range ((halfTraceForm E j).dualBasis hB b) ⊆ (trDual E j Λ : Set (Fin j → E)) := by
      rintro _ ⟨k, rfl⟩
      have hk : (halfTraceForm E j).dualBasis hB b k ∈ (trDual E j Λ).restrictScalars ℤ := by
        rw [hD]
        exact Submodule.subset_span ⟨k, rfl⟩
      exact hk
    exact Submodule.span_le_restrictScalars ℚ E _ (Submodule.span_mono h1 hv)
  · apply Submodule.restrictScalars_injective ℤ _ _
    rw [restrict_trDual, restrict_trDual, hb,
      LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis _ hB hS]

end GlobalTheory.MeanDual.Alg
end
end
