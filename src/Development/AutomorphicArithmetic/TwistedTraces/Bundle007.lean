module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SfDefs
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle001
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle005
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableCartan
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import GroundTheory.AutomorphicForms.TraceFormulaConvolution
public import GroundTheory.AutomorphicForms.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.exists_algHom_end_fixedVectors_to_fixed_subspace :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (τ : Representation ℂ G S) (hτ : GroundTheory.Automorphic.IsSmooth τ) (_ : τ.IsIrreducible) (π : UnitaryRep G H) (U : Subgroup G) (_ : IsCompact (U : Set G)) (_ : IsOpen (U : Set G)) (D X : Submodule ℂ H) [FiniteDimensional ℂ X] [FiniteDimensional ℂ (fixedVectors τ U)] [Nontrivial (fixedVectors τ U)], IsClosed (D : Set H) → π.IsInvariant D → X = D ⊓ fixU π U → X ≤ spanFix τ π D U → ∃ c : Module.End ℂ (fixedVectors τ U) →ₐ[ℂ] Module.End ℂ X, (∀ t f, Eqv τ π D f → ∀ (x : fixedVectors τ U) (y : X), (y : H) = f x → ((c t y : X) : H) = f (t x)) ∧ ∀ t, c t ∈ Algebra.adjoin ℂ {a : Module.End ℂ X | ∃ g, ∀ v : X, ((a v : X) : H) = prj (fixU π U) (π g v)} := by
  intro G H S _ _ _ _ _ _ _ _ _ _ _ τ hτ hirr π U hUc hUo D X _ _ _ hD hinv hX hle
  subst hX
  obtain ⟨p1, -, p3, -⟩ := UpperTheory.fixedProjection_invariant_and_commuting_reps G G H π π U U
  have hm : ∀ f, Eqv τ π D f → ∀ x : fixedVectors τ U, f x ∈ D ⊓ fixU π U := fun f hf x =>
    ⟨hf.mem _, fun u hu => by rw [← hf.map, mem_fixedVectors.1 x.2 u hu]⟩
  let res : ∀ f, Eqv τ π D f → fixedVectors τ U →ₗ[ℂ] ↥(D ⊓ fixU π U) := fun f hf =>
    (f ∘ₗ (fixedVectors τ U).subtype).codRestrict _ (hm f hf)
  let e : S →ₗ[ℂ] fixedVectors τ U := fixedProj τ hτ hUc hUo
  let b : G → Module.End ℂ (fixedVectors τ U) := fun g => e ∘ₗ τ g ∘ₗ (fixedVectors τ U).subtype
  let a : G → Module.End ℂ ↥(D ⊓ fixU π U) := fun g =>
    ((prj (fixU π U) ∘L π g).toLinearMap ∘ₗ (D ⊓ fixU π U).subtype).codRestrict _ fun v =>
      ⟨p3 D hD hinv _ (hinv g _ v.2.1), p1 _⟩
  obtain ⟨c, h1, h2⟩ := UpperTheory.exists_algHom_end_intertwining_mem_adjoin (fixedVectors τ U) ↥(D ⊓ fixU π U) {k | ∃ f hf, k = res f hf}
    (Set.range fun g => (b g, a g)) (by
      rw [eq_top_iff]
      rintro ⟨y, hy⟩ -
      have h3 : spanFix τ π D U ≤ (⨆ k ∈ {k | ∃ f hf, k = res f hf}, LinearMap.range k).map (D ⊓ fixU π U).subtype := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨f, hf, x, hx, rfl⟩
        exact ⟨res f hf ⟨x, hx⟩, Submodule.mem_iSup_of_mem (res f hf) (Submodule.mem_iSup_of_mem ⟨f, hf, rfl⟩ ⟨_, rfl⟩), rfl⟩
      obtain ⟨z, hz, e⟩ := h3 (hle hy)
      exact (Subtype.ext e : z = ⟨y, hy⟩) ▸ hz) (by
      rintro _ ⟨g, rfl⟩ _ ⟨f, hf, rfl⟩
      refine LinearMap.ext fun x => Subtype.ext ?_
      show prj (fixU π U) (π g (f x)) = f (fixedProj τ hτ hUc hUo (τ g x))
      rw [← hf.map]
      exact UpperTheory.fixedProjection_apply_equivariant_eq G H S τ hτ π U hUc hUo f ⟨fun _ => trivial, hf.map⟩ _) (by
      intro x hx
      let W : Subrepresentation τ := ⟨Submodule.span ℂ (Set.range fun g => τ g x), fun g v hv => by
        refine (Submodule.map_span_le (τ g) _ _).2 ?_ (Submodule.mem_map_of_mem hv)
        rintro _ ⟨h, rfl⟩
        exact Submodule.subset_span ⟨g * h, by simp⟩⟩
      have hW : Submodule.span ℂ (Set.range fun g => τ g x) = ⊤ := by
        rcases eq_bot_or_eq_top W with h | h
        · have h' : Submodule.span ℂ (Set.range fun g => τ g x) = ⊥ := congrArg Subrepresentation.toSubmodule h
          have : τ 1 x ∈ Submodule.span ℂ (Set.range fun g => τ g x) := Submodule.subset_span ⟨1, rfl⟩
          rw [h', map_one] at this
          exact (hx (Subtype.ext this)).elim
        · exact congrArg Subrepresentation.toSubmodule h
      rw [eq_top_iff]
      rintro y -
      have h4 : e y = y := Subtype.ext (fixedProj_apply_of_mem hτ hUc hUo y.2)
      rw [← h4]
      refine (Submodule.map_span_le e (Set.range fun g => τ g x) _).2 ?_ (Submodule.mem_map_of_mem (hW ▸ Submodule.mem_top))
      rintro _ ⟨g, rfl⟩
      exact Submodule.subset_span ⟨_, ⟨g, rfl⟩, rfl⟩)
  refine ⟨c, fun t f hf x y hy => ?_, fun t => Algebra.adjoin_mono ?_ (h2 t)⟩
  · obtain rfl : y = res f hf x := Subtype.ext hy
    exact congrArg Subtype.val (LinearMap.congr_fun (h1 t _ ⟨f, hf, rfl⟩) x)
  · rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, fun _ => rfl⟩
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

open scoped Classical in
private theorem trace_mixedSpace_eq {K : Type} [Field K] [NumberField K]
    (x : NumberField.mixedEmbedding.mixedSpace K) :
    Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K) x =
      mixedTraceL K x + ∑ v, (x.2 v).re := by
  rw [UpperTheory.trace_mixedSpace_eq_mixedTraceL_mul, mixedTraceL_apply, mixedTraceL_apply]
  simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_one, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, mul_zero, sub_zero, ← Finset.sum_mul]
  ring

open scoped Classical in
private theorem trace_eq_zero_of_star_neg {K : Type} [Field K] [NumberField K]
    (z : NumberField.mixedEmbedding.mixedSpace K) (hz : star z = -z) :
    Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K) z = 0 := by
  have h1 : mixedTraceL K (star z) = mixedTraceL K z := mixedTraceL_star z
  rw [hz, map_neg] at h1
  have h2 : ∑ v, (z.2 v).re = 0 := by
    have h3 : ∀ v, (z.2 v).re = 0 := fun v => by
      have h4 : star (z.2 v) = -(z.2 v) := congrFun (congrArg Prod.snd hz) v
      have h5 := congrArg Complex.re h4
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h5
      linarith
    simp [h3]
  rw [trace_mixedSpace_eq, h2]
  linarith

open scoped Classical in
private theorem trace_conjTranspose_mul_pos {K : Type} [Field K] [NumberField K] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (NumberField.mixedEmbedding.mixedSpace K)} (hA : A ≠ 0) :
    0 < Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K)
      (Matrix.trace (A.conjTranspose * A)) := by
  rw [trace_mixedSpace_eq]
  have h1 := mixedTraceL_trace_conjTranspose_mul_self_pos hA
  have h2 : 0 ≤ ∑ v, ((Matrix.trace (A.conjTranspose * A)).2 v).re := by
    refine Finset.sum_nonneg fun v _ => ?_
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Prod.snd_sum, Finset.sum_apply, Complex.re_sum, Prod.snd_mul, Pi.mul_apply, Prod.snd_star,
      Pi.star_apply]
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  linarith

theorem UpperTheory.trForm_definite_on_archSkew_archHerm :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), (∀ X ∈ archSkew K n, X ≠ 0 → trForm K n X X < 0) ∧ (∀ X ∈ archHerm K n, X ≠ 0 → 0 < trForm K n X X) ∧ (∀ X ∈ archSkew K n, ∀ Y ∈ archHerm K n, trForm K n X Y = 0) := by
  intro K _ _ n
  refine ⟨fun X hX h0 => ?_, fun X hX h0 => ?_, fun X hX Y hY => ?_⟩
  · rw [mem_archSkew] at hX
    have hX0 : mat (X : ArchMatrix K n) ≠ 0 := fun e => h0 (Subtype.ext (mat_injective e))
    have e : mat (X : ArchMatrix K n) * mat (X : ArchMatrix K n) =
        -((mat (X : ArchMatrix K n)).conjTranspose * mat (X : ArchMatrix K n)) := by
      rw [hX, Matrix.neg_mul, neg_neg]
    have h := trace_conjTranspose_mul_pos hX0
    have h2 : trForm K n X X = Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K)
        (Matrix.trace (mat (X : ArchMatrix K n) * mat (X : ArchMatrix K n))) := rfl
    rw [h2, e, Matrix.trace_neg, map_neg]
    linarith
  · rw [mem_archHerm] at hX
    have hX0 : mat (X : ArchMatrix K n) ≠ 0 := fun e => h0 (Subtype.ext (mat_injective e))
    have h := trace_conjTranspose_mul_pos hX0
    rw [hX] at h
    exact h
  · rw [mem_archSkew] at hX
    rw [mem_archHerm] at hY
    have h2 : trForm K n X Y = Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K)
        (Matrix.trace (mat (X : ArchMatrix K n) * mat (Y : ArchMatrix K n))) := rfl
    rw [h2]
    refine trace_eq_zero_of_star_neg _ ?_
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX, hY, Matrix.mul_neg,
      Matrix.trace_neg, Matrix.trace_mul_comm]
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

private noncomputable def mkL {K : Type} [Field K] [NumberField K] {n : ℕ} (L : ℂ →L[ℝ] ℂ) (f : TI K n) : TI K n :=
  ⟨⟨fun g => L (f g), L.continuous.comp f.continuous⟩, f.hasCompactSupport.comp_left (map_zero L)⟩

private theorem smoothT_mkL {K : Type} [Field K] [NumberField K] {n : ℕ} (L : ℂ →L[ℝ] ℂ) {f : TI K n}
    (hf : SmoothT f) : SmoothT (mkL L f) := by
  let _ := (isExpLieAlgebra K n).chartedSpace
  exact L.contDiff.comp_contMDiff hf

private noncomputable def reL : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

private noncomputable def imL : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM

private theorem conv_split {K : Type} [Field K] [NumberField K] {n : ℕ}
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a b : TI K n) (x : archGroup K n) :
    conv ν (mkL reL a) b x + conv ν (mkL imL a) (Complex.I • b) x = ∫ y, a y * b (y⁻¹ * x) ∂ν := by
  have hb : Continuous fun y : archGroup K n => b (y⁻¹ * x) := by fun_prop
  have i1 : Integrable (fun y => mkL reL a y * b (y⁻¹ * x)) ν :=
    ((mkL reL a).continuous.mul hb).integrable_of_hasCompactSupport
      (mkL reL a).hasCompactSupport.mul_right
  have i2 : Integrable (fun y => mkL imL a y * (Complex.I • b) (y⁻¹ * x)) ν :=
    ((mkL imL a).continuous.mul ((Complex.I • b).continuous.comp (by fun_prop))).integrable_of_hasCompactSupport
      (mkL imL a).hasCompactSupport.mul_right
  rw [conv_apply, conv_apply, ← integral_add i1 i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ((a y).re : ℂ) * b (y⁻¹ * x) + ((a y).im : ℂ) * (Complex.I * b (y⁻¹ * x)) = a y * b (y⁻¹ * x)
  have hz : ((a y).re : ℂ) + ((a y).im : ℂ) * Complex.I = a y := Complex.re_add_im _
  calc _ = (((a y).re : ℂ) + ((a y).im : ℂ) * Complex.I) * b (y⁻¹ * x) := by ring
    _ = _ := by rw [hz]

theorem UpperTheory.exists_sum_conv_real_smoothT :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
        (F : TI K n), SmoothT F → ∃ (ι : Type) (_ : Fintype ι) (κ γ : ι → TI K n),
          (∀ i, SmoothT (κ i) ∧ ∀ g, (κ i g).im = 0) ∧ F = ∑ i, conv ν (κ i) (γ i) := by
  intro K _ _ n ν _ F hF
  obtain ⟨N, φ, ψ, h, e⟩ := dixmierMalliavin (isExpLieAlgebra K n) ν (fun g => F g) hF F.hasCompactSupport
  let _ := (isExpLieAlgebra K n).chartedSpace
  let a : Fin N → TI K n := fun i => ⟨⟨φ i, (h i).1.continuous⟩, (h i).2.1⟩
  let b : Fin N → TI K n := fun i => ⟨⟨ψ i, (h i).2.2.1.continuous⟩, (h i).2.2.2⟩
  have has : ∀ i, SmoothT (a i) := fun i => (h i).1
  refine ⟨Fin N × Bool, inferInstance,
    fun p => if p.2 then mkL imL (a p.1) else mkL reL (a p.1),
    fun p => if p.2 then Complex.I • b p.1 else b p.1, ?_, ?_⟩
  · rintro ⟨i, _ | _⟩
    · exact ⟨smoothT_mkL _ (has i), fun g => by simp [mkL, reL]⟩
    · exact ⟨smoothT_mkL _ (has i), fun g => by simp [mkL, imL]⟩
  · ext x
    have ex : F x = ∑ i, groupConv ν (φ i) (ψ i) x := by
      have := congrFun e x
      simpa [Finset.sum_apply] using this
    rw [ex, CompactlySupportedContinuousMap.sum_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false]
    rw [add_comm, conv_split]
    rfl
end
