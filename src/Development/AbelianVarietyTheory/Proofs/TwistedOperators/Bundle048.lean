module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle042
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Topology

noncomputable section
namespace GlobalTheory.ColFourier

section Curry
variable {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)] {Y : (i : ι) → κ i → Type*}
  [∀ i j, MeasurableSpace (Y i j)]

theorem measurePreserving_piCurry (μ : ∀ i j, Measure (Y i j)) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry Y) (Measure.pi fun p : (i : ι) × κ i => μ p.1 p.2)
      (Measure.pi fun i => Measure.pi fun j => μ i j) := by
  refine ⟨(MeasurableEquiv.piCurry Y).measurable, ?_⟩
  symm
  refine Measure.pi_eq_generateFrom
    (C := fun i => Set.univ.pi '' Set.univ.pi fun j => {s : Set (Y i j) | MeasurableSet s})
    (fun i => generateFrom_pi) (fun i => isPiSystem_pi)
    (fun i => Measure.FiniteSpanningSetsIn.pi fun j => (μ i j).toFiniteSpanningSetsIn) fun s hs => ?_
  choose S hS hSs using hs
  have hpre : (MeasurableEquiv.piCurry Y) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi fun p : (i : ι) × κ i => S p.1 p.2 := by
    ext f
    simp only [Set.mem_preimage, Set.mem_univ_pi, ← hSs, MeasurableEquiv.piCurry_apply, Sigma.forall]
    rfl
  rw [Measure.map_apply (MeasurableEquiv.piCurry Y).measurable (MeasurableSet.univ_pi fun i => by
      rw [← hSs i]; exact MeasurableSet.univ_pi fun j => hS i j (Set.mem_univ j)), hpre, Measure.pi_pi,
    Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hSs i, Measure.pi_pi]

end Curry

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A C : Type*} [Fintype A] [DecidableEq C]


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
def restrictCols (P : Finset C) (X : Matrix A C k) : Matrix A P k := Matrix.of fun i j => X i j

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
@[simp] theorem restrictCols_setCols (P : Finset C) (Y : Matrix A C k) (U : Matrix A P k) :
    restrictCols P (setCols P Y U) = U := by
  ext i j; simp [restrictCols, setCols, j.2]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
@[simp] theorem setCols_restrictCols (P : Finset C) (Y : Matrix A C k) : setCols P Y (restrictCols P Y) = Y := by
  ext i j; by_cases h : j ∈ P <;> simp [restrictCols, setCols, h]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
@[simp] theorem setCols_setCols (P : Finset C) (Y : Matrix A C k) (U V : Matrix A P k) :
    setCols P (setCols P Y U) V = setCols P Y V := by
  ext i j; by_cases h : j ∈ P <;> simp [setCols, h]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem continuous_restrictCols (P : Finset C) : Continuous (restrictCols (k := k) (A := A) P) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply (j : C)).comp (continuous_apply i)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem continuous_setCols (P : Finset C) (Y : Matrix A C k) : Continuous (setCols P Y) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : j ∈ P
  · simp only [setCols, of_apply, dif_pos h]
    exact (continuous_apply (⟨j, h⟩ : P)).comp (continuous_apply i)
  · simp only [setCols, of_apply, dif_neg h]
    exact continuous_const

theorem comp_setCols_mem_SB {Ξ : Matrix A C k → ℂ} (hΞ : Ξ ∈ SB (Matrix A C k)) (P : Finset C)
    (Y : Matrix A C k) : (fun U => Ξ (setCols P Y U)) ∈ SB (Matrix A P k) := by
  haveI := t2Space k
  refine ⟨hΞ.1.comp_continuous (continuous_setCols P Y),
    HasCompactSupport.intro (hΞ.2.image (continuous_restrictCols P)) fun U hU => ?_⟩
  exact image_eq_zero_of_notMem_tsupport fun h => hU ⟨_, h, restrictCols_setCols P Y U⟩

theorem pairCols_eq_dotProduct (P : Finset C) (Y : Matrix A C k) (U : Matrix A P k) :
    pairCols P Y U = (fun p : (_ : A) × P => U p.1 p.2) ⬝ᵥ (fun p : (_ : A) × P => Y p.1 p.2) := by
  simp only [pairCols, dotProduct, Fintype.sum_sigma]

variable [MeasurableSpace k] [BorelSpace k]


omit [DecidableEq C] in
theorem isAddHaarMeasure_volM (m : Measure k) [m.IsAddHaarMeasure] (B : Type*) [Fintype B] :
    (volM m A B).IsAddHaarMeasure := by
  haveI := secondCountable k; haveI := t2Space k
  haveI : (Measure.pi fun _ : B => m).IsAddHaarMeasure := inferInstance
  exact Measure.pi.isAddHaarMeasure (fun _ : A => (Measure.pi fun _ : B => m))


omit [DecidableEq C] in
theorem integral_volM (m : Measure k) [SigmaFinite m] (B : Type*) [Fintype B] (f : Matrix A B k → ℂ) :
    ∫ U, f U ∂(volM m A B) =
      ∫ x : (_ : A) × B → k, f (Matrix.of fun i j => x ⟨i, j⟩) ∂(Measure.pi fun _ => m) := by
  have h := measurePreserving_piCurry (Y := fun (_ : A) (_ : B) => k) (fun _ _ => m)
  exact (h.integral_comp' (g := f)).symm

theorem fourierInt_eq_pi (ψ : AddChar k Circle) (m : Measure k) [SigmaFinite m] (P : Finset C)
    (Φ : Matrix A C k → ℂ) (Y : Matrix A C k) :
    fourierInt ψ m P Φ Y = ∫ x : (_ : A) × P → k, Φ (setCols P Y (Matrix.of fun i j => x ⟨i, j⟩)) *
      (ψ (x ⬝ᵥ fun p => Y p.1 p.2) : ℂ) ∂(Measure.pi fun _ => m) := by
  rw [fourierInt, integral_volM]
  congr 1
  funext x
  rw [pairCols_eq_dotProduct]
  rfl

end GlobalTheory.ColFourier

namespace GlobalTheory.ColFourier
variable {k : Type*} [Field k] [ValuativeRel k]

theorem hasConductor_inv {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) : HasConductor ψ⁻¹ c := fun x => by
  simpa only [AddChar.inv_apply', inv_eq_one] using h x

end GlobalTheory.ColFourier
end
end

section

open ContinuousLinearMap
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory

open GlobalTheory.OpTrace

theorem tensorTrace_summable_sq {ι : Type} [Fintype ι] {Hs : ι → Type} [∀ i, NormedAddCommGroup (Hs i)]
    [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Ψ : ContinuousMultilinearMap ℂ Hs H) (c : ℂ)
    (hΨ : ∀ y y', ⟪Ψ y', Ψ y⟫_ℂ = c * ∏ i, ⟪y' i, y i⟫_ℂ) (A : ∀ i, Hs i →L[ℂ] Hs i)
    (hA : ∀ i, IsHilbertSchmidt (A i)) :
    Summable fun j : ∀ i, stdIndex (Hs i) => ‖Ψ (fun i => A i (stdBasis (H := Hs i) (j i)))‖ ^ 2 := by
  have hs := (splitHeight_summable_pi_prod (α := fun i => stdIndex (Hs i))
    (f := fun i k => ‖A i (stdBasis (H := Hs i) k)‖ ^ 2) (fun _ _ => sq_nonneg _) hA).mul_left c.re
  refine hs.congr fun j => ?_
  have h1 := hΨ (fun i => A i (stdBasis (H := Hs i) (j i))) (fun i => A i (stdBasis (H := Hs i) (j i)))
  simp only [inner_self_eq_norm_sq_to_K] at h1
  have h2 : ((‖Ψ (fun i => A i (stdBasis (H := Hs i) (j i)))‖ ^ 2 : ℝ) : ℂ)
      = c * ((∏ i, ‖A i (stdBasis (H := Hs i) (j i))‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; exact h1
  have h3 := congrArg Complex.re h2
  rw [Complex.ofReal_re, Complex.re_mul_ofReal] at h3
  exact h3.symm

theorem tensorTrace_hasTrace : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ Φ' : ContinuousMultilinearMap ℂ Hs H) (κ κ' : ℂ), (∀ y y', inner ℂ (Φ y') (Φ y) = ∏ i, inner ℂ (y' i) (y i)) → (∀ y y', inner ℂ (Φ y') (Φ' y) = κ * ∏ i, inner ℂ (y' i) (y i)) → (∀ y y', inner ℂ (Φ' y') (Φ' y) = κ' * ∏ i, inner ℂ (y' i) (y i)) → ∀ (B : ∀ i, Hs i →L[ℂ] Hs i) (b : ι → ℂ), (∀ i, HasTrace (B i) (b i)) → ∀ X : H →L[ℂ] H, (∀ y, X (Φ y) = Φ' fun i => B i (y i)) → (∀ v, (∀ y, inner ℂ (Φ y) v = 0) → X v = 0) → HasTrace X (κ * ∏ i, b i) := by
  intro ι _ _ Hs _ _ _ H _ _ _ Φ Φ' κ κ' hΦ hΦΦ' hΦ' B b hB X hX hX0
  classical
  let J : ι → Type := fun i => stdIndex (Hs i)
  let e : ∀ i, HilbertBasis (J i) ℂ (Hs i) := fun i => stdBasis (H := Hs i)
  let u : (∀ i, J i) → H := fun j => Φ (fun i => e i (j i))

  have hu : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro j' j
    change ⟪Φ _, Φ _⟫_ℂ = _
    rw [hΦ]
    have : ∀ i, ⟪e i (j' i), e i (j i)⟫_ℂ = if j' i = j i then 1 else 0 := fun i =>
      (orthonormal_iff_ite.1 (e i).orthonormal) _ _
    simp only [this]
    by_cases h : ∀ x, j' x = j x
    · rw [if_pos (funext h)]
      exact Finset.prod_eq_one fun i _ => if_pos (h i)
    · rw [if_neg fun h' => h (congrFun h')]
      push_neg at h
      obtain ⟨i, hi⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

  have hperp : ∀ x : H, (∀ j, ⟪u j, x⟫_ℂ = 0) → ∀ y, ⟪Φ y, x⟫_ℂ = 0 := by
    intro x hx y
    have hL := GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' ι Hs J e ℂ
      ((innerSL ℂ x).compContinuousMultilinearMap Φ) 0 fun j => by
        simp only [compContinuousMultilinearMap_coe, Function.comp_apply, innerSL_apply_apply,
          ContinuousMultilinearMap.zero_apply]
        rw [← inner_conj_symm]; simp [u] at hx; simp [hx]
    have := congrArg (fun L : ContinuousMultilinearMap ℂ Hs ℂ => L y) hL
    simp only [compContinuousMultilinearMap_coe, Function.comp_apply, innerSL_apply_apply,
      ContinuousMultilinearMap.zero_apply] at this
    rw [← inner_conj_symm, this, map_zero]

  have hinj : Function.Injective u := hu.linearIndependent.injective
  obtain ⟨w, bH, hsw, hb⟩ :=
    Orthonormal.exists_hilbertBasis_extension ((orthonormal_subtype_range hinj).2 hu)
  have hoff : ∀ x ∈ w, x ∉ Set.range u → ∀ y, ⟪Φ y, x⟫_ℂ = 0 := by
    intro x hxw hxu
    refine hperp x fun j => ?_
    have hne : (⟨u j, hsw ⟨j, rfl⟩⟩ : w) ≠ ⟨x, hxw⟩ := fun h => hxu ⟨j, congrArg Subtype.val h⟩
    have := bH.orthonormal.2 hne
    simpa [hb] using this

  choose n C D hC hD hBeq using fun i => (hB i).1

  have hG : ∀ (Ψ : ContinuousMultilinearMap ℂ Hs H) (c : ℂ),
      (∀ y y', ⟪Ψ y', Ψ y⟫_ℂ = c * ∏ i, ⟪y' i, y i⟫_ℂ) → ∀ A : ∀ i, Hs i →L[ℂ] Hs i,
      (∀ i, IsHilbertSchmidt (A i)) → ∃ G : H →L[ℂ] H, (∀ y, G (Φ y) = Ψ (fun i => A i (y i))) ∧
        (∀ v, (∀ y, ⟪Φ y, v⟫_ℂ = 0) → G v = 0) ∧ IsHilbertSchmidt G := by
    intro Ψ c hΨ A hA
    obtain ⟨G, hG1, hG2, hG3⟩ := GlobalTheory.T.exists_isHilbertSchmidt_orthonormal_apply_alt H H (∀ i, J i) u
      (fun j => Ψ (fun i => A i (e i (j i)))) hu (tensorTrace_summable_sq Ψ c hΨ A hA)
    refine ⟨G, fun y => ?_, fun v hv => hG2 v fun j => hv _, hG3⟩
    have := GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' ι Hs J e H (G.compContinuousMultilinearMap Φ)
      (Ψ.compContinuousLinearMap A) fun j => by simpa using hG1 j
    simpa using congrArg (fun L : ContinuousMultilinearMap ℂ Hs H => L y) this
  have hΦ1 : ∀ y y', ⟪Φ y', Φ y⟫_ℂ = 1 * ∏ i, ⟪y' i, y i⟫_ℂ := fun y y' => by rw [one_mul, hΦ]
  choose GD hGD1 hGD2 hGD3 using fun k : ∀ i, Fin (n i) => hG Φ 1 hΦ1 (fun i => D i (k i)) fun i => hD i _
  choose GC hGC1 hGC2 hGC3 using fun k : ∀ i, Fin (n i) => hG Φ' κ' hΦ' (fun i => C i (k i)) fun i => hC i _

  have hXeq : X = ∑ k, GC k ∘L GD k := by
    have hd : Dense (Submodule.span ℂ w : Set H) := by
      have := bH.dense_span
      rw [hb, Subtype.range_coe] at this
      exact Submodule.dense_iff_topologicalClosure_eq_top.2 this
    refine ContinuousLinearMap.ext_on hd fun x hx => ?_
    by_cases hxu : x ∈ Set.range u
    · obtain ⟨j, rfl⟩ := hxu
      change X (Φ _) = _
      rw [hX, ContinuousLinearMap.sum_apply]
      simp only [comp_apply]
      rw [show (fun i => B i (e i (j i))) = fun i => ∑ m, C i m (D i m (e i (j i))) from
        funext fun i => by rw [hBeq i]; simp]

      rw [Φ'.map_sum (fun i m => C i m (D i m (e i (j i))))]
      refine Finset.sum_congr rfl fun k _ => ?_
      change _ = GC k (GD k (Φ fun i => e i (j i)))
      rw [hGD1, hGC1]
    · have h0 := hoff x hx hxu
      rw [hX0 x h0, ContinuousLinearMap.sum_apply]
      simp [hGD2 _ x h0]
  have hTC : IsTraceClass X := by
    rw [hXeq]; exact isTraceClass_sum _ fun k _ => (hGC3 k).isTraceClass_comp (hGD3 k)
  refine ⟨hTC, ?_⟩

  have htr := hTC.hasSum_trace bH
  let g : (∀ i, J i) → w := fun j => ⟨u j, hsw ⟨j, rfl⟩⟩
  have hg : Function.Injective g := fun j j' h => hinj (congrArg Subtype.val h)
  have hz : ∀ x ∉ Set.range g, ⟪bH x, X (bH x)⟫_ℂ = 0 := by
    intro x hx
    have hxu : x.1 ∉ Set.range u := fun ⟨j, hj⟩ => hx ⟨j, Subtype.ext hj⟩
    simp [hb, hX0 _ (hoff x.1 x.2 hxu)]
  rw [← hg.hasSum_iff hz] at htr
  have hval : ∀ j, ⟪bH (g j), X (bH (g j))⟫_ℂ = κ * ∏ i, ⟪e i (j i), B i (e i (j i))⟫_ℂ := by
    intro j
    simp only [hb, g]
    change ⟪Φ _, X (Φ _)⟫_ℂ = _
    rw [hX, hΦΦ']
  have hprod := (GlobalTheory.T.hasSum_tuple_prod_of_summable_norm_complex ι J (fun i k => ⟪e i k, B i (e i k)⟫_ℂ)
    fun i => (hB i).1.summable_norm (e i)).mul_left κ
  have hb' : ∀ i, ∑' k, ⟪e i k, B i (e i k)⟫_ℂ = b i := fun i =>
    ((hB i).1.hasSum_trace (e i)).tsum_eq.trans (hB i).2
  simp only [hb'] at hprod
  refine htr.unique ?_
  simpa only [Function.comp_def, hval] using hprod

end GlobalTheory
end
end

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology

noncomputable section

namespace GlobalTheory.GelfandKazhdan

section General

variable {G : Type} [Group G] [TopologicalSpace G]

def pull (t : G ≃ₜ G) : SB G →ₗ[ℂ] SB G where
  toFun φ := ⟨fun x => φ.1 (t x), φ.2.1.comp_continuous t.continuous, φ.2.2.comp_homeomorph t⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [TopologicalSpace G] in
theorem anti_one {t : G → G} (hm : ∀ x y, t (x * y) = t y * t x) : t 1 = 1 := by
  have := hm 1 1
  rw [one_mul] at this
  exact left_eq_mul.1 this

omit [TopologicalSpace G] in
theorem anti_inv {t : G → G} (hm : ∀ x y, t (x * y) = t y * t x) (x : G) : t x⁻¹ = (t x)⁻¹ := by
  have := hm x x⁻¹
  rw [mul_inv_cancel, anti_one hm] at this
  exact eq_inv_of_mul_eq_one_left this.symm

theorem exists_stable (t : G ≃ₜ G) (hm : ∀ x y, t (x * y) = t y * t x) (ht : ∀ x, t (t x) = x)
    (K₀ : Subgroup G) (hK : ∀ x ∈ K₀, t x ∈ K₀)
    (hb : ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧
      (J : Set G) ⊆ U ∧ J ≤ K₀ ∧ ∀ x ∈ K₀, ∀ j ∈ J, x * j * x⁻¹ ∈ J) :
    ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧
      (J : Set G) ⊆ U ∧ J ≤ K₀ ∧ (∀ x ∈ K₀, ∀ j ∈ J, x * j * x⁻¹ ∈ J) ∧ ∀ j ∈ J, t j ∈ J := by
  intro U hU
  obtain ⟨J, ho, hJU, hJK, hn⟩ := hb U hU
  refine ⟨{ carrier := {y | y ∈ J ∧ t y ∈ J}
            mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, by rw [hm]; exact mul_mem hb.2 ha.2⟩
            one_mem' := ⟨one_mem _, by rw [anti_one hm]; exact one_mem _⟩
            inv_mem' := fun ha => ⟨inv_mem ha.1, by rw [anti_inv hm]; exact inv_mem ha.2⟩ },
    ho.inter (ho.preimage t.continuous), fun y hy => hJU hy.1, fun y hy => hJK hy.1,
    fun x hx j hj => ⟨hn x hx j hj.1, ?_⟩, fun j hj => ⟨hj.2, by rw [ht]; exact hj.1⟩⟩
  have := hn _ (inv_mem (hK x hx)) _ hj.2
  rw [hm, hm, anti_inv hm, ← mul_assoc]
  rwa [inv_inv] at this

theorem invariant_of_anti [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (t : G ≃ₜ G) (hm : ∀ x y, t (x * y) = t y * t x)
    (ht : ∀ x, t (t x) = x) (K₀ : Subgroup G) (hKo : IsOpen (K₀ : Set G))
    (hKc : IsCompact (K₀ : Set G)) (hK : ∀ x ∈ K₀, t x ∈ K₀)
    (hb : ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧
      (J : Set G) ⊆ U ∧ J ≤ K₀ ∧ ∀ x ∈ K₀, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hs : ∀ x, ∃ s, t s = s ∧ s * x = t x * s) (T : SB G →ₗ[ℂ] ℂ)
    (hT : ∀ (g : G) (φ ψ : SB G), (∀ x, ψ.1 x = φ.1 (g * x * g⁻¹)) → T ψ = T φ) (φ : SB G) :
    T (pull t φ) = T φ := by
  obtain ⟨U, hU⟩ := (𝓝 (1 : G)).exists_antitone_basis
  choose J hJo hJU hJK hJn hJt using fun m =>
    exists_stable t hm ht K₀ hK hb (U m) (hU.1.mem_of_mem trivial)
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense G
  have : Countable S := hSc.to_subtype
  let K : S → ℕ → Subgroup G := fun c m => J m ⊓ (J m).comap (MulAut.conj (c : G)).toMonoidHom
  have hKm : ∀ c m y, y ∈ K c m ↔ y ∈ J m ∧ (c : G) * y * (c : G)⁻¹ ∈ J m := fun c m y => Iff.rfl
  have hD : T - T.comp (pull t) = 0 := by
    refine GlobalTheory.T.schwartzBruhat_distribution_eq_zero_baire G S K (fun c m => ?_) (fun c V hV => ?_) _ fun x => ?_
    · have ho : IsOpen (K c m : Set G) :=
        (hJo m).inter ((hJo m).preimage (f := fun y => (c : G) * y * (c : G)⁻¹) (by fun_prop))
      exact ⟨ho, hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun y hy => hJK m hy.1⟩
    · obtain ⟨m, -, hm⟩ := hU.1.mem_iff.1 hV
      exact ⟨m, fun y hy => hm (hJU m hy.1)⟩
    · obtain ⟨s, hts, hsx⟩ := hs x
      obtain ⟨c, hc, hcS⟩ := hSd.inter_open_nonempty _
        (hKo.preimage (f := fun y => y * s⁻¹) (by fun_prop)) ⟨s, by simp⟩
      have hc' : c * s⁻¹ ∈ K₀ := hc
      refine ⟨⟨c, hcS⟩, fun m ψ hψ => ?_⟩
      have hK' : ∀ y, y ∈ K ⟨c, hcS⟩ m ↔ y ∈ J m ∧ s * y * s⁻¹ ∈ J m := fun y => by
        rw [hKm]
        refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
        · have := hJn m _ (inv_mem hc') _ h
          convert this using 1
          simp only []
          group
        · have := hJn m _ hc' _ h
          convert this using 1
          simp only []
          group
      have hτ : ∀ y, t (s * y * s⁻¹) = s⁻¹ * t y * s := fun y => by
        rw [hm, hm, anti_inv hm, hts, mul_assoc]
      have hτK : ∀ y ∈ K ⟨c, hcS⟩ m, s⁻¹ * t y * s ∈ K ⟨c, hcS⟩ m := fun y hy => by
        rw [hK'] at hy ⊢
        refine ⟨hτ y ▸ hJt m _ hy.2, ?_⟩
        convert hJt m _ hy.1 using 1
        group
      have h1 : ∀ y, y ∈ {g : G | ∃ a ∈ K ⟨c, hcS⟩ m, ∃ b ∈ K ⟨c, hcS⟩ m, g = a * x * b} →
          s⁻¹ * t y * s ∈ {g : G | ∃ a ∈ K ⟨c, hcS⟩ m, ∃ b ∈ K ⟨c, hcS⟩ m, g = a * x * b} := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨_, hτK b hb, _, hτK a ha, ?_⟩
        have : t x = s * x * s⁻¹ := by rw [hsx]; group
        rw [hm, hm, this]
        group
      have h2 : ∀ y, s⁻¹ * t (s⁻¹ * t y * s) * s = y := fun y => by
        rw [hm, hm, anti_inv hm, hts, ht]
        group
      have h3 : T ψ = T (pull t ψ) := hT s _ _ fun y => by
        show ψ.1 y = ψ.1 (t (s * y * s⁻¹))
        rw [hτ, hψ]
        by_cases hy : y ∈ {g : G | ∃ a ∈ K ⟨c, hcS⟩ m, ∃ b ∈ K ⟨c, hcS⟩ m, g = a * x * b}
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (h1 y hy)]
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem fun h => hy (h2 y ▸ h1 _ h)]
      exact sub_eq_zero.2 h3
  exact (sub_eq_zero.1 (LinearMap.congr_fun hD φ)).symm

end General

section Transpose

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def trGL (g : GL n R) : GL n R :=
  ⟨g.val.transpose, g.inv.transpose, by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]⟩

theorem trGL_trGL (g : GL n R) : trGL (trGL g) = g := rfl

theorem trGL_mul (g h : GL n R) : trGL (g * h) = trGL h * trGL g :=
  Units.ext (Matrix.transpose_mul _ _)

theorem continuous_trGL [TopologicalSpace R] : Continuous (trGL : GL n R → GL n R) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_transpose,
    Units.continuous_coe_inv.matrix_transpose⟩

def trHomeo [TopologicalSpace R] : GL n R ≃ₜ GL n R where
  toFun := trGL
  invFun := trGL
  left_inv := trGL_trGL
  right_inv := trGL_trGL
  continuous_toFun := continuous_trGL
  continuous_invFun := continuous_trGL

end Transpose

theorem transpose_invariant (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (T : SB (GL n k) →ₗ[ℂ] ℂ)
    (hT : ∀ (g : GL n k) (φ ψ : SB (GL n k)), (∀ x, ψ.1 x = φ.1 (g * x * g⁻¹)) → T ψ = T φ)
    (φ ψ : SB (GL n k)) (h : ∀ x y : GL n k, y.val = x.val.transpose → ψ.1 x = φ.1 y) :
    T ψ = T φ := by
  have e : ψ = pull trHomeo φ := Subtype.ext (funext fun x => h x (trGL x) rfl)
  rw [e]
  refine invariant_of_anti trHomeo trGL_mul trGL_trGL (KO k n) SplitFlip.isOpen_KO
    SplitFlip.isCompact_KO (fun x hx => ?_) (exists_open_normalised_subgroup_subset k n)
    (fun x => ?_) T hT φ
  · obtain ⟨h1, h2⟩ := (SplitFlip.mem_KO_iff _).1 hx
    exact (SplitFlip.mem_KO_iff _).2 ⟨fun i j => h1 j i, fun i j => h2 j i⟩
  · obtain ⟨P, ⟨s, rfl⟩, h1, h2⟩ := GlobalTheory.T.matrix_conj_transpose_by_symmetric_taussky_zassenhaus k n x.val
    exact ⟨s, Units.ext h1, Units.ext h2⟩

end GlobalTheory.GelfandKazhdan
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem _root_.GlobalTheory.T.rootExchangeUnipotentSubgroup_succ_decomposition : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), ∀ g ∈ N k n c (p + 1), ∃ g₁ ∈ N k n c p ⊓ N k n c (p + 1), ∃ u : n → k, g = g₁ * rowE c p u := by
  first | exact @GlobalTheory.RootEx.RadicalDecomp.succ_decomp | exact GlobalTheory.RootEx.RadicalDecomp.succ_decomp | (intros; apply GlobalTheory.RootEx.RadicalDecomp.succ_decomp <;> assumption)
end
