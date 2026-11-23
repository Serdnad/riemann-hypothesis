module

public import Formalism.HermitianCurvature.StatementB
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.Bundle004
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Formalism.PeriodIntegrals.Bundle018
public import Formalism.RealPlaceAnalysis.Bundle003
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
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
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.Bundle001
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Composition.Comp

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CoefZero


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal Matrix.Norms.Elementwise in
theorem _root_.GlobalTheory.CoefZero.continuousOn_of_ckOn {k r : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {m : ℕ∞}
    {f : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} (h : _root_.Formalism.FourierDecayAlt.B.CkOn m (_root_.Formalism.FourierDecayAlt.B.GV k r) f) : ContinuousOn f (_root_.Formalism.FourierDecayAlt.B.GV k r) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfeq⟩ := h g₀ hg₀
  have hc : ContinuousOn f' U := hf'.continuousOn
  have hcont : ContinuousAt f' g₀ := hc.continuousAt (hU.mem_nhds hgU)
  refine hcont.continuousWithinAt.congr_of_eventuallyEq ?_ (hfeq g₀ hgU hg₀)
  filter_upwards [inter_mem_nhdsWithin (_root_.Formalism.FourierDecayAlt.B.GV k r) (hU.mem_nhds hgU)] with g hg
  exact hfeq g hg.2 hg.1

end GlobalTheory.CoefZero
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem map_ofFn_prod_apply_of_intertwine {M Wp : Type} [AddCommGroup M] [Module ℂ M]
    (l : M → Wp) :
    ∀ (t : ℕ) (f : Fin t → Module.End ℂ M) (g : Fin t → Wp → Wp),
      (∀ k v, l (f k v) = g k (l v)) → ∀ v,
      l ((List.ofFn f).prod v) = List.foldr (fun T h => T h) (l v) (List.ofFn g) := by
  intro t
  induction t with
  | zero => intro f g _ v; simp
  | succ t ih =>
    intro f g h v
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.foldr_cons, Module.End.mul_apply, h,
      ih (fun i => f i.succ) (fun i => g i.succ) (fun k v => h k.succ v) v]

theorem qminor_block_intertwine : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n m : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (w : Fin m → Fin n) (Pop : Fin m → Fin m → Wp → Wp), Function.Injective w → (∀ i j v, l (E (w i) (w j) v) = Pop i j (l v)) → ∀ u v, l (Formalism.REAL.qminor E w w u v) = Formalism.FourierDecayAlt.Q.qmF Pop id id u (l v) := by
  intro M Wp _ _ _ _ n m E l w Pop hw h u v
  unfold Formalism.REAL.qminor Formalism.FourierDecayAlt.Q.qmF

  rw [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have key := map_ofFn_prod_apply_of_intertwine (l : M → Wp) m
    (fun k => Formalism.REAL.Tm E (u - ((k : ℕ) : ℂ)) (w (σ k)) (w k))
    (fun k y => (if id (σ k) = id k then (u - ((k : ℕ) : ℂ)) • y else 0) + Pop (id (σ k)) (id k) y)
    (fun k x => by
      unfold Formalism.REAL.Tm
      by_cases hk : σ k = k
      · simp [hk, h, sub_smul, Nat.cast_smul_eq_nsmul]
      · have : w (σ k) ≠ w k := fun e => hk (hw e)
        simp [hk, this, h]) v
  rw [← key, Module.End.mul_apply]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.HaarInversion

def mulM {m : ℕ} (x y : PI.MtM m) : PI.MtM m := fun i j => (Matrix.of x * Matrix.of y) i j

noncomputable def invM {m : ℕ} (x : PI.MtM m) : PI.MtM m := fun i j => (Matrix.of x)⁻¹ i j

lemma of_mulM {m : ℕ} (x y : PI.MtM m) : Matrix.of (mulM x y) = Matrix.of x * Matrix.of y := rfl

lemma of_invM {m : ℕ} (x : PI.MtM m) : Matrix.of (invM x) = (Matrix.of x)⁻¹ := rfl

lemma measurable_mulM {m : ℕ} {α : Type*} [MeasurableSpace α] {u v : α → PI.MtM m}
    (hu : Measurable u) (hv : Measurable v) : Measurable fun a => mulM (u a) (v a) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [mulM, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
  · exact (measurable_pi_apply k).comp ((measurable_pi_apply i).comp hu)
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp hv)

lemma measurable_invM {m : ℕ} : Measurable (invM : PI.MtM m → PI.MtM m) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have hof : Continuous fun x : PI.MtM m => (Matrix.of x : Matrix (Fin m) (Fin m) ℂ) := continuous_id
  have h1 : Measurable fun x : PI.MtM m => (Matrix.of x).det := hof.matrix_det.measurable
  have h2 : Measurable fun x : PI.MtM m => (Matrix.of x).adjugate i j :=
    (hof.matrix_adjugate.matrix_elem i j).measurable
  simp only [invM, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact h1.inv.mul h2

theorem lintegral_inv_eq : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup S → PI.IsHaarOnM S μ → PI.IsRightInvM S μ → ∀ f : PI.MtM m → ℝ≥0∞, Measurable f → ∫⁻ s, f (fun i j => (Matrix.of s)⁻¹ i j) ∂μ = ∫⁻ s, f s ∂μ := by
  intro m S μ hS hμ hR f hf
  obtain ⟨hσ, hne, hc, hL⟩ := hμ
  obtain ⟨-, -, -, hinv⟩ := hS
  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ S := hc
  have left : ∀ a : PI.MtM m, Matrix.of a ∈ S → ∀ g : PI.MtM m → ℝ≥0∞, Measurable g →
      ∫⁻ y, g (mulM a y) ∂μ = ∫⁻ y, g y ∂μ := by
    intro a ha g hg
    have h := lintegral_map (μ := μ) hg (measurable_mulM (measurable_const (a := a)) measurable_id)
    have e : (fun y : PI.MtM m => mulM a (id y)) = PI.lmulQ (Matrix.of a) := rfl
    rw [e, hL _ ha] at h
    exact h.symm
  have right : ∀ a : PI.MtM m, Matrix.of a ∈ S → ∀ g : PI.MtM m → ℝ≥0∞, Measurable g →
      ∫⁻ y, g (mulM y a) ∂μ = ∫⁻ y, g y ∂μ := by
    intro a ha g hg
    have h := lintegral_map (μ := μ) hg (measurable_mulM measurable_id (measurable_const (a := a)))
    have e : (fun y : PI.MtM m => mulM (id y) a) = PI.rmulQ (Matrix.of a) := rfl
    rw [e, hR _ ha] at h
    exact h.symm
  obtain ⟨t, ht, -, ht0, ht1⟩ := Measure.exists_subset_measure_lt_top (μ := μ) (r := 0)
    MeasurableSet.univ (Measure.measure_univ_pos.mpr hne)
  set g : PI.MtM m → ℝ≥0∞ := t.indicator 1 with hgdef
  have hg : Measurable g := measurable_one.indicator ht
  have hgi : ∫⁻ y, g y ∂μ = μ t := lintegral_indicator_one ht
  have hfi : Measurable fun x => f (invM x) := hf.comp measurable_invM
  have key : (∫⁻ x, f (invM x) ∂μ) * μ t = (∫⁻ x, f x ∂μ) * μ t := by
    calc (∫⁻ x, f (invM x) ∂μ) * μ t
        = ∫⁻ x, ∫⁻ y, f (invM x) * g (mulM x y) ∂μ ∂μ := by
          rw [← lintegral_mul_const _ hfi]
          refine lintegral_congr_ae (hae.mono fun x hx => ?_)
          simp only
          have hm : Measurable fun y => g (mulM x y) :=
            hg.comp (measurable_mulM measurable_const measurable_id')
          rw [lintegral_const_mul _ hm, left x hx g hg, hgi]
      _ = ∫⁻ y, ∫⁻ x, f (invM x) * g (mulM x y) ∂μ ∂μ := by
          refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
          exact (hfi.comp measurable_fst).mul (hg.comp (measurable_mulM measurable_fst measurable_snd))
      _ = ∫⁻ y, ∫⁻ x, f (mulM y (invM x)) * g x ∂μ ∂μ := by
          refine lintegral_congr_ae (hae.mono fun y hy => ?_)
          simp only
          rw [← right y hy (fun x => f (mulM y (invM x)) * g x)
            ((hf.comp (measurable_mulM measurable_const measurable_invM)).mul hg)]
          refine lintegral_congr fun x => ?_
          congr 2
          apply Matrix.of.injective
          rw [of_mulM, of_invM, of_invM, of_mulM, Matrix.mul_inv_rev, ← Matrix.mul_assoc,
            (hinv _ hy).2, Matrix.one_mul]
      _ = ∫⁻ x, ∫⁻ y, f (mulM y (invM x)) * g x ∂μ ∂μ := by
          refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
          exact (hf.comp (measurable_mulM measurable_fst (measurable_invM.comp measurable_snd))).mul
            (hg.comp measurable_snd)
      _ = ∫⁻ x, (∫⁻ y, f y ∂μ) * g x ∂μ := by
          refine lintegral_congr_ae (hae.mono fun x hx => ?_)
          simp only
          have hm : Measurable fun y => f (mulM y (invM x)) :=
            hf.comp (measurable_mulM measurable_id' measurable_const)
          rw [lintegral_mul_const _ hm, right (invM x) (hinv _ hx).1 f hf]
      _ = (∫⁻ x, f x ∂μ) * μ t := by rw [lintegral_const_mul _ hg, hgi]
  exact (ENNReal.mul_left_inj ht0.ne' ht1.ne).mp key

end GlobalTheory.HaarInversion
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section
namespace GlobalTheory.MatHaar

open PI Topology

variable {m : ℕ}

abbrev Mx (m : ℕ) := Matrix (Fin m) (Fin m) ℂ

def invA (x : MtM m) : MtM m := Matrix.of.symm ((Matrix.of x : Mx m)⁻¹)

def mulA (p : MtM m × MtM m) : MtM m := (Matrix.of p.1 : Mx m) * (Matrix.of p.2 : Mx m)

def adjA (x : MtM m) : MtM m := (Matrix.of x : Mx m).adjugate

def detA (x : MtM m) : ℂ := (Matrix.of x : Mx m).det

theorem detA_cont : Continuous (detA (m := m)) := Continuous.matrix_det (continuous_id (X := Mx m))
theorem adjA_cont : Continuous (adjA (m := m)) := Continuous.matrix_adjugate (continuous_id (X := Mx m))

theorem invA_smul : (invA : MtM m → MtM m) = fun x => (detA x)⁻¹ • adjA x := by
  funext x
  show (Ring.inverse (Matrix.of x : Mx m).det • (Matrix.of x : Mx m).adjugate : Mx m) = _
  rw [Ring.inverse_eq_inv']; rfl

theorem invA_contOn : ContinuousOn (invA : MtM m → MtM m) {x | detA x ≠ 0} := by
  rw [invA_smul]
  exact (detA_cont.continuousOn.inv₀ (fun x hx => hx)).smul adjA_cont.continuousOn

theorem lmulQ_cont (a : Mx m) : Continuous (lmulQ a : MtM m → MtM m) := by
  unfold lmulQ
  exact (continuous_const (y := a)).matrix_mul (continuous_id (X := Mx m))

theorem mulA_cont : Continuous (mulA : MtM m × MtM m → MtM m) := by
  unfold mulA
  exact Continuous.matrix_mul (A := fun p : MtM m × MtM m => (Matrix.of p.1 : Mx m))
    (B := fun p : MtM m × MtM m => (Matrix.of p.2 : Mx m)) continuous_fst continuous_snd

theorem isUnit_det {G : Set (Mx m)} (hG : IsMatGroup G) {a : Mx m} (ha : a ∈ G) : IsUnit a.det :=
  Matrix.isUnit_det_of_right_inverse (hG.2.2.2 a ha).2

def amb (G : Set (Mx m)) : Set (MtM m) := {x | Matrix.of x ∈ G}

theorem amb_closed {G : Set (Mx m)} (hG : IsMatGroup G) : IsClosed (amb G) := hG.1

def Grp (G : Set (Mx m)) (_hG : IsMatGroup G) : Type := {x : MtM m // x ∈ amb G}

variable {G : Set (Mx m)} {hG : IsMatGroup G}

instance : TopologicalSpace (Grp G hG) := inferInstanceAs (TopologicalSpace {x : MtM m // x ∈ amb G})
instance : MeasurableSpace (Grp G hG) := inferInstanceAs (MeasurableSpace {x : MtM m // x ∈ amb G})
instance : BorelSpace (Grp G hG) := inferInstanceAs (BorelSpace {x : MtM m // x ∈ amb G})
instance : SecondCountableTopology (Grp G hG) :=
  inferInstanceAs (SecondCountableTopology {x : MtM m // x ∈ amb G})

def inc (x : Grp G hG) : MtM m := x.1

theorem inc_mem (x : Grp G hG) : Matrix.of (inc x) ∈ G := x.2

theorem inc_cont : Continuous (inc : Grp G hG → MtM m) := continuous_subtype_val

theorem inc_closedEmb : IsClosedEmbedding (inc : Grp G hG → MtM m) :=
  (amb_closed hG).isClosedEmbedding_subtypeVal

theorem inc_memb : MeasurableEmbedding (inc : Grp G hG → MtM m) :=
  MeasurableEmbedding.subtype_coe (amb_closed hG).measurableSet

theorem range_inc : Set.range (inc : Grp G hG → MtM m) = amb G := Subtype.range_coe

instance : LocallyCompactSpace (Grp G hG) := inc_closedEmb.locallyCompactSpace

instance : Group (Grp G hG) where
  mul a b := ⟨mulA (a.1, b.1), hG.2.2.1 _ a.2 _ b.2⟩
  one := ⟨(1 : Mx m), hG.2.1⟩
  inv a := ⟨invA a.1, (hG.2.2.2 _ a.2).1⟩
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc (Matrix.of a.1 : Mx m) (Matrix.of b.1) (Matrix.of c.1))
  one_mul a := Subtype.ext (Matrix.one_mul (Matrix.of a.1 : Mx m))
  mul_one a := Subtype.ext (Matrix.mul_one (Matrix.of a.1 : Mx m))
  inv_mul_cancel a := Subtype.ext (Matrix.nonsing_inv_mul (Matrix.of a.1 : Mx m) (isUnit_det hG a.2))

theorem inc_mul (a b : Grp G hG) : inc (a * b) = lmulQ (Matrix.of (inc a)) (inc b) := rfl

instance : IsTopologicalGroup (Grp G hG) where
  continuous_mul := by
    refine Continuous.subtype_mk (mulA_cont.comp ?_) _
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    refine Continuous.subtype_mk ?_ _
    exact invA_contOn.comp_continuous continuous_subtype_val (fun x => (isUnit_det hG x.2).ne_zero)

def pull (hG : IsMatGroup G) (μ : Measure (MtM m)) : Measure (Grp G hG) := μ.comap inc

theorem map_pull (μ : Measure (MtM m)) (h : μ {x | Matrix.of x ∉ G} = 0) : (pull hG μ).map inc = μ := by
  rw [pull, inc_memb.map_comap, range_inc]
  exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact h)

theorem pull_left (μ : Measure (MtM m)) (h : ∀ a ∈ G, μ.map (lmulQ a) = μ) : (pull hG μ).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext s hs
  rw [Measure.map_apply (continuous_const_mul g).measurable hs, pull, inc_memb.comap_apply, inc_memb.comap_apply]
  have e1 : (μ.map (lmulQ (Matrix.of (inc g)))) (inc '' s) = μ (inc '' s) :=
    congrArg (fun n : Measure (MtM m) => n (inc '' s)) (h (Matrix.of (inc g)) (inc_mem g))
  have e2 := Measure.map_apply (μ := μ) (lmulQ_cont (Matrix.of (inc g))).measurable (inc_memb.measurableSet_image.2 hs)
  rw [← e1, e2]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g * y, hy, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨g⁻¹ * z, ?_, ?_⟩
    · show g * (g⁻¹ * z) ∈ s
      rw [mul_inv_cancel_left]; exact hz
    · rw [inc_mul, hzx]
      exact Matrix.nonsing_inv_mul_cancel_left (Matrix.of (inc g) : Mx m) (Matrix.of x : Mx m)
        (isUnit_det hG (inc_mem g))

theorem pull_sigmaFinite (μ : Measure (MtM m)) [SigmaFinite μ] : SigmaFinite (pull hG μ) := by
  refine ⟨⟨⟨fun n => inc ⁻¹' spanningSets μ n, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · rw [pull, inc_memb.comap_apply]
    exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) (measure_spanningSets_lt_top μ n)
  · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]

theorem factor_pos_lt_top {X : Type*} [MeasurableSpace X] (μ ν : Measure X) [SigmaFinite μ] (h0 : μ ≠ 0)
    (c : ℝ≥0∞) (h : μ = c • ν) : 0 < c ∧ c < ⊤ := by
  refine ⟨pos_iff_ne_zero.2 fun hc => h0 (by rw [h, hc, zero_smul]), lt_top_iff_ne_top.2 fun hc => h0 ?_⟩
  rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets μ]
  refine measure_iUnion_null fun n => ?_
  have h1 := measure_spanningSets_lt_top μ n
  have h2 : μ (spanningSets μ n) = ⊤ * ν (spanningSets μ n) := by
    have := congrArg (fun ρ : Measure X => ρ (spanningSets μ n)) h
    simpa [hc] using this
  by_cases h3 : ν (spanningSets μ n) = 0
  · rw [h2, h3, mul_zero]
  · rw [h2, ENNReal.top_mul h3] at h1
    exact absurd h1 (lt_irrefl _)

def haar0 (hG : IsMatGroup G) : Measure (Grp G hG) := Measure.haar

instance : (haar0 hG).IsHaarMeasure := inferInstanceAs (Measure.IsHaarMeasure Measure.haar)

theorem eq_smul_haar (hG : IsMatGroup G) (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ μ = c • (haar0 hG).map inc := by
  obtain ⟨h1, h2, h3, h4⟩ := hμ
  have := pull_sigmaFinite (hG := hG) μ
  have := pull_left (hG := hG) μ h4
  have e := Measure.haarMeasure_unique (pull hG μ) (Classical.arbitrary _)
  have e' : μ = (pull hG μ (Classical.arbitrary (TopologicalSpace.PositiveCompacts (Grp G hG)) :
      TopologicalSpace.PositiveCompacts (Grp G hG))) • (haar0 hG).map inc := by
    rw [← Measure.map_smul _ inc_cont.measurable.aemeasurable]
    refine (map_pull (hG := hG) μ h3).symm.trans ?_
    exact congrArg (Measure.map inc) e
  obtain ⟨a, b⟩ := factor_pos_lt_top μ _ h2 _ e'
  exact ⟨_, a, b, e'⟩

theorem haar_unique_locFinite_openPos :
    ∀ (m : ℕ) (G : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsHaarOnM G μ →
      (∀ μ' : Measure (PI.MtM m), PI.IsHaarOnM G μ' → ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ μ' = c • μ) ∧
      (∀ K : Set (PI.MtM m), IsCompact K → (∀ x ∈ K, Matrix.of x ∈ G) → μ K < ⊤) ∧
      ∀ U : Set (PI.MtM m), IsOpen U → (∃ x ∈ U, Matrix.of x ∈ G) → 0 < μ U := by
  intro m G μ hG hμ
  obtain ⟨c, hc0, hct, hc⟩ := eq_smul_haar hG μ hμ
  refine ⟨fun μ' hμ' => ?_, fun K hK _ => ?_, fun U hU hx => ?_⟩
  · obtain ⟨d, hd0, hdt, hd⟩ := eq_smul_haar hG μ' hμ'
    refine ⟨d / c, ENNReal.div_pos hd0.ne' hct.ne, ENNReal.div_lt_top hdt.ne hc0.ne', ?_⟩
    rw [hd, hc, smul_smul, ENNReal.div_mul_cancel hc0.ne' hct.ne]
  · rw [hc, Measure.smul_apply, smul_eq_mul, inc_memb.map_apply]
    exact ENNReal.mul_lt_top hct (inc_closedEmb.isCompact_preimage hK).measure_lt_top
  · obtain ⟨x, hxU, hxG⟩ := hx
    rw [hc, Measure.smul_apply, smul_eq_mul, inc_memb.map_apply]
    exact ENNReal.mul_pos hc0.ne' ((hU.preimage inc_cont).measure_ne_zero _ ⟨⟨x, hxG⟩, hxU⟩)

end GlobalTheory.MatHaar

end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem unfold_integral_of_lintegral {S X Y E : Type*} [MeasurableSpace S] [MeasurableSpace X]
    [MeasurableSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Y) (σ : Measure S) (ν : Measure X) [SFinite σ] (m : S → X → Y)
    (hm : Measurable (fun q : S × X => m q.1 q.2))
    (hq : ∀ g : Y → ℝ≥0∞, Measurable g → ∫⁻ y, g y ∂μ = ∫⁻ x, ∫⁻ s, g (m s x) ∂σ ∂ν)
    (f : Y → E) (hf : StronglyMeasurable f) (hi : Integrable f μ) :
    (∀ᵐ x ∂ν, Integrable (fun s => f (m s x)) σ) ∧ Integrable (fun x => ∫ s, f (m s x) ∂σ) ν ∧
      ∫ y, f y ∂μ = ∫ x, (∫ s, f (m s x) ∂σ) ∂ν := by
  have hmx : ∀ x, Measurable (fun s => m s x) := fun x =>
    hm.comp (measurable_id.prodMk measurable_const)
  let η : ProbabilityTheory.Kernel X Y :=
    { toFun := fun x => σ.map (fun s => m s x)
      measurable' := by
        refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
        simp_rw [Measure.map_apply (hmx _) hA]
        exact measurable_measure_prodMk_right (hm hA) }
  have hη : ∀ x, η x = σ.map (fun s => m s x) := fun _ => rfl
  have hμ : (ProbabilityTheory.Kernel.comp η (ProbabilityTheory.Kernel.const Unit ν)) () = μ := by
    ext A hA
    rw [ProbabilityTheory.Kernel.comp_apply' _ _ _ hA, ProbabilityTheory.Kernel.const_apply,
      ← lintegral_indicator_one hA, hq _ (measurable_one.indicator hA)]
    refine lintegral_congr fun x => ?_
    rw [hη, ← lintegral_indicator_one hA, lintegral_map (measurable_one.indicator hA) (hmx x)]
  have hI : ∀ x, ∫ y, f y ∂η x = ∫ s, f (m s x) ∂σ := fun x => by
    rw [hη, integral_map (hmx x).aemeasurable hf.aestronglyMeasurable]
  rw [← hμ] at hi
  refine ⟨?_, ?_, ?_⟩
  · have h := hi.ae_of_comp
    rw [ProbabilityTheory.Kernel.const_apply] at h
    filter_upwards [h] with x hx
    rw [hη] at hx
    exact (integrable_map_measure hf.aestronglyMeasurable (hmx x).aemeasurable).1 hx
  · have h := hi.integral_comp
    rw [ProbabilityTheory.Kernel.const_apply] at h
    simpa only [hI] using h
  · have h := ProbabilityTheory.Kernel.integral_comp hi
    rw [ProbabilityTheory.Kernel.const_apply, hμ] at h
    simpa only [hI] using h

theorem weil_formula_integrable : ∀ (k r : ℕ) (μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)) [SFinite μS] (f : Formalism.QuantumDeterminants.Mt k r → ℂ), PI.BesselPeriodGGP.IsQuotMeas μG μS νq → Measurable f → Integrable f μG → (∀ᵐ x ∂νq, Integrable (fun s => f (fun i j => (Matrix.of s * Matrix.of x) i j)) μS) ∧ Integrable (fun x => ∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) νq ∧ ∫ x, f x ∂μG = ∫ x, (∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂νq := by
  intro k r μG μS νq _ f hq hf hi
  have hc : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of q.1 * Matrix.of q.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of q.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := continuous_fst
    have h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of q.2 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := continuous_snd
    exact h1.matrix_mul h2
  exact unfold_integral_of_lintegral μG μS νq
    (fun s x => (fun i j => (Matrix.of s * Matrix.of x) i j : Formalism.QuantumDeterminants.Mt k r))
    hc.measurable hq f hf.stronglyMeasurable hi

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_perm_of_range_eq {t : ℕ} {β : Type} (a a₂ : Fin t → β)
    (ha : Function.Injective a) (ha₂ : Function.Injective a₂) (h : Set.range a = Set.range a₂) :
    ∃ τ : Equiv.Perm (Fin t), a = a₂ ∘ τ := by
  refine ⟨(Equiv.ofInjective a ha).trans ((Set.equivOfEq h).trans (Equiv.ofInjective a₂ ha₂).symm), ?_⟩
  funext i
  simp [Equiv.apply_ofInjective_symm]

theorem qminor_eq_smul_of_range_eq : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a a₂ b b₂ : Fin t → Fin n), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective a₂ → Function.Injective b → Function.Injective b₂ → Set.range a = Set.range a₂ → Set.range b = Set.range b₂ → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u, Formalism.REAL.qminor E a b u = e • Formalism.REAL.qminor E a₂ b₂ u := by
  intro A _ _ n t E a a₂ b b₂ hE ha ha₂ hb hb₂ hra hrb
  obtain ⟨σ, rfl⟩ := exists_perm_of_range_eq a a₂ ha ha₂ hra
  obtain ⟨τ, rfl⟩ := exists_perm_of_range_eq b b₂ hb hb₂ hrb
  refine ⟨(((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ) : ℤ) : ℂ), ?_, fun u => ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h' | h' <;> simp [h, h']
  · rw [Formalism.REAL.quantumMinorRowSkew_holds A n t E a₂ (b₂ ∘ τ) σ u, Formalism.REAL.quantumMinorColSkew_holds A n t E hE a₂ b₂ τ u,
      Int.cast_smul_eq_zsmul, zsmul_eq_mul, ← mul_assoc, Int.cast_mul]

end GlobalTheory
end
