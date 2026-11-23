module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle001
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false
noncomputable section
open Topology Filter
open scoped ContDiff Matrix ComplexOrder

namespace GlobalTheory.GoodMetric.SmoothMetric

theorem exists_partition {F : Type} [Field F] (σ : F →+* ℂ) (X : Var F)
    (W : CxPts X.str σ → Set (CxPts X.str σ)) (hWo : ∀ y, IsOpen (W y)) (hW : ∀ y, y ∈ W y) :
    ∃ (n : ℕ) (pt : Fin n → CxPts X.str σ) (χ : Fin n → CxPts X.str σ → ℝ),
      (∀ j y, 0 ≤ χ j y) ∧ (∀ y, ∑ j, χ j y = 1) ∧ (∀ j, tsupport (χ j) ⊆ W (pt j)) ∧
      ∀ j y, CInfAt (χ j) y := by
  classical
  haveI := CxPts.compactSpace σ X.isProjOver
  have hc : ∀ y, ∃ c : AlgChart X.str σ X.dim, y ∈ c.e.source ∧ c.e.source ⊆ W y := fun y => by
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (p := X.str) (σ := σ) (D := X.dim) y
    exact ⟨c.restr (W y) (hWo y), ⟨hc, hW y⟩, Set.inter_subset_right⟩
  choose c hcy hcW using hc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (c y).e.source)
    (fun y => (c y).e.open_source) (fun y _ => Set.mem_iUnion.2 ⟨y, hcy y⟩)
  let pt : Fin t.card → CxPts X.str σ := fun j => (t.equivFin.symm j).1
  let Lc := EuclideanSpace.equiv (Fin X.dim) ℂ
  let L := Lc.toHomeomorph
  let e : Fin t.card → OpenPartialHomeomorph (CxPts X.str σ) (Fin X.dim → ℂ) :=
    fun j => (c (pt j)).e.transHomeomorph L
  have hcov : ∀ y, ∃ j, y ∈ (e j).source := by
    intro y
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    refine ⟨t.equivFin ⟨x, hx⟩, ?_⟩
    simpa [e, pt] using hy
  have htr : ∀ i j, ContDiffOn ℝ ∞ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source) := by
    intro i j
    have ho := isOpen_over (c (pt i)).e (c (pt j)).e.open_source
    have hg : ContDiffOn ℂ ∞ ((c (pt j)).e ∘ (c (pt i)).e.symm)
        ((c (pt i)).e.target ∩ (c (pt i)).e.symm ⁻¹' (c (pt j)).e.source) :=
      contDiffOn_euclidean.2 fun a => ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ _ ho
        (differentiableOn_euclidean.1 ((c (pt i)).holo_trans (c (pt j))) a)
    have h2 := (Lc.contDiff.restrict_scalars ℝ).comp_contDiffOn
      ((hg.restrict_scalars ℝ).comp (Lc.symm.contDiff.restrict_scalars ℝ).contDiffOn
        (s := Lc.symm ⁻¹' ((c (pt i)).e.target ∩ (c (pt i)).e.symm ⁻¹' (c (pt j)).e.source)) ?_)
    · refine h2.congr_mono ?_ ?_
      · intro v hv
        simp [e, L, Lc]
      · intro v hv
        simpa [e, L, Lc] using hv
    · intro v hv
      simpa using hv
  obtain ⟨χ, h0, h1, hs, hd⟩ := ReciprocityTheory.AnForm.exists_chart_partition e hcov htr
  refine ⟨t.card, pt, χ, h0, h1, fun j => (hs j).trans (hcW (pt j)), fun j y => ?_⟩
  obtain ⟨i, hi⟩ := hcov y
  have hi' : y ∈ (c (pt i)).e.source := hi
  refine cInfAt_of_chart (c (pt i)).e.open_source (c (pt i)) ?_ hi' hi'
  have h3 := (hd j i).comp (Lc.contDiff.restrict_scalars ℝ).contDiffOn
    (s := (c (pt i)).e.target) (fun v hv => by simpa [e, L, Lc] using hv)
  refine h3.congr_mono ?_ Set.inter_subset_left
  intro v hv
  simp [e, L, Lc]

end GlobalTheory.GoodMetric.SmoothMetric

namespace GlobalTheory.GoodMetric.SmoothMetric

theorem cInfAt_sum {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {κ : Type}
    (s : Finset κ) (f : κ → CxPts X.str σ → ℝ) {y : CxPts X.str σ} (h : ∀ j ∈ s, CInfAt (f j) y) :
    CInfAt (fun z => ∑ j ∈ s, f j z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (p := X.str) 0 y
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem exists_isMetricOn_top : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m 0), ∃ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H := by
  intro F _ σ X ι _ m E
  classical
  choose U A hz hA hU using fun y : CxPts X.str σ => E.loc (under y)
  obtain ⟨n, pt, χ, h0, h1, hs, hd⟩ := exists_partition σ X (fun y => ptsIn X.str σ (U y))
    (fun y => isOpen_ptsIn _) (fun y => mem_ptsIn.2 (hz y))
  let T : Fin n → Mat m X.Fn → CxPts X.str σ → Mat m ℂ := fun j B z => (B * (A (pt j))⁻¹).map (ratVal · z)

  have hpar : ∀ j y, y ∈ tsupport (χ j) → ∀ B ∈ E.S (under y),
      Par 0 ((ratOf X).O (under y)).toSubring (B * (A (pt j))⁻¹) := fun j y hy B hB =>
    (hU (pt j) (under y) (mem_ptsIn.1 (hs j hy)) B).1 hB
  have hpar' : ∀ j y, χ j y ≠ 0 → ∀ B ∈ E.S (under y),
      Par 0 ((ratOf X).O (under y)).toSubring (B * (A (pt j))⁻¹) := fun j y hy =>
    hpar j y (subset_tsupport _ hy)
  refine ⟨fun B z τ => ∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ), ⟨?_, ?_, ?_⟩⟩
  · intro y _ B hB τ
    obtain ⟨j, hj⟩ : ∃ j, χ j y ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      have := h1 y
      simp [hne] at this
    have hpos : 0 < χ j y := lt_of_le_of_ne (h0 j y) (Ne.symm hj)
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := X) (σ := σ) y
    have hdet := ((hpar' j y hj B hB).map_of (ratVal · y) ψ hψ).det_ne τ
    have hPD : (((χ j y : ℝ) : ℂ) • (T j B y τ * (T j B y τ)ᴴ)).PosDef :=
      Matrix.PosDef.smul (Matrix.PosDef.mul_conjTranspose_self _ (Matrix.vecMul_injective_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det _).2 hdet.isUnit))) (by exact_mod_cast hpos)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    refine hPD.add_posSemidef (Matrix.posSemidef_sum _ fun i _ => ?_)
    exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (Complex.zero_le_real.2 (h0 i y))
  · intro y _ B hB τ i k
    have key : ∀ g : ℂ →L[ℝ] ℝ, CInfAt (fun z =>
        g ((∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ)) i k)) y := by
      intro g
      have e : (fun z => g ((∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ)) i k)) =
          fun z => ∑ j ∈ Finset.univ, χ j z * g ((T j B z τ * (T j B z τ)ᴴ) i k) := by
        funext z

        rw [Matrix.sum_apply, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.smul_apply, smul_eq_mul, ← Complex.real_smul, map_smul, smul_eq_mul]
      rw [e]
      refine cInfAt_sum _ _ fun j _ => ?_
      by_cases hy : y ∈ tsupport (χ j)
      · have hr (x : Fin (m τ) × Fin (m τ)) : RegAt (under y) ((B * (A (pt j))⁻¹) τ x.1 x.2) :=
          mem_O_ratOf.1 ((hpar j y hy B hB τ).1 _ _)
        have hG : ContDiff ℝ (⊤ : ℕ∞) fun w : Fin (m τ) × Fin (m τ) → ℂ => ∑ l, w (i, l) * star (w (k, l)) :=
          ContDiff.sum fun l _ => (contDiff_apply ℝ (fun _ => ℂ) _).mul (Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) _))
        refine ((hd j y).comp₂ (cInfAt_ratVal hr (g.contDiff.comp hG))
          (contDiff_fst.mul contDiff_snd)).congr (Eventually.of_forall fun z => ?_)
        simp [T, Matrix.mul_apply, Mat.map]
      · have hz : χ j =ᶠ[𝓝 y] fun _ => 0 := by
          rw [tsupport, ← Set.mem_compl_iff] at hy
          filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with z hz'
          exact Function.notMem_support.1 fun h => hz' (subset_closure h)
        refine (cInfAt_const (p := X.str) 0 y).congr ?_
        filter_upwards [hz] with z hz'
        simp [hz']
    exact ⟨key Complex.reCLM, key Complex.imCLM⟩
  · intro y _ B hB B' hB' τ
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := X) (σ := σ) y
    have hBB : Par 0 ((ratOf X).O (under y)).toSubring (B' * B⁻¹) := (Fr.mem_iff hB).1 hB'
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : χ j y = 0
    · simp [hj]
    have e := Par.map_mul_of hBB (hpar' j y hj B hB) (ratVal · y) ψ hψ
    rw [mul_assoc, ← mul_assoc B⁻¹, Mat.inv_mul (Fr.det_ne hB), one_mul] at e
    simp only [T]
    rw [e, Pi.mul_apply, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

end GlobalTheory.GoodMetric.SmoothMetric
end
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.ChernMeas

def measPoly (X σ : Type) [MeasurableSpace X] : Subalgebra ℝ (X → MvPolynomial σ ℂ) where
  carrier := {f | ∀ d, Measurable fun x => AddMonoidAlgebra.coeff (f x) d}
  mul_mem' := by
    classical
    intro f g hf hg d
    simp only [Pi.mul_apply, coeff_mul]
    exact Finset.measurable_sum _ fun p _ => (hf p.1).mul (hg p.2)
  add_mem' := by
    intro f g hf hg d
    simp only [Pi.add_apply, MvPolynomial.coeff_add]
    exact (hf d).add (hg d)
  algebraMap_mem' := by
    intro c d
    exact measurable_const (a := AddMonoidAlgebra.coeff (algebraMap ℝ (MvPolynomial σ ℂ) c) d)

theorem C_mem {X σ : Type} [MeasurableSpace X] {f : X → ℂ} (hf : Measurable f) :
    (fun x => (C (f x) : MvPolynomial σ ℂ)) ∈ measPoly X σ := by
  classical
  intro d
  simp only [coeff_C]
  split_ifs
  · exact hf
  · exact measurable_const

theorem const_mem {X σ : Type} [MeasurableSpace X] (p : MvPolynomial σ ℂ) :
    (fun _ : X => p) ∈ measPoly X σ := fun _ => measurable_const

def evalAt {X σ : Type} [MeasurableSpace X] (x : X) : measPoly X σ →ₐ[ℝ] MvPolynomial σ ℂ :=
  (Pi.evalAlgHom ℝ (fun _ : X => MvPolynomial σ ℂ) x).comp (measPoly X σ).val

theorem charpolyRev_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {r : Type} [Fintype r] [DecidableEq r]
    (M : Matrix r r A) : (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem measurable_curv {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (ξ η : V n) (i j : r) :
    Measurable fun v => curv G v ξ η i j := by
  let f : V n → ℂ := fun x => conn G x ξ i j
  change Measurable fun v => -((1 / 2 : ℂ) * (fderiv ℝ f v η + Complex.I * fderiv ℝ f v (Complex.I • η)))
  exact (((measurable_fderiv_apply_const ℝ f η).add
    ((measurable_fderiv_apply_const ℝ f (Complex.I • η)).const_mul _)).const_mul _).neg

theorem curvPoly_mem {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (i j : r) :
    (fun v => curvPoly G v i j) ∈ measPoly (V n) (Fin n × Fin n) := by
  have e : (fun v => curvPoly G v i j) = ∑ a, ∑ b, (fun v => (C (curv G v (coordVec a) (coordVec b) i j) :
      MvPolynomial (Fin n × Fin n) ℂ)) * fun _ => X (a, b) := by
    funext v
    simp [curvPoly, Finset.sum_apply]
  rw [e]
  exact Subalgebra.sum_mem _ fun a _ => Subalgebra.sum_mem _ fun b _ =>
    Subalgebra.mul_mem _ (C_mem (measurable_curv G _ _ i j)) (const_mem _)

theorem chernPoly_mem {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (k : ℕ) :
    (fun v => chernPoly G v k) ∈ measPoly (V n) (Fin n × Fin n) := by
  let M : Matrix r r (measPoly (V n) (Fin n × Fin n)) := Matrix.of fun i j => ⟨_, curvPoly_mem G i j⟩
  have e : (fun v => chernPoly G v k) = ((Matrix.charpolyRev (-M)).coeff k).1 := by
    funext v
    have h : -curvPoly G v = (-M).map (evalAt v).toRingHom := by
      ext i j : 2
      rfl
    rw [chernPoly, h, charpolyRev_map, Polynomial.coeff_map]
    rfl
  rw [e]
  exact Subtype.property _

theorem measurable_chernTop {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ) :
    Measurable (fun v => chernTop R G v) := by
  let P : measPoly (V n) (Fin n × Fin n) :=
    aeval (fun x : ι × ℕ => (⟨_, chernPoly_mem (fun u => G u x.1) x.2⟩ : measPoly (V n) (Fin n × Fin n))) R
  have e (v : V n) : aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) R = P.1 v := by
    change _ = evalAt v P
    rw [← AlgHom.comp_apply, comp_aeval]
    rfl
  simp only [chernTop, e, topCoeff]
  refine Measurable.const_mul (Complex.measurable_re.comp ?_) _
  exact Finset.measurable_sum _ fun w _ => (P.2 _).const_mul _

end GlobalTheory.ChernMeas
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial MeasureTheory
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal

namespace GlobalTheory.ChernScale

section General

variable {α : Type*} [MeasurableSpace α] {κ : Sort*}

theorem restrict_iSup_eq (μ : κ → Measure α) {S : Set α} (hS : MeasurableSet S) :
    (⨆ i, μ i).restrict S = ⨆ i, (μ i).restrict S := by
  refine le_antisymm ?_ (iSup_le fun i => Measure.restrict_mono subset_rfl (le_iSup μ i))
  have h : (⨆ i, μ i) ≤ (⨆ i, (μ i).restrict S) + (⨆ i, μ i).restrict Sᶜ := by
    refine iSup_le fun i => Measure.le_iff.2 fun B hB => ?_
    rw [← Measure.restrict_add_restrict_compl (μ := μ i) hS, Measure.add_apply, Measure.add_apply]
    exact add_le_add (Measure.le_iff'.1 (le_iSup (fun i => (μ i).restrict S) i) B)
      (Measure.le_iff'.1 (Measure.restrict_mono subset_rfl (le_iSup μ i)) B)
  calc (⨆ i, μ i).restrict S ≤ ((⨆ i, (μ i).restrict S) + (⨆ i, μ i).restrict Sᶜ).restrict S :=
        Measure.restrict_mono subset_rfl h
    _ = (⨆ i, (μ i).restrict S).restrict S := by
        rw [Measure.restrict_add, Measure.restrict_restrict hS, Set.inter_compl_self,
          Measure.restrict_empty, add_zero]
    _ ≤ _ := Measure.restrict_le_self

theorem smul_iSup_eq (ν : κ → Measure α) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    c • (⨆ i, ν i) = ⨆ i, c • ν i := by
  have mono : ∀ (d : ℝ≥0∞) {μ μ' : Measure α}, μ ≤ μ' → d • μ ≤ d • μ' := fun d μ μ' h =>
    Measure.le_iff.2 fun s _ => by
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' le_rfl <| Measure.le_iff'.1 h s
  rcases eq_or_ne c 0 with rfl | h0
  · simp only [zero_smul]
    exact (le_antisymm (iSup_le fun _ => le_rfl) (Measure.zero_le _)).symm
  refine le_antisymm ?_ (iSup_le fun i => mono c (le_iSup ν i))
  have key : (⨆ i, ν i) ≤ c⁻¹ • ⨆ i, c • ν i := iSup_le fun i => by
    calc ν i = c⁻¹ • c • ν i := by rw [smul_smul, ENNReal.inv_mul_cancel h0 hc, one_smul]
      _ ≤ _ := mono _ (le_iSup (fun i => c • ν i) i)
  calc c • (⨆ i, ν i) ≤ c • c⁻¹ • ⨆ i, c • ν i := mono c key
    _ = _ := by rw [smul_smul, ENNReal.mul_inv_cancel h0 hc, one_smul]

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {n : ℕ}

theorem chartMeas_restrict_eq (e : OpenPartialHomeomorph X (V n)) {ρ ρ' : X → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : c ≠ ⊤) {S : Set X} (hS : MeasurableSet S) (h : ∀ y ∈ e.source, y ∈ S → ρ y = c * ρ' y) :
    (chartMeas e ρ).restrict S = c • (chartMeas e ρ').restrict S := by
  ext B hB
  rw [Measure.smul_apply, Measure.restrict_apply hB, Measure.restrict_apply hB, smul_eq_mul,
    chartMeas_apply e ρ (hB.inter hS), chartMeas_apply e ρ' (hB.inter hS), ← lintegral_const_mul' c _ hc]
  refine setLIntegral_congr_fun (measurableSet_image e (e.open_source.measurableSet.inter (hB.inter hS))
    Set.inter_subset_left) ?_
  rintro _ ⟨y, hy, rfl⟩
  show ρ (e.symm (e y)) = c * ρ' (e.symm (e y))
  rw [e.left_inv hy.1]
  exact h y hy.1 hy.2.2

theorem glueMeas_restrict_eq {ι : Type*} (e : ι → OpenPartialHomeomorph X (V n)) {ρ ρ' : ι → X → ℝ≥0∞}
    {c : ℝ≥0∞} (hc : c ≠ ⊤) {S : Set X} (hS : MeasurableSet S)
    (h : ∀ i, ∀ y ∈ (e i).source, y ∈ S → ρ i y = c * ρ' i y) :
    (glueMeas e ρ).restrict S = c • (glueMeas e ρ').restrict S := by
  rw [glueMeas, glueMeas, restrict_iSup_eq _ hS, restrict_iSup_eq _ hS, smul_iSup_eq _ hc]
  exact iSup_congr fun i => chartMeas_restrict_eq (e i) hc hS (h i)

end General

end GlobalTheory.ChernScale

namespace GlobalTheory.GoodMetric

open GlobalTheory.ChernScale

theorem hasChernIntegral_of_eq_mul : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}
    (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
    (R R₀ : MvPolynomial (ι × ℕ) ℝ) (t v : ℝ),
    (∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ A ∈ E.S (under y),
      chernTop R (fun w => H A (c.e.symm w)) (c.e y) = t * chernTop R₀ (fun w => H A (c.e.symm w)) (c.e y)) →
    HasChernIntegral E O H R₀ v → HasChernIntegral E O H R (t * v) := by
  intro F _ σ X ι m E O H R R₀ t v hRt hv
  have hP : MeasurableSet (ptsIn X.str σ O) := (isOpen_ptsIn O).measurableSet
  have key : ∀ (ε ε' : ℤˣ) (c : ℝ), 0 ≤ c → (∀ x : ℝ, ((ε : ℤ) : ℝ) * (t * x) = c * (((ε' : ℤ) : ℝ) * x)) →
      chernTopPart E H R ε (ptsIn X.str σ O) =
        ENNReal.ofReal c * chernTopPart E H R₀ ε' (ptsIn X.str σ O) := by
    intro ε ε' c hc hx
    have hm : (chernTopPart E H R ε).restrict (ptsIn X.str σ O) =
        ENNReal.ofReal c • (chernTopPart E H R₀ ε').restrict (ptsIn X.str σ O) :=
      glueMeas_restrict_eq _ ENNReal.ofReal_ne_top hP fun a y hy hyS => ?_
    · have := congrArg (fun μ : Measure (CxPts X.str σ) => μ (ptsIn X.str σ O)) hm
      simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_self] using this
    · have e1 := hRt y hyS a hy _ (E.nonempty (under y)).choose_spec
      beta_reduce
      rw [e1, hx, ENNReal.ofReal_mul hc]
  rcases le_or_gt 0 t with ht | ht
  · refine ⟨fun ε => ?_, ?_⟩
    · rw [key ε ε t ht (fun x => by ring)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hv.1 ε)
    · rw [← hv.2, measureReal_def, measureReal_def, measureReal_def, measureReal_def,
        key 1 1 t ht (fun x => by ring), key (-1) (-1) t ht (fun x => by ring),
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht]
      ring
  · have ht' : 0 ≤ -t := by linarith
    refine ⟨fun ε => ?_, ?_⟩
    · rw [key ε (-ε) (-t) ht' (fun x => by rw [Units.val_neg, Int.cast_neg]; ring)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hv.1 _)
    · rw [← hv.2, measureReal_def, measureReal_def, measureReal_def, measureReal_def,
        key 1 (-1) (-t) ht' (fun x => by push_cast; ring), key (-1) 1 (-t) ht' (fun x => by push_cast; ring),
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht']
      ring

end GlobalTheory.GoodMetric
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial MeasureTheory
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric

namespace GlobalTheory

theorem iSup_measure_apply_eq_zero {α κ : Type*} [MeasurableSpace α] (μ : κ → Measure α) {S : Set α}
    (hS : MeasurableSet S) (h : ∀ i, μ i S = 0) : (⨆ i, μ i) S = 0 := by
  have hle : (⨆ i, μ i) ≤ (⨆ i, μ i).restrict Sᶜ := by
    refine iSup_le fun i => ?_
    calc μ i = (μ i).restrict Sᶜ :=
          (Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.1 (h i))).symm
      _ ≤ (⨆ i, μ i).restrict Sᶜ := Measure.restrict_mono subset_rfl (le_iSup μ i)
  refine le_antisymm ?_ (zero_le)
  calc (⨆ i, μ i) S ≤ (⨆ i, μ i).restrict Sᶜ S := Measure.le_iff'.1 hle S
    _ = 0 := by rw [Measure.restrict_apply hS, Set.inter_compl_self, measure_empty]

theorem chernTopPart_neg_eq_zero_of_nonneg {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}
    (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
    (R : MvPolynomial (ι × ℕ) ℝ)
    (h : ∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ A ∈ E.S (under y),
      0 ≤ chernTop R (fun w => H A (c.e.symm w)) (c.e y)) :
    chernTopPart E H R (-1) (ptsIn X.str σ O) = 0 := by
  have hS : MeasurableSet (ptsIn X.str σ O) := (isOpen_ptsIn O).measurableSet
  unfold chernTopPart glueMeas
  refine iSup_measure_apply_eq_zero _ hS fun c => ?_
  rw [chartMeas_apply c.e _ hS]
  have hm : MeasurableSet (c.e '' (c.e.source ∩ ptsIn X.str σ O)) :=
    measurableSet_image c.e (c.e.open_source.measurableSet.inter hS) Set.inter_subset_left
  rw [setLIntegral_congr_fun hm (g := fun _ => 0) ?_, MeasureTheory.lintegral_zero]
  rintro _ ⟨y, ⟨hys, hyS⟩, rfl⟩
  have hz : c.e.symm (c.e y) ∈ c.e.source ∩ ptsIn X.str σ O := by
    rw [c.e.left_inv hys]; exact ⟨hys, hyS⟩
  beta_reduce
  generalize c.e.symm (c.e y) = z at hz ⊢
  apply ENNReal.ofReal_eq_zero.2
  have := h z hz.2 c hz.1 _ (E.nonempty (under z)).choose_spec
  push_cast
  linarith

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.PointFormSign

def domGram (m r : ℕ) (x : Fin m → Fin r → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ((1 - Matrix.of x * (Matrix.of x)ᴴ)⁻¹)ᵀ

def IsNegSq {E : Type*} [AddCommGroup E] [Module ℂ E] {m : ℕ} (F : E → E → Matrix (Fin m) (Fin m) ℂ) (r : ℕ) : Prop :=
  ∃ (S : Matrix (Fin m) (Fin m) ℂ) (T : E →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ), IsUnit S.det ∧
    ∀ ξ η, F ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S

def sqPoly {n m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ a, ∑ b, C ((T (coordVec a) * (T (coordVec b))ᴴ) i j) * X (a, b)

end GlobalTheory.PointFormSign
end
end
