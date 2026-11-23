module

public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle006
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EisensteinLatticeSumBound
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsCuspReductionBound
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle010
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.ModDet

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

theorem map_mul_unit (lam : Measure K) [lam.IsAddHaarMeasure] (u : Kˣ) :
    lam.map (fun y => (u : K) * y) = (distribHaarChar K u)⁻¹ • lam := by
  have hm : Measurable (fun y : K => (u : K) * y) :=
    (continuous_const.mul continuous_id).measurable
  ext s hs
  rw [Measure.map_apply hm hs, Measure.smul_apply, Measure.nnreal_smul_coe_apply, ← map_inv,
    distribHaarChar_mul lam u⁻¹ s]
  congr 1
  ext y
  simp [Set.mem_inv_smul_set_iff, Units.smul_def]

theorem pi_smul_const {ι : Type} [Fintype ι] (lam : Measure K) [SigmaFinite lam] (c : ι → ℝ≥0) :
    Measure.pi (fun i => c i • lam) = (∏ i, c i) • Measure.pi (fun _ : ι => lam) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    ENNReal.ofNNReal_finsetProd]

theorem pi_map_diag {ι : Type} [Fintype ι] (lam : Measure K) [lam.IsAddHaarMeasure] (D : ι → Kˣ) :
    (Measure.pi fun _ : ι => lam).map (fun x i => (D i : K) * x i) =
      (∏ i, (distribHaarChar K (D i))⁻¹) • Measure.pi fun _ : ι => lam := by
  have hm : ∀ i, Measurable (fun y : K => (D i : K) * y) := fun i =>
    (continuous_const.mul continuous_id).measurable
  have hs : ∀ i, SigmaFinite (lam.map (fun y : K => (D i : K) * y)) := fun i => by
    rw [map_mul_unit]; infer_instance
  rw [Measure.pi_map_pi (fun i => (hm i).aemeasurable)]
  simp_rw [map_mul_unit]
  exact pi_smul_const lam _

theorem smul_cancel (lam : Measure K) [lam.IsAddHaarMeasure] {a b : ℝ≥0}
    (h : a • lam = b • lam) : a = b := by
  obtain ⟨C, hC, hn⟩ := exists_compact_mem_nhds (0 : K)
  have h0 : lam C ≠ 0 := (Measure.measure_pos_of_mem_nhds lam hn).ne'
  have h1 : lam C ≠ ∞ := hC.measure_lt_top.ne
  have e := congrArg (fun m : Measure K => m C) h
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at e
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 h1).1 e)

theorem map_transvections {ι : Type} [Fintype ι] [DecidableEq ι] (μ : Measure (ι → K))
    [μ.IsAddHaarMeasure] (L : List (Matrix.TransvectionStruct ι K)) :
    μ.map (fun x => (L.map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) = μ := by
  induction L with
  | nil => simp
  | cons t L ih =>
    have hm : ∀ M : Matrix ι ι K, Measurable (fun x : ι → K => M *ᵥ x) := fun M =>
      (continuous_const.matrix_mulVec continuous_id).measurable
    have e : (fun x : ι → K => ((t :: L).map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) =
        (fun x => t.toMatrix *ᵥ x) ∘
          (fun x => (L.map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) := by
      funext x
      simp [Matrix.mulVec_mulVec]
    rw [e, ← Measure.map_map (hm _) (hm _), ih]
    exact GlobalTheory.T.haar_invariant_under_transvection K ι μ t

theorem det_transvections {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : List (Matrix.TransvectionStruct ι K)) :
    ((L.map Matrix.TransvectionStruct.toMatrix).prod).det = 1 := by
  induction L with
  | nil => simp
  | cons t L ih => simp [Matrix.det_mul, ih, Matrix.TransvectionStruct.det]

theorem map_mulVec_eq_smul : ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K]
    [BorelSpace K] [IsArtinianRing K] [IsReduced K] (ι : Type) [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → K)) [μ.IsAddHaarMeasure] (lam : Measure K) [lam.IsAddHaarMeasure]
    (A : Matrix ι ι K), IsUnit A.det → ∀ c : ℝ≥0,
      lam.map (fun y => A.det * y) = c • lam → μ.map (fun x => A *ᵥ x) = c • μ := by
  intro K _ _ _ _ _ _ _ _ _ _ ι _ _ μ _ lam _ A hA c hc
  obtain ⟨L, L', D, hAeq⟩ := GlobalTheory.T.matrix_transvection_diagonal_decomposition K ι A
  have hdet : A.det = ∏ i, D i := by
    rw [hAeq, Matrix.det_mul, Matrix.det_mul, det_transvections, det_transvections,
      Matrix.det_diagonal, one_mul, mul_one]
  have hu : ∀ i, IsUnit (D i) := fun i => by
    have h := hA
    rw [hdet, ← Finset.mul_prod_erase Finset.univ D (Finset.mem_univ i)] at h
    exact isUnit_of_mul_isUnit_left h
  obtain ⟨Du, hDu⟩ : ∃ Du : ι → Kˣ, ∀ i, (Du i : K) = D i :=
    ⟨fun i => (hu i).unit, fun i => (hu i).unit_spec⟩
  have hcc : (∏ i, (distribHaarChar K (Du i))⁻¹) = c := by
    refine smul_cancel lam ?_
    rw [← hc, hdet]
    have e : (∏ i, D i) = ((∏ i, Du i : Kˣ) : K) := by
      simp [Units.coe_prod, hDu]
    rw [e, map_mul_unit, map_prod, Finset.prod_inv_distrib]
  have hμ := Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : ι => lam)
  have hmd : Measurable (fun (x : ι → K) i => (Du i : K) * x i) :=
    (continuous_pi fun i => continuous_const.mul (continuous_apply i)).measurable
  have hdiag : μ.map (fun (x : ι → K) i => (Du i : K) * x i) = c • μ := by
    rw [hμ, Measure.map_smul, pi_map_diag, hcc, smul_comm]
    exact hmd.aemeasurable
  have hm : ∀ M : Matrix ι ι K, Measurable (fun x : ι → K => M *ᵥ x) := fun M =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have e : (fun x : ι → K => A *ᵥ x) =
      (fun x => (L.map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) ∘
        (fun (x : ι → K) i => (Du i : K) * x i) ∘
          (fun x => (L'.map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) := by
    funext x
    have hd : ∀ y : ι → K, (fun i => (Du i : K) * y i) = Matrix.diagonal D *ᵥ y := fun y => by
      funext i
      simp [Matrix.mulVec_diagonal, hDu]
    simp only [Function.comp_apply, hd, Matrix.mulVec_mulVec]
    rw [hAeq, Matrix.mul_assoc]
  rw [e, ← Measure.map_map (hm _) (hmd.comp (hm _)), ← Measure.map_map hmd (hm _),
    map_transvections μ L', hdiag, Measure.map_smul, map_transvections μ L]
  exact (hm _).aemeasurable

end GlobalTheory.CompanionTheory.SW.ModDet
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.eisenstein_lattice_sum_bound : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ M : ℕ, 2 ≤ M → ∀ t : ℝ, 0 < t → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, t ≤ (τ w).im) → Summable (fun r : 𝓞 F => (∏ w, ‖τ w + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹) ∧ ∑' r : 𝓞 F, (∏ w, ‖τ w + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹ ≤ C * ∏ w, (τ w).im * ((τ w).im ^ M)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.SW.LatSum.lattice_sum | exact GlobalTheory.CompanionTheory.SW.LatSum.lattice_sum | (intros; apply GlobalTheory.CompanionTheory.SW.LatSum.lattice_sum <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.exists_cusp_reduction_bound : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∃ c d : 𝓞 F, (c ≠ 0 ∨ d ≠ 0) ∧ ∀ w, ‖((ρ w (c : F) : ℝ) : ℂ) * τ w + (ρ w (d : F) : ℝ)‖ ^ 2 ≤ C * (τ w).im := by
  first | exact @GlobalTheory.CompanionTheory.SW.SmallPair.exists_small_pair | exact GlobalTheory.CompanionTheory.SW.SmallPair.exists_small_pair | (intros; apply GlobalTheory.CompanionTheory.SW.SmallPair.exists_small_pair <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TailConst

theorem tail_eq_mul_tail_insert {ι : Type} [DecidableEq ι] (a : ι → ℝ)
    (hs : Summable (fun v => |a v - 1|)) (S : Finset ι) (v : ι) (hv : v ∉ S) :
    ∏' w : {w // w ∉ S}, a w.1 = a v * ∏' w : {w // w ∉ insert v S}, a w.1 := by
  have h := (GlobalTheory.T.infinite_product_multipliable {w // w ∉ S} (fun w => a w.1)
    (hs.comp_injective Subtype.val_injective)).2.1 {⟨v, hv⟩}
  rw [h.2, Finset.prod_singleton]
  congr 1
  let e : {w : {w // w ∉ S} // w ∉ ({⟨v, hv⟩} : Finset {w // w ∉ S})} ≃
      {w // w ∉ insert v S} :=
    { toFun := fun x => ⟨x.1.1, by
        have h1 := x.1.2
        have h2 := x.2
        simp only [Finset.mem_singleton] at h2
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h3 => h2 (Subtype.ext h3), h1⟩⟩
      invFun := fun y => ⟨⟨y.1, fun h3 => y.2 (Finset.mem_insert_of_mem h3)⟩, by
        simp only [Finset.mem_singleton]
        intro h3
        exact y.2 (by
          have := congrArg Subtype.val h3
          simp only at this
          simp [this])⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  exact e.tprod_eq (fun w => a w.1)

theorem tail_pos {ι : Type} (a : ι → ℝ) (hs : Summable (fun v => |a v - 1|)) (S : Finset ι)
    (hpos : ∀ v, v ∉ S → 0 < a v) : 0 < ∏' w : {w // w ∉ S}, a w.1 :=
  (GlobalTheory.T.infinite_product_multipliable {w // w ∉ S} (fun w => a w.1)
    (hs.comp_injective Subtype.val_injective)).2.2.1 (fun w => hpos w.1 w.2)

theorem exists_const_mul_tail : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (c : Finset ι → ℝ≥0) (S₁ : Finset ι), (∀ v, 0 ≤ a v) → Summable (fun v => |a v - 1|) → (∀ S, S₁ ⊆ S → ∀ v, v ∉ S → (c S : ℝ) = c (insert v S) * a v) → ∃ (c₀ : ℝ≥0) (S₀ : Finset ι), S₁ ⊆ S₀ ∧ ∀ S, S₀ ⊆ S → (0 < ∏' v : {v // v ∉ S}, a v.1) ∧ (c S : ℝ) = c₀ * ∏' v : {v // v ∉ S}, a v.1 := by
  intro ι _ a c S₁ _ hs hc
  have hev : ∀ᶠ v in Filter.cofinite, |a v - 1| < 1 / 2 :=
    hs.tendsto_cofinite_zero.eventually (Iio_mem_nhds (by norm_num))
  have hfin : {v | ¬ |a v - 1| < 1 / 2}.Finite := Filter.eventually_cofinite.1 hev
  let S₀ : Finset ι := S₁ ∪ hfin.toFinset
  have hS₀ : ∀ v, v ∉ S₀ → 0 < a v := by
    intro v hv
    have h1 : |a v - 1| < 1 / 2 := by
      by_contra h2
      exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 h2))
    have h2 := (abs_lt.1 h1).1
    linarith
  have hposS : ∀ S, S₀ ⊆ S → 0 < ∏' v : {v // v ∉ S}, a v.1 := fun S hS =>
    tail_pos a hs S (fun v hv => hS₀ v (fun h => hv (hS h)))
  have hP₀ := hposS S₀ (Finset.Subset.refl _)
  refine ⟨⟨(c S₀ : ℝ) / ∏' v : {v // v ∉ S₀}, a v.1, div_nonneg (c S₀).2 hP₀.le⟩, S₀,
    Finset.subset_union_left, fun S hS => ⟨hposS S hS, ?_⟩⟩
  have key : ∀ T : Finset ι, (c (S₀ ∪ T) : ℝ) =
      ((c S₀ : ℝ) / ∏' v : {v // v ∉ S₀}, a v.1) * ∏' v : {v // v ∉ S₀ ∪ T}, a v.1 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.union_empty]
      field_simp
    | insert v T _ ih =>
      by_cases hv : v ∈ S₀ ∪ T
      · have h1 : S₀ ∪ insert v T = S₀ ∪ T := by
          rw [Finset.union_insert, Finset.insert_eq_of_mem hv]
        rw [h1]
        exact ih
      · have h1 : S₀ ∪ insert v T = insert v (S₀ ∪ T) := Finset.union_insert _ _ _
        have hsub : S₀ ⊆ S₀ ∪ T := Finset.subset_union_left
        have hav : 0 < a v := hS₀ v (fun h => hv (hsub h))
        have h2 := hc (S₀ ∪ T) (Finset.Subset.trans Finset.subset_union_left hsub) v hv
        have h3 := tail_eq_mul_tail_insert a hs (S₀ ∪ T) v hv
        rw [h1]
        rw [h2, h3] at ih
        have h4 : (c (insert v (S₀ ∪ T)) : ℝ) * a v = (((c S₀ : ℝ) / ∏' v : {v // v ∉ S₀}, a v.1) * ∏' w : {w // w ∉ insert v (S₀ ∪ T)}, a w.1) * a v := by
          rw [ih]; ring
        exact mul_right_cancel₀ hav.ne' h4
  have h := key S
  rw [Finset.union_eq_right.2 hS] at h
  exact h

end GlobalTheory.CompanionTheory.SW.TailConst
end
