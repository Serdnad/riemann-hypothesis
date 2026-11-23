module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle004
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Cutoff
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle002

@[expose] public section

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem isSSec_finset_sum_and_n1_le_card_mul_sum (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    (C : Cover A) (la : La) (T : Finset Y) (F : Y → ι → Y → ℂ)
    (hF : ∀ P ∈ T, A.IsSSec (A.kap + la) (F P)) :
    A.IsSSec (A.kap + la) (fun i y => ∑ P ∈ T, F P i y) ∧
      n1 C la (fun i y => ∑ P ∈ T, F P i y) ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, n1 C la (F P) := by
  refine ⟨⟨fun i => ?_, fun i j y hi hj => ?_⟩, ?_⟩
  · exact ContDiffOn.sum (fun P hP => (hF P hP).1 i)
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun P hP => (hF P hP).2 i j y hi hj)
  ·
    have key : ∀ a : Fin C.m,
        (∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
          ((∑ j, ‖wdb n j ((fun y => ∑ P ∈ T, F P (C.idx a) y) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))))
        ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, ∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
          ((∑ j, ‖wdb n j (F P (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
      intro a
      set i := C.idx a with hi
      set e := A.chart i with he
      have hball : Metric.ball (C.c a) (C.r a) ⊆ e.target :=
        Metric.ball_subset_closedBall.trans (C.sub a)
      have hdiff : ∀ P ∈ T, ∀ v ∈ Metric.ball (C.c a) (C.r a),
          DifferentiableAt ℝ (F P i ∘ e.symm) v := fun P hP v hv =>
        ((hF P hP).1 i).differentiableOn (by simp) |>.differentiableAt
          (e.open_target.mem_nhds (hball hv))

      have hcont : ∀ P ∈ T, ContinuousOn (fun v => ENNReal.ofReal
          ((∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) *
            Real.exp (-A.ph la i (e.symm v)))) (Metric.ball (C.c a) (C.r a)) := by
        intro P hP
        have hfd : ContinuousOn (fderiv ℝ (F P i ∘ e.symm)) e.target :=
          ((hF P hP).1 i).continuousOn_fderiv_of_isOpen e.open_target (by simp)
        have hph : ContinuousOn (fun v => A.ph la i (e.symm v)) e.target :=
          (A.smooth_ph la i).continuousOn
        refine ENNReal.continuous_ofReal.comp_continuousOn ?_
        refine ContinuousOn.mul ?_ ((hph.mono hball).neg.rexp)
        refine continuousOn_finsetSum _ (fun j _ => ?_)
        refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
        unfold wdb
        refine ContinuousOn.div_const (ContinuousOn.add ?_ (continuousOn_const.mul ?_)) _
        · exact (hfd.clm_apply continuousOn_const).mono hball
        · exact (hfd.clm_apply continuousOn_const).mono hball
      have hpt : ∀ v ∈ Metric.ball (C.c a) (C.r a),
          ENNReal.ofReal ((∑ j, ‖wdb n j ((fun y => ∑ P ∈ T, F P i y) ∘ e.symm) v‖ ^ 2) *
            Real.exp (-A.ph la i (e.symm v)))
          ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, ENNReal.ofReal
            ((∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) * Real.exp (-A.ph la i (e.symm v))) := by
        intro v hv
        have hfun : (fun y => ∑ P ∈ T, F P i y) ∘ e.symm = fun w => ∑ P ∈ T, (F P i ∘ e.symm) w := rfl
        rw [hfun]
        have hs : ∀ j, wdb n j (fun w => ∑ P ∈ T, (F P i ∘ e.symm) w) v
            = ∑ P ∈ T, wdb n j (F P i ∘ e.symm) v := fun j => wdb_sum T (fun P hP => hdiff P hP v hv)
        simp only [hs]
        have hE := Real.exp_pos (-A.ph la i (e.symm v))
        have hreal : (∑ j, ‖∑ P ∈ T, wdb n j (F P i ∘ e.symm) v‖ ^ 2) * Real.exp (-A.ph la i (e.symm v))
            ≤ (T.card : ℝ) * ∑ P ∈ T, (∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) *
              Real.exp (-A.ph la i (e.symm v)) := by
          rw [← Finset.sum_mul, ← mul_assoc, Finset.sum_comm, Finset.mul_sum]
          refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _ => ?_) hE.le
          calc ‖∑ P ∈ T, wdb n j (F P i ∘ e.symm) v‖ ^ 2
              ≤ (∑ P ∈ T, ‖wdb n j (F P i ∘ e.symm) v‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
            _ ≤ (T.card : ℝ) * ∑ P ∈ T, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2 :=
                sq_sum_le_card_mul_sum_sq
        refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun P _ => by positivity)]
      calc _ ≤ ∫⁻ v in Metric.ball (C.c a) (C.r a), (T.card : ℝ≥0∞) * ∑ P ∈ T, ENNReal.ofReal
            ((∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) * Real.exp (-A.ph la i (e.symm v))) :=
            lintegral_mono_ae ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).2
              (Filter.Eventually.of_forall hpt))
        _ = _ := by
          rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _),
            lintegral_finsetSum' _ (fun P hP => (hcont P hP).aemeasurable
              Metric.isOpen_ball.measurableSet)]
    unfold n1
    calc _ ≤ ∑ a, (T.card : ℝ≥0∞) * ∑ P ∈ T, ∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
          ((∑ j, ‖wdb n j (F P (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) :=
          Finset.sum_le_sum fun a _ => key a
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end GlobalTheory.OTY
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem sections_prod_quot_open : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), (∀ (la mu : La) (a b : ι → Y → ℂ), A.IsSec la a → A.IsSec mu b → A.IsSec (la + mu) (fun i y => a i y * b i y) ∧ ∀ y, A.nsq (la + mu) (fun i y => a i y * b i y) y = A.nsq la a y * A.nsq mu b y) ∧ (∀ (la : La) (a : ι → Y → ℂ), A.IsSec la a → IsOpen (nz A a)) ∧ (∀ (B la : La) (a b : ι → Y → ℂ) (U : Set Y), A.IsSec (B + la) a → A.IsSec B b → (∀ y ∈ U, a (A.pick y) y ≠ 0 ∧ b (A.pick y) y ≠ 0) → A.IsFrameOn la U (fun i y => a i y / b i y)) := by
  intro n Y _ _ _ _ _ ι La _ A
  refine ⟨?_, ?_, ?_⟩
  · intro la mu a b ha hb
    refine ⟨⟨fun i => ?_, fun i j y _ hi hj => ?_⟩, fun y => ?_⟩
    · exact (ha.1 i).mul (hb.1 i)
    · beta_reduce
      rw [A.g_add la mu i j y hi hj, ha.2 i j y trivial hi hj, hb.2 i j y trivial hi hj]
      ring
    · simp only [WeightedAtlas.nsq]
      rw [A.ph_add la mu _ y (A.mem_pick y), norm_mul, mul_pow, neg_add, Real.exp_add]
      ring
  · intro la a ha
    have hc : Continuous (A.nsq la a) := bsA_nsq_cont A ha
    have : nz A a = A.nsq la a ⁻¹' {0}ᶜ := by
      ext y
      simp only [nz, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff, WeightedAtlas.nsq]
      constructor
      · intro h
        exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr h)) (Real.exp_pos _).ne'
      · intro h h0
        apply h
        simp [h0]
    rw [this]
    exact isOpen_compl_singleton.preimage hc
  · intro B la a b U ha hb hU
    have hbne : ∀ i y, y ∈ U → y ∈ (A.chart i).source → b i y ≠ 0 := by
      intro i y hy hi
      rw [hb.2 i (A.pick y) y trivial hi (A.mem_pick y)]
      exact mul_ne_zero (A.g_ne B i (A.pick y) y hi (A.mem_pick y)) (hU y hy).2
    refine ⟨⟨fun i => ?_, fun i j y hy hi hj => ?_⟩, fun y hy => div_ne_zero (hU y hy).1 (hU y hy).2⟩
    · have hS : (A.chart i).target ∩ (A.chart i).symm ⁻¹' U ⊆
          (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ := fun v hv => ⟨hv.1, trivial⟩
      have h1 : DifferentiableOn ℂ (a i ∘ (A.chart i).symm)
          ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (ha.1 i).mono hS
      have h2 : DifferentiableOn ℂ (b i ∘ (A.chart i).symm)
          ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (hb.1 i).mono hS
      have h3 := h1.mul (h2.inv (fun v (hv : v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U) =>
        hbne i _ hv.2 ((A.chart i).map_target hv.1)))
      refine h3.congr (fun v _ => ?_)
      simp [div_eq_mul_inv]
    · have hgB := A.g_ne B i j y hi hj
      have hbj := hbne j y hy hj
      beta_reduce
      rw [ha.2 i j y trivial hi hj, hb.2 i j y trivial hi hj, A.g_add B la i j y hi hj]
      field_simp

end GlobalTheory.OTY
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ClsBasic

variable {R : Type} [CommRing R]

theorem single_add' {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {p q : ℤ}
    (f g : K.X p ⟶ L.X q) (n : ℤ) : Cochain.single (f + g) n = Cochain.single f n + Cochain.single g n := by
  ext p' q' h
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq; simp
    · simp [Cochain.single_v_eq_zero' _ _ _ _ _ hq]
  · simp [Cochain.single_v_eq_zero _ _ _ _ _ hp]

theorem ofHom_comp_single {C : Type*} [Category C] [Preadditive C] {K K' L : CochainComplex C ℤ} {p q : ℤ}
    (g : K' ⟶ K) (f : K.X p ⟶ L.X q) (n : ℤ) :
    (Cochain.ofHom g).comp (Cochain.single f n) (zero_add n) = Cochain.single (g.f p ≫ f) n := by
  ext p' q' h
  rw [Cochain.comp_v _ _ (zero_add n) p' p' q' (add_zero p') h, Cochain.ofHom_v]
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq; simp
    · simp [Cochain.single_v_eq_zero' _ _ _ _ _ hq]
  · simp [Cochain.single_v_eq_zero _ _ _ _ _ hp]

theorem resι_d (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  have h := (injectiveResolution F).ι'.comm 0 1
  have h0 : ((singleFunctor (Shv R) 0).obj F).d 0 1 = 0 := by simp
  rw [h0, zero_comp] at h
  change ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ (injectiveResolution F).ι'.f 0) ≫ (injectiveResolution F).cochainComplex.d 0 1 = 0
  erw [Category.assoc, h]

theorem chains_d (E : Spc) (n : ℕ) :
    ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (chainsXIso R E (n + 1)).hom ≫ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫
        (chainsXIso R E n).inv := by
  have h := HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := n + 1) (j := n) rfl rfl
  have h2 : ((chainsN R).obj E).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ n
  rw [← h2]
  exact h

theorem chainsXIso_nat {E E' : Spc} (f : E' ⟶ E) (n : ℕ) :
    ((chains R).map f).f (-(n : ℤ)) ≫ (chainsXIso R E n).hom = (chainsXIso R E' n).hom ≫ (free R).map (f.app (op ⦋n⦌)) := by
  have h := HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl
  change (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(n : ℤ)) ≫ _ = _
  rw [h]
  simp only [chainsXIso]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem δ_cls {E : Spc} {F : Shv R} {n : ℕ} (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) :
    δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n) =
      (((n + 1 : ℕ) : ℤ)).negOnePow • Cochain.single (p := -((n + 1 : ℕ) : ℤ)) (q := 0)
        ((chainsXIso R E (n + 1)).hom ≫ cobd s ≫ resι R F) ((n + 1 : ℕ) : ℤ) := by
  rw [Cochain.δ_single _ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (-((n + 1 : ℕ) : ℤ)) 1 (by push_cast; ring) rfl]
  rw [Category.assoc, Category.assoc, resι_d, comp_zero, comp_zero, Cochain.single_zero, zero_add]
  congr 2
  rw [chains_d, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  rw [← Category.assoc]
  congr 1
  rw [cobd, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.zsmul_comp]

end GlobalTheory.EtC.ClsBasic

open GlobalTheory.EtC.ClsBasic in
theorem GlobalTheory.EtC.isCls_basic : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ),
    (∀ s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd s = 0 → ∃ x : H R E F n, IsCls s x) ∧
    (∀ (s s' : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x x' : H R E F n),
      IsCls s x → IsCls s' x' → IsCls (s + s') (x + x')) ∧
    (∀ (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x x' : H R E F n),
      IsCls s x → IsCls s x' → x = x') ∧
    (∀ (t : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x : H R E F ((n + 1 : ℕ) : ℤ)),
      IsCls (cobd t) x → x = 0) ∧
    ∀ (E' : Spc) (f : E' ⟶ E) (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x : H R E F n),
      IsCls s x → IsCls ((free R).map (f.app (op ⦋n⦌)) ≫ s) (pull R f F n x) := by
  intro R _ F E n
  refine ⟨fun s hs => ?_, fun s s' x x' hx hx' => ?_, fun s x x' hx hx' => ?_, fun t x hx => ?_, fun E' f s x hx => ?_⟩
  · refine ⟨CohomologyClass.mk (Cocycle.mk (Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n)
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) ?_), _, rfl, rfl⟩
    rw [ClsBasic.δ_cls, hs, zero_comp, comp_zero, Cochain.single_zero, smul_zero]
  · obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hx'
    refine ⟨z + z', (CohomologyClass.mk_add z z').symm, ?_⟩
    change z.1 + z'.1 = _
    rw [hz, hz', ← ClsBasic.single_add', Preadditive.add_comp, Preadditive.comp_add]
  · obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hx'
    have : z = z' := Cocycle.ext (hz.trans hz'.symm)
    rw [this]
  · obtain ⟨z, rfl, hz⟩ := hx
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n : ℤ) (by push_cast; ring)]
    refine ⟨(((n + 1 : ℕ) : ℤ)).negOnePow • Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ t ≫ resι R F) n, ?_⟩
    rw [δ_units_smul, ClsBasic.δ_cls, smul_smul, Int.units_mul_self, one_smul, hz]
  · obtain ⟨z, rfl, hz⟩ := hx
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add _), rfl, ?_⟩
    change (Cochain.ofHom ((chains R).map f)).comp z.1 (zero_add _) = _
    rw [hz, ClsBasic.ofHom_comp_single, ← Category.assoc, ClsBasic.chainsXIso_nat]
    simp only [Category.assoc]

end
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem n1_lt_infty_of_isSSec : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ), A.IsSSec (A.kap + la) F0 → n1 C la F0 < ⊤ := by
  intro n Y _ _ _ _ _ ι La _ A C la F0 hF
  unfold n1
  rw [ENNReal.sum_lt_top]
  intro a _
  set i := C.idx a
  set T := (A.chart i).target
  have hT : IsOpen T := (A.chart i).open_target
  have hsub : closedBall (C.c a) (C.r a) ⊆ T := C.sub a
  have hF' : ContDiffOn ℝ ∞ (F0 i ∘ (A.chart i).symm) T := hF.1 i
  have hD : ContinuousOn (fun v => fderiv ℝ (F0 i ∘ (A.chart i).symm) v) T :=
    hF'.continuousOn_fderiv_of_isOpen hT (by simp)
  have hph : ContinuousOn (fun v => A.ph la i ((A.chart i).symm v)) T :=
    (A.smooth_ph la i).continuousOn
  have hcont : ContinuousOn (fun v => (∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
      Real.exp (-A.ph la i ((A.chart i).symm v))) (closedBall (C.c a) (C.r a)) := by
    refine ContinuousOn.mono ?_ hsub
    refine ContinuousOn.mul ?_ ?_
    · refine continuousOn_finsetSum _ (fun j _ => ?_)
      refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
      unfold wdb
      refine ContinuousOn.div_const (ContinuousOn.add ?_ (ContinuousOn.mul continuousOn_const ?_)) _
      · exact hD.clm_apply continuousOn_const
      · exact hD.clm_apply continuousOn_const
    · exact (hph.neg).rexp
  have hint : IntegrableOn (fun v => (∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
      Real.exp (-A.ph la i ((A.chart i).symm v))) (closedBall (C.c a) (C.r a)) :=
    hcont.integrableOn_compact (isCompact_closedBall _ _)
  calc _ ≤ ∫⁻ v in closedBall (C.c a) (C.r a), ENNReal.ofReal
        ((∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
          Real.exp (-A.ph la i ((A.chart i).symm v))) :=
        lintegral_mono_set ball_subset_closedBall
    _ < ⊤ := hint.lintegral_lt_top

end GlobalTheory
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem exists_isCut (T : ℝ) : ∃ θ : ℝ → ℝ, IsCut T θ := by
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ → ℝ, ReciprocityTheory.L2DbarEstimates.I.IsCutoff χ :=
    ⟨_, ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.isCutoff_chi⟩
  obtain ⟨hs, h1, h0, hb, hd⟩ := hχ
  set a : ℝ → ℝ := fun x => (x + T + 1) / 4 + 1 / 2 with ha
  have haS : ContDiff ℝ ∞ a := by
    simp only [ha]; fun_prop
  have hda : ∀ x, HasDerivAt a (1 / 4) x := by
    intro x
    have := (((hasDerivAt_id x).add_const T).add_const 1).div_const 4
    simpa [ha] using this.add_const (1 / 2)
  refine ⟨χ ∘ a, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs.comp haS
  · intro x hx
    exact h1 _ (by simp only [ha]; linarith)
  · intro x hx
    exact h0 _ (by simp only [ha]; linarith)
  · intro x
    exact hb _
  · intro x
    have hχd : DifferentiableAt ℝ χ (a x) :=
      (hs.differentiable (by simp)) _
    have hD : HasDerivAt (χ ∘ a) (deriv χ (a x) * (1 / 4)) x :=
      hχd.hasDerivAt.comp x (hda x)
    rw [hD.deriv, abs_mul]
    have := hd (a x)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    linarith

theorem exists_isCut₂ : ∀ T : ℝ, ∃ θ : ℝ → ℝ, IsCut T θ := exists_isCut

end GlobalTheory
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem nz_dense_of_ne_zero_on_components : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ) (T : Set Y), A.IsSec Λ τ →
    (∀ y, ∃ P ∈ T, P ∈ connectedComponent y) → (∀ P ∈ T, τ (A.pick P) P ≠ 0) →
    Dense (nz A τ) := by
  intro n Y _ _ _ _ _ ι La _ A Λ τ T hs hT hP
  set Zs : Set Y := {y | τ (A.pick y) y = 0} with hZs
  have hc : (nz A τ)ᶜ = Zs := by
    ext y; simp [nz, Zs]

  have toI : ∀ i x, x ∈ (A.chart i).source → τ (A.pick x) x = 0 → τ i x = 0 := by
    intro i x hx h0
    rw [hs.2 i (A.pick x) x (Set.mem_univ _) hx (A.mem_pick x), h0, mul_zero]
  have toP : ∀ i x, x ∈ (A.chart i).source → τ i x = 0 → τ (A.pick x) x = 0 := by
    intro i x hx h0
    rw [hs.2 (A.pick x) i x (Set.mem_univ _) (A.mem_pick x) hx, h0, mul_zero]
  set Z := interior Zs with hZ
  have hZo : IsOpen Z := isOpen_interior
  have hZc : IsClosed Z := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    set i := A.pick y
    set e := A.chart i
    have hyv : e y ∈ e.target := e.map_source (A.mem_pick y)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e y) hyv
    set W : Set Y := e.source ∩ e ⁻¹' ball (e y) r
    have hWo : IsOpen W := e.isOpen_inter_preimage isOpen_ball
    have hyW : y ∈ W := ⟨A.mem_pick y, by exact Set.mem_preimage.mpr (mem_ball_self hr)⟩
    obtain ⟨x, hxW, hxZ⟩ := (mem_closure_iff.mp hy) W hWo hyW
    set F : V n → ℂ := τ i ∘ e.symm
    have hF : DifferentiableOn ℂ F (ball (e y) r) := by
      have := hs.1 i
      refine this.mono ?_
      intro w hw; exact ⟨hball hw, Set.mem_univ _⟩
    have hxs : e x ∈ ball (e y) r := hxW.2
    have hev : F =ᶠ[𝓝 (e x)] 0 := by
      have hxt : e x ∈ e.target := e.map_source hxW.1
      have h1 : ∀ᶠ w in 𝓝 (e x), e.symm w ∈ Z := by
        have hca : ContinuousAt e.symm (e x) := e.continuousAt_symm hxt
        have : e.symm (e x) = x := e.left_inv hxW.1
        refine hca.preimage_mem_nhds ?_
        rw [this]; exact hZo.mem_nhds hxZ
      have h2 : ∀ᶠ w in 𝓝 (e x), w ∈ e.target := e.open_target.mem_nhds hxt
      filter_upwards [h1, h2] with w hw1 hw2
      have hsrc : e.symm w ∈ e.source := e.map_target hw2
      exact toI i _ hsrc (interior_subset (s := Zs) hw1)
    have hEq := ReciprocityTheory.L2DbarEstimates.C.ident n (ball (e y) r) F (e x) isOpen_ball (convex_ball _ _) hF hxs hev
    have hWZs : W ⊆ Zs := by
      intro z hz
      have h0 : F (e z) = 0 := hEq hz.2
      have : τ i z = 0 := by
        simpa [F, e.left_inv hz.1] using h0
      exact toP i z hz.1 this
    exact interior_maximal hWZs hWo hyW
  have hempty : Z = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨P, hPT, hPc⟩ := hT y
    have hsub := (IsClopen.connectedComponent_subset ⟨hZc, hZo⟩ hy)
    exact hP P hPT (interior_subset (s := Zs) (hsub hPc))
  have hd := interior_eq_empty_iff_dense_compl.mp hempty
  rw [← hc, compl_compl] at hd
  exact hd

end GlobalTheory
end
