module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.MeasureTheory.Integral.IntegrableOn

@[expose] public section

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.AeHoloGlue

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

theorem mu_ne_zero_of_open (A : WeightedAtlas n Y ι La) {O : Set Y} (hO : IsOpen O)
    (hne : O.Nonempty) : A.mu O ≠ 0 := by
  obtain ⟨y, hy⟩ := hne
  have hW : IsOpen (O ∩ (A.chart (A.pick y)).source) := hO.inter (A.chart (A.pick y)).open_source
  have hWs : O ∩ (A.chart (A.pick y)).source ⊆ (A.chart (A.pick y)).source := Set.inter_subset_right
  have hS : IsOpen (A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source)) :=
    (A.chart (A.pick y)).isOpen_image_of_subset_source hW hWs
  have hSne : (A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source)).Nonempty :=
    ⟨_, Set.mem_image_of_mem _ ⟨hy, A.mem_pick y⟩⟩
  have hSt : A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source) ⊆ (A.chart (A.pick y)).target := by
    rintro _ ⟨x, hx, rfl⟩; exact (A.chart (A.pick y)).map_source hx.2
  intro h0
  have h1 : A.mu (O ∩ (A.chart (A.pick y)).source) = 0 := measure_mono_null Set.inter_subset_left h0
  rw [A.mu_chart _ _ hW.measurableSet hWs] at h1
  have hc : ContinuousOn (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y) ((A.chart (A.pick y)).symm v))))
      (A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source)) := by
    have := (A.smooth_ph A.kap (A.pick y)).continuousOn.mono hSt
    exact ENNReal.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn this)
  rw [lintegral_eq_zero_iff' (hc.aemeasurable hS.measurableSet)] at h1
  have h3 := ae_iff.mp h1
  have hu : {v | ¬ (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y) ((A.chart (A.pick y)).symm v)))) v
      = (0 : V n → ℝ≥0∞) v} = Set.univ := by
    ext v; simp [ENNReal.ofReal_eq_zero, Real.exp_pos]
  rw [hu, Measure.restrict_apply_univ] at h3
  exact hS.measure_ne_zero volume hSne h3

theorem exists_null (A : WeightedAtlas n Y ι La) (i : ι) (c : V n) (r : ℝ) (u : V n → ℂ)
    (f : Y → ℂ) (h : u =ᵐ[volume.restrict (ball c r)] f ∘ (A.chart i).symm) :
    ∃ M : Set Y, A.mu M = 0 ∧ ∀ y ∈ (A.chart i).source, A.chart i y ∈ ball c r → y ∉ M →
      u (A.chart i y) = f y := by
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball] at h
  obtain ⟨T, hET, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.mp h)
  classical
  have hφ : Measurable ((A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n))) :=
    ContinuousOn.measurable_piecewise (A.chart i).continuousOn continuousOn_const
      (A.chart i).open_source.measurableSet
  refine ⟨(A.chart i).source ∩ (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) ⁻¹' T,
    ?_, ?_⟩
  · have hm : MeasurableSet ((A.chart i).source ∩
        (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) ⁻¹' T) :=
      (A.chart i).open_source.measurableSet.inter (hφ hTm)
    rw [A.mu_chart i _ hm Set.inter_subset_left]
    refine le_antisymm ?_ (by simp)
    calc _ ≤ ∫⁻ v in T, ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) := by
          apply lintegral_mono_set
          rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
          have : (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) x = A.chart i x :=
            Set.piecewise_eq_of_mem _ _ _ hx1
          simpa [this] using hx2
      _ = 0 := setLIntegral_measure_zero _ _ hT0
  · intro y hy hb hM
    by_contra hne
    apply hM
    refine ⟨hy, ?_⟩
    show (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) y ∈ T
    rw [Set.piecewise_eq_of_mem _ _ _ hy]
    apply hET
    simp only [Set.mem_setOf_eq]
    intro heq
    apply hne
    simpa [Function.comp, (A.chart i).left_inv hy] using heq hb

theorem continuousOn_g (A : WeightedAtlas n Y ι La) (la : La) (i j : ι) :
    ContinuousOn (A.g la i j) ((A.chart i).source ∩ (A.chart j).source) := by
  have h1 : ContinuousOn (A.g la i j ∘ (A.chart i).symm ∘ A.chart i)
      ((A.chart i).source ∩ (A.chart j).source) := by
    refine (A.holo_g la i j).continuousOn.comp ((A.chart i).continuousOn.mono Set.inter_subset_left) ?_
    intro y hy
    exact ⟨(A.chart i).map_source hy.1, by simpa [(A.chart i).left_inv hy.1] using hy.2⟩
  refine h1.congr ?_
  intro y hy
  simp [(A.chart i).left_inv hy.1]

theorem main : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La),
    ∀ (C : Cover A) (la : La) (f : ι → Y → ℂ) (u : Fin C.m → V n → ℂ),
    (∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → f i y = A.g la i j y * f j y) →
    (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) →
    (∀ a, u a =ᵐ[volume.restrict (ball (C.c a) (C.r a))] f (C.idx a) ∘ (A.chart (C.idx a)).symm) →
    ∃ F : ι → Y → ℂ, A.IsSec la F ∧ ∀ᵐ y ∂A.mu, F (A.pick y) y = f (A.pick y) y := by
  intro n Y _ _ _ _ _ ι La _ A C la f u hf hu hae
  classical

  have hBo : ∀ a, IsOpen ((A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) :=
    fun a => (A.chart (C.idx a)).isOpen_inter_preimage isOpen_ball
  have hcov : ∀ y, ∃ a, y ∈ (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) := by
    intro y
    by_contra hno
    push_neg at hno
    have h0 : ∀ a, C.chi a y = 0 := fun a => by
      by_contra hne
      exact hno a (C.supp a (subset_tsupport _ hne))
    have := C.sum_one y
    simp [h0] at this
  choose M hM0 hM using fun a => exists_null A (C.idx a) (C.c a) (C.r a) (u a) (f (C.idx a)) (hae a)
  have hM0' : A.mu (⋃ a, M a) = 0 := measure_iUnion_null hM0

  have hoff : ∀ a y, y ∈ (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) →
      y ∉ ⋃ a, M a → u a (A.chart (C.idx a) y) = f (C.idx a) y := fun a y hy hn =>
    hM a y hy.1 hy.2 (fun h => hn (Set.mem_iUnion.mpr ⟨a, h⟩))
  have hcu : ∀ a, ContinuousOn (fun y => u a (A.chart (C.idx a) y))
      ((A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) := fun a =>
    (hu a).continuousOn.comp ((A.chart (C.idx a)).continuousOn.mono Set.inter_subset_left)
      (fun y hy => hy.2)

  have hagree : ∀ a b y, y ∈ (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) →
      y ∈ (A.chart (C.idx b)).source ∩ A.chart (C.idx b) ⁻¹' ball (C.c b) (C.r b) →
      u a (A.chart (C.idx a) y) = A.g la (C.idx a) (C.idx b) y * u b (A.chart (C.idx b) y) := by
    intro a b y hya hyb
    set D := ((A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) ∩
      ((A.chart (C.idx b)).source ∩ A.chart (C.idx b) ⁻¹' ball (C.c b) (C.r b)) with hD
    have hcont : ContinuousOn (fun y => u a (A.chart (C.idx a) y) -
        A.g la (C.idx a) (C.idx b) y * u b (A.chart (C.idx b) y)) D :=
      ((hcu a).mono Set.inter_subset_left).sub
        (((continuousOn_g A la (C.idx a) (C.idx b)).mono
          (show D ⊆ (A.chart (C.idx a)).source ∩ (A.chart (C.idx b)).source from
            fun z hz => ⟨hz.1.1, hz.2.1⟩)).mul ((hcu b).mono Set.inter_subset_right))
    have hop := hcont.isOpen_inter_preimage ((hBo a).inter (hBo b)) (isOpen_compl_singleton (x := (0 : ℂ)))
    have hsub : D ∩ (fun y => u a (A.chart (C.idx a) y) -
        A.g la (C.idx a) (C.idx b) y * u b (A.chart (C.idx b) y)) ⁻¹' {0}ᶜ ⊆ ⋃ a, M a := by
      intro z ⟨hz, hz0⟩
      by_contra hn
      apply hz0
      simp only [Set.mem_singleton_iff]
      rw [hoff a z hz.1 hn, hoff b z hz.2 hn, hf _ _ z hz.1.1 hz.2.1]
      ring
    by_contra hne
    exact mu_ne_zero_of_open A hop ⟨y, ⟨hya, hyb⟩, by simpa [sub_eq_zero] using hne⟩
      (measure_mono_null hsub hM0')
  choose α hα using hcov
  refine ⟨fun i y => A.g la i (C.idx (α y)) y * u (α y) (A.chart (C.idx (α y)) y), ⟨?_, ?_⟩, ?_⟩
  ·
    intro i v hv
    have hvs : (A.chart i).symm v ∈ (A.chart i).source := (A.chart i).map_target hv.1
    set a0 := α ((A.chart i).symm v)
    have hO : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0))) :=
      (A.chart i).isOpen_inter_preimage_symm (hBo a0)
    have hvO : v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0)) :=
      ⟨hv.1, hα _⟩
    have hOovl : (A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0)) ⊆
        ovl A.chart i (C.idx a0) := fun w hw => ⟨hw.1, hw.2.1⟩
    have hG : DifferentiableOn ℂ (fun w => A.g la i (C.idx a0) ((A.chart i).symm w) *
        u a0 ((A.chart (C.idx a0) ∘ (A.chart i).symm) w))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹'
          ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0))) :=
      ((A.holo_g la i (C.idx a0)).mono hOovl).mul
        ((hu a0).comp ((A.holo_trans i (C.idx a0)).mono hOovl) (fun w hw => hw.2.2))
    have hloc : (fun w => A.g la i (C.idx a0) ((A.chart i).symm w) *
        u a0 ((A.chart (C.idx a0) ∘ (A.chart i).symm) w)) =ᶠ[𝓝 v]
        ((fun i y => A.g la i (C.idx (α y)) y * u (α y) (A.chart (C.idx (α y)) y)) i ∘
          (A.chart i).symm) := by
      filter_upwards [hO.mem_nhds hvO] with w hw
      have hws : (A.chart i).symm w ∈ (A.chart i).source := (A.chart i).map_target hw.1
      simp only [Function.comp]
      rw [hagree (α ((A.chart i).symm w)) a0 _ (hα _) hw.2, ← mul_assoc,
        ← A.g_cocycle la i _ _ _ hws (hα _).1 hw.2.1]
    exact ((hG.differentiableAt (hO.mem_nhds hvO)).congr_of_eventuallyEq hloc.symm).differentiableWithinAt
  ·
    intro i j y _ hi hj
    simp only
    rw [A.g_cocycle la i j (C.idx (α y)) y hi hj (hα y).1]
    ring
  ·
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hM0'] with y hy
    rw [hoff _ y (hα y) hy, ← hf _ _ y (A.mem_pick y) (hα y).1]

end GlobalTheory.AeHoloGlue
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ConeEl

variable {T : Type 1} [Category.{0} T] {C D : T ⥤ AbCx} (φ : C ⟶ D)

def coneD (U : T) (n : ℤ) :
    AddCommGrpCat.of ((C.obj U).X (n + 1) × (D.obj U).X n) ⟶
      AddCommGrpCat.of ((C.obj U).X (n + 1 + 1) × (D.obj U).X (n + 1)) :=
  AddCommGrpCat.ofHom
    { toFun := fun x => (-(C.obj U).d (n + 1) (n + 1 + 1) x.1,
        (φ.app U).f (n + 1) x.1 + (D.obj U).d n (n + 1) x.2)
      map_zero' := by simp
      map_add' := fun x y => by
        refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, map_add (f := _), neg_add] <;> abel }

lemma coneD_apply (U : T) (n : ℤ) (x : (C.obj U).X (n + 1) × (D.obj U).X n) :
    coneD φ U n x = (-(C.obj U).d (n + 1) (n + 1 + 1) x.1,
        (φ.app U).f (n + 1) x.1 + (D.obj U).d n (n + 1) x.2) := rfl

lemma dd_apply (K : AbCx) (i j k : ℤ) (x : K.X i) : K.d j k (K.d i j x) = 0 := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]; rfl

lemma comm_apply {K L : AbCx} (f : K ⟶ L) (i j : ℤ) (x : K.X i) : f.f j (K.d i j x) = L.d i j (f.f i x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm]

lemma coneD_sq (U : T) (n : ℤ) : coneD φ U n ≫ coneD φ U (n + 1) = 0 := by
  refine AddCommGrpCat.ext fun x => ?_
  change coneD φ U (n + 1) (coneD φ U n x) = 0
  rw [coneD_apply, coneD_apply]
  refine Prod.ext ?_ ?_
  · simp [dd_apply]
  · simp [dd_apply, comm_apply]

def coneObj (U : T) : AbCx :=
  CochainComplex.of (fun n => AddCommGrpCat.of ((C.obj U).X (n + 1) × (D.obj U).X n)) (coneD φ U) (coneD_sq φ U)

lemma nat_apply {U V : T} (g : U ⟶ V) (n : ℤ) (x : (C.obj U).X n) :
    (D.map g).f n ((φ.app U).f n x) = (φ.app V).f n ((C.map g).f n x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
    ← HomologicalComplex.comp_f, φ.naturality]

def coneMap {U V : T} (g : U ⟶ V) : coneObj φ U ⟶ coneObj φ V :=
  CochainComplex.ofHom (X := coneObj φ U) (Y := coneObj φ V)
    (fun n => AddCommGrpCat.ofHom (AddMonoidHom.prodMap ((C.map g).f (n + 1)).hom ((D.map g).f n).hom))
    (fun n => by
      refine AddCommGrpCat.ext fun x => ?_
      simp only [coneObj, CochainComplex.of_d]
      change coneD φ V n (((C.map g).f (n + 1)) x.1, ((D.map g).f n) x.2) =
        (((C.map g).f (n + 1 + 1)) (coneD φ U n x).1, ((D.map g).f (n + 1)) (coneD φ U n x).2)
      rw [coneD_apply]
      erw [coneD_apply]
      refine Prod.ext ?_ ?_
      · simp [comm_apply]
      · simp [comm_apply, nat_apply])

def cone : T ⥤ AbCx where
  obj := coneObj φ
  map := coneMap φ
  map_id U := by
    ext n x
    refine Prod.ext ?_ ?_
    · change (C.map (𝟙 U)).f (n + 1) x.1 = x.1
      rw [CategoryTheory.Functor.map_id]; rfl
    · change (D.map (𝟙 U)).f n x.2 = x.2
      rw [CategoryTheory.Functor.map_id]; rfl
  map_comp f g := by
    ext n x
    refine Prod.ext ?_ ?_
    · change (C.map (f ≫ g)).f (n + 1) x.1 = (C.map g).f (n + 1) ((C.map f).f (n + 1) x.1)
      rw [CategoryTheory.Functor.map_comp]; rfl
    · change (D.map (f ≫ g)).f n x.2 = (D.map g).f n ((D.map f).f n x.2)
      rw [CategoryTheory.Functor.map_comp]; rfl

def coneFst (n : ℤ) : term (cone φ) n ⟶ term C (n + 1) where
  app U := AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)
  naturality U V g := rfl

def coneSnd (n : ℤ) : term (cone φ) n ⟶ term D n where
  app U := AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)
  naturality U V g := rfl

end GlobalTheory.EtC.ConeEl


open GlobalTheory.EtC.ConeEl in
theorem GlobalTheory.EtC.coneEl_exists : ∀ (T : Type 1) [Category.{0} T] (C D : T ⥤ AbCx) (φ : C ⟶ D), ∃ (K : T ⥤ AbCx) (p : ∀ n : ℤ, term K n ⟶ term C (n + 1)) (q : ∀ n : ℤ, term K n ⟶ term D n), (∀ n U, Function.Bijective (fun x : (K.obj U).X n => ((p n).app U x, (q n).app U x))) ∧ ∀ n U (x : (K.obj U).X n), (p (n + 1)).app U ((K.obj U).d n (n + 1) x) = - (C.obj U).d (n + 1) (n + 1 + 1) ((p n).app U x) ∧ (q (n + 1)).app U ((K.obj U).d n (n + 1) x) = (φ.app U).f (n + 1) ((p n).app U x) + (D.obj U).d n (n + 1) ((q n).app U x) := by
  intro T _ C D φ
  refine ⟨cone φ, coneFst φ, coneSnd φ, fun n U => ?_, fun n U x => ?_⟩
  · refine ⟨fun x y h => ?_, fun y => ⟨(y.1, y.2), rfl⟩⟩
    exact Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  · have hd : (cone φ |>.obj U).d n (n + 1) = coneD φ U n := CochainComplex.of_d (fun n => AddCommGrpCat.of ((C.obj U).X (n + 1) × (D.obj U).X n)) (coneD φ U) n
    constructor
    · change ((cone φ |>.obj U).d n (n + 1) x).1 = _
      rw [hd]; rfl
    · change ((cone φ |>.obj U).d n (n + 1) x).2 = _
      rw [hd]; rfl
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConerveNerve

variable {T : Type 1} [Category.{0} T] (Ψ : T ⥤ PShᵒᵖ) {U V : T} (g : U ⟶ V) (J : Type) [HasWidePushout U (fun _ : J => V) (fun _ => g)]

def cmp : (Ψ.obj (widePushout U (fun _ : J => V) fun _ => g)).unop ⟶
    widePullback (Ψ.obj U).unop (fun _ : J => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) :=
  WidePullback.lift (Ψ.map (WidePushout.head _)).unop (fun i => (Ψ.map (WidePushout.ι _ i)).unop)
    (fun i => by rw [← unop_comp, ← Ψ.map_comp]; exact congrArg (fun k => (Ψ.map k).unop) (WidePushout.arrow_ι (fun _ : J => g) i))

lemma cmp_π (i : J) : cmp Ψ g J ≫ WidePullback.π _ i = (Ψ.map (WidePushout.ι _ i)).unop := by
  simp only [cmp, WidePullback.lift_π]

lemma cmp_base : cmp Ψ g J ≫ WidePullback.base _ = (Ψ.map (WidePushout.head _)).unop := by
  simp only [cmp, WidePullback.lift_base]

def coc : Cocone (WidePushoutShape.wideSpan U (fun _ : J => V) (fun _ => g) ⋙ Ψ) :=
  WidePushoutShape.mkCocone (X := op (widePullback (Ψ.obj U).unop (fun _ : J => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop)))
    (WidePullback.base _).op (fun i => (WidePullback.π _ i).op) (fun i => by
      apply Quiver.Hom.unop_inj
      exact WidePullback.π_arrow (fun _ : J => (Ψ.map g).unop) i)

lemma isIso_cmp [PreservesColimitsOfShape (WidePushoutShape J) Ψ] : IsIso (cmp Ψ g J) := by
  let hC := isColimitOfPreserves Ψ (colimit.isColimit (WidePushoutShape.wideSpan U (fun _ : J => V) (fun _ => g)))
  refine ⟨(hC.desc (coc Ψ g J)).unop, ?_, ?_⟩
  · apply Quiver.Hom.op_inj
    show hC.desc (coc Ψ g J) ≫ (cmp Ψ g J).op = 𝟙 _
    apply hC.hom_ext
    intro j
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (cmp Ψ g J).op) (hC.fac (coc Ψ g J) j)).trans ?_
    refine Eq.trans ?_ (Category.comp_id _).symm
    apply Quiver.Hom.unop_inj
    rcases j with _ | i
    · exact cmp_base Ψ g J
    · exact cmp_π Ψ g J i
  · apply WidePullback.hom_ext
    · intro i
      have := congrArg Quiver.Hom.unop (hC.fac (coc Ψ g J) (some i))
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg _ (cmp_π Ψ g J i)).trans ?_
      exact this.trans (Category.id_comp _).symm
    · have := congrArg Quiver.Hom.unop (hC.fac (coc Ψ g J) none)
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg _ (cmp_base Ψ g J)).trans ?_
      exact this.trans (Category.id_comp _).symm

end GlobalTheory.EtC.ConerveNerve

namespace GlobalTheory.EtC.ConerveNerve

theorem conerve_nerve : ∀ (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ), (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V), ∃ e : ((((Arrow.mk g).cechConerve ⋙ Ψ).leftOp : Spc) ⟶ (Arrow.mk (Ψ.map g).unop).cechNerve), IsIso e ∧ e ≫ (Arrow.mk (Ψ.map g).unop).augmentedCechNerve.hom = lev Ψ (coAug g) := by
  intro T _ _ Ψ hΨ U V g
  refine ⟨{ app := fun n => cmp Ψ g (Fin (n.unop.len + 1)), naturality := ?_ }, ?_, ?_⟩
  · intro m n f
    apply WidePullback.hom_ext
    · intro i
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine (congrArg _ (cmp_π Ψ g _ i)).trans ?_
      have hN : (Arrow.mk (Ψ.map g).unop).cechNerve.map f ≫ WidePullback.π (fun _ => (Arrow.mk (Ψ.map g).unop).hom) i =
          WidePullback.π (fun _ => (Arrow.mk (Ψ.map g).unop).hom) (f.unop.toOrderHom i) :=
        WidePullback.lift_π _ _ _ _ _
      refine Eq.trans ?_ (congrArg _ hN).symm
      refine Eq.trans ?_ (cmp_π Ψ g _ _).symm
      change (Ψ.map (WidePushout.ι _ i) ≫ Ψ.map ((Arrow.mk g).cechConerve.map f.unop)).unop = _
      refine (congrArg Quiver.Hom.unop (Ψ.map_comp _ _).symm).trans ?_
      exact congrArg (fun k => (Ψ.map k).unop) (by apply WidePushout.ι_desc)
    · refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine (congrArg _ (cmp_base Ψ g _)).trans ?_
      have hN : (Arrow.mk (Ψ.map g).unop).cechNerve.map f ≫ WidePullback.base (fun _ : Fin ((unop n).len + 1) => (Arrow.mk (Ψ.map g).unop).hom) =
          WidePullback.base (fun _ : Fin ((unop m).len + 1) => (Arrow.mk (Ψ.map g).unop).hom) := by
        apply WidePullback.lift_base
      refine Eq.trans ?_ (congrArg _ hN).symm
      refine Eq.trans ?_ (cmp_base Ψ g _).symm
      change (Ψ.map (WidePushout.head _) ≫ Ψ.map ((Arrow.mk g).cechConerve.map f.unop)).unop = _
      refine (congrArg Quiver.Hom.unop (Ψ.map_comp _ _).symm).trans ?_
      exact congrArg (fun k => (Ψ.map k).unop) (by apply WidePushout.head_desc)
  · have : ∀ n : SimplexCategoryᵒᵖ, IsIso (cmp Ψ g (Fin (n.unop.len + 1))) := fun n => by
      haveI := hΨ n.unop.len
      exact isIso_cmp Ψ g _
    exact (NatTrans.isIso_iff_isIso_app _).2 this
  · refine NatTrans.ext (funext fun n => ?_)
    exact cmp_base Ψ g _

end GlobalTheory.EtC.ConerveNerve
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

theorem isIndEtale_comp_etale {A B O : Type} [CommRing A] [CommRing B] [CommRing O] (φ : A →+* B)
    (hφ : φ.Etale) (g : B →+* O) (hg : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale g) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp φ) := by
  obtain ⟨J, _, _, D, s, t, hs, hj⟩ := hg
  refine ⟨J, inferInstance, inferInstance, D, (Functor.const J).map (CommRingCat.ofHom φ) ≫ s, t, hs,
    fun j => ⟨?_, ?_⟩⟩
  · show RingHom.Etale ((s.app j).hom.comp φ)
    exact RingHom.Etale.stableUnderComposition _ _ hφ (hj j).1
  · have h2 := (hj j).2
    show CommRingCat.ofHom φ ≫ s.app j ≫ t.app j = CommRingCat.ofHom (g.comp φ)
    rw [h2]
    rfl

theorem isStalk_affine : ∀ (A : Type) [CommRing A] (O : Type) [CommRing O]
    (s : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of A)), IsStalk O s →
    ∃ _ : Algebra A O, SH O ∧ IndEt A O ∧ s = Spec.map (CommRingCat.ofHom (algebraMap A O)) := by
  intro A _ O _ s hs
  obtain ⟨hSH, A', _, _, j, hj, hind, rfl⟩ := hs
  set φ := Spec.preimage j with hφdef
  have hjφ : Spec.map φ = j := Spec.map_preimage j
  have hφ : φ.hom.Etale := by
    rw [← hjφ] at hj
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp hj
  letI : Algebra A O := ((algebraMap A' O).comp φ.hom).toAlgebra
  refine ⟨this, hSH, ?_, ?_⟩
  · exact isIndEtale_comp_etale φ.hom hφ (algebraMap A' O) hind
  · rw [← hjφ, ← Spec.map_comp]
    rfl

end GlobalTheory.EtC
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contCone_of_whisker : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (I' : Type) [SmallCategory I'] [IsCofiltered I'] (L : I' ⥤ I) (G : I ⥤ Spc) (c : Cone G), (∀ i, ∃ i', Nonempty (L.obj i' ⟶ i)) → ContCone R F (c.whisker L) → ContCone R F c := by
  intro R _ F I _ _ I' _ _ L G c hL hc n
  obtain ⟨h1, h2⟩ := hc n
  refine ⟨fun x => ?_, fun i y hy => ?_⟩
  · obtain ⟨i', y, hy⟩ := h1 x
    exact ⟨L.obj i', y, hy⟩
  · obtain ⟨i', ⟨f⟩⟩ := hL i
    have hy' : pull R ((c.whisker L).π.app i') F n (pull R (G.map f) F n y) = 0 := by
      change pull R (c.π.app (L.obj i')) F n (pull R (G.map f) F n y) = 0
      rw [← pull_comp, c.w f]
      exact hy
    obtain ⟨k', g, hg⟩ := h2 i' _ hy'
    refine ⟨L.obj k', L.map g ≫ f, ?_⟩
    rw [Functor.map_comp, pull_comp]
    exact hg

end GlobalTheory.EtC
end
