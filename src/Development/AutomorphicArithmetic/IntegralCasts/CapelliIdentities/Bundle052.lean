module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Mathlib.MeasureTheory.Measure.Map
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.ExpDecay

@[expose] public section

section

namespace MeasureEqCardCosetsMul
end MeasureEqCardCosetsMul

theorem UpperTheory.Reformulated.B.Yla7.main :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G]
      [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsMulLeftInvariant] {I : Subgroup G},
      IsOpen (↑I : Set G) →
        ∀ {D : Set G},
          (∀ g ∈ D, ∀ i ∈ I, g * i ∈ D) →
            ∀ (S : Finset (G ⧸ I)),
              (∀ (q : G ⧸ I), q ∈ S ↔ Quotient.out q ∈ D) →
                (μ : Set G → ENNReal) D = (↑S.card : ENNReal) * (μ : Set G → ENNReal) (↑I : Set G) := by
  intro G _ _ _ _ _ μ _ I hI D hD S hS
  classical
  set f : G ⧸ I → Set G := fun q => (fun h => (Quotient.out q)⁻¹ * h) ⁻¹' (I : Set G) with hf
  have hmem : ∀ q x, x ∈ f q ↔ (Quotient.out q)⁻¹ * x ∈ I := fun q x => Iff.rfl
  have hmk : ∀ q x, x ∈ f q → (QuotientGroup.mk x : G ⧸ I) = q := by
    intro q x hx
    rw [hmem] at hx
    have : (QuotientGroup.mk (Quotient.out q) : G ⧸ I) = QuotientGroup.mk x :=
      QuotientGroup.eq.mpr hx
    rw [← this]
    exact Quotient.out_eq' q
  have hDeq : D = ⋃ q ∈ S, f q := by
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk x : G ⧸ I), ?_, ?_⟩
      · rw [hS]
        obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul I x
        rw [hh]
        exact hD x hx h h.2
      · rw [hmem]
        have : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk x : G ⧸ I)) : G ⧸ I) = QuotientGroup.mk x :=
          Quotient.out_eq' _
        exact QuotientGroup.eq.mp this
    · rintro ⟨q, hq, hx⟩
      rw [hmem] at hx
      have h1 := hD _ ((hS q).mp hq) _ hx
      simpa using h1
  have hdisj : (S : Set (G ⧸ I)).PairwiseDisjoint f := by
    intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro x hxa hxb
    exact hab ((hmk a x hxa).symm.trans (hmk b x hxb))
  have hmeas : ∀ q ∈ S, MeasurableSet (f q) := by
    intro q _
    exact (hI.preimage (continuous_const.mul continuous_id)).measurableSet
  rw [hDeq, MeasureTheory.measure_biUnion_finset hdisj hmeas]
  have : ∀ q ∈ S, μ (f q) = μ (I : Set G) := by
    intro q _
    exact MeasureTheory.measure_preimage_mul μ _ _
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
end

section

open MeasureTheory in
private theorem UpperTheory.restricted_product_measure_set
    (V G Gi : Type) (Gv : V → Type) [MeasurableSpace G] [MeasurableSpace Gi] [∀ v, MeasurableSpace (Gv v)]
    (q : G → Gi) (p : ∀ v, G → Gv v) (K : ∀ v, Set (Gv v))
    (μ : Measure G) (μi : Measure Gi) (m : ∀ v, Measure (Gv v))
    [SigmaFinite μi] [∀ v, SigmaFinite (m v)]
    (hq : Measurable q) (hp : ∀ v, Measurable (p v)) (hK : ∀ v, MeasurableSet (K v))
    (h1 : ∀ v, m v (K v) = 1) (A : Set Gi) (hA : MeasurableSet A)
    (S : Finset V) (a : NNReal)
    (h : Measure.map (fun g => (q g, fun v : S => p v g)) (μ.restrict {g | ∀ v ∉ S, p v g ∈ K v}) =
      a • μi.prod (Measure.pi fun v : S => m v)) :
    μ {g | q g ∈ A ∧ ∀ v, p v g ∈ K v} = (a : ENNReal) * μi A := by
  have hf : Measurable (fun g => (q g, fun v : S => p v g)) :=
    hq.prodMk (Measurable.of_eval fun v => hp v)
  have hB : MeasurableSet (A ×ˢ (Set.univ.pi fun v : S => K v)) :=
    hA.prod (MeasurableSet.univ_pi fun v => hK v)
  have h2 := congrArg (fun ν => ν (A ×ˢ (Set.univ.pi fun v : S => K v))) h
  simp only [Measure.map_apply hf hB, Measure.restrict_apply (hf hB)] at h2
  rw [Measure.coe_nnreal_smul_apply, Measure.prod_prod, Measure.pi_pi] at h2
  simp only [h1, Finset.prod_const_one, mul_one] at h2
  rw [← h2]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_pi,
    Set.mem_univ, true_imp_iff]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨⟨ha, fun v => hb v⟩, fun v _ => hb v⟩
  · rintro ⟨⟨ha, hb⟩, hc⟩
    refine ⟨ha, fun v => ?_⟩
    by_cases hv : v ∈ S
    · exact hb ⟨v, hv⟩
    · exact hc v hv

theorem UpperTheory.restricted_product_measure :
    ∀ (V G Gi : Type) (Gv : V → Type) [MeasurableSpace G] [MeasurableSpace Gi] [∀ v, MeasurableSpace (Gv v)]
        (q : G → Gi) (p : ∀ v, G → Gv v) (K : ∀ v, Set (Gv v))
        (μ : MeasureTheory.Measure G) (μi : MeasureTheory.Measure Gi) (m : ∀ v, MeasureTheory.Measure (Gv v))
        [MeasureTheory.SigmaFinite μi] [∀ v, MeasureTheory.SigmaFinite (m v)],
        Measurable q → (∀ v, Measurable (p v)) → (∀ v, MeasurableSet (K v)) → (∀ v, m v (K v) = 1) →
        (∃ A : Set Gi, MeasurableSet A ∧ μi A ≠ 0 ∧ μi A ≠ ⊤) →
        ∀ (S T : Finset V) (a b : NNReal),
          MeasureTheory.Measure.map (fun g => (q g, fun v : S => p v g)) (μ.restrict {g | ∀ v ∉ S, p v g ∈ K v}) =
            a • μi.prod (MeasureTheory.Measure.pi fun v : S => m v) →
          MeasureTheory.Measure.map (fun g => (q g, fun v : T => p v g)) (μ.restrict {g | ∀ v ∉ T, p v g ∈ K v}) =
            b • μi.prod (MeasureTheory.Measure.pi fun v : T => m v) →
          a = b := by
  intro V G Gi Gv _ _ _ q p K μ μi m _ _ hq hp hK h1 ⟨A, hA, h0, ht⟩ S T a b hS hT
  have e1 := UpperTheory.restricted_product_measure_set V G Gi Gv q p K μ μi m hq hp hK h1 A hA S a hS
  have e2 := UpperTheory.restricted_product_measure_set V G Gi Gv q p K μ μi m hq hp hK h1 A hA T b hT
  have e : (a : ENNReal) * μi A = (b : ENNReal) * μi A := e1.symm.trans e2
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 ht).1 e)
end

section

open MeasureTheory in
private theorem UpperTheory.Reformulated.B.Qe3b.mp_left.{u_1, u_2, u_3}
    {ι : Type u_1} {κ : Type u_2} {X : Type u_3} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] :
    MeasurePreserving (fun (f : ι → κ → X) (p : ι × κ) ↦ f p.1 p.2)
      (Measure.pi fun (_ : ι) ↦ Measure.pi fun (_ : κ) ↦ ν)
      (Measure.pi fun (_ : ι × κ) ↦ ν) := by
  have hm : Measurable (fun (f : ι → κ → X) (p : ι × κ) ↦ f p.1 p.2) := by fun_prop
  refine ⟨hm, (Measure.pi_eq fun s hs ↦ ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have h : (fun (f : ι → κ → X) (p : ι × κ) ↦ f p.1 p.2) ⁻¹' Set.univ.pi s
      = Set.univ.pi fun i ↦ Set.univ.pi fun k ↦ s (i, k) := by
    ext f
    simp [Set.mem_pi]
  rw [h, Measure.pi_pi, Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun i _ ↦ Measure.pi_pi _ _

open MeasureTheory in
private theorem UpperTheory.Reformulated.B.Qe3b.mp_right.{u_1, u_2, u_3}
    {ι : Type u_1} {κ : Type u_2} {X : Type u_3} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] :
    MeasurePreserving (fun (f : κ → ι → X) (p : ι × κ) ↦ f p.2 p.1)
      (Measure.pi fun (_ : κ) ↦ Measure.pi fun (_ : ι) ↦ ν)
      (Measure.pi fun (_ : ι × κ) ↦ ν) := by
  have hm : Measurable (fun (f : κ → ι → X) (p : ι × κ) ↦ f p.2 p.1) := by fun_prop
  refine ⟨hm, (Measure.pi_eq fun s hs ↦ ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have h : (fun (f : κ → ι → X) (p : ι × κ) ↦ f p.2 p.1) ⁻¹' Set.univ.pi s
      = Set.univ.pi fun k ↦ Set.univ.pi fun i ↦ s (i, k) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Prod.forall]
    exact forall_comm
  rw [h, Measure.pi_pi, Fintype.prod_prod_type_right]
  exact Finset.prod_congr rfl fun i _ ↦ Measure.pi_pi _ _

theorem UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi.{u_1, u_2, u_3} :
    ∀ {ι : Type u_1} {κ : Type u_2} {X : Type u_3} [inst : Fintype ι] [inst_1 : Fintype κ]
    [inst_2 : MeasurableSpace X] (ν : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite ν],
    MeasureTheory.MeasurePreserving (fun (f : ι → κ → X) (k : κ) (i : ι) ↦ f i k)
      (MeasureTheory.Measure.pi fun (x : ι) ↦ MeasureTheory.Measure.pi fun (x : κ) ↦ ν)
      (MeasureTheory.Measure.pi fun (x : κ) ↦ MeasureTheory.Measure.pi fun (x : ι) ↦ ν) := by
  intro ι κ X _ _ _ ν _
  let e : (κ → ι → X) ≃ᵐ (ι × κ → X) :=
    { toFun := fun f p ↦ f p.2 p.1
      invFun := fun g k i ↦ g (i, k)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      measurable_toFun := by
        change Measurable (fun (f : κ → ι → X) (p : ι × κ) ↦ f p.2 p.1)
        fun_prop
      measurable_invFun := by
        change Measurable (fun (g : ι × κ → X) (k : κ) (i : ι) ↦ g (i, k))
        fun_prop }
  exact (MeasureTheory.MeasurePreserving.symm e
    (UpperTheory.Reformulated.B.Qe3b.mp_right (ι := ι) (κ := κ) ν)).comp (UpperTheory.Reformulated.B.Qe3b.mp_left ν)
end

section

open MeasureTheory in
theorem UpperTheory.Reformulated.B.MapPiScale.map_pi_scale :
    ∀ {ι : Type} [inst : Fintype ι] {α : ι → Type}
    [inst_1 : (i : ι) → MeasurableSpace (α i)] (μ : (i : ι) → MeasureTheory.Measure (α i))
    [∀ (i : ι), MeasureTheory.SigmaFinite (μ i)] (g : (i : ι) → α i → α i),
    (∀ (i : ι), Measurable (g i)) →
      ∀ (c : ι → ENNReal),
        (∀ (i : ι), c i ≠ (0 : ENNReal)) →
          (∀ (i : ι), c i ≠ ⊤) →
            (∀ (i : ι), MeasureTheory.Measure.map (g i) (μ i) = c i • μ i) →
              MeasureTheory.Measure.map (fun (x : (i : ι) → α i) (i : ι) ↦ g i (x i)) (MeasureTheory.Measure.pi μ) =
                (∏ i : ι, c i) • MeasureTheory.Measure.pi μ := by
  intro ι _ α _ μ _ g hg c _ hc h
  have hs : ∀ i, SigmaFinite ((μ i).map (g i)) := by
    intro i
    rw [h i, ← ENNReal.coe_toNNReal (hc i)]
    exact (inferInstance : SigmaFinite ((c i).toNNReal • μ i))
  rw [Measure.pi_map_pi (fun i => (hg i).aemeasurable)]
  refine Measure.pi_eq fun s _ => ?_
  simp only [h, Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]
end

section

theorem UpperTheory.Reformulated.B.VolumePreservingUncurry.volume_preserving_uncurry.{u_1, u_2} :
    ∀ (ι : Type u_1) (κ : Type u_2) [inst : Fintype ι] [inst_1 : Fintype κ],
      @MeasureTheory.MeasurePreserving (ι → κ → Real) (Prod ι κ → Real)
        (@MeasureTheory.MeasureSpace.toMeasurableSpace (ι → κ → Real)
          (@MeasureTheory.MeasureSpace.pi ι inst (fun (a : ι) ↦ κ → Real) fun (i : ι) ↦
            @MeasureTheory.MeasureSpace.pi κ inst_1 (fun (a : κ) ↦ Real) fun (i : κ) ↦ Real.measureSpace))
        (@MeasureTheory.MeasureSpace.toMeasurableSpace (Prod ι κ → Real)
          (@MeasureTheory.MeasureSpace.pi (Prod ι κ) (@instFintypeProd ι κ inst inst_1) (fun (a : Prod ι κ) ↦ Real)
            fun (i : Prod ι κ) ↦ Real.measureSpace))
        (@Function.uncurry ι κ Real)
        (@MeasureTheory.MeasureSpace.volume (ι → κ → Real)
          (@MeasureTheory.MeasureSpace.pi ι inst (fun (a : ι) ↦ κ → Real) fun (i : ι) ↦
            @MeasureTheory.MeasureSpace.pi κ inst_1 (fun (a : κ) ↦ Real) fun (i : κ) ↦ Real.measureSpace))
        (@MeasureTheory.MeasureSpace.volume (Prod ι κ → Real)
          (@MeasureTheory.MeasureSpace.pi (Prod ι κ) (@instFintypeProd ι κ inst inst_1) (fun (a : Prod ι κ) ↦ Real)
            fun (i : Prod ι κ) ↦ Real.measureSpace)) := by
  intro ι κ _ _
  have hm : Measurable (@Function.uncurry ι κ ℝ) :=
    Measurable.of_eval fun p ↦ (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  refine ⟨hm, ?_⟩
  symm
  refine MeasureTheory.Measure.pi_eq (μ := fun _ : ι × κ ↦ (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ?_
  intro s hs
  rw [MeasureTheory.Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (@Function.uncurry ι κ ℝ) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi fun i ↦ Set.univ.pi fun k ↦ s (i, k) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Prod.forall,
      Function.uncurry_apply_pair]
  rw [hpre, MeasureTheory.volume_pi_pi, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [MeasureTheory.volume_pi_pi]
end

section

namespace YhaHelp
open MeasureTheory Set Real

private lemma F_int {c : ℝ} (hc : 0 < c) :
    Integrable ((Ici (0:ℝ)).indicator (fun x : ℝ => exp (-c * x))) := by
  rw [integrable_indicator_iff measurableSet_Ici]
  exact (exp_neg_integrableOn_Ioi (-1) hc).mono_set (fun x hx => by
    simp only [mem_Ici, mem_Ioi] at *; linarith)

end YhaHelp

theorem UpperTheory.Reformulated.B.Yha4.main :
    ∀ {c : ℝ}, (0 : ℝ) < c → MeasureTheory.Integrable (fun (x : ℝ) ↦ Real.exp (-c * |x|)) MeasureTheory.MeasureSpace.volume := by
  intro c hc
  have hF := YhaHelp.F_int hc
  have hG := hF.comp_neg
  refine (hF.add hG).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply, Set.indicator, Set.mem_Ici, Left.nonneg_neg_iff]
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h, if_pos h]
    split_ifs
    · linarith [Real.exp_pos (-c * -x)]
    · simp
  · rw [abs_of_neg h, if_neg (not_le.mpr h), if_pos h.le]
    simp
end

section

theorem UpperTheory.ae_fundamental_domain :
    ∀ {G Q : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableSpace Q]
        (Γ : Subgroup G) [Countable Γ] (μ : MeasureTheory.Measure G) [μ.IsMulLeftInvariant] (D : Set G) (π : G → Q),
        Measurable π → (∀ (γ : Γ) (g : G), π ((γ : G) * g) = π g) → (∀ g : G, ∃ γ : Γ, (γ : G) * g ∈ D) →
        ∀ p : Q → Prop, (∀ᵐ q ∂(MeasureTheory.Measure.map π (μ.restrict D)), p q) → ∀ᵐ y ∂μ, p (π y) := by
  intro G Q _ _ _ _ Γ _ μ _ D π hπ hinv hcov p hp
  rw [MeasureTheory.ae_iff] at hp ⊢
  obtain ⟨N, hsub, hNm, hN0⟩ := MeasureTheory.exists_measurable_superset_of_null hp
  rw [MeasureTheory.Measure.map_apply hπ hNm,
    MeasureTheory.Measure.restrict_apply (hπ hNm)] at hN0
  have hcover : {y | ¬ p (π y)} ⊆
      ⋃ γ : Γ, (fun g : G => (γ : G) * g) ⁻¹' (π ⁻¹' N ∩ D) := by
    intro y hy
    obtain ⟨γ, hγ⟩ := hcov y
    refine Set.mem_iUnion.2 ⟨γ, ?_, hγ⟩
    show π ((γ : G) * y) ∈ N
    rw [hinv]
    exact hsub hy
  refine MeasureTheory.measure_mono_null hcover (MeasureTheory.measure_iUnion_null fun γ => ?_)
  rw [MeasureTheory.measure_preimage_mul]
  exact hN0
end

section

namespace MulEquivHaarCharEqOfProjection
open MeasureTheory

private lemma smul_nn {α : Type*} [MeasurableSpace α] (c : NNReal) (μ : Measure α) (s : Set α) :
    (c • μ) s = (c : ENNReal) * μ s := Measure.coe_nnreal_smul_apply c μ s

end MulEquivHaarCharEqOfProjection

open MeasureTheory MeasureTheory.Measure in
theorem UpperTheory.Reformulated.B.Yhb4.main :
    ∀ {H N : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [inst_2 : IsTopologicalGroup H]
      [inst_3 : LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [inst_6 : MeasurableSpace H]
      [inst_7 : BorelSpace H] [inst_8 : Group N] [inst_9 : TopologicalSpace N] [inst_10 : IsTopologicalGroup N]
      [inst_11 : LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [inst_14 : MeasurableSpace N]
      [inst_15 : BorelSpace N] (ι : N →* H),
      Continuous (⇑ι : N → H) →
        ∀ (π : H → N),
          Continuous π →
            (∀ (x : N) (p : H), π ((ι : N → H) x * p) = x * π p) →
              ∀ (φ : H ≃ₜ* H) (ψ : N ≃ₜ* N),
                (∀ (p : H), π ((φ : H → H) p) = (ψ : N → N) (π p)) →
                  (∀ (p : H), ((ι : N → H) (π ((φ : H → H) p)))⁻¹ * (φ : H → H) p = ((ι : N → H) (π p))⁻¹ * p) →
                    MeasureTheory.mulEquivHaarChar φ = MeasureTheory.mulEquivHaarChar ψ := by
  intro H N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι hι π hπ hπι φ ψ hφψ hσ
  classical
  let σ : H → H := fun p => (ι (π p))⁻¹ * p
  have hσc : Continuous σ := ((hι.comp hπ).inv).mul continuous_id
  have hsplit : ∀ p, ι (π p) * σ p = p := by intro p; simp [σ]
  have hσmul : ∀ x p, σ (ι x * p) = σ p := by
    intro x p; simp [σ, hπι, mul_assoc]
  have hσφ : ∀ p, σ (φ p) = σ p := fun p => hσ p
  obtain ⟨C, hCc, hCn⟩ := exists_compact_mem_nhds (σ 1)
  let μH : Measure H := Measure.haar
  let μN : Measure N := Measure.haar
  let m : Measure N := Measure.map π (μH.restrict (σ ⁻¹' C))
  have hσC : MeasurableSet (σ ⁻¹' C) := (hCc.isClosed.preimage hσc).measurableSet
  have hmA : ∀ A, MeasurableSet A → m A = μH (π ⁻¹' A ∩ σ ⁻¹' C) := by
    intro A hA
    rw [Measure.map_apply hπ.measurable hA, Measure.restrict_apply (hπ.measurable hA)]
  have hinv : m.IsMulLeftInvariant := by
    refine ⟨fun x => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_mul x) hA, hmA _ hA, hmA _ ((measurable_const_mul x) hA)]
    have : π ⁻¹' ((fun y => x * y) ⁻¹' A) ∩ σ ⁻¹' C
        = (fun p => ι x * p) ⁻¹' (π ⁻¹' A ∩ σ ⁻¹' C) := by
      ext p; simp [hπι, hσmul]
    rw [this, measure_preimage_mul]
  have hfin : IsFiniteMeasureOnCompacts m := by
    refine ⟨fun K hK => ?_⟩
    rw [hmA _ hK.isClosed.measurableSet]
    have hcomp : IsCompact ((fun q : N × H => ι q.1 * q.2) '' (K ×ˢ C)) :=
      (hK.prod hCc).image ((hι.comp continuous_fst).mul continuous_snd)
    refine lt_of_le_of_lt (measure_mono ?_) hcomp.measure_lt_top
    rintro p ⟨hp1, hp2⟩
    exact ⟨(π p, σ p), ⟨hp1, hp2⟩, hsplit p⟩
  have hc : m = haarScalarFactor m μN • μN := isMulLeftInvariant_eq_smul m μN
  set c := haarScalarFactor m μN with hcdef
  have hmuniv : 0 < m Set.univ := by
    rw [hmA _ MeasurableSet.univ, Set.preimage_univ, Set.univ_inter]
    have h1 : σ ⁻¹' C ∈ nhds (1 : H) := hσc.continuousAt.preimage_mem_nhds hCn
    exact measure_pos_of_nonempty_interior μH ⟨1, mem_interior_iff_mem_nhds.2 h1⟩
  have hc0 : (c : ENNReal) ≠ 0 := by
    intro h0
    rw [hc, MulEquivHaarCharEqOfProjection.smul_nn, h0, zero_mul] at hmuniv
    exact lt_irrefl _ hmuniv
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds (1 : N)
  let A : Set N := ψ.symm ⁻¹' K
  have hAm : MeasurableSet A := (hKc.isClosed.preimage ψ.symm.continuous).measurableSet
  have hApre : ψ ⁻¹' A = K := by ext x; simp [A]
  have hK0 : μN K ≠ 0 :=
    (measure_pos_of_nonempty_interior μN ⟨1, mem_interior_iff_mem_nhds.2 hKn⟩).ne'
  have hKt : μN K ≠ ⊤ := hKc.measure_lt_top.ne

  have e1 := mulEquivHaarChar_smul_preimage μH (X := π ⁻¹' A ∩ σ ⁻¹' C) φ
  have hpre : ⇑φ ⁻¹' (π ⁻¹' A ∩ σ ⁻¹' C) = π ⁻¹' K ∩ σ ⁻¹' C := by
    ext p; simp [A, hφψ, hσφ]
  rw [hpre, ← hmA _ hKc.isClosed.measurableSet, ← hmA _ hAm, hc, ENNReal.smul_def,
    MulEquivHaarCharEqOfProjection.smul_nn, MulEquivHaarCharEqOfProjection.smul_nn] at e1
  have e2 := mulEquivHaarChar_smul_preimage μN (X := A) ψ
  rw [hApre] at e2
  simp only [ENNReal.smul_def, smul_eq_mul] at e1 e2
  have key : ((c : ENNReal) * μN K) * (mulEquivHaarChar φ : ENNReal)
      = ((c : ENNReal) * μN K) * (mulEquivHaarChar ψ : ENNReal) := by
    calc ((c : ENNReal) * μN K) * (mulEquivHaarChar φ : ENNReal)
        = (mulEquivHaarChar φ : ENNReal) * ((c : ENNReal) * μN K) := by ring
      _ = (c : ENNReal) * μN A := e1
      _ = (c : ENNReal) * ((mulEquivHaarChar ψ : ENNReal) * μN K) := by rw [e2]
      _ = ((c : ENNReal) * μN K) * (mulEquivHaarChar ψ : ENNReal) := by ring
  rw [ENNReal.mul_right_inj (mul_ne_zero hc0 hK0) (ENNReal.mul_ne_top ENNReal.coe_ne_top hKt)] at key
  exact_mod_cast key
end

section

noncomputable def UpperTheory.Reformulated.B.Yhb9.DenLE :
    {V H : Type} →
      [inst : MeasurableSpace V] →
        [inst_1 : MeasurableSpace H] → MeasureTheory.Measure V → MeasureTheory.Measure H → (V → H) → Set V → ENNReal → Prop :=
    fun {V H : Type} [MeasurableSpace V] [MeasurableSpace H] (μ : MeasureTheory.Measure V) (ν : MeasureTheory.Measure H)
        (q : V → H) (S : Set V) (C : ENNReal) ↦
      ∀ (Y : Set H), MeasurableSet Y → (μ : Set V → ENNReal) (S ∩ q ⁻¹' Y) ≤ C * (ν : Set H → ENNReal) Y

theorem UpperTheory.Reformulated.B.Yhb9.main :
    ∀ {V H : Type} [inst : MeasurableSpace V] [inst_1 : MeasurableSpace H] {μ : MeasureTheory.Measure V}
      {ν : MeasureTheory.Measure H} {q : V → H} {T : V → V} {τ : H → H},
      MeasurableEmbedding T →
        Measurable τ →
          (∀ (X : V), q (T X) = τ (q X)) →
            ∀ {a c : NNReal},
              a ≠ (0 : NNReal) →
                MeasureTheory.Measure.map T μ = a • μ →
                  MeasureTheory.Measure.map τ ν = c • ν →
                    ∀ {S : Set V} {C : ENNReal},
                      UpperTheory.Reformulated.B.Yhb9.DenLE μ ν q S C → UpperTheory.Reformulated.B.Yhb9.DenLE μ ν q (T '' S) ((↑(a⁻¹ * c) : ENNReal) * C) := by
  intro V H _ _ μ ν q T τ hT hτ hq a c ha hTμ hτν S C hS Y hY
  have h1 : T ⁻¹' (T '' S ∩ q ⁻¹' Y) = S ∩ q ⁻¹' (τ ⁻¹' Y) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, hT.injective.mem_set_image, hq]
  have h2 : (a : ENNReal) * μ (T '' S ∩ q ⁻¹' Y) = μ (S ∩ q ⁻¹' (τ ⁻¹' Y)) := by
    have := congrArg (fun m => m (T '' S ∩ q ⁻¹' Y)) hTμ
    rw [hT.map_apply, h1, MeasureTheory.Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    exact this.symm
  have h3 : ν (τ ⁻¹' Y) = (c : ENNReal) * ν Y := by
    have := congrArg (fun m => m Y) hτν
    rw [MeasureTheory.Measure.map_apply hτ hY, MeasureTheory.Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul] at this
    exact this
  have h4 := hS (τ ⁻¹' Y) (hτ hY)
  rw [h3, ← h2] at h4
  have ha' : (a : ENNReal) ≠ 0 := by exact_mod_cast ha
  calc μ (T '' S ∩ q ⁻¹' Y) = (a : ENNReal)⁻¹ * ((a : ENNReal) * μ (T '' S ∩ q ⁻¹' Y)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha' ENNReal.coe_ne_top, one_mul]
    _ ≤ (a : ENNReal)⁻¹ * (C * ((c : ENNReal) * ν Y)) := by gcongr
    _ = _ := by rw [ENNReal.coe_mul, ENNReal.coe_inv ha]; ring
end
