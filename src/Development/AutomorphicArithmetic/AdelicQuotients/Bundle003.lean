module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory
open scoped ENNReal NNReal

private theorem haar_inv_eq_self {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.inv = μ := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ.inv = c • μ :=
    ⟨Measure.haarScalarFactor μ.inv μ, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hinv : μ.inv.inv = μ := Measure.inv_inv μ
  have hsq : μ = (c * c) • μ := by
    calc μ = μ.inv.inv := hinv.symm
      _ = (c • μ).inv := by rw [hc]
      _ = c • μ.inv := by
        simpa only [Measure.inv_def] using Measure.map_smul c (μ := μ) measurable_inv.aemeasurable
      _ = c • (c • μ) := by rw [hc]
      _ = (c * c) • μ := by rw [smul_smul]
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have hpos : μ K ≠ 0 :=
    ((isOpen_interior.measure_pos μ K.interior_nonempty).trans_le
      (measure_mono interior_subset)).ne'
  have hfin : μ K ≠ ∞ := K.isCompact.measure_lt_top.ne
  have h3 : ((c * c : ℝ≥0) : ℝ≥0∞) * μ K = 1 * μ K := by
    rw [one_mul]
    conv_rhs => rw [hsq]
    simp
  have h4 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hpos hfin).1 h3
  have h5 : c = 1 := by
    rw [ENNReal.coe_eq_one, ← pow_two] at h4
    exact (pow_eq_one_iff_of_nonneg (zero_le : (0 : ℝ≥0) ≤ c) two_ne_zero).1 h4
  rw [hc, h5, one_smul]

theorem UpperTheory.haar_unimodular_criterion :
    UniOf := by
  intro G _ _ _ _ _ _ _ _ μ hμ
  have key : μ.IsMulRightInvariant → Uni μ := fun hr => ⟨hμ, ⟨haar_inv_eq_self μ⟩⟩
  refine ⟨key, fun hcomm => key ⟨fun g => ?_⟩⟩
  have h : (fun x : G => x * g) = fun x => g * x := funext fun x => hcomm x g
  rw [h]
  exact map_mul_left_eq_self μ g
end

section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory Topology Filter

theorem UpperTheory.exists_haarMeasure_adelicGL :
    HaarEx := by
  unfold HaarEx
  intro V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K hR μ μi m hμ hμi hm S
  classical
  haveI : ∀ v, (m v).IsHaarMeasure := hm
  have cf : Continuous (prS q p S) := by
    have h : ⇑(prS q p S) = fun g => (q g, fun v : S => p v g) := rfl
    rw [h]
    exact hR.cq.prodMk (continuous_pi fun v => hR.cp v)
  have mf : Measurable (prS q p S) := cf.measurable
  have hs : ∀ h : Gi × ∀ v : S, Gv v, ∃ u ∈ US p K S, prS q p S u = h := by
    rintro ⟨gi, gv⟩
    obtain ⟨g, h1, h2⟩ := hR.surj gi (fun v => if hv : v ∈ S then gv ⟨v, hv⟩ else 1) (by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ S := by simpa using hv
      rw [dif_neg hv']
      exact one_mem _)
    refine ⟨g, ?_, ?_⟩
    · intro v hv
      rw [h2, dif_neg hv]
      exact one_mem _
    · rw [prS_apply, h1]
      congr 1
      funext v
      rw [h2, dif_pos v.2]
  obtain ⟨ν, hν⟩ : ∃ ν, ν = (μ.restrict (US p K S : Set G)).map (prS q p S) := ⟨_, rfl⟩
  haveI inv : ν.IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    obtain ⟨u, hu, rfl⟩ := hs h
    ext A hA
    have hA' : MeasurableSet ((fun x => prS q p S u * x) ⁻¹' A) := measurable_const_mul _ hA
    rw [Measure.map_apply (measurable_const_mul _) hA, hν, Measure.map_apply mf hA',
      Measure.map_apply mf hA, Measure.restrict_apply (mf hA'), Measure.restrict_apply (mf hA)]
    have hset : prS q p S ⁻¹' ((fun x => prS q p S u * x) ⁻¹' A) ∩ (US p K S : Set G) =
        (fun x => u * x) ⁻¹' (prS q p S ⁻¹' A ∩ (US p K S : Set G)) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, SetLike.mem_coe,
        Subgroup.mul_mem_cancel_left _ hu]
    rw [hset, measure_preimage_mul]
  haveI fin : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun D hD => ?_⟩
    rw [hν, Measure.map_apply mf hD.measurableSet, Measure.restrict_apply (mf hD.measurableSet)]
    let C : ∀ v, Set (Gv v) := fun v =>
      if hv : v ∈ S then (fun h : Gi × ∀ v : S, Gv v => h.2 ⟨v, hv⟩) '' D else K v
    have hC : ∀ v, IsCompact (C v) := by
      intro v
      by_cases hv : v ∈ S
      · simp only [C, dif_pos hv]
        exact hD.image (by fun_prop)
      · simp only [C, dif_neg hv]
        exact hR.cpt v
    have hW := hR.prop (Prod.fst '' D) C (hD.image continuous_fst) hC (by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ S := by simpa using hv
      simp only [C, dif_neg hv']
      exact subset_rfl)
    refine lt_of_le_of_lt (measure_mono ?_) hW.measure_lt_top
    rintro g ⟨h1, h2⟩
    refine ⟨⟨_, h1, rfl⟩, fun v => ?_⟩
    by_cases hv : v ∈ S
    · simp only [C, dif_pos hv]
      exact ⟨_, h1, rfl⟩
    · simp only [C, dif_neg hv]
      exact h2 v hv
  have e := Measure.isMulLeftInvariant_eq_smul ν (μi.prod (Measure.pi fun v : S => m v))
  refine ⟨Measure.haarScalarFactor ν (μi.prod (Measure.pi fun v : S => m v)), ?_, ?_⟩
  · intro h0
    rw [h0, zero_smul] at e
    have h1 : ν Set.univ = 0 := by rw [e]; rfl
    rw [hν, Measure.map_apply mf MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ] at h1
    exact (hR.opnU S).measure_ne_zero μ ⟨1, one_mem _⟩ h1
  · unfold Eul
    rw [← hν]
    exact e
end

section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory
open scoped ENNReal Pointwise

private theorem inv_map_sub {G P : Type} [Group G] [Group P] [MeasurableSpace G] [MeasurableSpace P]
    [MeasurableInv G] [MeasurableInv P] (μ : Measure G) [μ.IsInvInvariant] (U : Subgroup G)
    (f : G →* P) (hf : Measurable f) (hU : MeasurableSet (U : Set G)) (E : Set P) (hE : MeasurableSet E) :
    ((μ.restrict (U : Set G)).map f) E⁻¹ = ((μ.restrict (U : Set G)).map f) E := by
  rw [Measure.map_apply hf hE.inv, Measure.map_apply hf hE, Measure.restrict_apply (hf hE.inv),
    Measure.restrict_apply (hf hE)]
  have h : f ⁻¹' E⁻¹ ∩ (U : Set G) = (f ⁻¹' E ∩ (U : Set G))⁻¹ := by
    ext x
    simp [Set.mem_inv, map_inv, Subgroup.inv_mem_iff]
  rw [h, Measure.measure_inv]

private theorem inv_all {P : Type} [Group P] [MeasurableSpace P] [MeasurableInv P] (ν : Measure P)
    (h : ∀ E, MeasurableSet E → ν E⁻¹ = ν E) (E : Set P) : ν E⁻¹ = ν E := by
  have hi : ν.inv = ν := Measure.ext fun E hE => by rw [Measure.inv_apply]; exact h E hE
  rw [← Measure.inv_apply, hi]

theorem UpperTheory.local_unimodular_of_exists_haar_measure :
    HaarEx → UniLoc := by
  intro hH V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K hRP μ μi m hμ hμi hm
  haveI := hμ.1
  haveI := hμ.2
  haveI := hμi
  haveI := fun v => hm v
  have key : ∀ (S : Finset V) (A : Set Gi) (B : ∀ v : S, Set (Gv v)),
      μi A⁻¹ * ∏ v : S, m v (B v)⁻¹ = μi A * ∏ v : S, m v (B v) := by
    intro S A B
    obtain ⟨a, ha, hE⟩ := hH V G Gi Gv q p K hRP μ μi m hμ.1 hμi hm S
    have hE' : (μ.restrict (US p K S : Set G)).map (prS q p S) = a • μi.prod (Measure.pi fun v : S => m v) := hE
    have hf : Measurable (prS q p S) := by
      have h1 : Measurable q := hRP.cq.measurable
      have h2 : Measurable fun g : G => fun v : S => p v g :=
        Measurable.of_eval fun v => (hRP.cp v).measurable
      exact h1.prodMk h2
    have hU : MeasurableSet (US p K S : Set G) := (hRP.opnU S).measurableSet
    have h1 := inv_all ((μ.restrict (US p K S : Set G)).map (prS q p S))
      (inv_map_sub μ (US p K S) (prS q p S) hf hU) (A ×ˢ Set.pi Set.univ B)
    have hset : (A ×ˢ Set.pi Set.univ B)⁻¹ = A⁻¹ ×ˢ Set.pi Set.univ (fun v => (B v)⁻¹) := by
      ext ⟨x, y⟩
      simp [Set.mem_prod, Set.mem_pi, Set.mem_inv]
    rw [hE', hset, Measure.smul_apply, Measure.smul_apply, Measure.prod_prod, Measure.prod_prod,
      Measure.pi_pi, Measure.pi_pi, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul] at h1
    exact (ENNReal.mul_right_inj (by exact_mod_cast ha) ENNReal.coe_ne_top).1 h1
  have hinv : ∀ A : Set Gi, μi A⁻¹ = μi A := by
    intro A
    have h := key ∅ A (fun _ => Set.univ)
    simpa using h
  refine ⟨⟨hμi, ⟨Measure.ext fun A _ => by rw [Measure.inv_apply]; exact hinv A⟩⟩, fun v => ⟨hm v, ⟨Measure.ext fun B _ => ?_⟩⟩⟩
  rw [Measure.inv_apply]
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : Gi)
  have hpos : μi C ≠ 0 := (Measure.measure_pos_of_mem_nhds μi hC1).ne'
  have htop : μi C ≠ ⊤ := hC.measure_lt_top.ne
  let v0 : ({v} : Finset V) := ⟨v, Finset.mem_singleton_self v⟩
  have h := key {v} C (Function.update (fun _ => Set.univ) v0 B)
  rw [hinv C, Fintype.prod_subsingleton _ v0, Fintype.prod_subsingleton _ v0] at h
  simp only [Function.update_self] at h
  exact (ENNReal.mul_right_inj hpos htop).1 h
end

section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

theorem UpperTheory.euler_product_support_finite :
    EulerSupp := by
  intro V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K T _ _ _ _ _ _ _ _
    Ti _ _ _ _ _ _ _ _ Tv _ _ _ _ _ _ _ _ qT pT KT hR hRT j ji jv hq hp hK S Fi Fv hFi hFii hFv hS
  classical
  have hKA : ∀ v x, x ∈ K v → ∃ t, ∃ y ∈ K v, x = jv v t * y :=
    fun v x hx => ⟨1, x, hx, by simp⟩
  have hfin : ∀ g, (Function.mulSupport fun v => Fv v (p v g)).Finite := by
    intro g
    refine ((Filter.eventually_cofinite.1 (hR.ae g)).union S.finite_toSet).subset ?_
    intro v hv
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, not_or, not_not] at hc
    exact hv ((hS v hc.2 _).1 (hKA v _ hc.1))
  obtain ⟨W, hW⟩ : ∃ W : Set G, W = {g | ∀ v ∉ S, ∃ t, ∃ y ∈ K v, p v g = jv v t * y} := ⟨_, rfl⟩
  have hmem : ∀ g, g ∈ W ↔ ∀ v ∉ S, ∃ t, ∃ y ∈ K v, p v g = jv v t * y := by
    intro g; rw [hW]; rfl
  have hoff : ∀ g, g ∉ W → ∏ᶠ v, Fv v (p v g) = 0 := by
    intro g hg
    rw [hmem] at hg
    push_neg at hg
    obtain ⟨v, hv, hx⟩ := hg
    refine finprod_eq_zero _ v ((hS v hv _).2 ?_) (hfin g)
    rintro ⟨t, y, hy, e⟩
    exact hx t y hy e
  have hon : ∀ g ∈ W, ∏ᶠ v, Fv v (p v g) = ∏ v ∈ S, Fv v (p v g) := by
    intro g hg
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hc
    exact hv ((hS v hc _).1 ((hmem g).1 hg v hc))
  have hWopen : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun x => g⁻¹ * x) ⁻¹' (US p K S : Set G), ?_,
      (continuous_const.mul continuous_id).isOpen_preimage _ (hR.opnU S), ?_⟩
    · intro x hx
      refine (hmem x).2 fun v hv => ?_
      obtain ⟨t, y, hy, e⟩ := (hmem g).1 hg v hv
      have hx' : p v (g⁻¹ * x) ∈ K v := hx v hv
      refine ⟨t, y * p v (g⁻¹ * x), mul_mem hy hx', ?_⟩
      rw [← mul_assoc, ← e, ← map_mul, mul_inv_cancel_left]
    · simp only [Set.mem_preimage, inv_mul_cancel]
      exact one_mem (US p K S)
  have hqm : Measurable q := hR.cq.measurable
  have hpm : ∀ v, Measurable (p v) := fun v => (hR.cp v).measurable
  have hmeas : Measurable fun g => Fi (q g) * ∏ v ∈ S, Fv v (p v g) :=
    (hFi.comp hqm).mul (Finset.measurable_prod _ fun v _ => (hFv v).1.comp (hpm v))
  have hEq : (fun g => Fi (q g) * ∏ᶠ v, Fv v (p v g)) =
      W.indicator (fun g => Fi (q g) * ∏ v ∈ S, Fv v (p v g)) := by
    funext g
    by_cases hg : g ∈ W
    · rw [Set.indicator_of_mem hg, hon g hg]
    · rw [Set.indicator_of_notMem hg, hoff g hg, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [hEq]
    exact hmeas.indicator hWopen.measurableSet
  · intro g h
    have hgW : g ∈ W := by
      by_contra hc
      exact h (by rw [hoff g hc, mul_zero])
    have hch : ∀ v, ∃ t : Tv v, (p v g ∈ K v → t = 1) ∧ (v ∉ S → (jv v t)⁻¹ * p v g ∈ K v) := by
      intro v
      by_cases hk : p v g ∈ K v
      · exact ⟨1, fun _ => rfl, fun _ => by simpa using hk⟩
      · by_cases hv : v ∈ S
        · exact ⟨1, fun h => absurd h hk, fun h => absurd hv h⟩
        · obtain ⟨t, y, hy, e⟩ := (hmem g).1 hgW v hv
          exact ⟨t, fun h => absurd h hk, fun _ => by rw [e]; simpa using hy⟩
    choose tv ht1 ht2 using hch
    obtain ⟨t, -, ht⟩ := hRT.surj 1 tv
      ((hR.ae g).mono fun v hv => by rw [ht1 v hv]; exact one_mem _)
    refine Set.mem_mul.2 ⟨j t, ⟨t, rfl⟩, (j t)⁻¹ * g, ?_, mul_inv_cancel_left _ _⟩
    refine SetLike.mem_coe.2 (mem_US.2 fun v hv => ?_)
    rw [map_mul, map_inv, hp, ht]
    exact ht2 v hv
  · intro u hu
    have huW : u ∈ W := (hmem u).2 fun v hv => hKA v _ (hu v hv)
    rw [hon u huW, Finset.prod_coe_sort S (fun v => Fv v (p v u))]
end

section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open Polynomial

private theorem charpoly_unit_smul {R : Type} [CommRing R] {n : ℕ} (r : Rˣ)
    (M : Matrix (Fin n) (Fin n) R) :
    ((r : R) • M).charpoly =
      C ((r : R) ^ n) * M.charpoly.comp (C ((r⁻¹ : Rˣ) : R) * X) := by
  have hc : (C (r : R) : R[X]) * C ((r⁻¹ : Rˣ) : R) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  have hmat : Matrix.charmatrix ((r : R) • M) =
      (C (r : R) : R[X]) • (Matrix.charmatrix M).map
        (compRingHom (C ((r⁻¹ : Rˣ) : R) * X)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.charmatrix_apply_eq, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        coe_compRingHom_apply, sub_comp, X_comp, C_comp, mul_sub, ← mul_assoc, hc, one_mul,
        ← C_mul]
    · simp only [Matrix.charmatrix_apply_ne _ _ _ h, Matrix.smul_apply, Matrix.map_apply,
        smul_eq_mul, coe_compRingHom_apply, neg_comp, C_comp, mul_neg, ← C_mul]
  have hdet : M.charpoly.comp (C ((r⁻¹ : Rˣ) : R) * X) =
      ((Matrix.charmatrix M).map (compRingHom (C ((r⁻¹ : Rˣ) : R) * X))).det := by
    rw [Matrix.charpoly, ← coe_compRingHom_apply, RingHom.map_det]
    rfl
  rw [Matrix.charpoly, hmat, Matrix.det_smul, Fintype.card_fin, hdet, C_pow]

private theorem separable_comp_unit {R : Type} [CommRing R] (r : Rˣ) {p : R[X]}
    (hp : p.Separable) : (p.comp (C ((r⁻¹ : Rˣ) : R) * X)).Separable := by
  obtain ⟨a, b, hab⟩ := hp
  set L : R[X] := C ((r⁻¹ : Rˣ) : R) * X with hL
  have hd : derivative (p.comp L) = C ((r⁻¹ : Rˣ) : R) * (derivative p).comp L := by
    rw [derivative_comp, hL, derivative_C_mul, derivative_X, mul_one]
  have hc : (C (r : R) : R[X]) * C ((r⁻¹ : Rˣ) : R) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  refine ⟨a.comp L, b.comp L * C (r : R), ?_⟩
  have h := congrArg (fun q : R[X] => q.comp L) hab
  simp only [add_comp, mul_comp, one_comp] at h
  rw [hd, ← h]
  linear_combination ((b.comp L) * (derivative p).comp L) * hc

theorem UpperTheory.charpoly_separable_unit_smul :
    SepSc := by
  intro R _ n r M h
  rw [charpoly_unit_smul, Polynomial.separable_def, derivative_C_mul]
  exact (isCoprime_mul_unit_left (isUnit_C.2 (r.isUnit.pow n)) _ _).2
    (separable_comp_unit r h)
end

section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

theorem UpperTheory.adelicGL_split_equiv :
    SplitEquiv := by
  intro G₁ R G _ _ _ _ _ _ _ i d c hi hd hc hs hcomm hk
  have hd1 : ∀ x, d (i x) = 1 := fun x => (hk _).2 ⟨x, rfl⟩
  have h : ∀ g, ∃ x, i x = g * (c (d g))⁻¹ := fun g => by
    have h1 : d (g * (c (d g))⁻¹) = 1 := by
      rw [map_mul, map_inv, hs, mul_inv_cancel]
    exact (hk _).1 h1
  choose f hf using h
  have hfc : Continuous f := by
    refine hi.continuous_iff.2 ?_
    have h2 : (i ∘ f) = fun g => g * (c (d g))⁻¹ := funext hf
    rw [h2]
    exact continuous_id.mul (hc.comp hd).inv
  let E : G₁ × R ≃* G :=
    { toFun := fun x => i x.1 * c x.2
      invFun := fun g => (f g, d g)
      left_inv := by
        rintro ⟨x, r⟩
        have hdr : d (i x * c r) = r := by rw [map_mul, hd1, hs, one_mul]
        refine Prod.ext (hi.injective ?_) hdr
        show i (f (i x * c r)) = i x
        rw [hf, hdr, mul_inv_cancel_right]
      right_inv := by
        intro g
        show i (f g) * c (d g) = g
        rw [hf, inv_mul_cancel_right]
      map_mul' := by
        rintro ⟨x, r⟩ ⟨y, s⟩
        show i (x * y) * c (r * s) = i x * c r * (i y * c s)
        rw [map_mul, map_mul, mul_assoc (i x) (c r), ← mul_assoc (c r), hcomm r (i y)]
        simp only [mul_assoc] }
  exact ⟨{ E with
    continuous_toFun := (hi.continuous.comp continuous_fst).mul (hc.comp continuous_snd)
    continuous_invFun := hfc.prodMk hd }, fun x => rfl⟩
end

section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

theorem UpperTheory.restrictedProduct_centralizer_adelicGL :
    RPCen := by
  intro V G Gi Gv _ _ _ _ _ _ _ _ _ _ _ _ q p K h g
  have comm : ∀ {A : Type} [Group A] {a b : A}, b ∈ Subgroup.centralizer ({a} : Set A) ↔ a * b = b * a := by
    intro A _ a b
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun e => e.symm, fun e => e.symm⟩
  have key : ∀ x : G, q x ∈ Subgroup.centralizer ({q g} : Set Gi) →
      (∀ v, p v x ∈ Subgroup.centralizer ({p v g} : Set (Gv v))) →
      x ∈ Subgroup.centralizer ({g} : Set G) := by
    intro x h1 h2
    refine comm.2 (h.ext _ _ ?_ fun v => ?_)
    · rw [map_mul, map_mul]; exact comm.1 h1
    · rw [map_mul, map_mul]; exact comm.1 (h2 v)
  refine
    { cq := ?_, cp := ?_, opn := ?_, cpt := ?_, ae := ?_, opnU := ?_, ext := ?_, surj := ?_, prop := ?_ }
  · exact Continuous.subtype_mk (h.cq.comp continuous_subtype_val) _
  · intro v
    exact Continuous.subtype_mk ((h.cp v).comp continuous_subtype_val) _
  · intro v
    exact (h.opn v).preimage continuous_subtype_val
  · intro v
    have hc : IsClosed ((Subgroup.centralizer ({p v g} : Set (Gv v)) : Subgroup (Gv v)) : Set (Gv v)) := by
      have : ((Subgroup.centralizer ({p v g} : Set (Gv v)) : Subgroup (Gv v)) : Set (Gv v))
          = {x | p v g * x = x * p v g} := by
        ext x; exact comm
      rw [this]
      exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
    exact hc.isClosedEmbedding_subtypeVal.isCompact_preimage (h.cpt v)
  · intro t
    exact h.ae t
  · intro S
    exact (h.opnU S).preimage continuous_subtype_val
  · intro a b h1 h2
    exact Subtype.ext (h.ext _ _ (congrArg Subtype.val h1) fun v => congrArg Subtype.val (h2 v))
  · intro gi gv hv
    obtain ⟨x, hx, hx'⟩ := h.surj gi.1 (fun v => (gv v).1) hv
    refine ⟨⟨x, key x (hx ▸ gi.2) fun v => (hx' v).symm ▸ (gv v).2⟩, Subtype.ext hx, fun v => Subtype.ext (hx' v)⟩
  · intro Ci C hCi hC hae
    rw [Subtype.isCompact_iff]
    have e : Subtype.val '' {t : Subgroup.centralizer ({g} : Set G) | cen q g t ∈ Ci ∧ ∀ v, cen (p v) g t ∈ C v}
        = {x | q x ∈ Subtype.val '' Ci ∧ ∀ v, p v x ∈ Subtype.val '' C v} := by
      ext x
      constructor
      · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
        exact ⟨⟨_, h1, rfl⟩, fun v => ⟨_, h2 v, rfl⟩⟩
      · rintro ⟨⟨a, ha, ea⟩, h2⟩
        have hx : x ∈ Subgroup.centralizer ({g} : Set G) := by
          refine key x (ea ▸ a.2) fun v => ?_
          obtain ⟨b, -, eb⟩ := h2 v
          exact eb ▸ b.2
        refine ⟨⟨x, hx⟩, ⟨?_, fun v => ?_⟩, rfl⟩
        · have : cen q g ⟨x, hx⟩ = a := Subtype.ext ea.symm
          rw [this]; exact ha
        · obtain ⟨b, hb, eb⟩ := h2 v
          have : cen (p v) g ⟨x, hx⟩ = b := Subtype.ext eb.symm
          rw [this]; exact hb
    rw [e]
    refine h.prop _ _ (Subtype.isCompact_iff.1 hCi) (fun v => Subtype.isCompact_iff.1 (hC v)) ?_
    filter_upwards [hae] with v hv
    rintro _ ⟨b, hb, rfl⟩
    exact hv hb
end
