module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory

namespace UpperTheory.ConvolutionTheory.L1

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

omit [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] in
private theorem cvb_int {a b : G → ℂ} (ha : Continuous a) (ha' : HasCompactSupport a) (hb : Continuous b) (x : G) :
    Integrable (fun y => a y * b (y⁻¹ * x)) μ :=
  Continuous.integrable_of_hasCompactSupport (by fun_prop) (ha'.mul_right)

private theorem cvb_cont {a b : G → ℂ} (ha : Continuous a) (ha' : HasCompactSupport a) (hb : Continuous b) :
    Continuous (cv μ a b) := by
  have h : cv μ a b = fun x => ∫ y in tsupport a, a y * b (y⁻¹ * x) ∂μ := by
    funext x
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  rw [h]
  refine continuous_parametric_integral_of_continuous (f := fun x y => a y * b (y⁻¹ * x)) ?_ ha'
  unfold Function.uncurry
  fun_prop

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [BorelSpace G] [μ.IsHaarMeasure] in
private theorem cvb_supp {a b : G → ℂ} (x : G) (hx : cv μ a b x ≠ 0) :
    ∃ y z, a y ≠ 0 ∧ b z ≠ 0 ∧ x = y * z := by
  by_contra h
  apply hx
  have : (fun y => a y * b (y⁻¹ * x)) = fun _ => 0 := by
    funext y
    by_contra h'
    exact h ⟨y, y⁻¹ * x, left_ne_zero_of_mul h', right_ne_zero_of_mul h', by simp⟩
  simp only [cv, this, integral_zero]

open scoped Pointwise in
omit [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G] [μ.IsHaarMeasure] in
private theorem cvb_cs {a b : G → ℂ} (ha' : HasCompactSupport a) (hb' : HasCompactSupport b) :
    HasCompactSupport (cv μ a b) := by
  refine HasCompactSupport.intro (K := tsupport a * tsupport b) (IsCompact.mul ha' hb') fun x hx => ?_
  by_contra h
  obtain ⟨y, z, hy, hz, rfl⟩ := cvb_supp μ x h
  exact hx (Set.mul_mem_mul (subset_tsupport _ hy) (subset_tsupport _ hz))

open scoped Pointwise in
private theorem cvb_assoc {a b c : G → ℂ} (ha : Continuous a) (ha' : HasCompactSupport a) (hb : Continuous b)
    (hb' : HasCompactSupport b) (hc : Continuous c) : cv μ (cv μ a b) c = cv μ a (cv μ b c) := by
  funext x
  have hint : Integrable (Function.uncurry fun y z : G => a z * b (z⁻¹ * y) * c (y⁻¹ * x)) (μ.prod μ) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · unfold Function.uncurry
      fun_prop
    · refine HasCompactSupport.intro (K := (tsupport a * tsupport b) ×ˢ tsupport a)
        ((IsCompact.mul ha' hb').prod ha') fun p hp => ?_
      by_contra h
      have h1 := left_ne_zero_of_mul h
      have h2 : a p.2 ≠ 0 := left_ne_zero_of_mul h1
      have h3 : b (p.2⁻¹ * p.1) ≠ 0 := right_ne_zero_of_mul h1
      refine hp ⟨?_, subset_tsupport _ h2⟩
      have := Set.mul_mem_mul (subset_tsupport _ h2) (subset_tsupport _ h3)
      simpa using this
  calc cv μ (cv μ a b) c x = ∫ y, ∫ z, a z * b (z⁻¹ * y) * c (y⁻¹ * x) ∂μ ∂μ := by
        simp only [cv, integral_mul_const]
    _ = ∫ z, ∫ y, a z * b (z⁻¹ * y) * c (y⁻¹ * x) ∂μ ∂μ := integral_integral_swap hint
    _ = cv μ a (cv μ b c) x := by
        simp only [cv]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [← integral_const_mul, ← integral_mul_left_eq_self _ z]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp [mul_assoc]

end

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.cvBasic :
    UpperTheory.ConvolutionTheory.L1.CvBasic := by
  intro G _ _ _ _ _ _ _ _ μ _ a b c ha ha' hb hb' hc hc'
  refine ⟨cvb_cont μ ha ha' hb, cvb_cs μ ha' hb', cvb_supp μ, cvb_assoc μ ha ha' hb hb' hc, ?_, ?_, fun t => ⟨?_, ?_⟩⟩
  · funext x
    simp only [cv, Pi.add_apply, add_mul]
    exact integral_add (cvb_int μ ha ha' hc x) (cvb_int μ hb hb' hc x)
  · funext x
    simp only [cv, Pi.add_apply, mul_add]
    exact integral_add (cvb_int μ ha ha' hb x) (cvb_int μ ha ha' hc x)
  · funext x
    simp only [cv, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  · funext x
    simp only [cv, Pi.smul_apply, smul_eq_mul, mul_left_comm _ t, integral_const_mul]
end

section

open MeasureTheory Topology
open scoped ENNReal

theorem UpperTheory.ConvolutionTheory.L1.quotFin :
    UpperTheory.ConvolutionTheory.L1.QuotFin := by
  intro X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ i hi Φ ρ hΦ hinv hsupp hn
  obtain ⟨C, hC, hsup⟩ := hsupp
  obtain ⟨hρ, hnorm⟩ := hn
  have hnorm' : ∀ x : X, ∫⁻ t, ρ (i t * x) ∂ν = 1 := hnorm
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hΦ.continuousOn
  obtain ⟨K, hK, hCK⟩ := exists_compact_superset hC
  have hKm : MeasurableSet K := hK.measurableSet
  have hcont : Continuous (fun p : T × X => i p.1 * p.2) :=
    (hi.comp continuous_fst).mul continuous_snd
  have hopen : IsOpen ((fun p : T × X => i p.1 * p.2) ⁻¹' interior K) :=
    isOpen_interior.preimage hcont
  have hsub : ({1} : Set T) ×ˢ C ⊆ (fun p : T × X => i p.1 * p.2) ⁻¹' interior K := by
    rintro ⟨t, c⟩ ⟨ht, hc⟩
    have ht' : t = 1 := ht
    subst ht'
    simpa using hCK hc
  obtain ⟨U, V, hU, hV, h1U, hCV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hC hopen hsub
  obtain ⟨N, hN, hNU, hNc⟩ := local_compact_nhds (hU.mem_nhds (h1U rfl))
  have hNm : MeasurableSet N := hNc.measurableSet
  have hNpos : ν N ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hN).ne'
  have hNfin : ν N ≠ ⊤ := hNc.measure_lt_top.ne
  have hinK : ∀ t ∈ N, ∀ c ∈ C, i t * c ∈ K := fun t ht c hc =>
    interior_subset (hUV (Set.mk_mem_prod (hNU ht) (hCV hc)))
  haveI : ν.IsMulRightInvariant := by
    have h := (inferInstance : ν.inv.IsMulRightInvariant)
    rwa [Measure.inv_eq_self] at h
  set ind : X → ℝ≥0∞ := K.indicator 1 with hind
  have hindm : Measurable ind := measurable_one.indicator hKm
  have him : Measurable i := hi.measurable
  set M : ℝ≥0∞ := ENNReal.ofReal B with hM
  have hA : ∀ t₀ : T, ∀ c ∈ C, ν N ≤ ∫⁻ t, ind (i t * (i t₀ * c)) ∂ν := by
    intro t₀ c hc
    have h1 : ∫⁻ t, ind (i t * (i t₀ * c)) ∂ν = ∫⁻ t, ind (i t * c) ∂ν := by
      have := lintegral_mul_right_eq_self (μ := ν) (fun t => ind (i t * c)) t₀
      rw [← this]
      simp only [map_mul, mul_assoc]
    rw [h1, ← lintegral_indicator_one hNm]
    refine lintegral_mono fun t => ?_
    by_cases ht : t ∈ N
    · simp [ht, hind, hinK t ht c hc]
    · simp [ht]
  have hpt : ∀ x, ‖Φ x‖ₑ ≤ M / ν N * ∫⁻ t, ind (i t * x) ∂ν := by
    intro x
    by_cases hx : Φ x = 0
    · simp [hx]
    obtain ⟨t₀, c, hc, rfl⟩ := hsup x hx
    have hle : ‖Φ (i t₀ * c)‖ₑ ≤ M := by
      rw [hinv, hM, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB c hc)
    calc ‖Φ (i t₀ * c)‖ₑ ≤ M := hle
      _ = M / ν N * ν N := (ENNReal.div_mul_cancel hNpos hNfin).symm
      _ ≤ _ := by gcongr; exact hA t₀ c hc
  have hj1 : Measurable (fun p : X × T => ind (i p.2 * p.1) * ρ p.1) :=
    (hindm.comp ((him.comp measurable_snd).mul measurable_fst)).mul (hρ.comp measurable_fst)
  have hj2 : Measurable (fun p : T × X => ind p.2 * ρ ((i p.1)⁻¹ * p.2)) :=
    (hindm.comp measurable_snd).mul
      (hρ.comp (((him.comp measurable_fst).inv).mul measurable_snd))
  have hmain : ∫⁻ x, (∫⁻ t, ind (i t * x) ∂ν) * ρ x ∂μ = μ K := by
    calc ∫⁻ x, (∫⁻ t, ind (i t * x) ∂ν) * ρ x ∂μ
        = ∫⁻ x, ∫⁻ t, ind (i t * x) * ρ x ∂ν ∂μ := by
          refine lintegral_congr fun x => ?_
          have hm : Measurable fun t : T => ind (i t * x) := hindm.comp (him.mul_const x)
          exact (lintegral_mul_const (ρ x) hm).symm
      _ = ∫⁻ t, ∫⁻ x, ind (i t * x) * ρ x ∂μ ∂ν :=
          lintegral_lintegral_swap hj1.aemeasurable
      _ = ∫⁻ t, ∫⁻ y, ind y * ρ ((i t)⁻¹ * y) ∂μ ∂ν := by
          refine lintegral_congr fun t => ?_
          have := lintegral_mul_left_eq_self (μ := μ) (fun y => ind y * ρ ((i t)⁻¹ * y)) (i t)
          rw [← this]
          simp
      _ = ∫⁻ y, ∫⁻ t, ind y * ρ ((i t)⁻¹ * y) ∂ν ∂μ :=
          lintegral_lintegral_swap hj2.aemeasurable
      _ = ∫⁻ y, ind y ∂μ := by
          refine lintegral_congr fun y => ?_
          have hm : Measurable fun t : T => ρ (i t * y) :=
            hρ.comp ((him).mul_const y)
          have h2 : ∫⁻ t, ρ ((i t)⁻¹ * y) ∂ν = 1 := by
            have := (Measure.measurePreserving_inv ν).lintegral_comp hm
            simp only [Pi.inv_apply, map_inv] at this
            rw [this, hnorm']
          have hm' : Measurable fun t : T => ρ ((i t)⁻¹ * y) := hρ.comp (him.inv.mul_const y)
          rw [lintegral_const_mul (ind y) hm', h2, mul_one]
      _ = μ K := by
          rw [hind, lintegral_indicator_one hKm]
  calc ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ
      ≤ ∫⁻ x, M / ν N * ((∫⁻ t, ind (i t * x) ∂ν) * ρ x) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← mul_assoc]
        gcongr
        exact hpt x
    _ = M / ν N * μ K := by
        rw [lintegral_const_mul' _ _ (ENNReal.div_ne_top ENNReal.ofReal_ne_top hNpos), hmain]
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.div_lt_top ENNReal.ofReal_ne_top hNpos) hK.measure_lt_top
end

section

open MeasureTheory

namespace UpperTheory.ConvolutionTheory.L1

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

private lemma fib_cons {m : ℕ} (a : G) (y : Fin m → G) (x : G) :
    fib (Fin.cons (α := fun _ => G) a y) x = Fin.cons (α := fun _ => G) a (fib y (a⁻¹ * x)) := by
  unfold fib
  rw [← Fin.cons_snoc_eq_snoc_cons]
  congr 2
  simp [List.ofFn_succ, mul_assoc]

private lemma continuous_fib {m : ℕ} (x : G) : Continuous fun y : Fin m → G => fib y x := by
  have hp : Continuous fun y : Fin m → G => (List.ofFn y).prod := by
    simp only [List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ => continuous_apply i
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [fib, Fin.snoc_last]
    exact (hp.inv).mul continuous_const
  · simp only [fib, Fin.snoc_castSucc]
    exact continuous_apply j

private lemma integrable_fib (μ : Measure G) [μ.IsHaarMeasure] (m : ℕ) (φ : Fin (m + 1) → G → ℂ)
    (hc : ∀ i, Continuous (φ i)) (hs : ∀ i, HasCompactSupport (φ i)) (x : G) :
    Integrable (fun y : Fin m → G => ∏ i, φ i (fib y x i)) (Measure.pi fun _ => μ) := by
  have hcont : Continuous fun y : Fin m → G => ∏ i, φ i (fib y x i) :=
    continuous_finsetProd _ fun i _ =>
      (hc i).comp ((continuous_apply i).comp (continuous_fib x))
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro
    (K := Set.pi Set.univ fun i : Fin m => tsupport (φ i.castSucc))
    (isCompact_univ_pi fun i => hs _) fun y hy => ?_
  simp only [Set.mem_pi, Set.mem_univ, forall_const, not_forall] at hy
  obtain ⟨i, hi⟩ := hy
  refine Finset.prod_eq_zero (Finset.mem_univ i.castSucc) ?_
  simp only [fib, Fin.snoc_castSucc]
  exact image_eq_zero_of_notMem_tsupport hi

private lemma push_tens (μ : Measure G) [μ.IsHaarMeasure] : ∀ (m : ℕ) (φ : Fin (m + 1) → G → ℂ),
    (∀ i, Continuous (φ i)) → (∀ i, HasCompactSupport (φ i)) →
    push μ m (fun g => ∏ i, φ i (g i)) = cvAll μ m φ := by
  intro m
  induction m with
  | zero =>
    intro φ _ _
    funext x
    simp [push, cvAll, fib, Measure.real, Measure.pi_empty_univ, Fin.snoc]
  | succ m ih =>
    intro φ hc hs
    funext x
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0
    have hint := integrable_fib μ (m + 1) φ hc hs x
    set F : (Fin (m + 1) → G) → ℂ := fun y => ∏ i, φ i (fib y x i) with hF
    have hsymm := hmp.symm
    have hint' : Integrable (F ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => G) 0).symm)
        (μ.prod (Measure.pi fun _ => μ)) :=
      (hsymm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hint
    have hval : ∀ (a : G) (y : Fin m → G),
        (F ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => G) 0).symm) (a, y) =
          φ 0 a * ∏ i, Fin.tail φ i (fib y (a⁻¹ * x) i) := by
      intro a y
      have : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => G) 0).symm (a, y) =
          Fin.cons (α := fun _ => G) a y := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove]
      simp only [Function.comp, this, hF, fib_cons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
    show ∫ y, F y ∂(Measure.pi fun _ => μ) = _
    refine (hsymm.integral_comp' F).symm.trans ((integral_prod _ hint').trans ?_)
    simp only [cvAll, cv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [hval, integral_const_mul]
    have := congrFun (ih (Fin.tail φ) (fun i => hc _) (fun i => hs _)) (a⁻¹ * x)
    rw [← this]
    rfl

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.pushTens :
    UpperTheory.ConvolutionTheory.L1.PushTens := by
  intro G _ _ _ _ _ _ _ _ μ _ m φ hc hs
  exact UpperTheory.ConvolutionTheory.L1.push_tens μ m φ hc hs
end

section

noncomputable section

open PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped Fin.NatCast Fin.CommRing

namespace UpperTheory.ConvolutionTheory.L1

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
  {ι : R →+* S} {s : S →+* S} {m : ℕ} (D : Split ι s m) (n : ℕ)

private theorem comp_apply (i : Fin (m + 1)) (x : GL (Fin n) S) (a b : Fin n) :
    (D.comp n i x : Matrix (Fin n) (Fin n) R) a b = D.e ((x : Matrix (Fin n) (Fin n) S) a b) i := rfl

private theorem comp_glue (g : Fin (m + 1) → GL (Fin n) R) (i : Fin (m + 1)) :
    D.comp n i (D.glue n g) = g i := by
  apply Units.ext
  ext a b
  rw [comp_apply]
  show D.e (D.e.symm fun i => (g i : Matrix (Fin n) (Fin n) R) a b) i = _
  simp

private theorem glue_comp (x : GL (Fin n) S) : D.glue n (fun i => D.comp n i x) = x := by
  apply Units.ext
  ext a b
  show D.e.symm (fun i => (D.comp n i x : Matrix (Fin n) (Fin n) R) a b) = _
  simp only [comp_apply]
  exact D.e.symm_apply_apply _

private theorem comp_inj {x y : GL (Fin n) S} (h : ∀ i, D.comp n i x = D.comp n i y) : x = y := by
  rw [← glue_comp D n x, ← glue_comp D n y]
  exact congrArg _ (funext h)

private theorem comp_diag (t : GL (Fin n) R) (i : Fin (m + 1)) : D.comp n i (mapGL n ι t) = t := by
  apply Units.ext
  ext a b
  rw [comp_apply]
  exact D.map_diag _ i

private theorem comp_shift (x : GL (Fin n) S) (i : Fin (m + 1)) :
    D.comp n i (mapGL n s x) = D.comp n (i + 1) x := by
  apply Units.ext
  ext a b
  rw [comp_apply, comp_apply]
  exact D.map_shift _ i

private theorem comp_pow (θ : Monoid.End (GL (Fin n) S)) (hθ : ∀ x, θ x = mapGL n s x) (k : ℕ)
    (x : GL (Fin n) S) (i : Fin (m + 1)) :
    D.comp n i ((θ ^ k) x) = D.comp n (i + (k : Fin (m + 1))) x := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    show D.comp n i (θ ((θ ^ k) x)) = _
    rw [hθ, comp_shift, ih]
    congr 1
    push_cast
    abel_nf

private theorem ofFn_range {G : Type} [Monoid G] (k : ℕ) (f : ℕ → G) :
    (List.ofFn fun i : Fin k => f i).prod = ((List.range k).map f).prod := by
  congr 1
  apply List.ext_getElem <;> simp

private theorem comp_twNorm (θ : Monoid.End (GL (Fin n) S)) (hθ : ∀ x, θ x = mapGL n s x)
    (δ : GL (Fin n) S) (j : Fin (m + 1)) :
    D.comp n j (twNorm θ (m + 1) δ) = (List.ofFn fun i => D.comp n (j + i) δ).prod := by
  have hh : (fun i : Fin (m + 1) => D.comp n (j + i) δ) =
      fun i : Fin (m + 1) => (fun k : ℕ => D.comp n (j + (k : Fin (m + 1))) δ) i := by
    funext i
    simp only [Fin.cast_val_eq_self]
  rw [hh, ofFn_range (m + 1) (fun k : ℕ => D.comp n (j + (k : Fin (m + 1))) δ), twNorm, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  exact comp_pow D n θ hθ k δ j

private theorem entry {T : Type} [CommRing T] [TopologicalSpace T] (a b : Fin n) :
    Continuous fun x : GL (Fin n) T => (x : Matrix (Fin n) (Fin n) T) a b :=
  (Units.continuous_val (M := Matrix (Fin n) (Fin n) T)).matrix_elem a b

private theorem entryInv {T : Type} [CommRing T] [TopologicalSpace T] (a b : Fin n) :
    Continuous fun x : GL (Fin n) T => ((x⁻¹ : GL (Fin n) T) : Matrix (Fin n) (Fin n) T) a b :=
  (Units.continuous_iff.mp (continuous_id (X := GL (Fin n) T))).2.matrix_elem a b

private theorem norm_shift {G : Type} [Group G] (c : Fin (m + 1) → G) (j : Fin (m + 1)) :
    (List.ofFn fun i => c (j + i)).prod * c j = c j * (List.ofFn fun i => c (j + 1 + i)).prod := by
  rw [List.ofFn_succ, List.ofFn_succ' (f := fun i => c (j + 1 + i))]
  simp only [List.prod_cons, List.concat_eq_append, List.prod_append, List.prod_nil, mul_one, List.prod_singleton,
    add_zero, Fin.zero_eta]
  have h1 : ∀ i : Fin m, j + i.succ = j + 1 + i.castSucc := fun i => by
    rw [← Fin.coeSucc_eq_succ]
    abel
  have h2 : j + 1 + Fin.last m = j := by
    rw [add_assoc, add_comm 1, Fin.last_add_one, add_zero]
  simp only [h1, h2, mul_assoc]

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.glueBasic :
    UpperTheory.ConvolutionTheory.L1.GlueBasic := by
  intro R S _ _ _ _ _ _ ι s m D n
  refine ⟨comp_glue D n, glue_comp D n, ?_, ?_, ?_, comp_diag D n, comp_shift D n, ?_⟩
  · intro g h
    apply comp_inj D n
    intro i
    rw [map_mul, comp_glue, comp_glue, comp_glue]
    rfl
  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_matrix fun a b => ?_
      exact D.cont_symm.comp (continuous_pi fun i => (entry n a b).comp (continuous_apply i))
    · refine continuous_matrix fun a b => ?_
      exact D.cont_symm.comp (continuous_pi fun i => (entryInv n a b).comp (continuous_apply i))
  · intro i
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_matrix fun a b => ?_
      exact (continuous_apply i).comp (D.cont.comp (entry n a b))
    · refine continuous_matrix fun a b => ?_
      have : (fun x : GL (Fin n) S => (((D.comp n i x)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b) =
          fun x => D.e (((x⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) a b) i := by
        funext x
        rw [← map_inv, comp_apply]
      show Continuous (fun x : GL (Fin n) S => (((D.comp n i x)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b)
      rw [this]
      exact (continuous_apply i).comp (D.cont.comp (entryInv n a b))
  · intro δ γ
    constructor
    · intro h
      have N : ∀ j : Fin (m + 1), (List.ofFn fun i => D.comp n (j + i) δ).prod = γ := fun j => by
        rw [← comp_twNorm D n (mapGL n s) (fun _ => rfl), h, comp_diag]
      refine ⟨fun i => ?_, ?_, N⟩
      · have e := norm_shift (fun i => D.comp n i δ) i
        rw [N, N] at e
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact e.symm
      · simpa using N 0
    · rintro ⟨-, -, N⟩
      apply comp_inj D n
      intro j
      rw [comp_twNorm D n (mapGL n s) (fun _ => rfl), N, comp_diag]
end
end
