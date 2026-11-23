module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.NumberTheory.GaussSum
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
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
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

section

open GlobalTheory.KummerEisensteinGalois Finset

namespace GlobalTheory.KummerEisensteinGalois.ChSum

theorem core {M : ℕ} [NeZero M] {K : Type} [Field K] (ψ : DirichletCharacter K M) (hψ : ψ.IsPrimitive)
    (e : AddChar (ZMod M) K) (he : e.IsPrimitive) (n₁ n₂ w D D' : ZMod M) (hw : n₁ * w = 1) :
    ∑ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') =
      (if D + w * n₂ * D' = 0 then (M : K) else 0) * (ψ⁻¹ (w * D') * gaussSum ψ e) := by
  have step : ∀ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') =
      ∑ s : ZMod M, ψ s * e (s * (w * D')) * e (a * (D + w * n₂ * D')) := by
    intro a
    let f : ZMod M ≃ ZMod M :=
      { toFun := fun s => w * (s + n₂ * a)
        invFun := fun b => n₁ * b - n₂ * a
        left_inv := fun s => by simp only; linear_combination (s + n₂ * a) * hw
        right_inv := fun b => by simp only; linear_combination b * hw }
    rw [← Equiv.sum_comp f]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [f, Equiv.coe_fn_mk]
    have h1 : n₁ * (w * (s + n₂ * a)) - n₂ * a = s := by linear_combination (s + n₂ * a) * hw
    have h2 : a * D + w * (s + n₂ * a) * D' = s * (w * D') + a * (D + w * n₂ * D') := by ring
    rw [h1, h2, AddChar.map_add_eq_mul]; ring
  have hG : ∑ s : ZMod M, ψ s * e (s * (w * D')) = ψ⁻¹ (w * D') * gaussSum ψ e := by
    rw [← gaussSum_mulShift_of_isPrimitive e hψ]
    unfold gaussSum
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [AddChar.mulShift_apply, mul_comm s]
  rw [Finset.sum_congr rfl fun a _ => step a, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [AddChar.sum_mulShift _ he, ← Finset.sum_mul, hG, ZMod.card]
  split_ifs <;> ring

theorem eval {M : ℕ} [NeZero M] {K : Type} [Field K] (ψ : DirichletCharacter K M) (hψ : ψ.IsPrimitive)
    (e : AddChar (ZMod M) K) (he : e.IsPrimitive) (n₁ n₂ w D D' : ZMod M) (hw : n₁ * w = 1) :
    (∀ u : (ZMod M)ˣ, D = u * (-n₂) → D' = u * n₁ →
      ∑ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') =
        (M : K) * ψ⁻¹ (u : ZMod M) * gaussSum ψ e) ∧
    ((¬ ∃ u : (ZMod M)ˣ, D = u * (-n₂) ∧ D' = u * n₁) →
      ∑ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') = 0) := by
  rw [core ψ hψ e he n₁ n₂ w D D' hw]
  refine ⟨fun u hD hD' => ?_, fun hno => ?_⟩
  · have h0 : D + w * n₂ * D' = 0 := by rw [hD, hD']; linear_combination (u : ZMod M) * n₂ * hw
    have hl : w * D' = u := by rw [hD']; linear_combination (u : ZMod M) * hw
    rw [if_pos h0, hl]; ring
  · by_cases hc : D + w * n₂ * D' = 0
    · have hnu : ¬ IsUnit (w * D') := by
        rintro ⟨v, hv⟩
        refine hno ⟨v, ?_, ?_⟩
        · rw [hv]; linear_combination hc
        · rw [hv]; linear_combination (-D') * hw
      rw [if_pos hc, MulChar.map_nonunit _ hnu]; ring
    · rw [if_neg hc, zero_mul]

theorem zpow_eq {M : ℕ} [NeZero M] {K : Type} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M) (z : ℤ) :
    ζ ^ z = AddChar.zmodChar M hζ.pow_eq_one (z : ZMod M) := by
  have hne : ζ ≠ 0 := hζ.ne_zero (NeZero.ne M)
  rw [AddChar.zmodChar_apply, ← zpow_natCast, ZMod.val_intCast]
  conv_lhs => rw [← Int.emod_add_mul_ediv z M]
  rw [zpow_add₀ hne, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow, mul_one]

theorem unit_of_not_dvd (p m : ℕ) (hp : p.Prime) (n : ℤ) (h : ¬ (p : ℤ) ∣ n) :
    ∃ w : ZMod (p ^ m), (n : ZMod (p ^ m)) * w = 1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hc : IsCoprime n ((p : ℤ) ^ m) :=
    (((Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr h).pow_left).symm
  obtain ⟨u, v, huv⟩ := hc
  refine ⟨(u : ZMod (p ^ m)), ?_⟩
  have := congrArg (fun z : ℤ => (z : ZMod (p ^ m))) huv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one] at this
  rw [← Nat.cast_pow, ZMod.natCast_self, mul_zero, add_zero] at this
  rw [mul_comm]; exact this

theorem charSum : ∀ (p m : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (ζm : K), 1 ≤ m → ψ.IsPrimitive → IsPrimitiveRoot ζm (p ^ m) → ∀ n₁ n₂ d d' : ℤ, ¬ ((p : ℤ) ∣ n₁ ∧ (p : ℤ) ∣ n₂) → (∀ u : (ZMod (p ^ m))ˣ, (d : ZMod (p ^ m)) = u * (-(n₂ : ZMod (p ^ m))) → (d' : ZMod (p ^ m)) = u * (n₁ : ZMod (p ^ m)) → ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = (p : K) ^ m * ψ⁻¹ (u : ZMod (p ^ m)) * gaussS p m ψ ζm) ∧ ((¬ ∃ u : (ZMod (p ^ m))ˣ, (d : ZMod (p ^ m)) = u * (-(n₂ : ZMod (p ^ m))) ∧ (d' : ZMod (p ^ m)) = u * (n₁ : ZMod (p ^ m))) → ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = 0) := by
  intro p m _ K _ _ ψ ζm _ hψ hζ n₁ n₂ d d' hn
  have hp : p.Prime := Fact.out
  have he := AddChar.zmodChar_primitive_of_primitive_root (p ^ m) hζ
  set e := AddChar.zmodChar (p ^ m) hζ.pow_eq_one with he_def
  have hG : gaussS p m ψ ζm = gaussSum ψ e := rfl
  have hz : ∀ a b : ZMod (p ^ m), ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') =
      e (a * (d : ZMod (p ^ m)) + b * (d' : ZMod (p ^ m))) := by
    intro a b
    rw [zpow_eq hζ]
    congr 1
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  simp only [hz, hG]
  rw [← Nat.cast_pow]
  by_cases h1 : (p : ℤ) ∣ n₁
  · have h2 : ¬ (p : ℤ) ∣ n₂ := fun h => hn ⟨h1, h⟩
    obtain ⟨w, hw⟩ := unit_of_not_dvd p m hp n₂ h2
    have hw' : (-(n₂ : ZMod (p ^ m))) * (-w) = 1 := by rw [neg_mul_neg, hw]
    have key := eval ψ hψ e he (-(n₂ : ZMod (p ^ m))) (-(n₁ : ZMod (p ^ m))) (-w)
      (d' : ZMod (p ^ m)) (d : ZMod (p ^ m)) hw'
    have hswap : ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m),
        ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) *
          e (a * (d : ZMod (p ^ m)) + b * (d' : ZMod (p ^ m))) =
        ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m),
        ψ (-(n₂ : ZMod (p ^ m)) * b - -(n₁ : ZMod (p ^ m)) * a) *
          e (a * (d' : ZMod (p ^ m)) + b * (d : ZMod (p ^ m))) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [show -(n₂ : ZMod (p ^ m)) * b - -(n₁ : ZMod (p ^ m)) * a =
        (n₁ : ZMod (p ^ m)) * a - (n₂ : ZMod (p ^ m)) * b by ring, add_comm (a * (d' : ZMod (p ^ m)))]
    rw [hswap]
    rw [neg_neg] at key
    exact ⟨fun u hd hd' => key.1 u hd' hd,
      fun hno => key.2 fun ⟨u, hd', hd⟩ => hno ⟨u, hd, hd'⟩⟩
  · obtain ⟨w, hw⟩ := unit_of_not_dvd p m hp n₁ h1
    exact eval ψ hψ e he _ _ w _ _ hw

end GlobalTheory.KummerEisensteinGalois.ChSum
end

section

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Topology
open scoped ENNReal

namespace GlobalTheory.RestrMeas

section Pi

theorem lintegral_fin_prod_eq_prod {n : ℕ} {E : Fin n → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
      Fin.prod_univ_succ, ← ih fun i => hf _, ← lintegral_prod_mul (hf 0)]
    · refine lintegral_congr fun a => ?_
      rw [Fin.prod_univ_succ]
      rfl
    · exact Finset.aemeasurable_fun_prod _ fun i _ =>
        (hf _).comp_quasiMeasurePreserving (quasiMeasurePreserving_eval (fun i : Fin n => μ i.succ) i)

theorem lintegral_fintype_prod_eq_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod_eq_prod fun i => hf _

end Pi

variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} {pa : ∀ w, X → Ya w} {pf : ∀ v, X → Yf v}
  {K : ∀ v, Set (Yf v)}

theorem finprod_eq_prod_of_mem {M : Type} [CommMonoid M] {ff : ∀ v, Yf v → M} {S : Finset V}
    (h1 : ∀ v ∉ S, ∀ y ∈ K v, ff v y = 1) {x : X} (hx : ∀ v ∉ S, pf v x ∈ K v) :
    ∏ᶠ v, ff v (pf v x) = ∏ v ∈ S, ff v (pf v x) :=
  finprod_eq_prod_of_mulSupport_subset _ fun v hv => by_contra fun h' => hv (h1 v h' _ (hx v h'))

theorem finprod_eq_zero_of_notMem {M : Type} [CommMonoidWithZero M] {ff : ∀ v, Yf v → M} {S : Finset V}
    (h1 : ∀ v ∉ S, ff v = (K v).indicator 1) {x : X} (hx : ∀ᶠ v in cofinite, pf v x ∈ K v)
    (hx' : ¬ ∀ v ∉ S, pf v x ∈ K v) : ∏ᶠ v, ff v (pf v x) = 0 := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_of_eventually hx
  push Not at hx'
  obtain ⟨u, hu, hu'⟩ := hx'
  rw [finprod_eq_prod_of_mem (K := K) (S := S ∪ T)
    (fun v hv y hy => by rw [h1 v fun h' => hv (Finset.mem_union_left _ h'), indicator_of_mem hy, Pi.one_apply])
    fun v hv => hT v fun h' => hv (Finset.mem_union_right _ h')]
  exact Finset.prod_eq_zero (Finset.mem_union_right _ (by_contra fun h' => hu' (hT u h')))
    (by rw [h1 u hu, indicator_of_notMem hu'])

variable [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)] [Countable V]

theorem measurableSet_level (hf : ∀ v, Measurable (pf v)) (hK : ∀ v, MeasurableSet (K v)) (S : Finset V) :
    MeasurableSet {x | ∀ v ∉ S, pf v x ∈ K v} := by
  simp only [setOf_forall]
  exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => hf v (hK v)

variable [Fintype W] {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ : Measure X}
  [∀ w, SigmaFinite (μa w)] [∀ v, SigmaFinite (μf v)]


omit [Countable V] in
theorem IsCylProd.measurePreserving_level (h : IsCylProd pa pf K μa μf μ) (ha : ∀ w, Measurable (pa w))
    (hf : ∀ v, Measurable (pf v)) {S : Finset V} (hS : ∀ v ∉ S, μf v (K v) = 1) :
    MeasurePreserving (fun x => (fun w => pa w x, fun v : S => pf v x)) (μ.restrict {x | ∀ v ∉ S, pf v x ∈ K v})
      ((Measure.pi μa).prod (Measure.pi fun v : S => μf v)) := by
  classical
  have hπ : Measurable fun x => (fun w => pa w x, fun v : S => pf v x) :=
    (Measurable.of_eval ha).prodMk (Measurable.of_eval fun v => hf v)
  refine ⟨hπ, (prod_eq_generateFrom generateFrom_pi generateFrom_pi isPiSystem_pi isPiSystem_pi
    (FiniteSpanningSetsIn.pi fun w => (μa w).toFiniteSpanningSetsIn)
    (FiniteSpanningSetsIn.pi fun v : S => (μf v).toFiniteSpanningSetsIn) ?_).symm⟩
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
  have hm := (MeasurableSet.univ_pi fun w => hA w (mem_univ _)).prod (MeasurableSet.univ_pi fun v => hB v (mem_univ _))
  have e := h.2 S hS A (fun v => if hv : v ∈ S then B ⟨v, hv⟩ else univ) (fun w => hA w (mem_univ _))
    fun v hv => by simp only [dif_pos hv]; exact hB ⟨v, hv⟩ (mem_univ _)
  rw [Measure.map_apply hπ hm, Measure.restrict_apply (hπ hm), Measure.pi_pi, Measure.pi_pi]
  convert e using 2
  · ext x
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ_pi, mem_cyl, mem_setOf_eq, and_assoc, Subtype.forall]
    exact and_congr_right fun _ => and_congr_left fun _ => forall₂_congr fun v hv => by rw [dif_pos hv]
  · rw [← Finset.prod_coe_sort S]
    exact Finset.prod_congr rfl fun v _ => by rw [dif_pos v.2]

variable (h : IsCylProd pa pf K μa μf μ) (ha : ∀ w, Measurable (pa w)) (hf : ∀ v, Measurable (pf v))
  (hK : ∀ v, MeasurableSet (K v))

include h ha hf hK

section Nonneg

variable {fa : ∀ w, Ya w → ℝ≥0∞} {ff : ∀ v, Yf v → ℝ≥0∞}

end Nonneg

variable {𝕜 : Type} [RCLike 𝕜] {fa : ∀ w, Ya w → 𝕜} {ff : ∀ v, Yf v → 𝕜}

theorem IsCylProd.setIntegral_tensor {S : Finset V} (hS : ∀ v ∉ S, μf v (K v) = 1)
    (h1 : ∀ v ∉ S, ∀ y ∈ K v, ff v y = 1) (hfa : ∀ w, Integrable (fa w) (μa w))
    (hff : ∀ v ∈ S, Integrable (ff v) (μf v)) :
    IntegrableOn (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) {x | ∀ v ∉ S, pf v x ∈ K v} μ ∧
    ∫ x in {x | ∀ v ∉ S, pf v x ∈ K v}, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) ∂μ =
      (∏ w, ∫ y, fa w y ∂μa w) * ∏ v ∈ S, ∫ y, ff v y ∂μf v := by
  have hp := h.measurePreserving_level ha hf hS
  have hi := (Integrable.fintype_prod_dep hfa).mul_prod
    (Integrable.fintype_prod_dep (μ := fun v : S => μf v) fun v : S => hff v v.2)
  have e : EqOn (fun x => (∏ w, fa w (pa w x)) * ∏ v : S, ff v (pf v x))
      (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) {x | ∀ v ∉ S, pf v x ∈ K v} := fun x hx => by
    simp only [finprod_eq_prod_of_mem h1 hx, ← Finset.prod_coe_sort S]
  refine ⟨IntegrableOn.congr_fun (hp.integrable_comp_of_integrable hi) e (measurableSet_level hf hK S), ?_⟩
  rw [← setIntegral_congr_fun (measurableSet_level hf hK S) e, ← Finset.prod_coe_sort S,
    ← integral_fintype_prod_eq_prod, ← integral_fintype_prod_eq_prod, ← integral_prod_mul, ← hp.map_eq,
    integral_map hp.aemeasurable (hp.map_eq ▸ hi.aestronglyMeasurable)]

theorem IsCylProd.integral_tensor_indicator (hX : ∀ x, ∀ᶠ v in cofinite, pf v x ∈ K v) {S : Finset V}
    (hS : ∀ v ∉ S, μf v (K v) = 1) (h1 : ∀ v ∉ S, ff v = (K v).indicator 1)
    (hfa : ∀ w, Integrable (fa w) (μa w)) (hff : ∀ v ∈ S, Integrable (ff v) (μf v)) :
    Integrable (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) μ ∧
    ∫ x, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) ∂μ =
      (∏ w, ∫ y, fa w y ∂μa w) * ∏ v ∈ S, ∫ y, ff v y ∂μf v := by
  obtain ⟨hi, e⟩ := h.setIntegral_tensor ha hf hK hS
    (fun v hv y hy => by rw [h1 v hv, indicator_of_mem hy, Pi.one_apply]) hfa hff
  have h0 : ∀ x ∉ {x | ∀ v ∉ S, pf v x ∈ K v}, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) = 0 := fun x hx => by
    rw [finprod_eq_zero_of_notMem h1 (hX x) hx, mul_zero]
  exact ⟨hi.integrable_of_forall_notMem_eq_zero h0, by rw [← e, setIntegral_eq_integral_of_forall_compl_eq_zero h0]⟩


end GlobalTheory.RestrMeas

namespace GlobalTheory.AdelicU

open NumberField IsDedekindDomain GlobalTheory.RestrMeas

end GlobalTheory.AdelicU

end
end

section

open GlobalTheory.K5

namespace GlobalTheory.K5

theorem gal_finite_subcover : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ S : Gal p Ω → Finset Ω, ∃ F : Finset (Gal p Ω), ∀ h : Gal p Ω, ∃ g ∈ F, ∀ x ∈ S g, h x = g x := by
  intro p _ Ω _ _ hΩ S
  classical
  letI : TopologicalSpace Ω := ⊥
  haveI : DiscreteTopology Ω := ⟨rfl⟩
  haveI : IsDomain (O0 p) := hΩ.inj.isDomain (algebraMap (O0 p) Ω)
  haveI : Module.IsTorsionFree (O0 p) Ω := Module.isTorsionFree_iff_algebraMap_injective.mpr hΩ.inj
  haveI := hΩ.alg
  choose P hP0 hP using fun x : Ω => (Algebra.IsAlgebraic.isAlgebraic (R := O0 p) x)
  have hmap : ∀ x, (P x).map (algebraMap (O0 p) Ω) ≠ 0 := fun x =>
    (Polynomial.map_ne_zero_iff hΩ.inj).mpr (hP0 x)
  let R : Ω → Set Ω := fun x => (((P x).map (algebraMap (O0 p) Ω)).roots.toFinset : Set Ω)
  have hR : ∀ (φ : Ω →ₐ[O0 p] Ω) x, φ x ∈ R x := by
    intro φ x
    simp only [R, Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots (hmap x), Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def,
      Polynomial.aeval_algHom_apply, hP x, map_zero]
  let K : Set (Ω → Ω) := Set.pi Set.univ R
  have hK : IsCompact K := isCompact_univ_pi (fun x => (Finset.finite_toSet _).isCompact)
  let C : Set (Ω → Ω) := (⋂ a, ⋂ b, {f | f (a + b) = f a + f b}) ∩ (⋂ a, ⋂ b, {f | f (a * b) = f a * f b})
      ∩ {f | f 1 = 1} ∩ ⋂ r : O0 p, {f | f (algebraMap (O0 p) Ω r) = algebraMap (O0 p) Ω r}
  have hC : IsClosed C := by
    have key : ∀ (u : (Ω → Ω) → Ω × Ω × Ω), Continuous u → ∀ T : Set (Ω × Ω × Ω),
        IsClosed (u ⁻¹' T) := fun u hu T => (isClosed_discrete T).preimage hu
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
    · refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
      exact key (fun f => (f (a + b), f a, f b)) (by fun_prop) {t | t.1 = t.2.1 + t.2.2}
    · refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
      exact key (fun f => (f (a * b), f a, f b)) (by fun_prop) {t | t.1 = t.2.1 * t.2.2}
    · exact key (fun f => (f 1, f 1, f 1)) (by fun_prop) {t | t.1 = 1}
    · refine isClosed_iInter fun r => ?_
      exact key (fun f => (f (algebraMap (O0 p) Ω r), f 1, f 1)) (by fun_prop)
        {t | t.1 = algebraMap (O0 p) Ω r}
  let U : Gal p Ω → Set (Ω → Ω) := fun g => ⋂ x ∈ S g, (fun f => f x) ⁻¹' {g x}
  have hU : ∀ g, IsOpen (U g) := fun g =>
    isOpen_biInter_finset (fun x _ => (isOpen_discrete {g x}).preimage (continuous_apply x))
  have hcov : K ∩ C ⊆ ⋃ g, U g := by
    rintro f ⟨-, ⟨⟨hadd, hmul⟩, h1⟩, halg⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hadd hmul h1 halg
    have h0 : f 0 = 0 := by
      have := hadd 0 0
      simp only [add_zero] at this
      exact left_eq_add.mp this
    let φ : Ω →ₐ[O0 p] Ω :=
      { toFun := f, map_one' := h1, map_mul' := hmul, map_zero' := h0, map_add' := hadd,
        commutes' := halg }
    let e : Gal p Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)
    refine Set.mem_iUnion.mpr ⟨e, ?_⟩
    simp only [U, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    intro x _
    rfl
  have hmem : ∀ h : Gal p Ω, (⇑h : Ω → Ω) ∈ K ∩ C := by
    intro h
    refine ⟨fun x _ => hR (h : Ω →ₐ[O0 p] Ω) x, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simp only [Set.mem_iInter, Set.mem_setOf_eq]; intro a b; exact map_add h a b
    · simp only [Set.mem_iInter, Set.mem_setOf_eq]; intro a b; exact map_mul h a b
    · exact map_one h
    · simp only [Set.mem_iInter, Set.mem_setOf_eq]; intro r; exact h.commutes r
  obtain ⟨F, hF⟩ := (hK.inter_right hC).elim_finite_subcover U hU hcov
  refine ⟨F, fun h => ?_⟩
  obtain ⟨g, hg, hgh⟩ := Set.mem_iUnion₂.mp (hF (hmem h))
  refine ⟨g, hg, fun x hx => ?_⟩
  have := Set.mem_iInter₂.mp hgh x hx
  simpa using this

end GlobalTheory.K5
end

section

open Polynomial IntermediateField

namespace GlobalTheory.K5.Span

variable (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]

def baseField : Subfield Ω :=
  Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp (p := p) x})

variable {p Ω}

theorem algebraMap_mem_baseField (a : O0 p) : algebraMap (O0 p) Ω a ∈ baseField p Ω :=
  Subfield.subset_closure (Or.inl ⟨a, rfl⟩)

theorem ggeo_fix_baseField {g : Gal p Ω} (hg : g ∈ Ggeo (p := p) Ω) {x : Ω}
    (hx : x ∈ baseField p Ω) :
    g x = x := by
  have hle : baseField p Ω ≤ RingHom.eqLocusField (g : Ω →+* Ω) (RingHom.id Ω) := by
    refine Subfield.closure_le.2 ?_
    rintro z (⟨a, rfl⟩ | hz)
    · show g (algebraMap (O0 p) Ω a) = algebraMap (O0 p) Ω a
      exact g.commutes a
    · show g z = z
      exact hg z hz
  exact hle hx

noncomputable def toGal (σ : Ω ≃ₐ[baseField p Ω] Ω) : Gal p Ω :=
  AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun a =>
    σ.commutes (⟨algebraMap (O0 p) Ω a, algebraMap_mem_baseField a⟩ : baseField p Ω)

theorem toGal_apply (σ : Ω ≃ₐ[baseField p Ω] Ω) (x : Ω) : toGal σ x = σ x := rfl

theorem isAlgebraic_baseField (h : IsClo p Ω) : Algebra.IsAlgebraic (baseField p Ω) Ω := by
  haveI := h.alg
  refine ⟨fun x => ?_⟩
  obtain ⟨P, hP0, hPx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := O0 p) x
  let φ : O0 p →+* baseField p Ω :=
    (algebraMap (O0 p) Ω).codRestrict (baseField p Ω) algebraMap_mem_baseField
  have hφ : Function.Injective φ := fun a b hab => h.inj (congrArg Subtype.val hab)
  refine ⟨P.map φ, (Polynomial.map_ne_zero_iff hφ).2 hP0, ?_⟩
  rw [aeval_def, eval₂_map]
  have : (algebraMap (baseField p Ω) Ω).comp φ = algebraMap (O0 p) Ω := by
    ext a; rfl
  rw [this, ← aeval_def, hPx]

end GlobalTheory.K5.Span

open GlobalTheory.K5.Span in
open GlobalTheory.K5 GlobalTheory.K5.Span in
theorem GlobalTheory.K5.span_fixed_ggeo_stab : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (y : Ω), (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) ∧
    y = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
  intro p _ Ω _ _ h T N y hy
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  haveI := h.clo
  set L := baseField p Ω
  haveI : CharZero L := inferInstance
  haveI : Algebra.IsAlgebraic L Ω := isAlgebraic_baseField h
  haveI : IsAlgClosure L Ω := ⟨h.clo, inferInstance⟩
  haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  set M : IntermediateField L Ω := IntermediateField.adjoin L {T.qq N}
  have hyM : y ∈ M := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup M, mem_fixedField_iff]
    intro σ hσ
    have hq : σ (T.qq N) = T.qq N :=
      (mem_fixingSubgroup_iff M σ).1 hσ _ (mem_adjoin_simple_self L _)
    refine hy (toGal σ) (Subgroup.mem_inf.2 ⟨fun x hx => ?_, ?_⟩)
    · exact σ.commutes (⟨x, Subfield.subset_closure (Or.inr hx)⟩ : L)
    · rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, toGal_apply, hq]
  have hyA : y ∈ (aeval (T.qq N) : L[X] →ₐ[L] Ω).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval,
      ← adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic _)]
    exact hyM
  obtain ⟨P, hP⟩ := hyA
  set q0 : L := ⟨algebraMap (O0 p) Ω (qO p), algebraMap_mem_baseField _⟩
  set Q : L[X] := X ^ (p ^ N) - C q0
  have hpN : p ^ N ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hQm : Q.Monic := monic_X_pow_sub_C _ hpN
  have hQd : Q.natDegree = p ^ N := natDegree_X_pow_sub_C _
  have hQ1 : Q ≠ 1 := by
    intro e; rw [e, natDegree_one] at hQd; exact hpN hQd.symm
  have hQq : aeval (T.qq N) Q = 0 := by
    simp only [Q, map_sub, map_pow, aeval_X, aeval_C, Basic.qq_pow]
    exact sub_self _
  set R := P %ₘ Q
  have hRd : R.natDegree < p ^ N := hQd ▸ natDegree_modByMonic_lt P hQm hQ1
  have hR : aeval (T.qq N) R = y := by
    have e := congrArg (aeval (T.qq N)) (modByMonic_add_div P Q)
    rw [map_add (f := _), map_mul, hQq, zero_mul, add_zero] at e
    rw [e]; exact hP
  refine ⟨fun j => ((R.coeff j : L) : Ω), fun j g hg => ggeo_fix_baseField hg (R.coeff j).2, ?_⟩
  rw [← hR, aeval_eq_sum_range' hRd]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def]
  rfl
end
