module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefExtendsHolomorphically
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyBallSubset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle021
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle215
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueProjectiveBundleFlagRefinement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

noncomputable section

namespace GlobalTheory.KFinSep

variable {n : ℕ} {ε : Fin n → Bool}

lemma kfin_of_span {ι : Type} [Finite ι] (b : ι → KG ε → ℂ) (hc : ∀ i, Continuous (b i))
    (ht : ∀ i (k₀ : KG ε), (fun k => b i (k₀ * k)) ∈ Submodule.span ℂ (Set.range b) ∧
      (fun k => b i (k * k₀)) ∈ Submodule.span ℂ (Set.range b)) (i : ι) : KFinFun ε (b i) := by
  refine ⟨Submodule.span ℂ (Set.range b), FiniteDimensional.span_of_finite ℂ (Set.finite_range b),
    Submodule.subset_span ⟨i, rfl⟩, ?_, ?_⟩
  · intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hc j
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul a x _ hx => exact hx.const_smul a
  · intro φ hφ k₀
    induction hφ using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact ht j k₀
    | zero => exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    | add x y _ _ hx hy => exact ⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩
    | smul a x _ hx => exact ⟨Submodule.smul_mem _ a hx.1, Submodule.smul_mem _ a hx.2⟩

lemma kfin_const (c : ℂ) : KFinFun ε (fun _ => c) :=
  kfin_of_span (ε := ε) (ι := Unit) (fun _ _ => c) (fun _ => continuous_const)
    (fun i _ => ⟨Submodule.subset_span ⟨i, rfl⟩, Submodule.subset_span ⟨i, rfl⟩⟩) ()

lemma kfin_add {p q : KG ε → ℂ} (hp : KFinFun ε p) (hq : KFinFun ε q) : KFinFun ε (p + q) := by
  obtain ⟨F, _, hpF, hFc, hF⟩ := hp
  obtain ⟨G, _, hqG, hGc, hG⟩ := hq
  refine ⟨F ⊔ G, inferInstance, Submodule.add_mem_sup hpF hqG, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hφ
    exact (hFc x hx).add (hGc y hy)
  · intro φ hφ k₀
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hφ
    exact ⟨Submodule.add_mem_sup (hF x hx k₀).1 (hG y hy k₀).1, Submodule.add_mem_sup (hF x hx k₀).2 (hG y hy k₀).2⟩

lemma kfin_mul {p q : KG ε → ℂ} (hp : KFinFun ε p) (hq : KFinFun ε q) : KFinFun ε (p * q) := by
  obtain ⟨F, hFf, hpF, hFc, hF⟩ := hp
  obtain ⟨G, hGf, hqG, hGc, hG⟩ := hq
  refine ⟨F * G, ?_, Submodule.mul_mem_mul hpF hqG, ?_, ?_⟩
  · exact Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hFf).mul (Module.Finite.iff_fg.1 hGf))
  · intro φ hφ
    refine Submodule.mul_induction_on hφ (fun x hx y hy => (hFc x hx).mul (hGc y hy)) (fun x y hx hy => hx.add hy)
  · intro φ hφ k₀
    refine Submodule.mul_induction_on (C := fun φ => (fun k => φ (k₀ * k)) ∈ F * G ∧ (fun k => φ (k * k₀)) ∈ F * G)
      hφ (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · exact ⟨Submodule.mul_mem_mul (hF x hx k₀).1 (hG y hy k₀).1, Submodule.mul_mem_mul (hF x hx k₀).2 (hG y hy k₀).2⟩
    · exact ⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩

lemma mem_span_of_sum {ι κ : Type} [Fintype κ] (b : ι → KG ε → ℂ) (f : KG ε → ℂ) (c : κ → ℂ) (j : κ → ι)
    (h : ∀ k, f k = ∑ l, c l * b (j l) k) : f ∈ Submodule.span ℂ (Set.range b) := by
  have : f = ∑ l, c l • b (j l) := by
    funext k; simp [h, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j l, rfl⟩)

lemma kfin_entry (i j : Fin n) : KFinFun ε (fun k => toMK k i j) := by
  refine kfin_of_span (ε := ε) (ι := Fin n × Fin n) (fun a k => toMK k a.1 a.2)
    (fun a => (GlobalTheory.KHolExt.ent ε a.1 a.2).continuous) (fun a k₀ => ⟨?_, ?_⟩) (i, j)
  · refine mem_span_of_sum _ _ (fun l => toMK k₀ a.1 l) (fun l => (l, a.2)) fun k => ?_
    simp only [GlobalTheory.KHolExt.toMK_mul, Matrix.mul_apply]
  · refine mem_span_of_sum _ _ (fun l => toMK k₀ l a.2) (fun l => (a.1, l)) fun k => ?_
    simp only [GlobalTheory.KHolExt.toMK_mul, Matrix.mul_apply, mul_comm]

lemma kfin_conjEntry (i j : Fin n) : KFinFun ε (fun k => star (toMK k i j)) := by
  refine kfin_of_span (ε := ε) (ι := Fin n × Fin n) (fun a k => star (toMK k a.1 a.2))
    (fun a => (GlobalTheory.KHolExt.ent ε a.1 a.2).continuous.star) (fun a k₀ => ⟨?_, ?_⟩) (i, j)
  · refine mem_span_of_sum _ _ (fun l => star (toMK k₀ a.1 l)) (fun l => (l, a.2)) fun k => ?_
    simp only [GlobalTheory.KHolExt.toMK_mul, Matrix.mul_apply, star_sum, star_mul']
  · refine mem_span_of_sum _ _ (fun l => star (toMK k₀ l a.2)) (fun l => (a.1, l)) fun k => ?_
    simp only [GlobalTheory.KHolExt.toMK_mul, Matrix.mul_apply, star_sum, star_mul', mul_comm]

def finAlg (ε : Fin n → Bool) : StarSubalgebra ℂ C(KG ε, ℂ) where
  carrier := {p | KFinFun ε p ∧ KFinFun ε (star p : C(KG ε, ℂ))}
  mul_mem' := fun {p q} hp hq => ⟨kfin_mul hp.1 hq.1, by
    rw [star_mul']; exact kfin_mul hp.2 hq.2⟩
  add_mem' := fun {p q} hp hq => ⟨kfin_add hp.1 hq.1, by
    rw [star_add]; exact kfin_add hp.2 hq.2⟩
  algebraMap_mem' := fun c => ⟨by
    have : ((algebraMap ℂ C(KG ε, ℂ) c : C(KG ε, ℂ)) : KG ε → ℂ) = fun _ => c := by
      funext k; simp
    rw [this]; exact kfin_const c, by
    have : ((star (algebraMap ℂ C(KG ε, ℂ) c) : C(KG ε, ℂ)) : KG ε → ℂ) = fun _ => star c := by
      funext k; simp
    rw [this]; exact kfin_const _⟩
  star_mem' := fun {p} hp => ⟨hp.2, by rw [star_star]; exact hp.1⟩

lemma finAlg_dense (ε : Fin n → Bool) : (finAlg ε).topologicalClosure = ⊤ := by
  refine ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_
  intro x y hxy
  have h : toMK x ≠ toMK y := fun h => hxy ((GlobalTheory.KHolExt.isEmb ε).injective h)
  obtain ⟨i, j, hij⟩ : ∃ i j, toMK x i j ≠ toMK y i j := by
    by_contra hc
    push Not at hc
    exact h (Matrix.ext hc)
  exact ⟨GlobalTheory.KHolExt.ent ε i j, ⟨GlobalTheory.KHolExt.ent ε i j, ⟨kfin_entry i j, kfin_conjEntry i j⟩, rfl⟩, hij⟩

end GlobalTheory.KFinSep
end
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.SobolevHaar

theorem cube_step {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : ℕ)
    (c : Fin (N + 1) → ℝ → G) (s : ℝ) (hs : 0 < s)
    (hc : ∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b)
    (f f' : G → ℂ) (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt (fun t => f (x * c (Fin.last N) t)) (f' x) 0) :
    ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ‖f (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod‖ ^ 2 ≤
      2 / s * (∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
        ‖f (List.ofFn fun i => c i (t i)).prod‖ ^ 2) +
      2 * s * ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
        ‖f' (List.ofFn fun i => c i (t i)).prod‖ ^ 2 := by
  set l := Fin.last N with hl
  have hΘ := continuous_prod_ofFn_curves (N + 1) c (fun i => (hc i).1)
  have hΘ' := continuous_prod_ofFn_curves N (fun i => c i.castSucc) (fun i => (hc _).1)
  have hsn : ∀ (t : Fin N → ℝ) (r : ℝ),
      (List.ofFn fun i => c i (Fin.snoc (α := fun _ => ℝ) t r i)).prod
        = (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c l r := by
    intro t r
    rw [List.ofFn_succ']
    simp [hl]
  have fub : ∀ w : G → ℂ, Continuous w →
      IntegrableOn (fun t : Fin N → ℝ => ∫ r in (0 : ℝ)..s,
        ‖w ((List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c l r)‖ ^ 2)
        (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s)) ∧
      ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
        ‖w (List.ofFn fun i => c i (t i)).prod‖ ^ 2 =
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ∫ r in (0 : ℝ)..s,
        ‖w ((List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c l r)‖ ^ 2 := by
    intro w hw
    have h := integral_cube_succ_last N s
      (fun t => ‖w (List.ofFn fun i => c i (t i)).prod‖ ^ 2) ((hw.comp hΘ).norm.pow 2)
    simp only [hsn] at h
    simp only [intervalIntegral.integral_of_le hs.le, ← integral_Icc_eq_integral_Ioc]
    exact h
  obtain ⟨i1, b1⟩ := fub f hf
  obtain ⟨i2, b2⟩ := fub f' hf'
  have pt : ∀ x : G, ‖f x‖ ^ 2 ≤ 2 / s * (∫ r in (0 : ℝ)..s, ‖f (x * c l r)‖ ^ 2)
      + 2 * s * ∫ r in (0 : ℝ)..s, ‖f' (x * c l r)‖ ^ 2 := by
    intro x
    have h := sobolev_endpoint_one_variable ℂ (fun r => f (x * c l r))
      (fun r => f' (x * c l r)) s hs ?_ ?_
    · simpa only [(hc l).2.1, mul_one] using h
    · intro r _
      have h1 : HasDerivAt (fun t => f (x * c l r * c l t)) (f' (x * c l r)) (r - r) := by
        rw [sub_self]; exact hd _
      have h2 := h1.comp_sub_const r r
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [mul_assoc, ← (hc l).2.2, add_sub_cancel]
    · exact (hf'.comp (continuous_const.mul (hc l).1)).continuousOn
  have i0 : IntegrableOn (fun t : Fin N → ℝ =>
      ‖f (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod‖ ^ 2)
      (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s)) :=
    ((hf.comp hΘ').norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc)
  have key := integral_mono i0 ((i1.const_mul (2 / s)).add (i2.const_mul (2 * s)))
    (fun t => pt _)
  simp only [Pi.add_apply] at key
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
    integral_const_mul] at key
  rw [b1, b2]
  exact key

theorem cube_sum {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : Set V) (u : V)
    (hu : u ∈ A) (s : ℝ) (hs : 0 < s) : ∀ (N : ℕ) (c : Fin N → ℝ → G) (D : Fin N → V → V),
    (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) →
    (∀ i, ∀ v ∈ A, D i v ∈ A) →
    ∃ (S : List V) (C : ℝ), (∀ v ∈ S, v ∈ A) ∧ 0 ≤ C ∧ ∀ Fr : V → G → ℂ, (∀ v ∈ A, Continuous (Fr v)) →
      (∀ v ∈ A, ∀ i x, HasDerivAt (fun t => Fr v (x * c i t)) (Fr (D i v) x) 0) →
      ‖Fr u 1‖ ^ 2 ≤ C * (S.map fun v => ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ‖Fr v (List.ofFn fun i => c i (t i)).prod‖ ^ 2).sum := by
  intro N
  induction N with
  | zero =>
    intro c D _ _
    refine ⟨[u], 1, by simpa using hu, zero_le_one, fun Fr _ _ => ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [volume_pi, Measure.restrict_pi_pi]
    simp [Measure.real]
  | succ N ih =>
    intro c D hc hD
    obtain ⟨S, C, hS, hC, h⟩ := ih (fun i => c i.castSucc) (fun i => D i.castSucc) (fun i => hc _)
      (fun i => hD _)
    refine ⟨S ++ S.map (D (Fin.last N)), C * (2 / s + 2 * s), ?_, by positivity, fun Fr h1 h2 => ?_⟩
    · intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact hS v hv
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
        exact hD _ w (hS w hw)
    refine (h Fr h1 fun v hv i => h2 v hv _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC
    rw [List.map_append, List.sum_append, List.map_map, ← List.sum_map_add, ← List.sum_map_mul_left]
    refine List.sum_le_sum fun v hv => ?_
    refine (cube_step N c s hs hc (Fr v) (Fr (D (Fin.last N) v)) (h1 v (hS v hv))
      (h1 _ (hD _ v (hS v hv))) (h2 v (hS v hv) _)).trans ?_
    simp only [Function.comp_apply]
    have p : ∀ w, 0 ≤ ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
        ‖Fr w (List.ofFn fun i => c i (t i)).prod‖ ^ 2 := fun w => integral_nonneg fun t => by positivity
    have a1 := mul_nonneg (show 0 ≤ 2 * s by positivity) (p v)
    have a2 := mul_nonneg (show 0 ≤ 2 / s by positivity) (p (D (Fin.last N) v))
    nlinarith

theorem exists_small (n : ℕ) : ∃ s : ℝ, 0 < s ∧ n * (Real.exp (3 * n ^ 2 * s) - 1) ≤ 1 / 2 := by
  have h : ContinuousAt (fun s : ℝ => n * (Real.exp (3 * n ^ 2 * s) - 1)) 0 := by fun_prop
  have h2 : ∀ᶠ s : ℝ in 𝓝 0, n * (Real.exp (3 * n ^ 2 * s) - 1) < 1 / 2 :=
    h.eventually_lt continuousAt_const (by simp)
  obtain ⟨s, h3, h4⟩ := ((h2.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi 0))).and self_mem_nhdsWithin).exists
  exact ⟨s, h4, h3.le⟩

theorem sobolev_at_one : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ F : List (Mx n) → Mx n → ℂ, (∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε)) → IsDerFam ε F → (∀ l ∈ S, Integrable (fun g : UJ ε => ‖F l (umat g)‖ ^ 2) (muG ε)) → ‖F [] 1‖ ^ 2 ≤ C * (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).sum := by
  intro n ε
  obtain ⟨E, hE1, hE2, -⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  obtain ⟨κ, hκ, hg, -⟩ := GlobalTheory.GaugeConst.exists_unique_isGauge n ε
  obtain ⟨s, hs, hsn⟩ := exists_small n
  let c : Fin (n ^ 2) → ℝ → UJ ε := fun i t =>
    GlobalTheory.GaugeConst.expJ ε (t • (⟨E i, (hE1 i).1⟩ : GlobalTheory.GaugeConst.lieJ ε))
  have hc : ∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b := fun i =>
    ⟨(GlobalTheory.GaugeConst.continuous_expJ ε).comp (continuous_id.smul continuous_const),
      GlobalTheory.GaugeConst.uMat_injective ε (by
        change NormedSpace.exp ((0 : ℝ) • E i) = 1
        simp),
      fun a b => GlobalTheory.GaugeConst.uMat_injective ε (exp_add_smul (E i) a b)⟩
  obtain ⟨S, C, hS, hC, h⟩ := cube_sum {l : List (Mx n) | ∀ Y ∈ l, Y ∈ lieSet ε} [] (by simp) s hs (n ^ 2) c
    (fun i l => E i :: l) hc (fun i l hl Y hY => by
      rcases List.mem_cons.1 hY with rfl | hY
      exacts [(hE1 i).1, hl Y hY])
  set K := Real.exp (2 * n ^ 3 * (Real.exp (2 * n ^ 2 * s) - 1)) * κ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨S, C * K, hS, by positivity, fun F hF hD hI => ?_⟩
  have hcont : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → Continuous fun g : UJ ε => F l (umat g) :=
    fun l hl => (hF l hl).comp_continuous (GlobalTheory.GaugeConst.continuous_uMat ε) fun g => g.2
  refine (h (fun l g => F l (umat g)) hcont fun l hl i x => hD l hl (E i) (hE1 i).1 _ x.2).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC
  rw [← List.sum_map_mul_left]
  refine List.sum_le_sum fun l hl => ?_
  have hl' := hcont l (hS l hl)
  have hΘ := continuous_prod_ofFn_curves (n ^ 2) c (fun i => (hc i).1)
  have hch := GlobalTheory.ProductChart.lintegral_chart_le n ε κ s E (fun t => (List.ofFn fun i => c i (t i)).prod) hg
    (fun i => (hE1 i).1) hE2 hs hsn (fun t => by
      have := map_list_prod ((Units.coeHom (Mx n)).comp (UJ ε).subtype) (List.ofFn fun i => c i (t i))
      refine this.trans ?_
      rw [List.map_ofFn]
      simp only [Complex.coe_smul]
      rfl)
    (fun g => ENNReal.ofReal (‖F l (umat g)‖ ^ 2)) (hl'.norm.pow 2).measurable.ennreal_ofReal
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun t : Fin (n ^ 2) → ℝ => ‖F l (umat (List.ofFn fun i => c i (t i)).prod)‖ ^ 2)
    (Filter.Eventually.of_forall fun t => by positivity)
    ((hl'.comp hΘ).norm.pow 2).aestronglyMeasurable]
  have hp : 0 ≤ ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε) := integral_nonneg fun g => by positivity
  refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK0 hp) (hch.trans ?_)
  rw [ENNReal.ofReal_mul hK0, ofReal_integral_eq_lintegral_ofReal (hI l hl)
    (Filter.Eventually.of_forall fun g => by positivity)]
  exact mul_le_mul_right (setLIntegral_le_lintegral _ _) _

end GlobalTheory.SobolevHaar
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

noncomputable section

namespace GlobalTheory.TypeSumCtrl

def allWords {α : Type} {k : ℕ} (E : Fin k → α) (m : ℕ) : List (List α) :=
  Nat.rec [[]] (fun _ T => [] :: T.flatMap fun l => (List.ofFn E).map fun X => X :: l) m

theorem allWords_zero {α : Type} {k : ℕ} (E : Fin k → α) : allWords E 0 = [[]] := rfl

theorem allWords_succ {α : Type} {k : ℕ} (E : Fin k → α) (m : ℕ) :
    allWords E (m + 1) = [] :: (allWords E m).flatMap fun l => (List.ofFn E).map fun X => X :: l := rfl

theorem mem_allWords {α : Type} {k : ℕ} (E : Fin k → α) :
    ∀ (m : ℕ) (l : List α), l ∈ allWords E m ↔ l.length ≤ m ∧ ∀ X ∈ l, ∃ i, E i = X
  | 0, l => by
    cases l <;> simp [allWords_zero]
  | m + 1, [] => by simp [allWords_succ]
  | m + 1, X :: l => by
    simp only [allWords_succ, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_ofFn, List.length_cons,
      reduceCtorEq, false_or, List.cons.injEq, forall_eq_or_imp, Nat.add_le_add_iff_right]
    constructor
    · rintro ⟨l', h1, Y, h2, rfl, rfl⟩
      exact ⟨((mem_allWords E m _).1 h1).1, h2, ((mem_allWords E m _).1 h1).2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨l, (mem_allWords E m _).2 ⟨h1, h3⟩, X, h2, rfl, rfl⟩

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} {k : ℕ}

def cf (E : Fin k → Mx n) (X : Mx n) : ℝ := ∑ i, |((X * (E i)ᴴ).trace).re|

theorem cf_nonneg (E : Fin k → Mx n) (X : Mx n) : 0 ≤ cf E X := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem continuous_cf (E : Fin k → Mx n) : Continuous (cf E) := by
  unfold cf
  refine continuous_finsetSum _ fun i _ => ?_
  exact (Complex.continuous_re.comp ((continuous_id.matrix_mul continuous_const).matrix_trace)).abs

omit [CompleteSpace H] in
theorem Dw_sum (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) (c : Fin k → ℂ)
    {x : Fin k → H} (hx : ∀ i, Sm ε σ (x i)) : Dw σ l (∑ i, c i • x i) = ∑ i, c i • Dw σ l (x i) := by
  obtain ⟨L, hL⟩ := exists_word (isUnit_Jm ε) hσ l hl
  have := congrArg Subtype.val (map_sum L (fun i => c i • (⟨x i, hx i⟩ : smooth (Jm ε) σ)) Finset.univ)
  simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, hL] at this
  exact this

theorem key (h : Std ε σ) {E : Fin k → Mx n} (hE : ∀ i, E i ∈ lieSet ε)
    (hx : ∀ X ∈ lieSet ε, X = ∑ i, ((X * (E i)ᴴ).trace).re • E i) (m : ℕ) {w : H} (hw : Sm ε σ w)
    (l : List (Mx n)) (hl : ∀ X ∈ l, X ∈ lieSet ε) :
    ∀ p : List (Mx n), (∀ X ∈ p, ∃ i, E i = X) → p.length + l.length ≤ m →
      ‖Dw σ (p ++ l) w‖ ≤ (l.map (cf E)).prod * sobNorm σ (allWords E m) w := by
  induction l with
  | nil =>
    intro p hp hm
    simpa using norm_Dw_le_sobNorm σ ((mem_allWords E m p).2 ⟨by simpa using hm, hp⟩) w
  | cons X l ih =>
    intro p hp hm
    have hX := hl X List.mem_cons_self
    have hl' := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    have hp' : ∀ Y ∈ p, Y ∈ lieSet ε := fun Y hY => by
      obtain ⟨i, rfl⟩ := hp Y hY
      exact hE i
    have hs := hw.word h.1 hl'
    have e1 : Dw σ (p ++ X :: l) w =
        ∑ i, ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • Dw σ ((p ++ [E i]) ++ l) w := by
      rw [Dw_append]
      show Dw σ p (dRep σ X (Dw σ l w)) = _
      conv_lhs => rw [hx X hX]
      rw [h.dRep_sum hE hs, Dw_sum h.1 hp' _ (fun i => dRep_mem (isUnit_Jm ε) h.1 hs (hE i))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Dw_append, Dw_append]
      rfl
    rw [e1, List.map_cons, List.prod_cons, mul_assoc, cf, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left (ih hl' _ ?_ ?_) (abs_nonneg _)
    · intro Y hY
      rcases List.mem_append.1 hY with hY | hY
      · exact hp Y hY
      · exact ⟨i, (List.mem_singleton.1 hY).symm⟩
    · simp only [List.length_append, List.length_cons, List.length_nil] at hm ⊢
      omega

theorem sob_le (h : Std ε σ) {E : Fin k → Mx n} (hE : ∀ i, E i ∈ lieSet ε)
    (hx : ∀ X ∈ lieSet ε, X = ∑ i, ((X * (E i)ᴴ).trace).re • E i) (m : ℕ) {w : H} (hw : Sm ε σ w)
    (S : List (List (Mx n))) (hS : Words (lieSet ε) S) (hm : ∀ l ∈ S, l.length ≤ m) :
    sobNorm σ S w ≤ (S.map fun l => (l.map (cf E)).prod).sum * sobNorm σ (allWords E m) w := by
  rw [← List.sum_map_mul_right]
  conv_lhs => unfold sobNorm
  refine List.sum_le_sum fun l hl => ?_
  simpa using key h hE hx m hw l (hS l hl) [] (by simp) (by simpa using hm l hl)

theorem exists_ctrl : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ S₀ : List (List (Mx n)), Words (lieSet ε) S₀ → ∃ S : List (List (Mx n)), Words (lieSet ε) S ∧ [] ∈ S ∧ Ctrl (lieSet ε) (UJset ε) σ S ∧ ∃ A : ℝ, 0 ≤ A ∧ ∀ w, Sm ε σ w → sobNorm σ S₀ w ≤ A * sobNorm σ S w := by
  intro n ε H _ _ _ σ h S₀ hS₀
  obtain ⟨E, hE, -, hx⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  have hE' : ∀ i, E i ∈ lieSet ε := fun i => (hE i).1
  have hx' : ∀ X ∈ lieSet ε, X = ∑ i, ((X * (E i)ᴴ).trace).re • E i := fun X hX => by
    simpa only [Complex.coe_smul] using hx X hX
  set m := (S₀.map List.length).sum with hm
  have hW : Words (lieSet ε) (allWords E m) := fun l hl X hX => by
    obtain ⟨i, rfl⟩ := ((mem_allWords E m l).1 hl).2 X hX
    exact hE' i
  refine ⟨allWords E m, hW, (mem_allWords E m _).2 (by simp), ?_,
    (S₀.map fun l => (l.map (cf E)).prod).sum, ?_, fun w hw => sob_le h hE' hx' m hw S₀ hS₀ fun l hl => ?_⟩
  · refine ⟨fun g => ((allWords E m).map fun l => (l.map fun X => cf E (Jm ε * gᴴ * Jm ε * X * g)).prod).sum, ?_,
      fun g hg w hw => ?_⟩
    · refine continuous_list_sum _ fun l _ => continuous_list_prod _ fun X _ => ?_
      exact (continuous_cf E).comp (f := fun g : Mx n => Jm ε * gᴴ * Jm ε * X * g)
        (((((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul
          continuous_const).matrix_mul continuous_const)).matrix_mul continuous_id)
    · rw [sobNorm_translate h.1 hg hw hW]
      have := sob_le h hE' hx' m hw ((allWords E m).map fun l => l.map fun X => g⁻¹ * X * g) ?_ ?_
      · simpa only [List.map_map, Function.comp_def, inv_eq_UJ hg] using this
      · intro l hl X hX
        obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
        obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        exact conj_mem_lie (isUnit_Jm ε) hg (hW l' hl' Y hY)
      · intro l hl
        obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
        simpa using ((mem_allWords E m l').1 hl').1
  · refine List.sum_nonneg fun x hx => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    refine List.prod_nonneg fun y hy => ?_
    obtain ⟨X, -, rfl⟩ := List.mem_map.1 hy
    exact cf_nonneg E X
  · exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨l, hl, rfl⟩)

end GlobalTheory.TypeSumCtrl

end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.projective_bundle_points_of_rational_model : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J] [DecidableEq J] (EE : M.Lat J) (s : J → Ω'), ProjBundle M EE M' φ f s → ProjPoints M EE M' φ f s := by
  first | exact @GlobalTheory.FlagBundle.projPoints_of_projBundle | exact GlobalTheory.FlagBundle.projPoints_of_projBundle | (intros; apply GlobalTheory.FlagBundle.projPoints_of_projBundle <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.exists_projectiveBundleOfLattice_isProjOver : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (J : Type) [Fintype J] [DecidableEq J] [Nonempty J] (EE : M.Lat J), IsProjOver M.s → ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra F Ω') (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (s : J → Ω'), ProjBundle M EE M' φ f s ∧ IsProjOver M'.s := by
  first | exact @GlobalTheory.FlagBundle.exists_projBundle | exact GlobalTheory.FlagBundle.exists_projBundle | (intros; apply GlobalTheory.FlagBundle.exists_projBundle <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.existsUnique_projectiveBundle_flagRefinement : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (ι : Type) [Finite ι] (m k k' : ι → ℕ) (S : Fr M m k) (S' : Fr M' m k') (τ : ι) (hk : k τ < m τ) (A₀ : Mat m Ω) (EE : M.Lat (Rest m k τ)) (s : Rest m k τ → Ω'), k' τ = k τ + 1 → (∀ τ', τ' ≠ τ → k' τ' = k τ') → A₀ ∈ S.S (genericPoint M.Z) → (∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧ EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A))) → ProjPoints M EE M' φ f s → (∀ z', S'.S z' = stepSet S τ hk A₀ M' φ f s z') → ∀ (K : Type) [Field K] (x : Sp K ⟶ M.Z), ∀ A ∈ S.S (x (IsLocalRing.closedPoint K)), ∀ h : Mat m K, Par k ⊤ h → ∃! p : Sp K ⟶ M'.Z, p ≫ f = x ∧ Bears S' φ A h p := by
  first | exact @GlobalTheory.FlagBundle.StepLift.existsUnique_bears | exact GlobalTheory.FlagBundle.StepLift.existsUnique_bears | (intros; apply GlobalTheory.FlagBundle.StepLift.existsUnique_bears <;> assumption)
end
