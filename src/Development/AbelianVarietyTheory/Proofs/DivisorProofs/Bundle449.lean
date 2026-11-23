module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle438
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle399
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle437
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle433
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle400
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle004
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.GlueDist

theorem sq_norm_smoothSection_sub_glued_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), A.IsSSec (A.kap + la) F0 → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → n0 A la (F0 - glue C la u) ≤ (C.m : ℝ≥0∞) * ∑ a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
  intro n Y _ _ _ _ _ ι La _ A C la F0 u hF hu
  classical
  set L := A.kap + la with hL

  set D : Fin C.m → ι → Y → ℂ := fun a j y =>
    F0 j y - A.g L j (C.idx a) y * u a (A.chart (C.idx a) y) with hD
  set S : Fin C.m → Set Y := fun a =>
    (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) with hS
  have hSo : ∀ a, IsOpen (S a) := fun a =>
    (A.chart (C.idx a)).isOpen_inter_preimage isOpen_ball
  have hsec : ∀ a, ∀ y ∈ (A.chart (C.idx a)).source, ∀ j, y ∈ (A.chart j).source →
      D a j y = A.g L j (C.idx a) y * D a (C.idx a) y := by
    intro a y hy j hj
    simp only [hD]
    rw [hF.2 j (C.idx a) y hj hy, A.g_self L (C.idx a) hy]
    ring
  have hchart : ∀ a, ∀ y ∈ (A.chart (C.idx a)).source,
      A.nsq L (D a) y = ‖F0 (C.idx a) y - u a (A.chart (C.idx a) y)‖ ^ 2 *
        Real.exp (-A.ph L (C.idx a) y) := by
    intro a y hy
    rw [A.nsq_chart L (D a) (C.idx a) hy (hsec a y hy _ (A.mem_pick y))]
    simp only [hD, A.g_self L (C.idx a) hy, one_mul]

  have hsum1 : ∀ y, ∑ a, (C.chi a y : ℂ) = 1 := by
    intro y; rw [← Complex.ofReal_sum, C.sum_one y, Complex.ofReal_one]
  have hG : F0 - glue C la u = fun j y => ∑ a, (C.chi a y : ℂ) * D a j y := by
    funext j y
    simp only [Pi.sub_apply, glue, hD, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hsum1 y, one_mul]
    congr 1
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have hchi1 : ∀ a y, C.chi a y ≤ 1 := by
    intro a y
    rw [← C.sum_one y]
    exact Finset.single_le_sum (fun b _ => C.nonneg b y) (Finset.mem_univ a)

  have hpt : ∀ y, A.nsq L (F0 - glue C la u) y ≤
      (C.m : ℝ) * ∑ a, (S a).indicator (A.nsq L (D a)) y := by
    intro y
    rw [hG]
    refine (A.nsq_sum_le L Finset.univ (fun a j y => (C.chi a y : ℂ) * D a j y) y).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (Nat.cast_nonneg _)
    have he : A.nsq L (fun j y => (C.chi a y : ℂ) * D a j y) y = C.chi a y ^ 2 * A.nsq L (D a) y := by
      unfold WeightedAtlas.nsq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (C.nonneg a y)]
      ring
    rw [he]
    by_cases h0 : C.chi a y = 0
    · rw [h0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      exact Set.indicator_nonneg (fun x _ => A.nsq_nonneg L (D a) x) y
    · have hyS : y ∈ S a := C.supp a (subset_tsupport _ h0)
      rw [Set.indicator_of_mem hyS]
      have h2 : C.chi a y ^ 2 ≤ 1 := pow_le_one₀ (C.nonneg a y) (hchi1 a y)
      nlinarith [A.nsq_nonneg L (D a) y]

  have hF0c : ∀ i, ContinuousOn (F0 i) (A.chart i).source := by
    intro i
    have h1 : ContinuousOn (F0 i ∘ (A.chart i).symm) (A.chart i).target := (hF.1 i).continuousOn
    refine (h1.comp (A.chart i).continuousOn (fun x hx => (A.chart i).map_source hx)).congr
      (fun x hx => ?_)
    simp [Function.comp, (A.chart i).left_inv hx]
  have hcont : ∀ a, ContinuousOn (fun y => ENNReal.ofReal (A.nsq L (D a) y)) (S a) := by
    intro a
    refine ENNReal.continuous_ofReal.comp_continuousOn ?_
    have hu' : ContinuousOn (fun y => u a (A.chart (C.idx a) y)) (S a) :=
      (hu a).continuousOn.comp ((A.chart (C.idx a)).continuousOn.mono Set.inter_subset_left)
        (fun y hy => hy.2)
    have hc : ContinuousOn (fun y => ‖F0 (C.idx a) y - u a (A.chart (C.idx a) y)‖ ^ 2 *
        Real.exp (-A.ph L (C.idx a) y)) (S a) :=
      ((((hF0c (C.idx a)).mono Set.inter_subset_left).sub hu').norm.pow 2).mul
        ((A.continuousOn_ph L (C.idx a)).mono Set.inter_subset_left).neg.rexp
    exact hc.congr (fun y hy => hchart a y hy.1)
  have hmeas : ∀ a, AEMeasurable ((S a).indicator (fun y => ENNReal.ofReal (A.nsq L (D a) y))) A.mu :=
    fun a => (aemeasurable_indicator_iff (hSo a).measurableSet).2
      ((hcont a).aemeasurable (hSo a).measurableSet)

  have hpiece : ∀ a, ∫⁻ y in S a, ENNReal.ofReal (A.nsq L (D a) y) ∂A.mu =
      ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
    intro a
    have hWt : ball (C.c a) (C.r a) ⊆ (A.chart (C.idx a)).target :=
      ball_subset_closedBall.trans (C.sub a)
    have heq : ∀ v ∈ ball (C.c a) (C.r a),
        D a (C.idx a) ((A.chart (C.idx a)).symm v) = F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v := by
      intro v hv
      have hvt := hWt hv
      simp only [hD, A.g_self L (C.idx a) ((A.chart (C.idx a)).map_target hvt),
        (A.chart (C.idx a)).right_inv hvt, one_mul]
    have hae : AEMeasurable (D a (C.idx a) ∘ (A.chart (C.idx a)).symm) (volume.restrict (ball (C.c a) (C.r a))) := by
      have hc : ContinuousOn (fun v => F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v) (ball (C.c a) (C.r a)) :=
        (((hF.1 (C.idx a)).continuousOn.mono hWt).sub (hu a).continuousOn)
      exact (hc.congr (fun v hv => heq v hv)).aemeasurable measurableSet_ball
    rw [GlobalTheory.T.lintegral_nsq_canonical_add_chart_part n Y ι La A la (C.idx a) (ball (C.c a) (C.r a)) (D a) measurableSet_ball hWt
      (fun y hy _ => hsec a y hy _ (A.mem_pick y)) hae]
    refine setLIntegral_congr_fun measurableSet_ball (fun v hv => ?_)
    rw [heq v hv]

  unfold n0
  calc ∫⁻ y, ENNReal.ofReal (A.nsq L (F0 - glue C la u) y) ∂A.mu
      ≤ ∫⁻ y, (C.m : ℝ≥0∞) * ∑ a, (S a).indicator (fun y => ENNReal.ofReal (A.nsq L (D a) y)) y ∂A.mu := by
        refine lintegral_mono fun y => ?_
        refine (ENNReal.ofReal_le_ofReal (hpt y)).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun a _ => Set.indicator_nonneg (fun x _ => A.nsq_nonneg L (D a) x) y)]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases hy : y ∈ S a
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy]
    _ = (C.m : ℝ≥0∞) * ∑ a, ∫⁻ y in S a, ENNReal.ofReal (A.nsq L (D a) y) ∂A.mu := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _), lintegral_finsetSum' _ (fun a _ => hmeas a)]
        congr 1
        exact Finset.sum_congr rfl fun a _ => lintegral_indicator (hSo a).measurableSet _
    _ = _ := by
        congr 1
        exact Finset.sum_congr rfl fun a _ => hpiece a

end GlobalTheory.GlueDist
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties : ∀ (k K : Type) [Field k] [Field K] [Algebra k K], ∀ (B : Subalgebra k K) (p q : ℕ), (∀ a ∈ omB k K B p, ∀ b ∈ omB k K B q, a * b ∈ omB k K B (p + q)) ∧ (∀ a ∈ omB k K B p, dDR k K a ∈ omB k K B (p + 1) ∧ sg k K a = (-1 : k) ^ p • a ∧ a ∈ ⋀[K]^p Ω[K⁄k] ∧ ∀ c ∈ B, c • a ∈ omB k K B p) ∧ (∀ B' : Subalgebra k K, B ≤ B' → omB k K B p ≤ omB k K B' p) ∧ ∀ y : DR k K, y ∈ omB k K B 0 ↔ ∃ c ∈ B, y = algebraMap K (DR k K) c := by
  first | (exact @GlobalTheory.PD.omB_alg) | (exact GlobalTheory.PD.omB_alg) | (intros; apply GlobalTheory.PD.omB_alg <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → ∀ y : F, y ∈ rA k x I ↔ ∃ N : ℕ, y * (∏ j ∈ I, x j / x i) ^ N ∈ rA k x {i} := by
  first | (exact @GlobalTheory.PD.rA_eq_loc) | (exact GlobalTheory.PD.rA_eq_loc) | (intros; apply GlobalTheory.PD.rA_eq_loc  <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

section Wedge

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem omB_smul_mem (B : Subalgebra k K) (q : ℕ) {c : K} (hc : c ∈ B) {z : DR k K}
    (hz : z ∈ omB k K B q) : c • z ∈ omB k K B q := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hz
    exact Submodule.subset_span ⟨c * b, B.mul_mem hc hb, v, hv, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

def topCoefBasis {n : ℕ} (b : Module.Basis (Fin n) K Ω[K⁄k]) : DR k K →ₗ[K] K :=
  ExteriorAlgebra.liftAlternating (fun i => if h : i = n then h ▸ b.det else 0)

theorem topCoefBasis_ιMulti {n : ℕ} (b : Module.Basis (Fin n) K Ω[K⁄k]) (v : Fin n → Ω[K⁄k]) :
    topCoefBasis b (ExteriorAlgebra.ιMulti K n v) = b.det v := by
  simp [topCoefBasis, ExteriorAlgebra.liftAlternating_apply_ιMulti]

theorem topCoefBasis_mem (B : Subalgebra k K) {n : ℕ} (b : Module.Basis (Fin n) K Ω[K⁄k]) (f : K)
    (hf : ∀ (v : B) (j : Fin n), ∃ c : B, f * b.repr (D k K (v : K)) j = c)
    {z : DR k K} (hz : z ∈ omB k K B n) : ∃ e : B, f ^ n * topCoefBasis b z = e := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b0, hb0, v, hv, rfl⟩ := hz
    choose M hM using fun i j => hf ⟨v j, hv j⟩ i
    have hmat : f • b.toMatrix (fun j => D k K (v j)) = (B.val : B →+* K).mapMatrix (Matrix.of M) := by
      ext i j
      simp [Module.Basis.toMatrix_apply, ← hM]
    have hdet := congrArg Matrix.det hmat
    rw [Matrix.det_smul, Fintype.card_fin, ← RingHom.map_det] at hdet
    refine ⟨⟨b0, hb0⟩ * (Matrix.of M).det, ?_⟩
    rw [map_smul, topCoefBasis_ιMulti, Module.Basis.det_apply, smul_eq_mul, mul_left_comm, hdet]
    simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨e1, h1⟩ := hx
    obtain ⟨e2, h2⟩ := hy
    exact ⟨e1 + e2, by rw [map_add (f := _), mul_add, h1, h2]; simp⟩
  | smul r x _ hx =>
    obtain ⟨e, he⟩ := hx
    exact ⟨r • e, by rw [LinearMap.map_smul_of_tower, mul_smul_comm, he]; simp⟩

theorem eq_sum_exteriorPower_basis {n q : ℕ} (b : Module.Basis (Fin n) K Ω[K⁄k]) (Y : ⋀[K]^q Ω[K⁄k]) :
    (Y : DR k K) = ∑ t, (b.exteriorPower q).repr Y t •
      ExteriorAlgebra.ιMulti K q (b ∘ (Set.powersetCard.ofFinEmbEquiv.symm t)) := by
  conv_lhs => rw [← (b.exteriorPower q).sum_repr Y]
  simp [exteriorPower.coe_basis, exteriorPower.ιMulti_family]

theorem wedge_coef_mem (B : Subalgebra k K) {p q : ℕ} (b : Module.Basis (Fin (p + q)) K Ω[K⁄k])
    (u : Fin (p + q) → B) (hb : ∀ j, b j = D k K (u j : K)) (f : K)
    (hf : ∀ (v : B) (j : Fin (p + q)), ∃ c : B, f * b.repr (D k K (v : K)) j = c)
    (Y : ⋀[K]^q Ω[K⁄k]) (hmul : ∀ a ∈ omB k K B p, a * (Y : DR k K) ∈ omB k K B (p + q))
    (s : Set.powersetCard (Fin (p + q)) q) :
    ∃ e : B, f ^ (p + q) * (b.exteriorPower q).repr Y s = e := by
  classical
  have hcard : (s.val)ᶜ.card = p := by
    rw [Finset.card_compl, Fintype.card_fin, s.prop]; omega
  set g := Finset.orderEmbOfFin (s.val)ᶜ hcard with hg
  set a : DR k K := ExteriorAlgebra.ιMulti K p (b ∘ g) with ha_def
  have ha : a ∈ omB k K B p :=
    Submodule.subset_span ⟨1, B.one_mem, fun j => (u (g j) : K), fun j => (u (g j)).2,
      by simp [a, Function.comp_def, hb]⟩
  obtain ⟨e, he⟩ := topCoefBasis_mem B b f hf (hmul a ha)
  have happ : ∀ h : Fin q → Fin (p + q),
      Fin.append (b ∘ g) (b ∘ h) = b ∘ Fin.append (fun i => g i) h := by
    intro h; funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  have hterm : ∀ t, t ≠ s → topCoefBasis b
      (a * ExteriorAlgebra.ιMulti K q (b ∘ (Set.powersetCard.ofFinEmbEquiv.symm t))) = 0 := by
    intro t hts
    obtain ⟨i, hit, his⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne t s).mp hts
    have hi1 : i ∈ Set.range g := by
      rw [hg, Finset.range_orderEmbOfFin]; simpa using his
    have hi2 : i ∈ Set.range (Set.powersetCard.ofFinEmbEquiv.symm t) :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t i).mpr hit
    obtain ⟨a1, ha1⟩ := hi1
    obtain ⟨a2, ha2⟩ := hi2
    rw [ha_def, ExteriorAlgebra.ιMulti_mul_ιMulti, topCoefBasis_ιMulti, happ]
    refine b.det.map_eq_zero_of_eq _ (i := Fin.castAdd q a1) (j := Fin.natAdd p a2) ?_ ?_
    · simp [ha1, ha2]
    · intro h; have := congrArg Fin.val h; simp at this; omega
  have hdiag : ∃ ε : ℤˣ, topCoefBasis b
      (a * ExteriorAlgebra.ιMulti K q (b ∘ (Set.powersetCard.ofFinEmbEquiv.symm s))) = ((ε : ℤ) : K) := by
    set h := Fin.append (fun i => g i) (Set.powersetCard.ofFinEmbEquiv.symm s) with hh
    have hinj : Function.Injective h := by
      rw [hh, Fin.append_injective_iff]
      refine ⟨g.injective, (Set.powersetCard.ofFinEmbEquiv.symm s).injective, fun i j hij => ?_⟩
      have h1 : g i ∈ (s.val)ᶜ := by
        rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin (s.val)ᶜ hcard]; exact ⟨i, rfl⟩
      have h2 : Set.powersetCard.ofFinEmbEquiv.symm s j ∈ s.val :=
        (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨j, rfl⟩
      rw [hij] at h1
      exact (Finset.mem_compl.mp h1) h2
    set σ := Equiv.ofBijective h (Finite.injective_iff_bijective.mp hinj)
    refine ⟨Equiv.Perm.sign σ, ?_⟩
    rw [ha_def, ExteriorAlgebra.ιMulti_mul_ιMulti, topCoefBasis_ιMulti, happ]
    have : b ∘ h = b ∘ σ := rfl
    rw [this, b.det.map_perm, Module.Basis.det_self, Units.smul_def, zsmul_eq_mul, mul_one]
  obtain ⟨ε, hε⟩ := hdiag
  have hsum : topCoefBasis b (a * (Y : DR k K)) = (b.exteriorPower q).repr Y s * ((ε : ℤ) : K) := by

    rw [eq_sum_exteriorPower_basis b Y, Finset.mul_sum, map_sum, Finset.sum_eq_single s]
    · rw [mul_smul_comm, map_smul, hε, smul_eq_mul]
    · intro t _ hts; rw [mul_smul_comm, map_smul, hterm t hts, smul_zero]
    · intro h; exact absurd (Finset.mem_univ s) h
  refine ⟨e * ((ε : ℤ) : B), ?_⟩
  have hεε : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  push_cast
  rw [← he, hsum]
  calc f ^ (p + q) * (b.exteriorPower q).repr Y s
      = f ^ (p + q) * (b.exteriorPower q).repr Y s * (((ε : ℤ) : K) * ((ε : ℤ) : K)) := by rw [hεε, mul_one]
    _ = _ := by ring

theorem mem_omB_of_mul_mem_omB :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K]
      [Algebra.Smooth k B] (d p q : ℕ), Module.finrank K Ω[K⁄k] = d → p + q = d →
      ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K B p, a * y ∈ omB k K B d) → y ∈ omB k K B q := by
  intro k K _ _ _ B _ _ d p q hd hpq y hy hmul
  classical
  subst hpq
  let I : Ideal B :=
    { carrier := {c | (c : K) • y ∈ omB k K B q}
      add_mem' := fun {a c} ha hc => by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, add_smul] at *
        exact Submodule.add_mem _ ha hc
      zero_mem' := by simp
      smul_mem' := fun a c hc => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, mul_smul] at *
        exact omB_smul_mem B q a.2 hc }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨f, u, b, hfP, hb, hf⟩ := GlobalTheory.T.exists_local_kaehlerD_basis_smooth_subalgebra k K B (p + q) hd P
    apply hfP
    refine hP.isPrime.mem_of_pow_mem (p + q) (hIP ?_)
    show ((f ^ (p + q) : B) : K) • y ∈ omB k K B q
    have hy' := eq_sum_exteriorPower_basis b ⟨y, hy⟩
    simp only at hy'
    rw [hy', Finset.smul_sum]
    refine Submodule.sum_mem _ fun t _ => ?_
    obtain ⟨e, he⟩ := wedge_coef_mem B b u hb (f : K) hf ⟨y, hy⟩ hmul t
    rw [smul_smul, SubmonoidClass.coe_pow, he]
    exact Submodule.subset_span ⟨e, e.2, fun j => (u (Set.powersetCard.ofFinEmbEquiv.symm t j) : K),
      fun j => (u _).2,
      by simp [Function.comp_def, hb]⟩
  have h1 : (1 : B) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

end Wedge

end GlobalTheory.PD
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {k : Type} [Field k]


omit [Field k] in
theorem mem_augIdeal_iff' {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A] (a : A) :
    a ∈ augIdeal R A ↔ counit (R := R) a = 0 := by
  rw [augIdeal, RingHom.mem_ker, Bialgebra.counitAlgHom_apply]

theorem eq_zero_of_app_augIdeal {G H : PDivGroup p k} (f : G ⟶ H)
    (hf : ∀ n, ∀ a ∈ augIdeal k (H.A n), f.app n a = 0) : f = 0 := by
  refine Hom.ext (funext fun n => BialgHom.ext fun a => ?_)
  have hmem : a - algebraMap k (H.A n) (counit (R := k) a) ∈ augIdeal k (H.A n) := by
    rw [mem_augIdeal_iff', map_sub, ← Bialgebra.counitAlgHom_apply (R := k),
      ← Bialgebra.counitAlgHom_apply (R := k), AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  have h := hf n _ hmem
  rw [map_sub, AlgHomClass.commutes, sub_eq_zero] at h
  exact h

variable [Fact p.Prime] [CharP k p] [PerfectRing k p]

theorem exists_augIdeal_pow_eq {A : Type} [CommRing A] [Bialgebra k A] [Module.Finite k A]
    [IsReduced A] (r : ℕ) : ∀ a ∈ augIdeal k A, ∃ b ∈ augIdeal k A, a = b ^ p ^ r := by
  induction r with
  | zero => exact fun a ha => ⟨a, ha, by rw [pow_zero, pow_one]⟩
  | succ r ih =>
    intro a ha
    obtain ⟨b, hb, rfl⟩ := ih a ha
    obtain ⟨c, rfl⟩ := exists_pow_char_eq_of_isReduced_finite p k A b
    refine ⟨c, ?_, by rw [← pow_mul, ← pow_succ']⟩
    rw [mem_augIdeal_iff'] at hb ⊢
    rw [← Bialgebra.counitAlgHom_apply (R := k), map_pow, Bialgebra.counitAlgHom_apply] at hb
    exact pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.1 hb

theorem eq_zero_of_isConn_of_isEt {G H : PDivGroup p k} (hG : G.IsConn) (hH : H.IsEt)
    (f : G ⟶ H) : f = 0 := by
  refine eq_zero_of_app_augIdeal f fun n a ha => ?_
  haveI := hH n
  haveI : IsNoetherianRing (G.A n) := isNoetherian_of_tower k inferInstance
  obtain ⟨N, hN⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical
    (IsNoetherian.noetherian (augIdeal k (G.A n)))).2 fun x hx => mem_nilradical.2 (hG n x hx)
  obtain ⟨b, hb, rfl⟩ := exists_augIdeal_pow_eq (A := H.A n) N a ha
  have hfb : f.app n b ∈ augIdeal k (G.A n) := by
    rw [mem_augIdeal_iff', CoalgHomClass.counit_comp_apply]
    exact (mem_augIdeal_iff' b).1 hb
  have hle : N ≤ p ^ N := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have h1 := Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hfb (p ^ N))
  rw [hN] at h1
  rw [map_pow]
  exact (Submodule.mem_bot _).1 h1

theorem eq_zero_of_isEt_of_isConn {G H : PDivGroup p k} (hG : G.IsConn) (hH : H.IsEt)
    (f : H ⟶ G) : f = 0 := by
  refine eq_zero_of_app_augIdeal f fun n a ha => ?_
  haveI := hH n
  exact ((hG n a ha).map (f.app n)).eq_zero

end PDivGroup

theorem PDivGroup.hom_eq_zero_of_isConn_of_isEt :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
      (G H : PDivGroup p k), G.IsConn → H.IsEt → (∀ f : G ⟶ H, f = 0) ∧ ∀ f : H ⟶ G, f = 0 :=
  fun _ _ _ _ _ _ _ _ hG hH =>
    ⟨PDivGroup.eq_zero_of_isConn_of_isEt hG hH, PDivGroup.eq_zero_of_isEt_of_isConn hG hH⟩

end GlobalTheory
end
end

section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.CechDR

theorem appLE_ι_appLE_eq_secMap : ∀ (X T : Scheme.{0}) (p : T ⟶ X) (U : X.affineOpens) (O : T.Opens) (hO : O ≤ p ⁻¹ᵁ U.1) (V : (p ⁻¹ᵁ U.1).toScheme.Opens) (e : V ≤ (p ⁻¹ᵁ U.1).ι ⁻¹ᵁ O) (r : Γ(X, U.1)), ((p ⁻¹ᵁ U.1).ι.appLE O V e).hom ((p.appLE U.1 O hO).hom r) = (GlobalTheory.CechDR.secMap ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) V).hom r := by
  intro X T p U O hO V e r
  have hU : IsAffineOpen U.1 := U.2
  have key : (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ ((p ∣_ U.1) ≫ hU.isoSpec.hom).appLE ⊤ V (by simp) =
      p.appLE U.1 O hO ≫ (p ⁻¹ᵁ U.1).ι.appLE O V e := by
    change (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ (Scheme.Hom.appTop ((p ∣_ U.1) ≫ hU.isoSpec.hom) ≫
      (p ⁻¹ᵁ U.1).toScheme.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) = _
    rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change U.1.topIso.inv ≫ (p ∣_ U.1).appLE ⊤ V (show V ≤ (p ∣_ U.1) ⁻¹ᵁ ⊤ from fun _ _ => trivial) = _
    rw [morphismRestrict_appLE, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    exact (p.map_appLE _ _).trans (p.appLE_map _ _).symm
  exact (congrArg (fun f => f.hom r) key).symm

end GlobalTheory.CechDR
end

section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

theorem _root_.GlobalTheory.T.exists_holomorphic_param_of_degZero_compatible : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ G : C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T)) → ∃ p : Hol F.V, ∀ T : K.Obj, G T = algebraMap (Hol F.V) T.C p := by
  first | exact @GlobalTheory.AnPer.Charts.exists_param_of_deg_zero | exact GlobalTheory.AnPer.Charts.exists_param_of_deg_zero | (intros; apply GlobalTheory.AnPer.Charts.exists_param_of_deg_zero <;> assumption)
end
