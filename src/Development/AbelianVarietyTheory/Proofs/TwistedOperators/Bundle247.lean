module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SatakeDualWeyl.StatementG
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GLZetaBound

theorem norm_mul_sub_one_le {a b : ℂ} {c : ℝ} (hc : 0 ≤ c) {m k : ℕ}
    (ha : ‖a - 1‖ ≤ (1 + c) ^ m - 1) (hb : ‖b - 1‖ ≤ (1 + c) ^ k - 1) :
    ‖a * b - 1‖ ≤ (1 + c) ^ (m + k) - 1 := by
  have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by ring
  rw [e, pow_add]
  have h1 : ‖(a - 1) * (b - 1)‖ ≤ ((1 + c) ^ m - 1) * ((1 + c) ^ k - 1) := by
    rw [norm_mul]; exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)
  calc ‖(a - 1) * (b - 1) + (a - 1) + (b - 1)‖
      ≤ ‖(a - 1) * (b - 1)‖ + ‖a - 1‖ + ‖b - 1‖ := norm_add₃_le
    _ ≤ ((1 + c) ^ m - 1) * ((1 + c) ^ k - 1) + ((1 + c) ^ m - 1) + ((1 + c) ^ k - 1) := by
        gcongr
    _ = (1 + c) ^ m * (1 + c) ^ k - 1 := by ring

theorem norm_inv_one_sub_sub_one_le {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) :
    ‖(1 - y)⁻¹ - 1‖ ≤ 2 * ‖y‖ := by
  have h1 : 1 - ‖y‖ ≤ ‖1 - y‖ := by
    have := norm_sub_norm_le (1 : ℂ) y
    rwa [norm_one] at this
  have h2 : (1 : ℂ) - y ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; linarith
  have e : (1 - y)⁻¹ - 1 = y / (1 - y) := by field_simp; ring
  rw [e, norm_div, div_le_iff₀ (norm_pos_iff.2 h2)]
  nlinarith [norm_nonneg y]

theorem norm_eulerFac_sub_one_le {B : Multiset ℂˣ} {x : ℂ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (h : ∀ b ∈ B, ‖(b : ℂ) * x‖ ≤ δ) : ‖GlobalTheory.LFun.eulerFac B x - 1‖ ≤ (1 + 2 * δ) ^ B.card - 1 := by
  rw [GlobalTheory.LFun.eulerFac_eq_prod]
  induction B using Multiset.induction_on with
  | empty => simp
  | cons b B ih =>
    have h1 := ih fun c hc => h c (Multiset.mem_cons_of_mem hc)
    have h2 := h b (Multiset.mem_cons_self _ _)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm B.card 1]
    refine norm_mul_sub_one_le (by linarith) ?_ h1
    rw [pow_one]
    have := norm_inv_one_sub_sub_one_le (h2.trans hδ)
    linarith

theorem norm_prod_one_sub_sub_one_le {ι : Type*} (s : Finset ι) (z : ι → ℂ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h : ∀ i ∈ s, ‖z i‖ ≤ δ) : ‖∏ i ∈ s, (1 - z i) - 1‖ ≤ (1 + 2 * δ) ^ s.card - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 := ih fun c hc => h c (Finset.mem_insert_of_mem hc)
    have h2 := h a (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_comm s.card 1]
    refine norm_mul_sub_one_le (by linarith) ?_ h1
    rw [pow_one]
    have e : (1 - z a) - 1 = -z a := by ring
    rw [e, norm_neg]
    linarith

theorem one_add_two_mul_pow_sub_one_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) (m : ℕ) :
    (1 + 2 * δ) ^ m - 1 ≤ 3 ^ m * δ := by
  have key : (1 + 2 * δ) ^ m - 1 ≤ (3 ^ m - 1) * δ := by
    induction m with
    | zero => simp
    | succ m ih =>
      have h3 : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
      have hf : 0 ≤ (1 + 2 * δ) ^ m - 1 := by
        have : (1 : ℝ) ≤ (1 + 2 * δ) ^ m := one_le_pow₀ (by linarith)
        linarith
      have e : (1 + 2 * δ) ^ (m + 1) - 1 = (1 + 2 * δ) * ((1 + 2 * δ) ^ m - 1) + 2 * δ := by ring
      rw [e, pow_succ]
      have : (1 + 2 * δ) * ((1 + 2 * δ) ^ m - 1) ≤ (3 / 2) * ((3 ^ m - 1) * δ) := by
        have : 1 + 2 * δ ≤ 3 / 2 := by linarith
        exact mul_le_mul this ih hf (by norm_num)
      nlinarith
  have : (3 ^ m - 1) * δ ≤ 3 ^ m * δ := by nlinarith
  linarith

theorem norm_trivial_sub_one_le : ∀ (q : ℕ), 2 ≤ q → ∀ (r t : ℕ), r + 5 ≤ t → ∀ (B : Multiset ℂˣ), B.card = r → (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (q : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (q : ℝ) ^ (((r : ℝ) - 1) / 2)) → ∀ X : ℂ, ‖X‖ = (q : ℝ) ^ (-((1 + (t : ℝ)) / 2)) → ‖eulerFac B X * eulerFac (B.map fun β => β⁻¹) X * ∏ i ∈ Finset.Ioc t (r + t), (1 - ((q : ℂ) ^ i)⁻¹) - 1‖ ≤ 27 ^ r * ((q : ℝ) ^ 2)⁻¹ := by
  intro q hq r t hrt B hB hβ X hX
  set δ : ℝ := ((q : ℝ) ^ 2)⁻¹ with hδdef
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hδ0 : 0 ≤ δ := by positivity
  have hδ : δ ≤ 1 / 4 := by
    rw [hδdef]
    have : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hrt' : (r : ℝ) + 5 ≤ t := by exact_mod_cast hrt
  have hbx : (q : ℝ) ^ (((r : ℝ) - 1) / 2) * ‖X‖ ≤ δ := by
    rw [hX, ← Real.rpow_add hq0]
    have e : δ = (q : ℝ) ^ (-(2 : ℝ)) := by
      rw [hδdef, Real.rpow_neg hq0.le, Real.rpow_two]
    rw [e]
    apply Real.rpow_le_rpow_of_exponent_le hq1
    linarith
  have hB1 : ∀ b ∈ B, ‖(b : ℂ) * X‖ ≤ δ := by
    intro b hb
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hβ b hb).1 (norm_nonneg _)).trans hbx
  have hB2 : ∀ b ∈ B.map (fun β : ℂˣ => β⁻¹), ‖(b : ℂ) * X‖ ≤ δ := by
    intro b hb
    obtain ⟨β, hβB, rfl⟩ := Multiset.mem_map.1 hb
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hβ β hβB).2 (norm_nonneg _)).trans hbx
  have h1 := norm_eulerFac_sub_one_le hδ0 (by linarith) hB1
  have h2 := norm_eulerFac_sub_one_le hδ0 (by linarith) hB2
  have h3 := norm_prod_one_sub_sub_one_le (Finset.Ioc t (r + t)) (fun i => ((q : ℂ) ^ i)⁻¹) hδ0
    (by
      intro i hi
      have hi2 : 2 ≤ i := by
        have := (Finset.mem_Ioc.1 hi).1; omega
      rw [norm_inv, norm_pow, Complex.norm_natCast, hδdef]
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_right₀ hq1 hi2)
  rw [Multiset.card_map] at h2
  rw [Nat.card_Ioc, show r + t - t = r by omega] at h3
  rw [hB] at h1 h2
  have h12 := norm_mul_sub_one_le (by linarith) h1 h2
  have h123 := norm_mul_sub_one_le (by linarith) h12 h3
  have h4 := one_add_two_mul_pow_sub_one_le hδ0 hδ (r + r + r)
  have e27 : (3 : ℝ) ^ (r + r + r) = 27 ^ r := by
    rw [show r + r + r = 3 * r by ring, pow_mul]; norm_num
  rw [e27] at h4
  exact h123.trans h4

end GlobalTheory.GLZetaBound
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevCong

variable {D : D7}

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := by
  intro v
  simp only [map_one]
  exact one_mem _

theorem toAf_mem_hatV {k : ℕ} {L : Lt D.host.E k} {x : Fin k → D.host.E} (hx : x ∈ L) :
    toAf (D := D) x ∈ hatV L :=
  AddSubgroup.subset_closure ⟨1, one_mem_intAf, x, hx, rfl⟩

theorem hatV_mono {k : ℕ} {L L' : Lt D.host.E k} (h : L ≤ L') : hatV (D := D) L ≤ hatV L' :=
  AddSubgroup.closure_mono fun _ ⟨a, ha, x, hx, e⟩ => ⟨a, ha, x, h hx, e⟩

theorem toAf_add {k : ℕ} (x y : Fin k → D.host.E) : toAf (D := D) (x + y) = toAf x + toAf y := by
  funext i; simp [toAf, TensorProduct.tmul_add]

theorem toAf_sub {k : ℕ} (x y : Fin k → D.host.E) : toAf (D := D) (x - y) = toAf x - toAf y := by
  funext i; simp [toAf, TensorProduct.tmul_sub]

theorem toAf_zero {k : ℕ} : toAf (D := D) (0 : Fin k → D.host.E) = 0 := by
  funext i; simp [toAf]

theorem toAf_smul {k : ℕ} (c : 𝓞 D.host.E) (x : Fin k → D.host.E) :
    toAf (D := D) (c • x) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • toAf x := by
  funext i
  simp [toAf, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]

theorem smul_mem_hatV {k : ℕ} (c : 𝓞 D.host.E) {L L' : Lt D.host.E k} (h : ∀ x ∈ L, c • x ∈ L')
    {u : Fin k → AfE D} (hu : u ∈ hatV L) :
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • u ∈ hatV L' := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a, ha, c • x, h x hx, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

section
variable {r : ℕ} (m : Matrix (Fin r) (Fin r) (AfE D))

theorem fadd (x y : Fin r → D.host.E) : m *ᵥ toAf (D := D) (x + y) - toAf (x + y) =
    (m *ᵥ toAf x - toAf x) + (m *ᵥ toAf y - toAf y) := by
  rw [toAf_add, Matrix.mulVec_add]; abel

theorem fsmul (c : 𝓞 D.host.E) (x : Fin r → D.host.E) : m *ᵥ toAf (D := D) (c • x) - toAf (c • x) =
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • (m *ᵥ toAf x - toAf x) := by
  rw [toAf_smul, Matrix.mulVec_smul, smul_sub]

theorem sum_one_smul (β : Fin r → Fin r → D.host.E) (i : Fin r) :
    ∑ j, (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) j i • β j = β i := by
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_sub_one (β : Fin r → Fin r → D.host.E) (κ' : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) (i : Fin r) :
    ∑ j, (κ' j i - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) j i) • β j = ∑ j, κ' j i • β j - β i := by
  rw [← sum_one_smul β i, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sub_smul]
end

theorem mem_of_smul {r : ℕ} (Λ : Lt D.host.E r) (𝔪 I : Ideal (𝓞 D.host.E)) (h𝔪I : 𝔪 ≤ I)
    (m : Matrix (Fin r) (Fin r) (AfE D)) (hmov : IsMov m Λ Λ) :
    ∀ t ∈ 𝔪 • Λ, m *ᵥ toAf (D := D) t - toAf t ∈ hatV (I • Λ) := by
  intro t ht
  refine Submodule.smul_induction_on ht ?_ ?_
  · intro p hp y hy
    have h1 : m *ᵥ toAf (D := D) y ∈ hatV Λ := (hmov _).2 ⟨_, toAf_mem_hatV hy, rfl⟩
    rw [fsmul]
    rw [smul_sub]
    refine sub_mem (smul_mem_hatV p (fun x hx => Submodule.smul_mem_smul (h𝔪I hp) hx) h1) ?_
    rw [← toAf_smul]; exact toAf_mem_hatV (Submodule.smul_mem_smul (h𝔪I hp) hy)
  · intro x y hx hy; rw [fadd]; exact add_mem hx hy

theorem mem_of_span {r : ℕ} (Λ : Lt D.host.E r) (β : Fin r → Fin r → D.host.E) (𝔪 I : Ideal (𝓞 D.host.E))
    (hβ : ∀ i, β i ∈ Λ) (h𝔪I : 𝔪 ≤ I) (m : Matrix (Fin r) (Fin r) (AfE D))
    (κ' : Matrix (Fin r) (Fin r) (𝓞 D.host.E))
    (hκ : ∀ i j, κ' i j - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) i j ∈ I)
    (hfr : ∀ i, m *ᵥ toAf (β i) - toAf (∑ j, κ' j i • β j) ∈ hatV (𝔪 • Λ)) :
    ∀ s ∈ Submodule.span (𝓞 D.host.E) (Set.range β), m *ᵥ toAf (D := D) s - toAf s ∈ hatV (I • Λ) := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have e : m *ᵥ toAf (D := D) (β i) - toAf (β i) = (m *ᵥ toAf (β i) - toAf (∑ j, κ' j i • β j)) +
        toAf (∑ j, (κ' j i - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) j i) • β j) := by
      rw [sum_sub_one, toAf_sub, sub_add_sub_cancel]
    rw [e]
    exact add_mem (hatV_mono (Submodule.smul_mono_left h𝔪I) (hfr i))
      (toAf_mem_hatV (sum_mem fun j _ => Submodule.smul_mem_smul (hκ j i) (hβ j)))
  | zero => rw [toAf_zero, Matrix.mulVec_zero, sub_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [fadd]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [fsmul]; exact smul_mem_hatV c (fun y hy => Submodule.smul_mem _ c hy) hx

theorem cong_of_frame : ∀ (D : D7) {r : ℕ} (Λ : Lt D.host.E r) (β : Fin r → Fin r → D.host.E) (𝔪 I : Ideal (𝓞 D.host.E)), (∀ i, β i ∈ Λ) → Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ 𝔪 • Λ → 𝔪 ≤ I → ∀ (m : Matrix (Fin r) (Fin r) (AfE D)) (κ' : Matrix (Fin r) (Fin r) (𝓞 D.host.E)), (∀ i j, κ' i j - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) i j ∈ I) → IsMov m Λ Λ → (∀ i, m *ᵥ toAf (β i) - toAf (∑ j, κ' j i • β j) ∈ hatV (𝔪 • Λ)) → ∀ x ∈ Λ, m *ᵥ toAf x - toAf x ∈ hatV (I • Λ) := by
  intro D r Λ β 𝔪 I hβ hspan h𝔪I m κ' hκ hmov hfr x hx
  obtain ⟨s, hs', t, ht', rfl⟩ := Submodule.mem_sup.1 (hspan hx)
  rw [fadd]
  exact add_mem (mem_of_span Λ β 𝔪 I hβ h𝔪I m κ' hκ hfr s hs') (mem_of_smul Λ 𝔪 I h𝔪I m hmov t ht')

end GlobalTheory.LevCong

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevExt

variable {D : D7}

theorem intAf_mul {a b : Af D.host.F} (ha : a ∈ intAf D.host.F) (hb : b ∈ intAf D.host.F) :
    a * b ∈ intAf D.host.F := by
  intro v
  rw [map_mul]
  exact mul_mem (ha v) (hb v)

theorem smul_mem_hatV {k : ℕ} (L : Lt D.host.E k) {a : Af D.host.F} (ha : a ∈ intAf D.host.F) :
    ∀ w ∈ hatV L, a • w ∈ hatV L := by
  intro w hw
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨a * a', intAf_mul ha ha', x, hx, ?_⟩
    funext i
    simp [TensorProduct.smul_tmul', smul_eq_mul]
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

theorem mulVec_sub_mem_hatV : ∀ (D : D7) {k : ℕ} (L L' : Lt D.host.E k) (m : Matrix (Fin k) (Fin k) (AfE D)),
    (∀ x ∈ L, m *ᵥ toAf x - toAf x ∈ hatV L') → ∀ u ∈ hatV L, m *ᵥ u - u ∈ hatV L' := by
  intro D k L L' m h u hu
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    have hy : (fun i => a ⊗ₜ[D.host.F] x i) = a • toAf (D := D) x := by
      funext i
      simp [toAf, TensorProduct.smul_tmul', smul_eq_mul]
    rw [hy, Matrix.mulVec_smul, ← smul_sub]
    exact smul_mem_hatV L' ha _ (h x hx)
  | zero => simp
  | add y z _ _ hy hz =>
    have : m *ᵥ (y + z) - (y + z) = (m *ᵥ y - y) + (m *ᵥ z - z) := by
      rw [Matrix.mulVec_add]; abel
    rw [this]; exact add_mem hy hz
  | neg y _ hy =>
    have : m *ᵥ (-y) - (-y) = -(m *ᵥ y - y) := by
      rw [Matrix.mulVec_neg]; abel
    rw [this]; exact neg_mem hy

end GlobalTheory.LevExt

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevkSmul

theorem smul_mem_hatV : ∀ (D : D7) {k : ℕ} (L L' : Lt D.host.E k) (c : D.host.E), (∀ x ∈ L, c • x ∈ L') → ∀ u ∈ hatV L, ((1 : Af D.host.F) ⊗ₜ[D.host.F] c) • u ∈ hatV L' := by
  intro D k L L' c hc u hu
  unfold hatV Formalism.MainNotions.StandardLattice.latHat at hu ⊢
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨a, ha, c • x, hc x hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

end GlobalTheory.LevkSmul
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

variable {D : D7}

def thPDatum (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (e : AE D) : WO S T → ℂ :=
  fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) then
    omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
      omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x))
    else 0

def indL {S T : HSp D} (L : AddSubgroup (WO S T)) : WO S T → ℂ := fun x => if x ∈ L then 1 else 0

def partAt {S T : HSp D} (a : AE D) (w : WO S T) : WO S T := w.map fun z => a * z

abbrev LvCls {S T : HSp D} (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X) : Type :=
  tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ) ⧸
    (tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪 * Lv.𝔪) • C.X.Λ)).addSubgroupOf _

end GlobalTheory.LiftLevel

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicRestrict

theorem ext_restrict {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (Ψ : GA D V → c.W)
    (hΨ : ∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h,
      Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h)) (h : GA D V) :
    c.ext (fun u => Ψ (GlobalTheory.AdelicScalar.finLift V u)) h = Ψ h := by
  set h₀ := GlobalTheory.AdelicScalar.finLift V ((finHom V).rangeRestrict h) with eh₀
  have m₀ : h₀ ∈ GfC V := GlobalTheory.AdelicScalar.finLift_mem V _
  have s₀ : finHom V h₀ = finHom V h :=
    congrArg Subtype.val (GlobalTheory.AdelicScalar.finLift_spec V ((finHom V).rangeRestrict h))
  set k := h₀⁻¹ * h with ek
  have hk1 : finHom V k = 1 := by rw [ek, map_mul, map_inv, s₀, inv_mul_cancel]
  have hkE : Lev.finE V k = 1 := by
    unfold Lev.finE
    rw [MonoidHom.comp_apply, hk1, map_one]
  have hkL : Lev.finE V k ∈ lev D.sp.cm V.gram β L := by rw [hkE]; exact Subgroup.one_mem _
  have hχ : Lev.levChi V β L k = 1 := by
    unfold Lev.levChi
    rw [hkE]
    have := map_one (levChar D.sp.cm V.gram β L)
    have e : levFn β L 1 = (levChar D.sp.cm V.gram β L 1 : ℂˣ) := rfl
    rw [e, this]
    rfl
  have hlaw := hΨ 1 (Subgroup.one_mem _) k hkL h₀
  have eh : 1 * h₀ * k = h := by rw [ek, one_mul, mul_inv_cancel_left]
  rw [eh, hχ, one_smul] at hlaw
  change c.ρ h⁻¹ (Ψ (GlobalTheory.AdelicScalar.finLift V ((finHom V).rangeRestrict h))) = Ψ h
  rw [← eh₀, hlaw]
  have hρ : c.ρ h⁻¹ = c.ρ k⁻¹ := by
    rw [← eh, one_mul, _root_.mul_inv_rev, map_mul, hc.1 _ (inv_mem m₀), mul_one]
  rw [hρ]

end GlobalTheory.AdelicRestrict

end
end
