module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import GroundTheory.LocalFields.HerbrandFunction
public import GroundTheory.LocalFields.SeparableClosure
public import Mathlib.FieldTheory.Galois.Abelian
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle451
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle247
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle271
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle323
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle453
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle720
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle248
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle450
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle079
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle238
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiQuotientInvariantsLiftRationally
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
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem Lam_main : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (y : ℕ → Fl l), 1 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) ∧ ‖abelian₂ h j y - lam h j (y 0)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r ∧ ‖abelian₂ h j y‖ ≤ gam l h j r ∧ ∀ N : ℕ, abelian₂ h j (fun k => y k ^ l ^ (h * N)) = (l : ℂ_[l]) ^ N * abelian₂ h j y := by
  intro l _ h j r y hh hr hy
  have hl : ‖(l : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hl0 : 0 ≤ ‖(l : ℂ_[l])‖ := norm_nonneg _
  have hlam : ∀ k, ‖lam h j (y k)‖ ≤ gam l h j r := fun k =>
    (GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j r (y k) hh hr (hy k)).2.1
  have hterm : ∀ k : ℕ, ‖(l : ℂ_[l]) ^ k * lam h j (y k)‖ ≤ ‖(l : ℂ_[l])‖ ^ k * gam l h j r := by
    intro k
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hlam k) (pow_nonneg hl0 k)
  have hsum : Summable (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hl0 hl).mul_right _) hterm
  have hHas : HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) := hsum.hasSum
  have hg0 : 0 ≤ gam l h j r := le_trans (norm_nonneg _) (hlam 0)
  refine ⟨hHas, ?_, ?_, ?_⟩
  · have := GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le ℂ_[l] ℕ (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) {0}
      (‖(l : ℂ_[l])‖ * gam l h j r) (mul_nonneg hl0 hg0) hHas (by
        intro k hk
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by simpa using hk)
        refine le_trans (hterm k) (mul_le_mul_of_nonneg_right ?_ hg0)
        simpa using pow_le_pow_of_le_one hl0 hl.le hk1)
    simpa using this
  · have := GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le ℂ_[l] ℕ (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) ∅
      (gam l h j r) hg0 hHas (by
        intro k _
        refine le_trans (hterm k) ?_
        calc ‖(l : ℂ_[l])‖ ^ k * gam l h j r ≤ 1 * gam l h j r :=
              mul_le_mul_of_nonneg_right (pow_le_one₀ hl0 hl.le) hg0
          _ = gam l h j r := one_mul _)
    simpa using this
  · have hsh := GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l

    have key : ∀ (N : ℕ) (x : Fl l), ‖sh x‖ ≤ r → lam h j (x ^ l ^ (h * N)) = (l : ℂ_[l]) ^ N * lam h j x := by
      intro N
      induction N with
      | zero => intro x _; simp
      | succ N ih =>
        intro x hx
        have hx' : ‖sh (x ^ l ^ (h * N))‖ ≤ r := by
          rw [hsh.2.2.2.1, norm_pow]
          have h1 : ‖sh x‖ ≤ 1 := hsh.2.2.2.2.1 x
          have hpos : 1 ≤ l ^ (h * N) := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
          exact le_trans (pow_le_of_le_one (norm_nonneg _) h1 (by omega)) hx
        have e : x ^ l ^ (h * (N + 1)) = (x ^ l ^ (h * N)) ^ l ^ h := by
          rw [← pow_mul, ← pow_add, Nat.mul_succ]
        rw [e, (GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j r _ hh hr hx').2.2.1, ih x hx, pow_succ]
        ring
    intro N
    unfold abelian₂
    rw [← tsum_mul_left]
    congr 1
    funext k
    rw [key N (y k) (hy k)]
    ring

end GlobalTheory.PSer
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.pow_mem_upperRamificationGroup_abelian_nat' : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e n : ℕ), OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M (n : ℝ), σ ^ p ∈ upperRamificationGroup F ↥M ((min (2 * n) (n + e) : ℕ) : ℝ) := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_abelian_nat | exact GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_abelian_nat | (intros; apply GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_abelian_nat <;> assumption)
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.continuousOn_gaussNormAcrisRadius_Ico : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), ContinuousOn (fun ρ => gC l ρ x) (Set.Ico (l : ℝ)⁻¹ 1) := by
  first | exact @GlobalTheory.PMon.Gauss.continuousOn_gC_target | exact GlobalTheory.PMon.Gauss.continuousOn_gC_target | (intros; apply GlobalTheory.PMon.Gauss.continuousOn_gC_target <;> assumption)
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.teichmuller_pow_eq_of_frobenius_ratio : ∀ (l : ℕ) [Fact l.Prime] (w' : Formalism.Per.Acris l) (ζ : Formalism.Per.Fl l), w' ≠ 0 → φc l (tc l ζ * w') * w' = tc l ζ * w' * φc l w' → ζ ^ l = ζ := by
  first | exact @GlobalTheory.PMon.Gauss.teich_eq_of_phi_ratio | exact GlobalTheory.PMon.Gauss.teich_eq_of_phi_ratio | (intros; apply GlobalTheory.PMon.Gauss.teich_eq_of_phi_ratio <;> assumption)
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.equal_gaussNorm_teichmuller_cancel : ∀ (l : ℕ) [Fact l.Prime] (w w' : Formalism.Per.Acris l), w' ≠ 0 → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → ∃ (ζ : Formalism.Per.Fl l) (o : ℕ) (ρ₀ : ℝ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧ (l : ℝ)⁻¹ < ρ₀ ∧ ρ₀ < 1 ∧ gC l ρ₀ (w - tc l ζ * w') < gC l ρ₀ w' := by
  first | exact @GlobalTheory.GaussCancel.equal_gauss_cancel | exact GlobalTheory.GaussCancel.equal_gauss_cancel | (intros; apply GlobalTheory.GaussCancel.equal_gauss_cancel <;> assumption)
end

section

noncomputable section
namespace GlobalTheory.TopSteps.ExtPair
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps
open scoped LaurentSeries PowerSeries

variable {k : Type} [Field k]

theorem exists_proj {m m' : ℕ} (hm : m' = m + 1) (a : (Fin m → k) →ₗ[k] (Fin m' → k)) (e : Fin m' → k)
    (ha : Function.Injective a) (he : e ∉ LinearMap.range a) :
    ∃ p : (Fin m' → k) →ₗ[k] (Fin 1 → k), Function.Exact a p ∧ p e = (fun _ => 1) ∧ Function.Surjective p := by
  obtain ⟨f, hf, hfe⟩ := LinearMap.exists_extend_of_notMem (0 : LinearMap.range a →ₗ[k] k) he 1
  have hfs : Function.Surjective f := fun c => ⟨c • e, by simp [hfe]⟩
  have hle : LinearMap.range a ≤ LinearMap.ker f := fun x hx => by
    simpa using LinearMap.congr_fun hf ⟨x, hx⟩
  have h1 := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 hfs] at h1
  have h2 := LinearMap.finrank_range_of_inj ha
  simp only [finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1 h2
  have heq : LinearMap.range a = LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  refine ⟨LinearMap.pi fun _ => f, fun x => ?_, funext fun _ => hfe, fun y => ?_⟩
  · change _ ↔ x ∈ LinearMap.range a
    rw [heq, LinearMap.mem_ker]
    constructor
    · intro h; exact congrFun h 0
    · intro h; exact funext fun _ => h
  · obtain ⟨x, hx⟩ := hfs (y 0)
    exact ⟨x, funext fun j => by rw [Subsingleton.elim j 0]; exact hx⟩

theorem mem_sh_comap {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (N : Submodule k⟦X⟧ (Vc k b)) (s : ℤ) (x : Vc k a) :
    x ∈ sh s (N.comap (φ.restrictScalars k⟦X⟧)) ↔ φ x ∈ sh s N := by
  rw [mem_sh_iff_smul_mem, mem_sh_iff_smul_mem, ← map_smul]; rfl

theorem aeval_nab_mem {a : ℕ} (g : Vc k a →ₗ[k] Vc k a) (N : Submodule k⟦X⟧ (Vc k a)) (hN : CondC g N)
    (f : Polynomial k) (x : Vc k a) (hx : x ∈ N) : Polynomial.aeval (nab g) f x ∈ N := by
  induction f using Polynomial.induction_on generalizing x with
  | C c =>
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact N.smul_of_tower_mem c hx
  | add p q hp hq =>
    simp only [map_add (f := _), LinearMap.add_apply]
    exact N.add_mem (hp x hx) (hq x hx)
  | monomial m c ih =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    exact ih _ ((condC_iff_nab_mem g N).1 hN x hx)

theorem aeval_nab_fixed {a : ℕ} (g : Vc k a →ₗ[k] Vc k a) (f : Polynomial k) (u : Vc k a) (hu : g u = u) :
    Polynomial.aeval (nab g) f u = f.eval 0 • u := by
  apply Module.End.aeval_apply_of_mem_apply_eq_smul
  rw [nab_apply_eq, hu, sub_self, smul_zero, zero_smul]

theorem exists_model_repr_inZZ : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l →
    ∀ (A : Ob k G) (z : G → Fin A.m → k), z ∈ M.twistedModelAdmissibleCocycles A →
      ∃ (N : Lats k n A.m) (b g : ZMod n → Vc k A.m), M.Model A N ∧ Repr F A z b g ∧ InZZ (F.D A) Dt N b g := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 A z hz
  obtain ⟨E, NE, ⟨hm, a, e, ha, hai, he, hez⟩, hNE⟩ := hz
  obtain ⟨p, hex, hpe, hps⟩ := exists_proj hm a e hai he
  have hpa : ∀ y, p (a y) = 0 := hex.apply_apply_eq_zero
  have hp : IsHom E (chr 1) p := by
    intro σ x
    obtain ⟨y, hy⟩ := (hex (x - p x 0 • e)).1 (by
      rw [map_sub, map_smul, hpe]; funext j; rw [Subsingleton.elim j 0]; simp)
    have hx : x = a y + p x 0 • e := by rw [hy]; abel
    have h : p (E.ρ σ x) = p x := by
      conv_lhs => rw [hx]
      conv_rhs => rw [hx]
      rw [map_add (f := _), map_smul, ← ha, hez]
      simp only [map_add (f := _), map_smul, hpa, add_zero]
    rw [h]
    change _ = (((1 : G →* kˣ) σ : kˣ) : k) • p x
    simp
  obtain ⟨oE, -, hAB, hC⟩ := GlobalTheory.T.obj_and_abc_of_model F M E NE hNE
  have oA := F.obj_sub A E a ha hai oE
  have o1 := F.obj_one
  have hq : M.Model (chr 1) (F.push E (chr 1) p NE) :=
    GlobalTheory.Models.ModTh.model_push_of_surjective F M E (chr 1) p NE hp hps hNE
  have hq' : ∀ χ : G →* kˣ, χ = 1 → M.Model (chr χ) (F.push E (chr 1) p NE) := by
    rintro _ rfl; exact hq
  have hpush : ∀ i, F.push E (chr 1) p NE i = Submodule.span k⟦X⟧ {F.unit i} := fun i => by
    rw [← M.χ_zero i]
    exact congrFun (GlobalTheory.T.twistedPhiGammaModel_character_eq_standard F M h1 h2 h3 0 le_rfl (by exact_mod_cast Dt.one_le_letterBlockLength) _
      (hq' _ (by simp))) i
  have hε : ∀ i, ∃ ε ∈ NE i, F.map E (chr 1) p i ε = F.unit i := fun i => by
    have : F.unit i ∈ F.push E (chr 1) p NE i := by
      rw [hpush]; exact Submodule.mem_span_singleton_self _
    exact this
  choose ε hεN hεp using hε
  have hD := GlobalTheory.Models.DFun.map_exact_middle F A E (chr 1) a p oE ha hp hai hps hex
  have hinj := F.map_inj A E a oA oE ha hai
  have aφ := F.map_φ A E a oA oE ha
  have aγ := F.map_γ A E a oA oE ha
  have pφ := F.map_φ E (chr 1) p oE o1 hp
  have pγ := F.map_γ E (chr 1) p oE o1 hp
  have hb : ∀ i, ∃ b, F.map A E a i b = (F.D E).φ i (ε (i - 1)) - ε i := fun i =>
    (hD i _).1 (by rw [map_sub, pφ, hεp, hεp, F.unit_φ, sub_self])
  have hg : ∀ i, ∃ g, F.map A E a i g = (F.D E).γ i (ε i) - ε i := fun i =>
    (hD i _).1 (by rw [map_sub, pγ, hεp, F.unit_γ, sub_self])
  choose b hb using hb
  choose g hg using hg
  refine ⟨F.pre A E a NE, b, g, GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A E a NE ha hai hNE,
    ⟨E, a, p, e, ε, oE, ha, hp, hai, hex, hpe, hez, fun i => ⟨hεp i, hb i, hg i⟩⟩, fun i => ⟨?_, ?_, ?_, ?_⟩⟩
  · apply hinj i
    rw [map_sub, map_sub, aφ, aγ, hb, hg, hg, map_sub, map_sub, (F.D E).comm]
    abel
  · refine (mem_sh_comap _ _ _ _).2 ?_
    rw [hg]; exact hC i _ (hεN i)
  · intro _
    refine (mem_sh_comap _ _ _ _).2 ?_
    rw [hb]
    have hw : 1 ≤ Dt.w i := (Dt.range i (Dt.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2
      ⟨le_rfl, by have := Dt.one_le_letterBlockLength; omega⟩)))).1
    refine Submodule.sub_mem _ ((hAB i).1 (Submodule.subset_span ⟨_, hεN _, rfl⟩)) ?_
    apply sh_le_sh_of_le (a := 0) (by omega)
    rw [sh_zero_eq]; exact hεN i
  · intro hi
    constructor
    · have hdec : ∀ y ∈ pull ((F.D E).φ i) (NE (i - 1)), ∃ m ∈ pull ((F.D A).φ i) (F.pre A E a NE (i - 1)),
          ∃ c : k⸨X⸩, y = F.map A E a i m + c • (F.D E).φ i (ε (i - 1)) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨x, hx, rfl⟩ := hy
          have h4 : F.map E (chr 1) p (i - 1) x ∈ F.push E (chr 1) p NE (i - 1) := ⟨x, hx, rfl⟩
          rw [hpush, Submodule.mem_span_singleton] at h4
          obtain ⟨c, hc⟩ := h4
          obtain ⟨m, hm⟩ := (hD (i - 1) (x - c • ε (i - 1))).1 (by
            rw [map_sub, LinearMap.map_smul_of_tower, hεp, hc, sub_self])
          have hmN : m ∈ F.pre A E a NE (i - 1) := by
            change F.map A E a (i - 1) m ∈ NE (i - 1)
            rw [hm]; exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ (hεN _))
          refine ⟨(F.D A).φ i m, Submodule.subset_span ⟨m, hmN, rfl⟩, R.φ (algebraMap k⟦X⟧ k⸨X⸩ c), ?_⟩
          rw [aφ, hm, ← (F.D E).φ_semi i, algebraMap_smul, ← map_add (f := _), sub_add_cancel]
        | zero => exact ⟨0, Submodule.zero_mem _, 0, by simp⟩
        | add y y' _ _ hy hy' =>
          obtain ⟨m, hm, c, rfl⟩ := hy
          obtain ⟨m', hm', c', rfl⟩ := hy'
          exact ⟨m + m', Submodule.add_mem _ hm hm', c + c', by rw [map_add (f := _), add_smul]; abel⟩
        | smul d y _ hy =>
          obtain ⟨m, hm, c, rfl⟩ := hy
          refine ⟨d • m, Submodule.smul_mem _ _ hm, d • c, ?_⟩
          rw [smul_add, LinearMap.map_smul_of_tower, smul_assoc]
      obtain ⟨m, hm, c, hc⟩ := hdec _ ((hAB i).2 (mem_sh_iff_exists.2 ⟨_, hεN i, rfl⟩))
      have h5 := congrArg (F.map E (chr 1) p i) hc
      rw [map_smul, map_add (f := _), map_smul, pφ, hεp, hεp, F.unit_φ, (hD i).apply_apply_eq_zero, zero_add] at h5
      have h6 : vv k ^ Dt.wst i = c := smul_left_injective _ (F.unit_ne i) h5
      rw [mem_sh_iff_smul_mem, neg_neg]
      have h7 : vv k ^ Dt.wst i • b i = -m := by
        apply hinj i
        rw [map_smul, hb, smul_sub, hc, h6, map_neg]; abel
      rw [h7]; exact Submodule.neg_mem _ hm
    · obtain ⟨f, hf, hfN⟩ := GlobalTheory.Models.EPolyModel.model_ePoly F M h1 h3 E NE hNE i hi
      obtain ⟨x, hx⟩ := (hD i (ε i - (f.eval 0)⁻¹ • Polynomial.aeval (nab ((F.D E).γ i)) f (ε i))).1 (by
        rw [map_sub, LinearMap.map_smul_of_tower,
          EPolyModel.map_aeval_nab (F.map E (chr 1) p i) _ _ (pγ i), hεp, aeval_nab_fixed _ _ _ (F.unit_γ i),
          smul_smul, inv_mul_cancel₀ hf, one_smul, sub_self])
      refine ⟨x, ?_, (mem_sh_comap _ _ _ _).2 ?_⟩
      · change F.map A E a i x ∈ NE i
        rw [hx]
        exact Submodule.sub_mem _ (hεN i)
          (Submodule.smul_of_tower_mem _ _ (aeval_nab_mem _ _ (hC i) f _ (hεN i)))
      · have h4 := hfN _ (hεN i)
        set y := Polynomial.aeval (nab ((F.D E).γ i)) f (ε i)
        have h5 : (F.D E).γ i y - y ∈ sh (Dt.wst i + 2) (NE i) := by
          rw [show Dt.wst i + 2 = 1 + (Dt.wst i + 1) by ring, ← sh_sh_eq, mem_sh_iff_smul_mem, zpow_neg_one]
          exact h4
        have h6 : F.map A E a i (g i - ((F.D A).γ i x - x)) = (f.eval 0)⁻¹ • ((F.D E).γ i y - y) := by
          rw [map_sub, map_sub, aγ, hg, hx, map_sub, map_smul, smul_sub]; abel
        rw [h6]
        exact Submodule.smul_of_tower_mem _ _ h5

end GlobalTheory.TopSteps.ExtPair
end
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.GGNorm

variable {g : ℕ} [Fact g.Prime]

theorem wh_formula (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (χ : Gn g n → ℂ) :
    wh ψ χ = ((Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card : ℂ)⁻¹ *
      ∑ u : Gn g n, (if IsUniUp (u : Mt g n) then
        (ψ (∑ i ∈ Finset.range (n - 1), entN (u : Mt g n) i (i + 1)))⁻¹ else 0) * χ u := by
  unfold wh tr eU eDat
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, Finsupp.single_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc]
  congr 2
  rw [Finset.sum_ite_eq']
  simp

theorem gg_term_inv (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (u : Gn g n) :
    (if IsUniUp ((u⁻¹ : Gn g n) : Mt g n) then
        ψ (∑ i ∈ Finset.range (n - 1), entN ((u⁻¹ : Gn g n) : Mt g n) i (i + 1)) else 0) =
      if IsUniUp (u : Mt g n) then (ψ (∑ i ∈ Finset.range (n - 1), entN (u : Mt g n) i (i + 1)))⁻¹ else 0 := by
  by_cases hu : IsUniUp (u : Mt g n)
  · have hi := GlobalTheory.BadCount.Inh.isUniUp_inv u hu
    rw [if_pos hi, if_pos hu]
    have h := GlobalTheory.BadCount.Inh.sd_mul hi hu
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, GlobalTheory.BadCount.Inh.sd_one] at h
    have e : (∑ i ∈ Finset.range (n - 1), entN ((u⁻¹ : Gn g n) : Mt g n) i (i + 1)) =
        -(∑ i ∈ Finset.range (n - 1), entN (u : Mt g n) i (i + 1)) :=
      eq_neg_of_add_eq_zero_left h.symm
    rw [e, AddChar.map_neg_eq_inv]
  · have hi : ¬ IsUniUp ((u⁻¹ : Gn g n) : Mt g n) := fun h =>
      hu (by simpa using GlobalTheory.BadCount.Inh.isUniUp_inv u⁻¹ h)
    rw [if_neg hi, if_neg hu]

theorem ip_gg (ψ : AddChar (ZMod g) ℂ) (n : ℕ) (χ : Gn g n → ℂ) (hχ : IsClass χ) :
    ip χ (gg ψ n) = wh ψ χ := by
  set c : ℂ := ((Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card : ℂ)⁻¹ with hc
  set F : Gn g n → ℂ := fun z => if IsUniUp (z : Mt g n) then
    ψ (∑ i ∈ Finset.range (n - 1), entN (z : Mt g n) i (i + 1)) else 0 with hF
  have hgg : ∀ x, gg ψ n x = c * ∑ y : Gn g n, F (y⁻¹ * x * y) := fun x => rfl
  have hinner : ∀ y : Gn g n, ∑ x : Gn g n, χ x * F (y⁻¹ * x⁻¹ * y) = ∑ u : Gn g n, χ u * F u⁻¹ := by
    intro y
    let e : Gn g n ≃ Gn g n :=
      ⟨fun x => y⁻¹ * x * y, fun u => y * u * y⁻¹, fun x => by group, fun u => by group⟩
    refine Fintype.sum_equiv e _ _ fun x => ?_
    have h1 : χ (y⁻¹ * x * y) = χ x := by
      have := hχ x y⁻¹
      rwa [inv_inv] at this
    have h2 : y⁻¹ * x⁻¹ * y = (y⁻¹ * x * y)⁻¹ := by group
    change χ x * F (y⁻¹ * x⁻¹ * y) = χ (y⁻¹ * x * y) * F (y⁻¹ * x * y)⁻¹
    rw [h1, h2]
  have hG : (Fintype.card (Gn g n) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have e1 : ∑ x : Gn g n, χ x * gg ψ n x⁻¹ = c * ∑ y : Gn g n, ∑ x : Gn g n, χ x * F (y⁻¹ * x⁻¹ * y) := by
    simp only [hgg, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
  have e2 : wh ψ χ = c * ∑ u : Gn g n, χ u * F u⁻¹ := by
    rw [wh_formula]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_comm]
    congr 1
    exact (gg_term_inv ψ u).symm
  unfold ip
  rw [e1, e2, Finset.sum_congr rfl fun y _ => hinner y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_left_comm, ← mul_assoc, ← mul_assoc, mul_assoc c, inv_mul_cancel₀ hG, mul_one]

theorem wh_gg (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n) :
    wh ψ (gg ψ n) = (g : ℂ) ^ n - (g : ℂ) ^ (n - 1) := by
  have h1 := GlobalTheory.GLm.GGSum.sum_wh_gg g ψ hψ n
  have h2 := GlobalTheory.GLm.GGSum.sum_wh_gg g ψ hψ (n - 1)
  rw [Nat.sub_add_cancel hn] at h2
  rw [Finset.sum_range_succ, h2] at h1
  linear_combination h1

theorem gg_norm : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ n : ℕ, 0 < n →
    wh ψ (gg ψ n) = (g : ℂ) ^ n - (g : ℂ) ^ (n - 1) ∧
      ∀ χ : Gn g n → ℂ, IsClass χ → ip χ (gg ψ n) = wh ψ χ :=
  fun _ _ ψ hψ n hn => ⟨wh_gg ψ hψ n hn, fun χ hχ => ip_gg ψ n χ hχ⟩

end GlobalTheory.GLq.GGNorm
end
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq

theorem list_sum_posNat {ι : Type} (L : List ι) (f : ι → ℂ) (hf : ∀ p ∈ L, ∃ n : ℕ, 0 < n ∧ f p = n) :
    ∃ m : ℕ, (L.map f).sum = m ∧ (L ≠ [] → 0 < m) := by
  induction L with
  | nil => exact ⟨0, by simp, fun h => absurd rfl h⟩
  | cons p L ih =>
    obtain ⟨n, hn, hp⟩ := hf p (List.mem_cons_self ..)
    obtain ⟨m, hm, -⟩ := ih fun q hq => hf q (List.mem_cons_of_mem _ hq)
    refine ⟨n + m, ?_, fun _ => by omega⟩
    simp [List.map_cons, List.sum_cons, hp, hm]

theorem res_cusp_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (d a : ℕ) (χ : Gn g d → ℂ), IsCusp χ → 0 < a → a < d →
    ∀ x y, res a (d - a) χ x y = 0 := by
  intro g _ d a χ hχ ha had x y
  obtain ⟨-, hirr, hc⟩ := hχ
  have hchar : IsChar χ := by
    obtain ⟨V, -, hV⟩ := hirr
    exact ⟨V, hV⟩
  obtain ⟨L, hL, hres⟩ := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g a (d - a) d (by omega)).2 χ hchar
  have hpos : ∀ p ∈ L, ∃ n : ℕ, 0 < n ∧ (fun p : (Gn g a → ℂ) × (Gn g (d - a) → ℂ) => p.1 1 * p.2 1) p = n := by
    intro p hp
    obtain ⟨d₁, hd₁, h₁⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g a) 0 p.1).2.1 (hL p hp).1
    obtain ⟨d₂, hd₂, h₂⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g (d - a)) 0 p.2).2.1 (hL p hp).2
    exact ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, by simp [h₁, h₂]⟩
  obtain ⟨m, hm, hmpos⟩ := list_sum_posNat L _ hpos
  have hL0 : L = [] := by
    by_contra hne
    have h0 : res a (d - a) χ 1 1 = 0 := hc a ha had
    rw [hres, hm] at h0
    have := hmpos hne
    exact absurd (by exact_mod_cast h0 : m = 0) (by omega)
  rw [hres, hL0]
  simp

end GlobalTheory.GLq
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.xiQuotient_invariants_lift_rationally : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm5 D → adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (a e b : ℤ) (j : ℕ) (hle : Gj K j ≤ GK K), s ≤ j → a ≤ e → e ≤ b → IsCrysOn S S.W.GKs T → ∀ p : Qab (AinfSub l) (xiU (D.locA l)) a b →ₗ[ℤ_[l]] Qab (AinfSub l) (xiU (D.locA l)) a e, (∀ x, p (Submodule.Quotient.mk x) = Submodule.Quotient.mk x) → letI := zlMod LL T; ∀ z : (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) a e)), (∀ g, (repQ (D.locA l) (Gj K j) ((actTZ LL T).comp (Subgroup.inclusion hle)) a e) g z = z) → ∃ (k : ℕ) (x : (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) a b))), (∀ g, (repQ (D.locA l) (Gj K j) ((actTZ LL T).comp (Subgroup.inclusion hle)) a b) g x = x) ∧ LinearMap.lTensor ↥T.L.T p x = (l : ℤ_[l]) ^ k • z := by
  first | exact @GlobalTheory.InvariantLift.invariants_lift | exact GlobalTheory.InvariantLift.invariants_lift | (intros; apply GlobalTheory.InvariantLift.invariants_lift <;> assumption)
end
