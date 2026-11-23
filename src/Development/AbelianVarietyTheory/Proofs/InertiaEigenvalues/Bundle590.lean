module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle562
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle563
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle564
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDisc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowMulEqThetaWitt
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.bezout_eisenstein_derivative_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (c : ℕ) (a b : Polynomial (Wq l bk.a)), a * bk.Ep + b * Polynomial.derivative bk.Ep = Polynomial.C ((l : Wq l bk.a) ^ c) := by
  first | exact @GlobalTheory.BSP.bezout_Ep_derivative | exact GlobalTheory.BSP.bezout_Ep_derivative | (intros; apply GlobalTheory.BSP.bezout_Ep_derivative <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinPrismCoproduct_hom_eq_of_agree : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (d p : B.A) (En : Env bk B d p) (C : Type) [CommRing C] (φ : C →+* C) (F F' : En.Q.A →+* C), (∀ c : C, ((l : ℕ) : C) * c = 0 → c = 0) → (∀ a, F (En.Q.D.φ a) = φ (F a)) → (∀ a, F' (En.Q.D.φ a) = φ (F' a)) → (∀ b, F (En.inl.f b) = F' (En.inl.f b)) → F (BK.hf En.inr X) = F' (BK.hf En.inr X) → F (En.inl.f d) ∈ nonZeroDivisors C → IsHausdorff ((Ideal.span {((l : ℕ) : B.A)} ⊔ B.I).map (F.comp En.inl.f)) C → F = F' := by
  first | exact @GlobalTheory.BSP.envExt_agree | exact GlobalTheory.BSP.envExt_agree | (intros; apply GlobalTheory.BSP.envExt_agree <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_breuilKisin_frobenius_period : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ τ : Ainf l, bk.IsPer τ := by
  first | exact @GlobalTheory.BSP.exists_isPer | exact GlobalTheory.BSP.exists_isPer | (intros; apply GlobalTheory.BSP.exists_isPer <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.ideal_span_prime_variable_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (ι : Type) (b : ι → Ainf l) (i₀ : ι), b i₀ = 1 ∧ (∀ x : Ainf l, ∃ a : ι →₀ bk.S, x - a.sum (fun i y => bk.ev y * b i) ∈ (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev) ∧ ∀ a : ι →₀ bk.S, a.sum (fun i y => bk.ev y * b i) ∈ (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev → ∀ i, a i ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} := by
  first | exact @GlobalTheory.BSP.BK.exists_residue_basis | exact GlobalTheory.BSP.BK.exists_residue_basis | (intros; apply GlobalTheory.BSP.BK.exists_residue_basis <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.stratifiedPhiModule_of_coproduct_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (d a b : ℕ) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S) → ∀ ε : Matrix (Fin d) (Fin d) En.Q.A, BK.hf En.inr bk.E ^ a • (A.map (BK.hf En.inl) * ε.map En.Q.D.φ) = BK.hf En.inl bk.E ^ a • (ε * A.map (BK.hf En.inr)) → (∀ (B : Obj l ↥(OL K)), (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧ ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl → k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f) → ∃ S : Strat bk d, S.a = a ∧ S.A = A ∧ ∀ (B : Obj l ↥(OL K)) (k : Hom En.Q B), S.ε (k.comp En.inl) (k.comp En.inr) = ε.map k.f := by
  first | exact @GlobalTheory.BSP.strat_of_envCocycle | exact GlobalTheory.BSP.strat_of_envCocycle | (intros; apply GlobalTheory.BSP.strat_of_envCocycle <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.wittVector_map_breuilKisin_ev_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [CharP O l] [PerfectRing O l] (ψ ψ' : OCb l →+* O), ψ bk.flat ≠ 0 → IsAdicComplete (Ideal.span {ψ bk.flat}) O → (∀ s : bk.S, ψ ((bk.ev s).coeff 0) = ψ' ((bk.ev s).coeff 0)) → ∀ s : bk.S, WittVector.map ψ (bk.ev s) = WittVector.map ψ' (bk.ev s) := by
  first | exact @GlobalTheory.BSP.wmap_ev_eq | exact GlobalTheory.BSP.wmap_ev_eq | (intros; apply GlobalTheory.BSP.wmap_ev_eq <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem envelopes_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X))
    (En₂ : Env bk En.Q (BK.hf En.inl bk.E) (BK.hf En.inl X)),
    Nonempty (TopBasis (BK.hf En.inl) bk.J (Digits l)) ∧
      ∃ ι : Type, Nonempty (TopBasis (BK.hf (En₂.inl.comp En.inl)) bk.J ι) := by
  intro l _ K bk En En₂
  have h1 : bk.J.map (BK.hf En.inl) =
      Ideal.span {(BK.hf En.inl) (l : bk.S)} ⊔ Ideal.span {(BK.hf En.inl) bk.E} := by
    simp only [BK.J, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have h2 : (BK.hf En.inl) (l : bk.S) = (l : En.Q.A) := map_natCast (BK.hf En.inl) l
  have h3 : En.Q.I = Ideal.span {(BK.hf En.inl) bk.E} := En.I_eq
  have hI : Ideal.span {(l : En.Q.A)} ⊔ En.Q.I = bk.J.map (BK.hf En.inl) :=
    (h1.trans (congrArg₂ (· ⊔ ·) (congrArg (fun x => Ideal.span {x}) h2) h3.symm)).symm
  have T₁ : TopBasis (BK.hf En.inl) bk.J (Digits l) := En.tb
  have T₂ : TopBasis En₂.inl.f (Ideal.span {(l : En.Q.A)} ⊔ En.Q.I) (Digits l) := En₂.tb
  have key := GlobalTheory.T.adicTopologicalBasis_exists_comp bk.S En.Q.A (BK.hf En.inl) bk.J (Digits l) T₁ En₂.Q.A En₂.inl.f
    (Ideal.span {(l : En.Q.A)} ⊔ En.Q.I) (Digits l) T₂ hI
  exact ⟨⟨T₁⟩, Digits l × Digits l, key.elim fun TC _ => ⟨TC⟩⟩

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.BSP.TopBasis.dvd_iff_dvd_c : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (a : bk.S) (x : A), s a ∣ x ↔ ∀ i, a ∣ TB.c i x := by
  intro l _ K bk A _ s ι TB a x
  haveI hH : IsHausdorff bk.J bk.S := bk.complete.toIsHausdorff
  obtain ⟨h1, -, -, h4, -⟩ := GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB hH
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨TB.c i y, TB.c_mul i a y⟩
  · intro h
    by_cases ha : a = 0
    · subst ha
      refine ⟨0, ?_⟩
      rw [mul_zero]
      exact h1 x fun i => zero_dvd_iff.1 (h i)
    · choose z hz using h
      obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul bk.J (M := bk.S) (Submodule.span bk.S {a})
      have key : ∀ (n : ℕ) (w : bk.S), a * w ∈ bk.J ^ (n + k) → w ∈ bk.J ^ n := by
        intro n w hw
        have hmem : a * w ∈ bk.J ^ (n + k) • (⊤ : Submodule bk.S bk.S) ⊓ Submodule.span bk.S {a} := by
          refine Submodule.mem_inf.2 ⟨?_, ?_⟩
          · rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact hw
          · exact Submodule.mem_span_singleton.2 ⟨w, by rw [smul_eq_mul, mul_comm]⟩
        rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at hmem
        have h2 : bk.J ^ n • (bk.J ^ k • (⊤ : Submodule bk.S bk.S) ⊓ Submodule.span bk.S {a}) ≤
            bk.J ^ n * Ideal.span {a} :=
          Submodule.smul_mono le_rfl inf_le_right
        obtain ⟨v, hv, hva⟩ := Ideal.mem_mul_span_singleton.1 (h2 hmem)
        have hwv : w = v := mul_left_cancel₀ ha (by rw [← hva, mul_comm])
        exact hwv ▸ hv
      have hfin : ∀ n : ℕ, {i | z i ∉ bk.J ^ n}.Finite := fun n =>
        (TB.fin x (n + k)).subset fun i hi hx => hi (key n (z i) (hz i ▸ hx))
      obtain ⟨y, hy⟩ := h4 z hfin
      refine ⟨y, ?_⟩
      have h0 := h1 (x - s a * y) fun i => by
        rw [map_sub, TB.c_mul, hy, hz, sub_self]
      exact sub_eq_zero.1 h0
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.RhoZeroNormBounds

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem ρ₀_pos (bk : BK K) : 0 < bk.ρ₀ := by
  have hl0 : (0 : ℝ≥0) < l := Nat.cast_pos.2 hl.out.pos
  unfold BK.ρ₀
  exact NNReal.rpow_pos hl0

theorem ρ₀_pow (bk : BK K) : bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  have hl0 : (0 : ℝ≥0) < l := Nat.cast_pos.2 hl.out.pos
  have he : (bk.Ep.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.2 bk.deg_pos.ne'
  unfold BK.ρ₀
  rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, neg_mul, one_div, inv_mul_cancel₀ he, NNReal.rpow_neg_one]

theorem norm_l_mul (bk : BK K) (y : bk.DA bk.ρ₀) : ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖ := by
  rw [(GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Ainf l) (bk.ev X) bk.ρ₀).2.1 y, div_eq_inv_mul]

theorem norm_iS_le (bk : BK K) (x : bk.S) : ‖bk.iS x‖ ≤ 1 :=
  norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (bk.ev x)

theorem norm_iS_E (bk : BK K) : ‖bk.iS bk.E‖ ≤ (l : ℝ)⁻¹ := by
  haveI := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Ainf l) (bk.ev X) bk.ρ₀).1
  have hE : bk.E = bk.Ep.eval₂ PowerSeries.C PowerSeries.X := (Polynomial.eval₂_C_X_eq_coe).symm
  rw [hE, Polynomial.hom_eval₂, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ]
  have hinv : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hinv fun i hi => ?_
    obtain ⟨d, hd⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
    have e : (bk.iS.comp PowerSeries.C) (bk.Ep.coeff i) * bk.iS PowerSeries.X ^ i =
        (l : bk.DA bk.ρ₀) * bk.iS (PowerSeries.C d * PowerSeries.X ^ i) := by
      rw [hd, RingHom.comp_apply, map_mul, map_mul, map_mul, map_pow, map_natCast, map_natCast, mul_assoc]
    rw [e, norm_l_mul]
    exact mul_le_of_le_one_right hinv (norm_iS_le bk _)
  · rw [bk.monic.coeff_natDegree, map_one, one_mul, ← map_pow]
    change ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev (PowerSeries.X ^ bk.Ep.natDegree))‖ ≤ _
    rw [map_pow]
    refine (norm_toDisc_pow_le _ (ρ₀_pos bk)).trans ?_
    rw [← NNReal.coe_pow, ρ₀_pow, NNReal.coe_inv, NNReal.coe_natCast]

theorem norm_iA_ker (bk : BK K) (a : Ainf l) (ha : Per.θ l a = 0) : ‖bk.iA a‖ ≤ (l : ℝ)⁻¹ := by
  have hmem : a ∈ Ideal.span {bk.ev bk.E} := by rw [bk.span_ev]; exact ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hmem
  rw [map_mul]
  refine (norm_mul_le _ _).trans ?_
  have h1 : ‖bk.iA c‖ ≤ 1 := norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) c
  have h2 : ‖bk.iA (bk.ev bk.E)‖ ≤ (l : ℝ)⁻¹ := norm_iS_E bk
  calc ‖bk.iA c‖ * ‖bk.iA (bk.ev bk.E)‖ ≤ 1 * (l : ℝ)⁻¹ := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem seed_norms : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ‖bk.iS bk.E‖ ≤ (l : ℝ)⁻¹ ∧ (∀ y : bk.DA bk.ρ₀, ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖) ∧ ∀ a : Ainf l, Per.θ l a = 0 → ‖bk.iA a‖ ≤ (l : ℝ)⁻¹ :=
  fun _ _ _ bk => ⟨norm_iS_E bk, norm_l_mul bk, norm_iA_ker bk⟩

end GlobalTheory.BSP.RhoZeroNormBounds
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_gaussNorm_coeff_wittDisc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∃ a : ℕ → (bk.DS ρ →+ Disc l (0 : Wq l bk.a) 1), (∀ n x, a n (toDisc l (X : bk.S) ρ x) = toDisc l (0 : Wq l bk.a) 1 (coeff n x)) ∧ (∀ n y, ‖a n y‖ * (ρ : ℝ) ^ n ≤ ‖y‖) ∧ (∀ y (r : ℝ), 0 ≤ r → (∀ n, ‖a n y‖ * (ρ : ℝ) ^ n ≤ r) → ‖y‖ ≤ r) ∧ ∀ y, Filter.Tendsto (fun n => ‖a n y‖ * (ρ : ℝ) ^ n) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.BSP.DiscSer.exists_coeff_disc | exact GlobalTheory.BSP.DiscSer.exists_coeff_disc | (intros; apply GlobalTheory.BSP.DiscSer.exists_coeff_disc <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_prime_pow_mul_eq_theta_witt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (x : Om l), x ∈ K.1 → x ∈ MaximalUnramifiedExtension l → ∃ (n : ℕ) (w : Wq l bk.a), ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) = ((((l : Om l) ^ n * x : Om l)) : ℂ_[l]) := by
  first | exact @GlobalTheory.UnrWitt.exists_pow_mul_eq_theta | exact GlobalTheory.UnrWitt.exists_pow_mul_eq_theta | (intros; apply GlobalTheory.UnrWitt.exists_pow_mul_eq_theta <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LiftDiv

theorem dvd_mod_E : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (s : bk.S) (n : ℕ) (y : OC l), Per.θ l (bk.ev s) = (l : OC l) ^ n * y → ∃ s' t : bk.S, s = (l : bk.S) ^ n * s' + bk.E * t := by
  intro l _ K bk s n y h
  set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ s) with hr
  have hθ : Per.θ l (bk.ev s) = intToOC K r := bk.θ_ev r s (by rw [hr, RingEquiv.apply_symm_apply])
  have hC : ((((r : ↥K.1) : Om l)) : ℂ_[l]) = (l : ℂ_[l]) ^ n * ((y : OC l) : ℂ_[l]) := by
    rw [← coe_intToOC, ← hθ, h]
    push_cast
    rfl
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hnorm : ‖((r : ↥K.1) : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ n := by
    rw [← PadicComplex.norm_extends, hC, norm_mul, norm_pow, GlobalTheory.UnrWitt.norm_l_C]
    exact mul_le_of_le_one_right (by positivity) (GlobalTheory.UnrWitt.norm_OC_le y)
  set q : ↥K.1 := (r : ↥K.1) / (l : ↥K.1) ^ n with hq
  have hqO : ((q : ↥K.1) : Om l) = ((r : ↥K.1) : Om l) / (l : Om l) ^ n := by
    rw [hq]; push_cast; rfl
  have hq1 : ‖((q : ↥K.1) : Om l)‖ ≤ 1 := by
    rw [hqO, norm_div, norm_pow, GlobalTheory.UnrWitt.norm_l_Om]
    rw [div_le_one (by positivity)]
    exact hnorm
  let r' : ↥(OL K) := ⟨q, GlobalTheory.UnrWitt.mem_OL_of_norm_le K q hq1⟩
  have hrr : r = (l : ↥(OL K)) ^ n * r' := by
    apply Subtype.ext
    apply Subtype.ext
    have : ((((l : ↥(OL K)) ^ n * r' : ↥(OL K)) : ↥K.1) : Om l) = (l : Om l) ^ n * ((q : ↥K.1) : Om l) := by
      push_cast; rfl
    rw [this, hqO, mul_div_cancel₀ _ (pow_ne_zero _ hl0)]
  obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (bk.str r')
  have hmk : Ideal.Quotient.mk (Ideal.span {bk.E}) (s - (l : bk.S) ^ n * s') = 0 := by
    have e1 : Ideal.Quotient.mk (Ideal.span {bk.E}) s = bk.str r := by
      rw [hr, RingEquiv.apply_symm_apply]
    rw [map_sub, map_mul, map_pow, map_natCast, e1, hs', hrr, map_mul, map_pow, map_natCast, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)
  exact ⟨s', t, by rw [mul_comm bk.E t, ht]; ring⟩

end GlobalTheory.LiftDiv
end
end
