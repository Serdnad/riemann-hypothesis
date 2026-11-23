module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinInfGaloisActsThroughDescentDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValueMemFiltrationZeroTame
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle530
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle748
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle749
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_bcris_comparison_kisinLattice : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T), ∃ jB, IsCrisCmp I jB := by
  first | exact @GlobalTheory.BKGal.exists_isCrisCmp | exact GlobalTheory.BKGal.exists_isCrisCmp | (intros; apply GlobalTheory.BKGal.exists_isCrisCmp <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.kisinInfGalois_acts_through_descentDatum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (Δ : Descent P), IsCrisCmp I jB → IsGalDesc (sQ l) I Δ → ∀ (g : Gl l) (γ : TameGal K l e a), Covers K t ϖ (sQ l g) γ → ∀ σ σ' : P.MMl, σ'.1 = Δ.act γ σ.1 → actB (sQ l) T g (jB (toBcris t ϖ P σ)) = jB (toBcris t ϖ P σ') := by
  first | exact @GlobalTheory.TameAct.main | exact GlobalTheory.TameAct.main | (intros; apply GlobalTheory.TameAct.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.value_mem_filtration_zero_tame : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O), phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ → ∃ b₁, IsCrisVal t ϖ D.toPhiMod R.jB m₀ b₁ ∧ ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g b₁ - b₁ ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.value_mem_filtration_zero | exact GlobalTheory.BKGal.value_mem_filtration_zero | (intros; apply GlobalTheory.BKGal.value_mem_filtration_zero <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem GlobalTheory.BKLim.theta_gal_fixed_of_congr : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (x : Per.BdRp l) (M k : ℕ) (s : bk.S), (l : Per.BdRp l) ^ k * aDp l (bk.ev bk.E) ^ M * x - aDp l (bk.ev s) ∈ Per.FilP l (M + 1) → ∀ g : ↥(GK K), Per.σC (g : GQ l) (Per.θD l x) = Per.θD l x := by
  intro l _ K bk x M k s h g
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  obtain ⟨hfil, -⟩ := GlobalTheory.MemLoc.seed_fil l C (bk.ev bk.E) bk.span_ev
  obtain ⟨-, hker, -, hth, -⟩ := GlobalTheory.MemLoc.thetaD_props l
  haveI : IsDomain (Per.BdRp l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).1
  haveI : IsDomain (Ainf l) := inclW_injective.isDomain (inclW l)
  set ξ := aDp l (bk.ev bk.E) with hξ

  have hξ0 : ξ ≠ 0 := by
    intro h0
    have h2 : aDp l (bk.ev bk.E) ∈ Per.FilP l 2 := by
      rw [hfil, ← hξ, h0]; exact zero_mem _
    have h3 := ((GlobalTheory.AinfEPow.ePow_facts l K bk 2).2.2.1 _).1 h2
    obtain ⟨c, hc⟩ := h3
    have hE := GlobalTheory.AinfEPow.evE_ne_zero bk
    have h4 : bk.ev bk.E * 1 = bk.ev bk.E * (bk.ev bk.E * c) := by rw [mul_one]; nth_rewrite 1 [hc]; ring
    have h5 := mul_left_cancel₀ hE h4
    have h6 := congrArg (Per.θ l) h5
    have h7 : Per.θ l (bk.ev bk.E) = 0 := by
      rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
    rw [map_one, map_mul, h7, zero_mul] at h6
    exact one_ne_zero h6

  have hsM : aDp l (bk.ev s) ∈ Per.FilP l M := by
    have h1 : (l : Per.BdRp l) ^ k * ξ ^ M * x ∈ Per.FilP l M := by
      rw [hfil, Ideal.mem_span_singleton]; exact ⟨(l : Per.BdRp l) ^ k * x, by ring⟩
    have h2 : (l : Per.BdRp l) ^ k * ξ ^ M * x - aDp l (bk.ev s) ∈ Per.FilP l M := by
      rw [hfil] at h ⊢
      rw [Ideal.mem_span_singleton] at h ⊢
      exact (pow_dvd_pow _ (Nat.le_succ M)).trans h
    have := Ideal.sub_mem _ h1 h2
    rwa [sub_sub_cancel] at this
  obtain ⟨s', hs'⟩ := (GlobalTheory.AinfEPow.ePow_facts l K bk M).2.1 s (((GlobalTheory.AinfEPow.ePow_facts l K bk M).2.2.1 _).1 hsM)

  have hdiff : (l : Per.BdRp l) ^ k * x - aDp l (bk.ev s') ∈ Per.FilP l 1 := by
    rw [hfil, pow_one, Ideal.mem_span_singleton]
    have h' := h
    rw [hfil, Ideal.mem_span_singleton, hs', map_mul, map_mul, map_pow, map_pow, ← hξ] at h'
    obtain ⟨y, hy⟩ := h'
    refine ⟨y, ?_⟩
    have e : ξ ^ M * ((l : Per.BdRp l) ^ k * x - aDp l (bk.ev s')) = ξ ^ M * (ξ * y) := by
      rw [← mul_assoc, ← pow_succ, ← hy]; ring
    exact mul_left_cancel₀ (pow_ne_zero M hξ0) e
  rw [← hker, map_sub, sub_eq_zero, map_mul, map_pow, map_natCast, hth,
    bk.θ_ev (bk.str.symm (Ideal.Quotient.mk _ s')) s' (bk.str.apply_symm_apply _).symm] at hdiff
  have hfix : Per.σC (g : GQ l) ((intToOC K (bk.str.symm (Ideal.Quotient.mk _ s')) : OC l) : ℂ_[l]) =
      ((intToOC K (bk.str.symm (Ideal.Quotient.mk _ s')) : OC l) : ℂ_[l]) := by
    rw [coe_intToOC]
    exact (GlobalTheory.RingBasics.σC_coe (g : GQ l) _).trans (congrArg _
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (_ : ↥K.1).2))
  have hl : ((l : ℂ_[l]) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  apply mul_left_cancel₀ hl
  have e2 := congrArg (Per.σC (g : GQ l)) hdiff
  rw [map_mul, map_pow, map_natCast, hfix, ← hdiff] at e2
  exact e2
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.ainf_closed_membership_limit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (mem : (Fin d → Ainf l) → Prop), mem 0 → (∀ y z, mem y → mem z → mem (y + z)) → (∀ (c : bk.S) y, mem y → mem (fun a => bk.ev c * y a)) → (∀ y, mem (fun a => (l : Ainf l) * y a) → mem y) → (∀ y : ℕ → Fin d → Ainf l, (∀ n, mem (y n)) → (∀ n a, (l : Ainf l) ^ n ∣ y (n + 1) a - y n a) → ∀ z : Fin d → Ainf l, (∀ n a, (l : Ainf l) ^ n ∣ z a - y n a) → mem z) → ∀ (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Y' : Matrix (Fin d) (Fin d) (WCb l)), (Y1.map (inclW l)).det ≠ 0 → IsUnit Y' → (∀ c : Fin d → bk.S, mem (Y1 *ᵥ fun a => bk.ev (c a))) → (∀ y, mem y → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun a => inclW l (y a)) = Y' *ᵥ w) → ∃ Y : Matrix (Fin d) (Fin d) (Ainf l), IsUnit (Y.map (inclW l)) ∧ ∀ y, mem y ↔ ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a) := by
  first | exact @GlobalTheory.BSP.saturated_module_free | exact GlobalTheory.BSP.saturated_module_free | (intros; apply GlobalTheory.BSP.saturated_module_free <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem norm_toDisc_natPow_mul_le {l : ℕ} [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (n : ℕ)
    (w : A) : ‖toDisc l u ρ ((l : A) ^ n * w)‖ ≤ ((l : ℝ)⁻¹) ^ n := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hm : algebraMap A (PreDisc l u ρ) ((l : A) ^ n * u ^ 0) * IsLocalization.Away.invSelf (l : A) ^ 0 ∈
      ball l u ρ (((l : ℝ)⁻¹) ^ n) :=
    Submodule.subset_span ⟨n, 0, 0, by rw [pow_zero, pow_zero, mul_one, ← mul_pow, inv_mul_cancel₀ hl0.ne', one_pow], rfl⟩
  have e : algebraMap A (PreDisc l u ρ) ((l : A) ^ n * w) =
      w • (algebraMap A (PreDisc l u ρ) ((l : A) ^ n * u ^ 0) * IsLocalization.Away.invSelf (l : A) ^ 0) := by
    rw [Algebra.smul_def, pow_zero, pow_zero, mul_one, mul_one, ← map_mul, mul_comm]
  show ‖ofPre l u ρ (algebraMap A _ _)‖ ≤ _
  rw [norm_ofPre, e]
  exact gauge_le l u ρ (by positivity) (Submodule.smul_mem _ w hm)

theorem BK.ρ₀_mem_Ioo_zero_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  refine ⟨NNReal.rpow_pos (by exact_mod_cast hl.out.pos), ?_⟩
  apply NNReal.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hl.out.one_lt
  · have : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
    rw [neg_lt_zero]; positivity

theorem seed_module_lAdic_closed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ y : ℕ → Fin d → Ainf l, (∀ n, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (y n)) → (∀ n a, (l : Ainf l) ^ n ∣ y (n + 1) a - y n a) → ∀ z : Fin d → Ainf l, (∀ n a, (l : Ainf l) ^ n ∣ z a - y n a) → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) z := by
  intro l _ K bk τ hτ d ρ hρ s y hy _hcau z hz
  beta_reduce at hy ⊢
  obtain ⟨hρ0, hρ1⟩ := bk.ρ₀_mem_Ioo_zero_one
  have hX : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  set j₀ : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev hX with hj₀
  have hj₀d : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j₀ := isDiscMap_map bk.ev hX
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨cD, hc_to, hc_mul, hc_norm, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j₀ hj₀d
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB (2 * s.N * d)
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hr

  set V : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀) := s.W'.det • adjugate s.W with hV
  have hVW : V * s.W = bk.iA (τ ^ (2 * s.N * d)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have hd : s.W.det * s.W'.det = bk.iA (τ ^ (2 * s.N * d)) := by
      rw [← det_mul, s.W_mul, det_smul, det_one, mul_one, Fintype.card_fin, map_pow]
      ring
    rw [hV, smul_mul, adjugate_mul, smul_smul, mul_comm, hd]

  let Φ : bk.DA bk.ρ₀ → bk.DS bk.ρ₀ := fun w => ∑ i ∈ f.support, toDisc l (X : bk.S) bk.ρ₀ (f i) * cD i w
  have key : ∀ (x : Fin d → bk.DS bk.ρ₀) (a : Fin d),
      (l : bk.DS bk.ρ₀) ^ r * x a = Φ ((V *ᵥ (s.W *ᵥ fun b => j₀ (x b))) a) := by
    intro x a
    have hsm : ∀ (c : bk.DA bk.ρ₀) (v : Fin d → bk.DA bk.ρ₀), (c • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))) *ᵥ v = c • v := by
      intro c v; ext b; simp [mulVec, dotProduct, Matrix.one_apply]
    rw [mulVec_mulVec, hVW, hsm]
    have h1 : ∀ i, cD i ((bk.iA (τ ^ (2 * s.N * d)) • fun b => j₀ (x b)) a) =
        x a * toDisc l (X : bk.S) bk.ρ₀ (TB.c i (τ ^ (2 * s.N * d))) := by
      intro i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm, hc_mul, hc_to]
    simp only [Φ, h1]
    have h2 := congrArg (toDisc l (X : bk.S) bk.ρ₀) hf

    rw [Finsupp.sum, map_sum, map_pow, map_natCast] at h2
    rw [← h2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, map_mul]; ring
  obtain ⟨u, hu⟩ : IsUnit ((l : bk.DS bk.ρ₀) ^ r) := (isUnit_l_disc l (X : bk.S) bk.ρ₀).pow r
  have hsol : ∀ (x : Fin d → bk.DS bk.ρ₀) (a : Fin d),
      x a = ↑u⁻¹ * Φ ((V *ᵥ (s.W *ᵥ fun b => j₀ (x b))) a) := by
    intro x a
    rw [← key, ← hu, Units.inv_mul_cancel_left]

  have hcont : ∀ {F : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀}, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev F → Continuous F := fun hF =>
    AddMonoidHomClass.continuous_of_bound _ 1 fun x => (hF.norm_le x).trans (one_mul _).ge
  have hcDc : ∀ i, Continuous (cD i) := fun i =>
    AddMonoidHomClass.continuous_of_bound _ 1 fun x => (hc_norm i x).trans (one_mul _).ge
  let G : (Fin d → bk.DA bk.ρ₀) → (Fin d → bk.DA bk.ρ₀) := fun v =>
    s.W *ᵥ fun a => j₀ (↑u⁻¹ * Φ ((V *ᵥ v) a))
  have hGc : Continuous G := by
    refine continuous_const.matrix_mulVec (continuous_pi fun a => (hcont hj₀d).comp (continuous_const.mul ?_))
    exact continuous_finsetSum _ fun i _ => continuous_const.mul
      ((hcDc i).comp ((continuous_apply a).comp (continuous_const.matrix_mulVec continuous_id)))
  have hGy : ∀ n, G (fun a => bk.iA (y n a)) = fun a => bk.iA (y n a) := by
    intro n
    obtain ⟨x, hx⟩ := hy n
    have hxe := hx j₀ hj₀d
    have h3 : G (s.W *ᵥ fun b => j₀ (x b)) = s.W *ᵥ fun b => j₀ (x b) := by
      dsimp only [G]; congr 1; funext a; rw [← hsol x a]
    rwa [hxe] at h3

  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have ht : Filter.Tendsto (fun n => fun a => bk.iA (y n a)) Filter.atTop (nhds fun a => bk.iA (z a)) := by
    rw [tendsto_pi_nhds]; intro a
    have h0 : Filter.Tendsto (fun n => bk.iA (z a - y n a)) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm (fun n => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl1))
      obtain ⟨w, hw⟩ := hz n a
      rw [hw]; exact norm_toDisc_natPow_mul_le _ _ n w
    have h4 := (tendsto_const_nhds (x := bk.iA (z a))).sub h0
    simpa only [sub_zero, map_sub, sub_sub_cancel] using h4
  have hfix : G (fun a => bk.iA (z a)) = fun a => bk.iA (z a) :=
    (isClosed_eq hGc continuous_id).mem_of_tendsto ht (Filter.Eventually.of_forall hGy)
  refine ⟨fun a => ↑u⁻¹ * Φ ((V *ᵥ fun b => bk.iA (z b)) a), fun j hj => ?_⟩
  rw [hj.unique hj₀d]
  exact hfix

end GlobalTheory.BSP
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

theorem breuilKisinDatum_radius_pos_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have h1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := by
    have := bk.deg_pos
    positivity
  refine ⟨NNReal.rpow_pos (by exact_mod_cast hl.out.pos), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg h1 (neg_neg_of_pos he)

theorem height_Z_isUnit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ)
    (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (k : ℕ)
    (S' : Matrix (Fin d) (Fin d) (Ainf l)),
    Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) →
    (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z.map j = Y.map bk.iA) → IsUnit Z := by
  intro l _ K bk τ hτ d ρ _ s Y Z k S' hYS hW
  obtain ⟨hρ0, hρ1⟩ := breuilKisinDatum_radius_pos_lt_one bk
  have hu : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  let j0 : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map (u := (X : bk.S)) (ρ := bk.ρ₀) bk.ev hu
  have hj0 : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j0 := isDiscMap_map bk.ev hu
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨cD, hcD1, hcD2, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j0 hj0
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB (2 * s.N * d)

  set δ := Z.det with hδ
  have hdet : j0 δ * (s.W.det * bk.iA S'.det) =
      bk.iA (bk.ev ((l : bk.S) ^ (k * d)) * τ ^ (2 * s.N * d)) := by
    have h1 := congrArg (fun M => bk.iA M.det) hYS
    simp only [det_mul, det_smul, det_one, mul_one, Fintype.card_fin] at h1
    have h2 : bk.iA Y.det = s.W.det * j0 δ := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hW j0 hj0, det_mul, hδ, RingHom.map_det,
        RingHom.mapMatrix_apply]
    rw [map_mul, h2] at h1
    have e : bk.ev ((l : bk.S) ^ (k * d)) * τ ^ (2 * s.N * d) = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) ^ d := by
      rw [map_pow, map_natCast]; ring
    rw [e, ← h1]
    ring
  have hdvd : ∀ i, δ ∣ toDisc l (X : bk.S) bk.ρ₀ (TB.c i (τ ^ (2 * s.N * d))) := by
    intro i
    have h3 := congrArg (cD i) hdet
    rw [hcD2, hcD1, TB.c_mul, map_mul (toDisc l (X : bk.S) bk.ρ₀)] at h3
    have hunit : IsUnit (toDisc l (X : bk.S) bk.ρ₀ ((l : bk.S) ^ (k * d))) := by
      rw [map_pow, map_natCast]; exact (isUnit_l_disc l _ _).pow _
    exact (hunit.dvd_mul_left).1 ⟨_, h3.symm⟩
  have hle : Ideal.span (Set.range fun i => TB.c i (τ ^ (2 * s.N * d))) ≤
      (Ideal.span {δ}).comap (toDisc l (X : bk.S) bk.ρ₀) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_span_singleton.2 (hdvd i)
  have hl := Ideal.mem_span_singleton.1 (hle hr)
  rw [map_pow, map_natCast] at hl
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_dvd_unit hl ((isUnit_l_disc l _ _).pow _)

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.HeightAprime

theorem dvd_of_dvd_prime_pow_mul {R : Type} [CommRing R] [IsDomain R] {p a b : R} (hp : Prime p)
    (ha : ¬ p ∣ a) : ∀ n : ℕ, a ∣ p ^ n * b → a ∣ b := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro h
    obtain ⟨x, hx⟩ := h
    have hpx : p ∣ a * x := ⟨p ^ n * b, by rw [← hx]; ring⟩
    obtain ⟨y, rfl⟩ := (hp.dvd_or_dvd hpx).resolve_left ha
    refine ih ⟨y, mul_left_cancel₀ hp.ne_zero ?_⟩
    linear_combination hx

theorem C_dvd_iff {R : Type} [CommRing R] (p : R) (f : R⟦X⟧) :
    C p ∣ f ↔ ∀ n, p ∣ coeff n f := by
  constructor
  · rintro ⟨g, rfl⟩ n
    rw [coeff_C_mul]; exact dvd_mul_right _ _
  · intro h
    refine ⟨mk fun n => (h n).choose, ?_⟩
    ext n
    rw [coeff_C_mul, coeff_mk]
    exact (h n).choose_spec

theorem prime_C {R : Type} [CommRing R] [IsDomain R] {p : R} (hp : Prime p) : Prime (C p : R⟦X⟧) := by
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  let q : R →+* R ⧸ Ideal.span {p} := Ideal.Quotient.mk _
  have key : ∀ f : R⟦X⟧, C p ∣ f ↔ PowerSeries.map q f = 0 := by
    intro f
    rw [C_dvd_iff]
    constructor
    · intro h; ext n
      rw [coeff_map, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (h n))
    · intro h n
      have := congrArg (coeff n) h
      rw [coeff_map, map_zero] at this
      exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 this)
  refine ⟨fun h => hp.ne_zero (by simpa using congrArg (constantCoeff) h), fun h => hp.not_unit ?_, ?_⟩
  · simpa using h.map (constantCoeff (R := R))
  · intro f g hfg
    rw [key, key]
    rw [key, map_mul] at hfg
    exact mul_eq_zero.1 hfg

theorem prime_l {l : ℕ} [Fact l.Prime] (a : ℕ) [NeZero a] : Prime (l : (Wq l a)⟦X⟧) := by
  have h : Prime (l : Wq l a) := (WittVector.irreducible l).prime
  have := prime_C h
  simpa using this

end GlobalTheory.BSP.HeightAprime

namespace GlobalTheory.BSP.HeightAprime

variable {l : ℕ} [hl : Fact l.Prime]

theorem not_l_dvd_det {K : FinExt l} (bk : BK K) {d : ℕ} (Y : Matrix (Fin d) (Fin d) (Ainf l))
    (A : Matrix (Fin d) (Fin d) bk.S) (hY : IsUnit (Y.map (inclW l)))
    (hφ : Y.map WittVector.frobenius = Y * A.map bk.ev) : ¬ (l : bk.S) ∣ A.det := by
  rintro ⟨t, ht⟩
  have h2 : WittVector.frobenius Y.det = Y.det * bk.ev A.det := by
    rw [RingHom.map_det, RingHom.map_det, ← det_mul]
    exact congrArg det hφ
  have h0 := congrArg WittVector.constantCoeff h2
  rw [ht, map_mul, map_mul, map_mul, map_natCast, map_natCast, CharP.cast_eq_zero, zero_mul, mul_zero] at h0
  have hc : (WittVector.frobenius Y.det).coeff 0 = Y.det.coeff 0 ^ l :=
    WittVector.coeff_frobenius_charP l _ 0
  have hz : Y.det.coeff 0 = 0 := by
    have : WittVector.constantCoeff (WittVector.frobenius Y.det) = (WittVector.frobenius Y.det).coeff 0 := rfl
    rw [this, hc] at h0
    exact pow_eq_zero_iff hl.out.ne_zero |>.1 h0
  have hu : IsUnit (inclW l Y.det) := by
    rw [RingHom.map_det]; exact (Matrix.isUnit_iff_isUnit_det _).1 hY
  have hu0 := hu.map (WittVector.constantCoeff (p := l) (R := Cb l))
  have : WittVector.constantCoeff (inclW l Y.det) = (inclW l Y.det).coeff 0 := rfl
  rw [this, inclW, WittVector.map_coeff, hz, map_zero] at hu0
  exact not_isUnit_zero hu0

end GlobalTheory.BSP.HeightAprime

theorem GlobalTheory.BSP.HeightAprime.main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (Y S' : Matrix (Fin d) (Fin d) (Ainf l)) (A : Matrix (Fin d) (Fin d) (bk.S)) (k M : ℕ), IsUnit (Y.map (inclW l)) → Y * S' = ((l : Ainf l) ^ k * τ ^ M) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → Y.map WittVector.frobenius = Y * A.map bk.ev → ∃ (b : ℕ) (A' : Matrix (Fin d) (Fin d) (bk.S)), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) (bk.S)) := by
  intro l _ K bk τ hτ d Y S' A k M hY hYS hφ
  have h1 : Y.det * S'.det = ((l : Ainf l) ^ k * τ ^ M) ^ d := by
    rw [← det_mul, hYS, det_smul, det_one, mul_one, Fintype.card_fin]
  have h2 : WittVector.frobenius Y.det = Y.det * bk.ev A.det := by
    rw [RingHom.map_det, RingHom.map_det, ← det_mul]
    exact congrArg det hφ
  have h3 : bk.ev A.det * (Y.det * WittVector.frobenius S'.det) =
      bk.ev ((l : bk.S) ^ (k * d) * bk.E ^ (M * d)) * τ ^ (M * d) := by
    have := congrArg WittVector.frobenius h1
    rw [map_mul, h2, map_pow, map_mul, map_pow, map_pow, map_natCast, hτ.1] at this
    rw [map_mul, map_pow, map_pow, map_natCast, pow_mul, pow_mul, pow_mul]
    linear_combination this
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB (M * d)
  set c : bk.S := (l : bk.S) ^ (k * d) * bk.E ^ (M * d)
  have hdiv : ∀ i, A.det ∣ c * TB.c i (τ ^ (M * d)) := fun i => by
    have := congrArg (TB.c i) h3
    rw [TB.c_mul, TB.c_mul] at this
    exact ⟨_, this.symm⟩
  have hdvd : A.det ∣ c * (l : bk.S) ^ r := by
    refine Submodule.span_induction (p := fun x _ => A.det ∣ c * x) ?_ ?_ ?_ ?_ hr
    · rintro _ ⟨i, rfl⟩; exact hdiv i
    · simp
    · intro x y _ _ hx hy; rw [mul_add]; exact dvd_add hx hy
    · intro a x _ hx; rw [smul_eq_mul, mul_left_comm]; exact dvd_mul_of_dvd_right hx a
  have hdvd' : A.det ∣ (l : bk.S) ^ (k * d + r) * bk.E ^ (M * d) := by
    have e : c * (l : bk.S) ^ r = (l : bk.S) ^ (k * d + r) * bk.E ^ (M * d) := by
      simp only [c]; ring
    rwa [e] at hdvd
  obtain ⟨q, hq⟩ := GlobalTheory.BSP.HeightAprime.dvd_of_dvd_prime_pow_mul (GlobalTheory.BSP.HeightAprime.prime_l bk.a)
    (GlobalTheory.BSP.HeightAprime.not_l_dvd_det bk Y A hY hφ) _ hdvd'
  refine ⟨M * d, q • A.adjugate, ?_⟩
  rw [Matrix.mul_smul, mul_adjugate, smul_smul, mul_comm q, ← hq]
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.crystallineLattice_discSpan_frobenius_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (fun a => WittVector.frobenius (y a)) := by
  first | exact @GlobalTheory.BSP.seed_span_frobenius_stable | exact GlobalTheory.BSP.seed_span_frobenius_stable | (intros; apply GlobalTheory.BSP.seed_span_frobenius_stable <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), (∀ a : Ainf l, bk.ev bk.E ^ m ∣ (l : Ainf l) * a → bk.ev bk.E ^ m ∣ a) ∧ (∀ s : bk.S, bk.ev bk.E ^ m ∣ bk.ev s → bk.E ^ m ∣ s) ∧ (∀ a : Ainf l, aDp l a ∈ Per.FilP l m ↔ bk.ev bk.E ^ m ∣ a) ∧ ∀ a : Ainf l, (∀ n : ℕ, ∃ b c : Ainf l, a = bk.ev bk.E ^ m * b + (l : Ainf l) ^ n * c) → bk.ev bk.E ^ m ∣ a := by
  first | exact @GlobalTheory.AinfEPow.ePow_facts | exact GlobalTheory.AinfEPow.ePow_facts | (intros; apply GlobalTheory.AinfEPow.ePow_facts; all_goals assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.crystallineLattice_rational_in_columns : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (Y1.map (inclW l)).det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → ∃ (δ : bk.S) (c : Fin d → bk.S), δ ≠ 0 ∧ (fun a => bk.ev δ * y a) = Y1 *ᵥ fun a => bk.ev (c a) := by
  first | exact @GlobalTheory.BSP.rational_in_columns | exact GlobalTheory.BSP.rational_in_columns | (intros; apply GlobalTheory.BSP.rational_in_columns <;> assumption)
end
