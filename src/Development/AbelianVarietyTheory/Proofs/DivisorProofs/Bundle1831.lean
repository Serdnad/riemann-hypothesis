module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle285
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1787
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle028
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
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps
open Formalism.L2.Host (unif atFin unif_spec IsUnitAt)

noncomputable section

namespace GlobalTheory.TameTwistEps

variable {E : Type} [Field E] [NumberField E]

theorem pow_apply_eq_one {ξ : HChar E} {N : ℕ} (h : ξ.OrderDvd N) (x : Ideles E) : ((ξ.1 x : ℂˣ) : ℂ) ^ N = 1 := by
  have h1 : ((ξ ^ N : HChar E).1 x) = (ξ.1 x) ^ N := by
    rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]
  rw [← Units.val_pow_eq_pow_val, ← h1, h]
  rfl

theorem locK_pow_eq_one {ξ : HChar E} {N : ℕ} (h : ξ.OrderDvd N) (w : HeightOneSpectrum (𝓞 E)) (x : Eˣ) :
    ((ξ.locK w x : ℂˣ) : ℂ) ^ N = 1 :=
  pow_apply_eq_one h _

theorem isUnitary_of_orderDvd {ξ : HChar E} {N : ℕ} (hN : 0 < N) (h : ξ.OrderDvd N) : IsUnitary ξ := fun x =>
  Complex.norm_eq_one_of_pow_eq_one (pow_apply_eq_one h x) hN.ne'

theorem expAt_unr_mul {χ ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (hχ : χ.UnrAt w) (hξ : ExpAt ξ w a) :
    ExpAt (χ * ξ) w a := by
  intro k
  have hk : χ.LevelLe w k := hχ.levelLe k
  refine ⟨fun hx => (hξ k).1 ?_, fun hn => hk.mul ((hξ k).2 hn)⟩
  have := hk.inv.mul hx
  rwa [inv_mul_cancel_left] at this

theorem psiAt_natMul (w : HeightOneSpectrum (𝓞 E)) (t : w.adicCompletion E) (k : ℕ) :
    psiAt w ((k : w.adicCompletion E) * t) = psiAt w t ^ k := by
  induction k with
  | zero => simpa using psiAt_eq_one (w := w) (t := 0) (by simp)
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, psiAt_add, ih, pow_succ]

theorem gaussSumAt_unr_mul {χ ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w) {a : ℕ} (ha : a ≠ 0) (c : Eˣ) :
    gaussSumAt (χ * ξ) w a c = gaussSumAt ξ w a c := by
  unfold gaussSumAt
  congr 1
  funext y
  have hy := out_notMem w ha y
  have hy1 : w.valuation E ((Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ a) : 𝓞 E) : E) = 1 :=
    (w.valuation_eq_one_iff_notMem (K := E)).2 hy
  have hz0 : ((Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ a) : 𝓞 E) : E) ≠ 0 := fun h => by
    rw [h, map_zero] at hy1
    exact zero_ne_one hy1
  rw [gaussTerm, gaussTerm, dite_eq_right hz0, dite_eq_right hz0]
  have h1 : χ.locK w (Units.mk0 _ hz0) = 1 := by
    refine hχ _ ?_
    show Valued.v (((atFin w (Units.mk0 _ hz0)) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1
    simp only [atFin, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.val_mk0]
    have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
    rw [hval, hy1]
  have e : (χ * ξ).locK w (Units.mk0 _ hz0) = χ.locK w (Units.mk0 _ hz0) * ξ.locK w (Units.mk0 _ hz0) := rfl
  rw [e, h1, one_mul]

end GlobalTheory.TameTwistEps

namespace GlobalTheory.TameTwistEps

variable {E : Type} [Field E] [NumberField E]

theorem exists_gaussSumAt_dvd {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    {q N : ℕ} (hq : q.Prime) (hqw : Ideal.absNorm w.asIdeal = q) (hN : 0 < N) (hξN : ξ.OrderDvd N) (hξ : ExpAt ξ w 1)
    (hξK : ∀ x : Eˣ, ((ξ.locK w x : ℂˣ) : ℂ) ∈ Set.range σ) (hqK : ∀ z : ℂ, z ^ q = 1 → z ∈ Set.range σ) :
    ∃ g : 𝓞 K, σ (g : K) = gaussSumAt ξ w 1 (unif w ^ (1 + diffExp w)) ∧ g ∣ (q : 𝓞 K) := by
  classical
  set c : Eˣ := unif w ^ (1 + diffExp w) with hc
  haveI : Fintype (𝓞 E ⧸ w.asIdeal ^ 1)ˣ := Fintype.ofFinite _
  have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  have hqv : w.valuation E ((q : 𝓞 E) : E) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have h := valuation_sub_le (w := w) (a := 1) (y := (q : 𝓞 E)) (y' := 0)
      (by rw [sub_zero, pow_one, ← hqw]; exact Ideal.absNorm_mem _)
    simpa using h
  have hterm : ∀ y : (𝓞 E ⧸ w.asIdeal ^ 1)ˣ, ∃ x : K,
      σ x = gaussTerm ξ w c ((Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ 1) : 𝓞 E) : E) ∧ x ^ (N * q) = 1 := by
    intro y
    have hy := out_notMem w one_ne_zero y
    set z : 𝓞 E := Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ 1)
    have hy1 : w.valuation E (z : E) = 1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hy
    have hz0 : (z : E) ≠ 0 := fun h => by
      rw [h, map_zero] at hy1
      exact zero_ne_one hy1
    rw [gaussTerm, dite_eq_right hz0]
    obtain ⟨x1, hx1⟩ := hξK (Units.mk0 _ hz0)⁻¹
    have hp : psiAt w (algebraMap E (w.adicCompletion E) ((z : E) / c)) ^ q = 1 := by
      rw [← psiAt_natMul]
      apply psiAt_eq_one
      have e : ((q : ℕ) : w.adicCompletion E) * algebraMap E (w.adicCompletion E) ((z : E) / c) =
          algebraMap E (w.adicCompletion E) (((q : 𝓞 E) : E) * ((z : E) / c)) := by simp
      rw [e, hval, map_mul, map_div₀, hy1, hc, valuation_unif_pow, one_div, ← div_eq_mul_inv,
        div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add]
      convert hqv using 2
      push_cast
      ring
    obtain ⟨x2, hx2⟩ := hqK _ hp
    have hx1N : x1 ^ N = 1 := σ.injective (by rw [map_pow, hx1, locK_pow_eq_one hξN, map_one])
    have hx2q : x2 ^ q = 1 := σ.injective (by rw [map_pow, hx2, hp, map_one])
    refine ⟨x1 * x2, by rw [map_mul, hx1, hx2, map_inv], ?_⟩
    rw [mul_pow, pow_mul, hx1N, one_pow, one_mul, mul_comm N q, pow_mul, hx2q, one_pow]
  choose X hX using hterm
  have hpos : 0 < N * q := Nat.mul_pos hN hq.pos
  have hXi : ∀ y, IsIntegral ℤ (X y) := fun y => IsIntegral.of_pow hpos (by rw [(hX y).2]; exact isIntegral_one)
  have hXi' : ∀ y, IsIntegral ℤ (X y)⁻¹ := fun y =>
    IsIntegral.of_pow hpos (by rw [inv_pow, (hX y).2, inv_one]; exact isIntegral_one)
  have hnorm : ∀ y, ‖σ (X y)‖ = 1 := fun y =>
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, (hX y).2, map_one]) hpos.ne'
  have hgi : IsIntegral ℤ (∑ y, X y) := IsIntegral.sum _ fun y _ => hXi y
  have hgi' : IsIntegral ℤ (∑ y, (X y)⁻¹) := IsIntegral.sum _ fun y _ => hXi' y
  have hσg : σ (∑ y, X y) = gaussSumAt ξ w 1 c := by

    rw [map_sum, gaussSumAt, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun y _ => (hX y).1
  have hσg' : σ (∑ y, (X y)⁻¹) = starRingEnd ℂ (gaussSumAt ξ w 1 c) := by

    rw [← hσg, map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [map_inv₀, Complex.inv_eq_conj (hnorm y)]
  have hu : IsUnitary ξ := isUnitary_of_orderDvd hN hξN
  have hG := GlobalTheory.GaussMod.gaussSumAt_normSq ξ w 1 c one_ne_zero hξ hu (valuation_unif_pow w _)
  have hprod : (∑ y, X y) * (∑ y, (X y)⁻¹) = (q : K) := σ.injective (by
    rw [map_mul, hσg, hσg', Complex.mul_conj, Complex.normSq_eq_norm_sq, hG, hqw, map_natCast]
    push_cast
    ring)
  refine ⟨⟨_, hgi⟩, hσg, ⟨⟨_, hgi'⟩, RingOfIntegers.ext ?_⟩⟩
  have e : ((q : 𝓞 K) : K) = (q : K) := by simp
  rw [e, ← hprod]
  rfl

end GlobalTheory.TameTwistEps

namespace GlobalTheory.TameTwistEps

theorem locEps_tame_twist : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (q m N : ℕ) (s : ℤ), q.Prime → Nat.card (𝓞 E ⧸ w.asIdeal) = q → q ∣ m → 0 < N → ξ.OrderDvd N → χ.UnrAt w → ExpAt ξ w 1 → (∀ x : Eˣ, ((ξ.locK w x : ℂˣ) : ℂ) ∈ Set.range σ) → (∀ z : ℂ, z ^ q = 1 → z ∈ Set.range σ) → s ≤ 0 → ExpAt (χ * ξ) w 1 ∧ ∃ g : K, GlobalTheory.Square.IsAwayUnit m g ∧ locEps (χ * ξ) w 1 (s : ℂ) = σ g * ((χ.val w : ℂˣ) : ℂ) * locEps χ w 0 (s : ℂ) := by
  intro E _ _ K _ _ _ σ χ ξ w q m N s hq hcard hqm hN hξN hχ hξ hξK hqK hs
  have hqw : Ideal.absNorm w.asIdeal = q := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; exact hcard
  refine ⟨expAt_unr_mul hχ hξ, ?_⟩
  obtain ⟨gG, hgG, hdvd⟩ := exists_gaussSumAt_dvd σ hq hqw hN hξN hξ hξK hqK
  obtain ⟨x1, hx1⟩ := hξK (unif w ^ (1 + diffExp w))
  have hx1N : x1 ^ N = 1 := σ.injective (by rw [map_pow, hx1, locK_pow_eq_one hξN, map_one])
  have hx1i : IsIntegral ℤ x1 := IsIntegral.of_pow hN (by rw [hx1N]; exact isIntegral_one)
  set a1 : 𝓞 K := ⟨x1, hx1i⟩ with ha1d
  have ha1 : IsUnit a1 := by
    have e : ((a1 : 𝓞 K) : K) = x1 := rfl
    exact IsUnit.of_pow_eq_one (RingOfIntegers.ext (by push_cast; exact (congrArg (· ^ N) e).trans hx1N)) hN.ne'
  have hqm' : (q : 𝓞 K) ∣ (m : 𝓞 K) := Nat.cast_dvd_cast hqm
  refine ⟨x1 * (q : K) ^ (-s).toNat * (gG : K), ?_, ?_⟩
  · have h1 : GlobalTheory.Square.IsAwayUnit m x1 := GlobalTheory.Square.IsAwayUnit.of_dvd (a := a1) (k := 0) (by simpa using ha1.dvd)
    have h2 : GlobalTheory.Square.IsAwayUnit m ((q : K) ^ (-s).toNat) := by
      have := GlobalTheory.Square.IsAwayUnit.of_dvd (K := K) (m := m) (a := (q : 𝓞 K) ^ (-s).toNat) (pow_dvd_pow_of_dvd hqm' _)
      simpa using this
    have h3 : GlobalTheory.Square.IsAwayUnit m (gG : K) := GlobalTheory.Square.IsAwayUnit.of_dvd (k := 1) (by rw [pow_one]; exact hdvd.trans hqm')
    exact (h1.mul h2).mul h3
  · have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hj : (((-s).toNat : ℕ) : ℂ) = -(s : ℂ) := by
      have : (((-s).toNat : ℕ) : ℤ) = -s := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have e1 : ((q : ℕ) : ℂ) ^ (-(s : ℂ) * ((1 + diffExp w : ℕ) : ℂ)) =
        ((q : ℕ) : ℂ) ^ (-(s : ℂ) * ((0 + diffExp w : ℕ) : ℂ)) * (q : ℂ) ^ ((-s).toNat) := by
      rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq0, hj]
      congr 1
      push_cast
      ring
    have e2 : (χ * ξ).locK w (unif w ^ (1 + diffExp w)) =
        χ.val w * χ.locK w (unif w ^ (0 + diffExp w)) * ξ.locK w (unif w ^ (1 + diffExp w)) := by
      show χ.locK w (unif w ^ (1 + diffExp w)) * ξ.locK w (unif w ^ (1 + diffExp w)) = _
      rw [pow_add, pow_one, map_mul, zero_add]
      rfl
    rw [locEps, locEps, if_neg one_ne_zero, if_pos rfl, gaussSumAt_unr_mul hχ one_ne_zero, hqw, e1, e2, map_mul, map_mul,
      hx1, hgG, map_pow σ, map_natCast σ]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    ring

end GlobalTheory.TameTwistEps
end
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.HolAtlas

variable {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n) (A' : HolAtlas M' n')

theorem loc_pullback_eq {f : M' → M} {α : A.Fld} (hf : A.IsHolo A' f) (hα : A.IsForm α) (j : A'.ι) (i : A.ι) :
    IsOpen ((A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source)) ∧
    ∀ v ∈ (A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source),
      A'.loc (A.pullback A' f α) j v =
        pull (fderiv ℂ (A.e i ∘ f ∘ (A'.e j).symm) v) (A.loc α i ((A.e i ∘ f ∘ (A'.e j).symm) v)) := by
  refine ⟨(A'.e j).continuousOn_symm.isOpen_inter_preimage (A'.e j).open_target
    ((A.e i).open_source.preimage hf.1), fun v hv => ?_⟩
  have hs : (A'.e j).symm v ∈ (A'.e j).source := (A'.e j).map_target hv.1
  have hτ : (A.e i ∘ f ∘ (A'.e j).symm) v ∈ (A.e i).target := (A.e i).map_source hv.2
  rw [HolAtlas.loc, dite_eq_left hv.1, HolAtlas.loc, dite_eq_left hτ,
    GlobalTheory.T.holAtlas_pullback_eq_chart_expression M M' n n' A A' f α hf hα ⟨(j, (A'.e j).symm v), hs⟩ i hv.2]
  have hc : (A'.e j) ((A'.e j).symm v) = v := (A'.e j).right_inv hv.1
  simp only [Pt.crd, Pt.ch, Pt.pt, hc]
  congr 2
  exact Subtype.ext (Prod.ext rfl ((A.e i).left_inv hv.2).symm)

theorem pullback_del_dbar (f : M' → M) (α : A.Fld) (hf : A.IsHolo A' f) (hα : A.IsForm α) :
    A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧
      A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α) := by
  have key : ∀ x : A'.Pt, A'.del (A.pullback A' f α) x = A.pullback A' f (A.del α) x ∧
      A'.dbar (A.pullback A' f α) x = A.pullback A' f (A.dbar α) x := by
    intro x
    have hi : f x.pt ∈ (A.e (A.cover (f x.pt)).choose).source := (A.cover (f x.pt)).choose_spec
    obtain ⟨hU, hloc⟩ := loc_pullback_eq A A' hf hα x.1.1 (A.cover (f x.pt)).choose
    have hx : x.crd ∈ (A'.e x.1.1).target ∩ (A'.e x.1.1).symm ⁻¹' (f ⁻¹' (A.e (A.cover (f x.pt)).choose).source) := by
      refine ⟨(A'.e x.1.1).map_source x.2, ?_⟩
      show (A'.e x.1.1).symm (A'.e x.1.1 x.1.2) ∈ f ⁻¹' (A.e (A.cover (f x.pt)).choose).source
      rw [(A'.e x.1.1).left_inv x.2]
      exact hi
    have hτx : (A.e (A.cover (f x.pt)).choose ∘ f ∘ (A'.e x.1.1).symm) x.crd =
        A.e (A.cover (f x.pt)).choose (f x.pt) := by
      show A.e _ (f ((A'.e x.1.1).symm (A'.e x.1.1 x.1.2))) = _
      rw [(A'.e x.1.1).left_inv x.2]
    have hdiff : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α (A.cover (f x.pt)).choose y) S)
        ((A.e (A.cover (f x.pt)).choose ∘ f ∘ (A'.e x.1.1).symm) x.crd) := by
      intro S
      rw [hτx]
      exact ((hα.smooth _ S).differentiableOn (by simp)).differentiableAt
        ((A.e _).open_target.mem_nhds ((A.e _).map_source hi))
    have hc := GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n' n _ _ (A.loc α (A.cover (f x.pt)).choose) x.crd hU hx (hf.2 x.1.1 _) hdiff
    have hl := (GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n' x.crd).2.2.2.1 _ _ (Filter.eventually_of_mem (hU.mem_nhds hx) hloc)
    rw [hτx] at hc
    exact ⟨(hl.1.trans hc.1 : _), (hl.2.trans hc.2 : _)⟩
  exact ⟨funext fun x => (key x).1, funext fun x => (key x).2⟩

end GlobalTheory.CxForm.HolAtlas

theorem GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ)
    (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A.IsForm (A.del α) → A.IsForm (A.dbar α) →
    A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧ A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α) :=
  fun _ _ _ _ _ _ A A' f α hf hα _ _ => HolAtlas.pullback_del_dbar A A' f α hf hα
end
end

section

open Formalism.MainNotions.S

namespace GlobalTheory.IrrAdm

theorem isIrrAdm_of_irred : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsURepOn (UJset ε) π → IsIrredOn (UJset ε) π → GlobalTheory.RealInd.IsIrrAdm ε π := by
  intro n ε H _ _ _ _ π hU hI
  have hK : ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, ‖π k v‖ = ‖v‖ := fun k hk v =>
    hU.2.1 k (GlobalTheory.GKModule.mem_UJset_of_mem_Kset hk) v
  refine ⟨inferInstance, ⟨hU.1, hU.2.2, hK, ?_⟩, hI⟩
  intro Λ
  classical
  by_cases hne : ∃ S₀ : Submodule ℂ H, S₀ ≤ ⊤ ∧ IsKTypeOf ε π Λ S₀
  · obtain ⟨S₀, -, hS₀⟩ := hne
    haveI : FiniteDimensional ℂ S₀ := hS₀.1
    have hY := (GlobalTheory.T.irreducible_K_stable_finite_subspace n ε H π hU hI).1 S₀ hS₀.1 hS₀.2.1
    let b := Module.finBasis ℂ S₀
    choose Y hYf hvY hYB using fun i => hY (b i) (b i).2
    haveI : ∀ i, FiniteDimensional ℂ (Y i) := hYf
    refine Submodule.finiteDimensional_of_le (sSup_le fun S hS => ?_) (S₂ := ⨆ i, Y i)
    obtain ⟨B, hB, rfl⟩ := (GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso n ε H π hU.1 hU.2.2 hK).2 Λ S₀ S hS₀ hS.2
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    have hx' : (⟨x, hx⟩ : S₀) ∈ Submodule.span ℂ (Set.range b) := b.span_eq ▸ Submodule.mem_top
    have h2 := Submodule.apply_mem_span_image_of_mem_span S₀.subtype hx'
    rw [← Set.range_comp] at h2
    refine (Submodule.span_le.2 ?_) h2
    rintro _ ⟨i, rfl⟩
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, Function.comp_apply, Submodule.subtype_apply,
      SetLike.mem_coe]
    exact Submodule.mem_iSup_of_mem i (hYB i B hB _ (hvY i))
  · have : {S : Submodule ℂ H | S ≤ ⊤ ∧ IsKTypeOf ε π Λ S} = ∅ :=
      Set.eq_empty_of_forall_notMem fun S hS => hne ⟨S, hS⟩
    rw [this, sSup_empty]
    infer_instance

end GlobalTheory.IrrAdm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitary_adelic_character_trivial_rat_and_split : ∀ (D : D7) (V : HSp D) (ν : GA D V →* Circle), Continuous ν → (∀ γ ∈ GQ V, ν γ = 1) → (∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) → ∀ g, ν g = 1 := by
  first | exact @GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split | exact GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split | (intros; apply GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_level_place_datum_over_number_field : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_vP → ∀ (i : Fin D.R.m), VStd D i → ∀ (t : T0) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ M' : IntermediateField ℚ ℂ, M ≤ M' → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ J : Ideal (𝓞 D.host.E), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) → ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M', PhiIs R i M'.val.toRingHom t ι (J • ⊤) φ := by
  first | exact @GlobalTheory.LevelDatum.exists_phi | exact GlobalTheory.LevelDatum.exists_phi | (intros; apply GlobalTheory.LevelDatum.exists_phi <;> assumption)
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finite_adelic_matrix_mem_lattice_of_columns : ∀ (D : D7) (V W : HSp D), V.gram = 1 → ∀ (k : GA D W) (x : WO V W), x.map (infPart D) = 0 → (∀ b, (fun a => finPart D (x a b)) ∈ latGHat W k) → x ∈ (latO V W (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True) := by
  first | exact @GlobalTheory.ColsInLat.mem_latO_of_cols | exact GlobalTheory.ColsInLat.mem_latO_of_cols | (intros; apply GlobalTheory.ColsInLat.mem_latO_of_cols <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.WeilTypeChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isCMField_of_cmExt {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : IsCMField E := by
  haveI := h.1; haveI := h.2.1
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  exact IsCMField.ofCMExtension F E

def phase : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)) (div_ne_zero z.ne_zero (by simp))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    ring

theorem phase_val (z : ℂˣ) : ((phase z : ℂˣ) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

theorem continuous_phase : Continuous phase := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun z : ℂˣ => (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)
    exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm) fun z => by simp
  · have : (fun z : ℂˣ => (((phase z)⁻¹ : ℂˣ) : ℂ)) = fun z => ((phase z⁻¹ : ℂˣ) : ℂ) :=
      funext fun z => by rw [map_inv]
    show Continuous fun z : ℂˣ => (((phase z)⁻¹ : ℂˣ) : ℂ)
    rw [this]
    show Continuous fun z : ℂˣ => ((z⁻¹ : ℂˣ) : ℂ) / ((‖((z⁻¹ : ℂˣ) : ℂ)‖ : ℝ) : ℂ)
    exact Units.continuous_coe_inv.div (Complex.continuous_ofReal.comp Units.continuous_coe_inv.norm) fun z => by simp

theorem norm_phase (z : ℂˣ) : ‖((phase z : ℂˣ) : ℂ)‖ = 1 := by
  rw [phase_val, norm_div, Complex.norm_real, norm_norm, div_self (by simp)]

def chiInf (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : (AF F ⊗[F] E)ˣ →* ℂˣ :=
  ∏ w, phase.comp (Units.map (piInf (emb w)).toMonoidHom)

theorem chiInf_apply (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (z : (AF F ⊗[F] E)ˣ) :
    ((chiInf emb z : ℂˣ) : ℂ) = ∏ w, (piInf (emb w) z / ((‖piInf (emb w) z‖ : ℝ) : ℂ)) := by
  simp [chiInf, phase_val]

theorem continuous_chiInf (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Continuous (chiInf emb) := by
  have e : ⇑(chiInf emb) = fun z => ∏ w, phase (Units.map (piInf (emb w)).toMonoidHom z) :=
    funext fun z => by simp [chiInf]
  rw [e]
  exact continuous_finsetProd _ fun w _ =>
    continuous_phase.comp (Continuous.units_map _ (GlobalTheory.ContMapReal.continuous_piInf (emb w)))

theorem norm_chiInf (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (z : (AF F ⊗[F] E)ˣ) :
    ‖((chiInf emb z : ℂˣ) : ℂ)‖ = 1 := by
  simp [chiInf, norm_prod, norm_phase]

theorem exists_weil_char : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ ξ : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ξ ∧ HasExp B.emb ξ (fun _ => 1) := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsCMField E := isCMField_of_cmExt hB.cm
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨q, hq1, hq⟩ := Nat.exists_infinite_primes (max 3 (Nat.card (Units.torsion E) + 1))
  have hq2 : 2 < q := by omega
  have htq : Nat.card (Units.torsion E) < q := by omega
  have ht : ¬ q ∣ Nat.card (Units.torsion E) := fun h => absurd (Nat.le_of_dvd Nat.card_pos h) (by omega)
  obtain ⟨U, hU, hUinf, hUk⟩ := GlobalTheory.T.exists_open_idele_subgroup_congruence_mod_q F E q hq.ne_zero
  obtain ⟨χ, hχc, hχ1, hχU, hχk⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (AF F ⊗[F] E)ˣ Eˣ U hU
    (Units.map (incAF F E).toMonoidHom) 1 (chiInf B.emb) (continuous_chiInf B.emb) (norm_chiInf B.emb)
    (fun _ => by simp) (fun k hk => by
      obtain ⟨u, hu, hu1⟩ := hUk k hk
      refine Units.ext ?_
      rw [chiInf_apply, MonoidHom.one_apply, Units.val_one]
      have e : ∀ w, piInf (B.emb w) ((Units.map (incAF F E).toMonoidHom k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
          (B.emb w).1 ((u : 𝓞 E) : E) := fun w => by
        rw [hu]
        exact GlobalTheory.ThK.EvAt0.ZPartArc.piInf_inclR' (B.emb w) (k : E)
      simp only [e]
      exact (GlobalTheory.T.cmType_unit_phase_prod_eq_one_of_congruent_one F E σ hB.cm B.emb q hq hq2 ht u hu1).symm)
  refine ⟨GlobalTheory.unitaryCharToCircle χ hχ1, ⟨?_, fun k => ?_⟩, fun z hz => ?_⟩
  · exact Continuous.subtype_mk (Units.continuous_val.comp hχc) _
  · apply Circle.ext
    show ((χ (Units.map (incAF F E).toMonoidHom k) : ℂˣ) : ℂ) = 1
    rw [hχk]; rfl
  · show ((χ z : ℂˣ) : ℂ) = _
    rw [hχU z (hUinf z hz), chiInf_apply]
    simp

end GlobalTheory.WeilTypeChar
end
end
