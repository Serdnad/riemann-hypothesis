module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizePos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Bundle004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.T2SpaceOfNonarchimedeanLocalField
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDeltaC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.PsiTower
public import Formalism.RealPlaceAnalysis.Bundle001
public import Formalism.HarderNarasimhan.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle227
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle228
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.HermitianLattices.StatementLat

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec

namespace GlobalTheory.Dec.BoundedDistance

theorem bound_le (s la R : ℝ) (m f : ℕ) (hs : 1 ≤ s) (hla : 0 < la) (hla1 : la ≤ 1) (hR : 0 ≤ R) (hf : 0 < f) :
    (1 + 2 * s * Real.exp (R / f) / la) ^ (2 * (m * f)) ≤ (3 * s / la) ^ (2 * m * f) * Real.exp (2 * (m : ℝ) * R) := by
  have hf' : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  have he : 1 ≤ Real.exp (R / f) := Real.one_le_exp (div_nonneg hR (Nat.cast_nonneg _))

  have hone : 1 ≤ s * Real.exp (R / f) / la := by
    rw [le_div_iff₀ hla]
    nlinarith
  have hbase0 : 0 ≤ 1 + 2 * s * Real.exp (R / f) / la := by positivity
  have hbase : 1 + 2 * s * Real.exp (R / f) / la ≤ 3 * s / la * Real.exp (R / f) := by
    have h3 : 3 * s / la * Real.exp (R / f) =
        s * Real.exp (R / f) / la + 2 * s * Real.exp (R / f) / la := by ring
    linarith
  have hk : 2 * (m * f) = 2 * m * f := by ring
  rw [hk]
  calc (1 + 2 * s * Real.exp (R / f) / la) ^ (2 * m * f)
      ≤ (3 * s / la * Real.exp (R / f)) ^ (2 * m * f) := pow_le_pow_left₀ hbase0 hbase _
    _ = (3 * s / la) ^ (2 * m * f) * Real.exp (2 * (m : ℝ) * R) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      field_simp

theorem countRat : CountRat := by
  intro I x y r hn hr
  obtain ⟨hfin, hcard⟩ := GlobalTheory.RationalCount.count_le I x y r hn hr
  have hx := GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn x
  have hy := GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn y

  have hx2 : tau1 I x ≤ 1 / 2 := by unfold tau1; exact min_le_left _ _
  have hy2 : tau1 I y ≤ 1 / 2 := by unfold tau1; exact min_le_left _ _
  have hs : (1 : ℝ) ≤ Real.sqrt I.n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hf : 0 < I.f := Module.finrank_pos
  have hla1 : tau1 I x * tau1 I y ≤ 1 := by nlinarith
  have key := bound_le (Real.sqrt I.n) (tau1 I x * tau1 I y) (∑ v, r v) (I.n ^ 2) I.f hs
    (mul_pos hx hy) hla1 (Finset.sum_nonneg fun v _ => hr v) hf
  push_cast at key
  exact ⟨hfin, hcard.trans key⟩

end GlobalTheory.Dec.BoundedDistance
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitAlmostAll

variable {D : D7}

theorem exists_nat_mul_integral (x : D.host.E) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : D.host.E) * x) := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have : Algebra.IsAlgebraic ℤ D.host.E := Algebra.IsAlgebraic.trans ℤ ℚ D.host.E
  obtain ⟨y, hy0, hy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x).exists_integral_multiple

  refine ⟨y.natAbs * y.natAbs, by simpa using hy0, ?_⟩
  have hsq : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := by
    rw [Nat.cast_mul]
    exact Int.natAbs_mul_self' y
  have e : ((y.natAbs * y.natAbs : ℕ) : D.host.E) * x = (y : D.host.E) * (y • x) := by
    rw [zsmul_eq_mul, ← mul_assoc]
    have hc : ((y.natAbs * y.natAbs : ℕ) : D.host.E) = (((y.natAbs * y.natAbs : ℕ) : ℤ) : D.host.E) :=
      (Int.cast_natCast _).symm
    rw [hc, hsq, Int.cast_mul]
  rw [e]
  have hyi : IsIntegral ℤ (y : D.host.E) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ D.host.E y))
  exact hyi.mul hy

theorem iota_mem_O (Z : LocDat D) (p : PlF D) (x : D.host.E) (n : ℕ)
    (hint : IsIntegral ℤ ((n : D.host.E) * x)) (hn : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal)) :
    (D.s.atP p).ιE x ∈ (Z.M p).L.O := by
  rw [(show (Z.M p).L.O = (D.s.atP p).O from (Z.agree p).2.2.2.1), (D.s.atP p).O_def]
  have : CharZero (D.s.atP p).Fp := (D.s.atP p).char0
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  have hcn : (D.s.atP p).ιF (n : D.host.F) = (n : (D.s.atP p).Fp) := map_natCast _ n
  have hc0 : (n : (D.s.atP p).Fp) ≠ 0 := by exact_mod_cast hn0

  have hv : p.valuation D.host.F (n : D.host.F) = 1 := by
    have := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
      (v := p) (K := D.host.F) (r := (n : 𝓞 D.host.F))).mpr hn
    rwa [map_natCast] at this
  have hle : (1 : (D.s.atP p).Fp) ≤ᵥ (n : (D.s.atP p).Fp) := by
    have := ((D.s.atP p).val 1 (n : D.host.F)).mpr (by rw [hv, map_one])
    rwa [map_one, hcn] at this
  have hinv : (n : (D.s.atP p).Fp)⁻¹ ∈ (ValuativeRel.valuation (D.s.atP p).Fp).integer := by
    rw [Valuation.mem_integer_iff, map_inv₀]
    have h1 := (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (D.s.atP p).Fp) 1
      (n : (D.s.atP p).Fp)).mp hle
    rw [map_one] at h1
    exact inv_le_one_of_one_le₀ h1
  have hx : (D.s.atP p).ιE x = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (n : (D.s.atP p).Fp)⁻¹ *
      (D.s.atP p).ιE ((n : D.host.E) * x) := by
    have hE : (n : D.host.E) = algebraMap D.host.F D.host.E (n : D.host.F) := (map_natCast _ n).symm
    rw [map_mul, hE, (D.s.atP p).compat, hcn, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  rw [hx]
  refine IsIntegral.mul ?_ ?_
  · exact isIntegral_algebraMap (R := (ValuativeRel.valuation (D.s.atP p).Fp).integer) (x := ⟨(n : (D.s.atP p).Fp)⁻¹, hinv⟩)
  · exact (hint.map (D.s.atP p).ιE.toIntAlgHom).tower_top

theorem unit_almost_all : ∀ (D : D7) (Z : LocDat D) (x : D.host.E), x ≠ 0 →
    {p : PlF D | ¬ Formalism.MainNotions.S.LocNG.IsUnitO (Z.M p) ((D.s.atP p).ιE x)}.Finite := by
  intro D Z x hx
  obtain ⟨n, hn0, hn⟩ := exists_nat_mul_integral x
  obtain ⟨m, hm0, hm⟩ := exists_nat_mul_integral x⁻¹

  have hI : Ideal.span {((n * m : ℕ) : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast Nat.mul_ne_zero hn0 hm0
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hnm
  apply hp
  have hn' : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal) := fun h => hnm (by
    push_cast
    exact Ideal.mul_mem_right _ _ h)
  have hm' : ¬ ((m : 𝓞 D.host.F) ∈ p.asIdeal) := fun h => hnm (by
    push_cast
    exact Ideal.mul_mem_left _ _ h)
  refine ⟨iota_mem_O Z p x n hn hn', (D.s.atP p).ιE x⁻¹, iota_mem_O Z p x⁻¹ m hm hm', ?_⟩
  rw [← map_mul, mul_inv_cancel₀ hx, map_one]

end GlobalTheory.UnitAlmostAll
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.nonzero_cm_element_local_unit_almost_all : ∀ (D : D7) (Z : LocDat D) (x : D.host.E), x ≠ 0 →
    {p : PlF D | ¬ Formalism.MainNotions.S.LocNG.IsUnitO (Z.M p) ((D.s.atP p).ιE x)}.Finite := by
  have exists_nat_mul_integral {D : D7} (x : D.host.E) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : D.host.E) * x) := by
    have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have : Algebra.IsAlgebraic ℤ D.host.E := Algebra.IsAlgebraic.trans ℤ ℚ D.host.E
    obtain ⟨y, hy0, hy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x).exists_integral_multiple
  
    refine ⟨y.natAbs * y.natAbs, by simpa using hy0, ?_⟩
    have hsq : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := by
      rw [Nat.cast_mul]
      exact Int.natAbs_mul_self' y
    have e : ((y.natAbs * y.natAbs : ℕ) : D.host.E) * x = (y : D.host.E) * (y • x) := by
      rw [zsmul_eq_mul, ← mul_assoc]
      have hc : ((y.natAbs * y.natAbs : ℕ) : D.host.E) = (((y.natAbs * y.natAbs : ℕ) : ℤ) : D.host.E) :=
        (Int.cast_natCast _).symm
      rw [hc, hsq, Int.cast_mul]
    rw [e]
    have hyi : IsIntegral ℤ (y : D.host.E) := by
      simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ D.host.E y))
    exact hyi.mul hy
  
  have iota_mem_O {D : D7} (Z : LocDat D) (p : PlF D) (x : D.host.E) (n : ℕ)
      (hint : IsIntegral ℤ ((n : D.host.E) * x)) (hn : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal)) :
      (D.s.atP p).ιE x ∈ (Z.M p).L.O := by
    rw [(show (Z.M p).L.O = (D.s.atP p).O from (Z.agree p).2.2.2.1), (D.s.atP p).O_def]
    have : CharZero (D.s.atP p).Fp := (D.s.atP p).char0
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hn (by simp)
    have hcn : (D.s.atP p).ιF (n : D.host.F) = (n : (D.s.atP p).Fp) := map_natCast _ n
    have hc0 : (n : (D.s.atP p).Fp) ≠ 0 := by exact_mod_cast hn0
  
    have hv : p.valuation D.host.F (n : D.host.F) = 1 := by
      have := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
        (v := p) (K := D.host.F) (r := (n : 𝓞 D.host.F))).mpr hn
      rwa [map_natCast] at this
    have hle : (1 : (D.s.atP p).Fp) ≤ᵥ (n : (D.s.atP p).Fp) := by
      have := ((D.s.atP p).val 1 (n : D.host.F)).mpr (by rw [hv, map_one])
      rwa [map_one, hcn] at this
    have hinv : (n : (D.s.atP p).Fp)⁻¹ ∈ (ValuativeRel.valuation (D.s.atP p).Fp).integer := by
      rw [Valuation.mem_integer_iff, map_inv₀]
      have h1 := (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (D.s.atP p).Fp) 1
        (n : (D.s.atP p).Fp)).mp hle
      rw [map_one] at h1
      exact inv_le_one_of_one_le₀ h1
    have hx : (D.s.atP p).ιE x = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (n : (D.s.atP p).Fp)⁻¹ *
        (D.s.atP p).ιE ((n : D.host.E) * x) := by
      have hE : (n : D.host.E) = algebraMap D.host.F D.host.E (n : D.host.F) := (map_natCast _ n).symm
      rw [map_mul, hE, (D.s.atP p).compat, hcn, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
    rw [hx]
    refine IsIntegral.mul ?_ ?_
    · exact isIntegral_algebraMap (R := (ValuativeRel.valuation (D.s.atP p).Fp).integer) (x := ⟨(n : (D.s.atP p).Fp)⁻¹, hinv⟩)
    · exact (hint.map (D.s.atP p).ιE.toIntAlgHom).tower_top
  
  intro D Z x hx
  obtain ⟨n, hn0, hn⟩ := exists_nat_mul_integral x
  obtain ⟨m, hm0, hm⟩ := exists_nat_mul_integral x⁻¹

  have hI : Ideal.span {((n * m : ℕ) : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast Nat.mul_ne_zero hn0 hm0
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hnm
  apply hp
  have hn' : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal) := fun h => hnm (by
    push_cast
    exact Ideal.mul_mem_right _ _ h)
  have hm' : ¬ ((m : 𝓞 D.host.F) ∈ p.asIdeal) := fun h => hnm (by
    push_cast
    exact Ideal.mul_mem_left _ _ h)
  refine ⟨iota_mem_O Z p x n hn hn', (D.s.atP p).ιE x⁻¹, iota_mem_O Z p x⁻¹ m hm hm', ?_⟩
  rw [← map_mul, mul_inv_cancel₀ hx, map_one]
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocSplitFinite

theorem finite_resChar_eq (F : Type) [Field F] [NumberField F] (l : ℕ) (hl : l ≠ 0) :
    {p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) | Formalism.MainNotions.S.Loc.resChar p = l}.Finite := by
  have hx : ((l : 𝓞 F)) ≠ 0 := Nat.cast_ne_zero.2 hl
  have hI : Ideal.span {((l : 𝓞 F))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  unfold Formalism.MainNotions.S.Loc.resChar at hp
  rw [← hp]
  exact ringChar.Nat.cast_ringChar

theorem split_finite : ∀ (D : D7) (Z : LocDat D), {p : PlF D | (Z.M p).split ≠ none}.Finite := by
  intro D Z
  have h0 := finite_resChar_eq D.host.F (D.host.g 0) (D.host.g_prime 0).ne_zero
  have h1 := finite_resChar_eq D.host.F (D.host.g 1) (D.host.g_prime 1).ne_zero
  refine (h0.union h1).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  have hs : (D.s.atP p).split.isSome := by
    have ha := (Z.agree p).2.2.2.2.2
    revert ha
    cases h : (Z.M p).split with
    | none => exact absurd h hp
    | some g =>
      cases h' : (D.s.atP p).split with
      | none => intro ha; exact ha.elim
      | some sg => intro _; rfl
  have hm := (D.s_split p).1 hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · exact Or.inl hm
  · exact Or.inr hm

end GlobalTheory.LocSplitFinite
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

namespace GlobalTheory.LocDiffGen

variable {D : D7}

theorem iF_int (p : PlF D) (a : 𝓞 D.host.F) :
    (D.s.atP p).ιF (a : D.host.F) ∈ 𝒪[(D.s.atP p).Fp] := by
  have h1 : (D.s.atP p).ιF (a : D.host.F) ≤ᵥ (D.s.atP p).ιF 1 := by
    rw [(D.s.atP p).val, map_one]
    exact p.valuation_le_one (K := D.host.F) a
  rw [map_one, Valuation.Compatible.vle_iff_le (v := valuation (D.s.atP p).Fp), map_one] at h1
  exact (Valuation.mem_integer_iff _ _).2 h1

theorem dual_sub (Z : LocDat D) (p : PlF D) (z : (D.s.atP p).Fp)
    (hz : haveI := (D.s.atP p).ellPrime; ∀ c ∈ 𝒪[(D.s.atP p).Fp],
      ‖Algebra.trace ℚ_[Loc.resChar p] (D.s.atP p).Fp (c * z)‖ ≤ 1) :
    Z.δ p * z ∈ 𝒪[(D.s.atP p).Fp] := by
  haveI : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime
  obtain ⟨-, hδ, -, hO, hpsi, -⟩ := Z.agree p
  have hx : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * z) ∈ (Z.M p).L.O := by
    rw [← (Z.M p).L.additive_character_dual_ring]
    intro y hy
    rw [hO] at hy
    rw [hpsi]
    have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * z) * y *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)⁻¹ = y * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep z := by
      have e2 : Z.δ p * z * (Z.δ p)⁻¹ = z := by field_simp
      rw [← e2, map_mul (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep) (Z.δ p * z) (Z.δ p)⁻¹, e2]
      ring
    rw [e]
    refine (PI.LocDualGen.Top.psi_tower PI.LocDualGen.Psi.addCharKernel (D.s.atP p) _).2 ?_
    rw [map_neg, PI.LocDualGen.Top.tr_smul, map_neg, norm_neg]
    exact hz _ (PI.UnitaryGroupMassFormula.CntFormula.DeltaC.trace_mem (D.s.atP p) hy)
  rw [hO, (D.s.atP p).O_def] at hx
  have hi : IsIntegral 𝒪[(D.s.atP p).Fp] (Z.δ p * z) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[(D.s.atP p).Fp] (D.s.atP p).Fp (D.s.atP p).Ep)
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective).1 hx
  exact PI.UnitaryGroupMassFormula.CntFormula.DeltaC.mem_of_isIntegral_fp (D.s.atP p) hi

theorem diff_sub (Z : LocDat D) (p : PlF D) (x : 𝓞 D.host.F) (hx : x ∈ differentIdeal ℤ (𝓞 D.host.F)) :
    (Z.δ p)⁻¹ * (D.s.atP p).ιF (x : D.host.F) ∈ 𝒪[(D.s.atP p).Fp] := by
  obtain ⟨t, ht, hne, -, hinv⟩ := PI.CntNotIntW.locDiff_of PI.CntNotIntW.trace_dual_lattice
    (PI.CntNotIntW.dualApprox_of PI.CntNotIntW.small_powers_bound PI.CntNotIntW.tensorLiftSurjective)
    PI.CntNotIntW.small_powers_bound D Z.δ Z.M Z.agree p
  have hB := PI.CntNotIntW.dual_mul_different_integral D t ht x hx
  let w : 𝓞 D.host.F := ⟨_, (mem_integralClosure_iff ℤ D.host.F).2 hB⟩
  have hw : (D.s.atP p).ιF (w : D.host.F) ∈ 𝒪[(D.s.atP p).Fp] := iF_int p w
  have hw' : (D.s.atP p).ιF (w : D.host.F) = (D.s.atP p).ιF t * (D.s.atP p).ιF (x : D.host.F) := by
    rw [← map_mul]; rfl
  have ht0 : (D.s.atP p).ιF t ≠ 0 := right_ne_zero_of_mul hne
  have hδ0 : Z.δ p ≠ 0 := left_ne_zero_of_mul hne
  have e : (Z.δ p)⁻¹ * (D.s.atP p).ιF (x : D.host.F) =
      (D.s.atP p).ιF (w : D.host.F) * (Z.δ p * (D.s.atP p).ιF t)⁻¹ := by
    rw [hw']; field_simp
  rw [e]
  exact mul_mem hw hinv

theorem dual_glob (Z : LocDat D) (p : PlF D) (t : D.host.F)
    (ht : ∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (t * a) = n) :
    Z.δ p * (D.s.atP p).ιF t ∈ 𝒪[(D.s.atP p).Fp] := by
  haveI : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime
  haveI := (D.s.atP p).lf
  exact dual_sub Z p _ (fun c hc => trace_dual_local D.host.F p (D.s.atP p).Fp (D.s.atP p).qlCont
    (D.s.atP p).qlFin (D.s.atP p).ιF (D.s.atP p).dense (D.s.atP p).val t ht c hc)

theorem span_different_eq : ∀ (D : D7) (Z : LocDat D) (p : PlF D), Submodule.span (Z.M p).L.O ((fun x : 𝓞 D.host.F => (D.s.atP p).ιE (algebraMap D.host.F D.host.E x)) '' (differentIdeal ℤ (𝓞 D.host.F) : Set (𝓞 D.host.F))) = Submodule.span (Z.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)} := by
  intro D Z p
  obtain ⟨-, hδ, -, hO, -, -⟩ := Z.agree p
  have hmem : ∀ c ∈ 𝒪[(D.s.atP p).Fp], algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (Z.M p).L.O := by
    intro c hc; rw [hO]; exact PI.CntNotIntW.algMap_mem_O D p c hc
  have hf : ∀ x : 𝓞 D.host.F, (D.s.atP p).ιE (algebraMap D.host.F D.host.E x) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (x : D.host.F)) :=
    fun x => (D.s.atP p).compat _
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨⟨_, hmem _ (diff_sub Z p x hx)⟩, ?_⟩
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((Z.δ p)⁻¹ * (D.s.atP p).ιF (x : D.host.F)) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) = _
    rw [← map_mul]
    show _ = (D.s.atP p).ιE (algebraMap D.host.F D.host.E (x : D.host.F))
    rw [hf]
    congr 1
    field_simp
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    set N := Submodule.span (Z.M p).L.O ((fun x : 𝓞 D.host.F => (D.s.atP p).ιE (algebraMap D.host.F D.host.E x)) '' (differentIdeal ℤ (𝓞 D.host.F) : Set (𝓞 D.host.F))) with hN
    have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0 := one_ne_zero
    have hIJ : ((differentIdeal ℤ (𝓞 D.host.F) : Ideal (𝓞 D.host.F)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) *
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) = 1 := by
      rw [coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := D.host.F) (B := 𝓞 D.host.F)]
      exact inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ h10)
    have key : ∀ y : D.host.F, y ∈ (((differentIdeal ℤ (𝓞 D.host.F) : Ideal (𝓞 D.host.F)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) *
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)) →
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * (D.s.atP p).ιF y) ∈ N := by
      intro y hy
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro m hm n hn
        obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
        have hn' := (FractionalIdeal.mem_dual h10).1 hn
        have ht : ∀ a : 𝓞 D.host.F, ∃ k : ℤ, Algebra.trace ℚ D.host.F (n * a) = k := by
          intro a
          obtain ⟨k, hk⟩ := hn' _ ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
          exact ⟨k, by rw [← Algebra.traceForm_apply, ← hk]; simp⟩
        have hc := dual_glob Z p n ht
        have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F x * n)) =
            (⟨_, hmem _ hc⟩ : (Z.M p).L.O) • (D.s.atP p).ιE (algebraMap D.host.F D.host.E (x : D.host.F)) := by
          rw [hf, Subring.smul_def]
          show _ = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * (D.s.atP p).ιF n) * _
          rw [← map_mul, map_mul (D.s.atP p).ιF]
          congr 1
          show _ = _ * (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F x)
          ring
        rw [e]
        exact N.smul_mem _ (Submodule.subset_span ⟨x, hx, rfl⟩)
      · intro a b ha hb
        rw [map_add (f := _), mul_add, map_add (f := _)]
        exact N.add_mem ha hb
    have h1 := key 1 (by rw [hIJ]; exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩)
    have e1 : Z.δ p * (D.s.atP p).ιF 1 = Z.δ p := by rw [map_one, mul_one]
    rw [e1] at h1
    exact h1

end GlobalTheory.LocDiffGen
end
end

section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

theorem _root_.GlobalTheory.T.coveringRadius_hom_subquotient_sublattice : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (A S R : Submodule (𝓞 K) (Fin n → K)) (lo hi : ℝ), (∀ w, IsUnit (X w).det) → A.FG → IsSat (realize (Pi.basisFun K (Fin n)) X) A S → R.FG → 0 < lo → 0 < hi → (∀ N, S < N → N ≤ A → lo ≤ Formalism.HN.sizeQ (Pi.basisFun K (Fin n)) X N S) → Formalism.HN.largestSize (Pi.basisFun K (Fin n)) X R ≤ hi → ∀ T : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ w, ∀ y ∈ S, T w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y = 0) → (∀ w, ∀ y ∈ A, T w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K)))) → ∃ φ : Matrix (Fin n) (Fin n) K, (∀ y ∈ S, φ *ᵥ y = 0) ∧ (∀ y ∈ A, φ *ᵥ y ∈ R) ∧ ∃ D : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ w, ∀ y ∈ A, D w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y = (T w - (X w)⁻¹ * φ.map w.embedding * X w) *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y) ∧ Real.sqrt (∑ w, Formalism.REAL.hs (D w)) ≤ ((rkK A : ℝ) - rkK S) * rkK R * Real.sqrt (Formalism.HN.nPl K) * |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) * hi / (2 * lo) := by
  first | exact @GlobalTheory.SubquotCover.subquot_cover | exact GlobalTheory.SubquotCover.subquot_cover | (intros; apply GlobalTheory.SubquotCover.subquot_cover <;> assumption)
end

section

open Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.unipotentRadical_isotropicFlag_moves_step_into_prev : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r) (n : V ≃ₗ[E] V), n ∈ Fr.N → ∀ j : ℕ, j ≤ r → ∀ v ∈ Fr.Fj j, n v - v ∈ Fr.Fj (j - 1) ∧ n.symm v - v ∈ Fr.Fj (j - 1) := by
  first | exact @GlobalTheory.unipRadical_moves_step_into_prev | exact GlobalTheory.unipRadical_moves_step_into_prev | (intros; apply GlobalTheory.unipRadical_moves_step_into_prev <;> assumption)
end
