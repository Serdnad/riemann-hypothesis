module

public import Formalism.LocalToGlobal.InertKernelTheory.Bundle001
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Bundle001
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle006
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.LeadingConstantNeZero
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PowerSeriesEmbedding
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SqrtInUnramifiedCompletion
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TransportFirstLevel
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle003
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle005
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelConditionEquivalent
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.HalfTorsionNotMemCmLattice
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticDedekindZeta.GenBase
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticInvariants.QuadPolyIrreducible
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.HalfPeriodStandardCM
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IsTorsionPointStandardCM
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open NumberField Formalism.BasicNotions
open scoped Pointwise

namespace Formalism.L2.KerInert.CcGen

variable {K : Type} [Field K] [NumberField K]

theorem coprime_absNorm_of_not_le {p : ℕ} (hp : p.Prime) (hP : (Ideal.span {(p : 𝓞 K)}).IsMaximal)
    {I : Ideal (𝓞 K)} (hI : ¬ I ≤ Ideal.span {(p : 𝓞 K)}) : Nat.Coprime (Ideal.absNorm I) p := by
  have hsup : I ⊔ Ideal.span {(p : 𝓞 K)} = ⊤ := by
    by_contra h
    exact hI (le_sup_left.trans (hP.eq_of_le h le_sup_right).ge)
  have h1 : (1 : 𝓞 K) ∈ I ⊔ Ideal.span {(p : 𝓞 K)} := hsup ▸ Submodule.mem_top
  obtain ⟨i, hi, z, hz, hiz⟩ := Submodule.mem_sup.mp h1
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  have hunit : Ideal.Quotient.mk I y * (p : 𝓞 K ⧸ I) = 1 := by
    have := congrArg (Ideal.Quotient.mk I) hiz
    rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr hi, zero_add, map_mul, map_one, map_natCast] at this
    exact this
  have hI0 : I ≠ ⊥ := fun h => hI (h ▸ bot_le)
  have hc : Nat.card (𝓞 K ⧸ I) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 K ⧸ I) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Ideal.absNorm_eq_zero_iff.not.mpr hI0)
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ I) p (hc ▸ hdvd)
  have hpx : (p : 𝓞 K ⧸ I) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  apply hx0
  calc x = (Ideal.Quotient.mk I y * (p : 𝓞 K ⧸ I)) * x := by rw [hunit, one_mul]
    _ = Ideal.Quotient.mk I y * ((p : 𝓞 K ⧸ I) * x) := mul_assoc _ _ _
    _ = 0 := by rw [hpx, mul_zero]

theorem factor_inert {p : ℕ} (hp : p.Prime) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime)
    (hP0 : Ideal.span {(p : 𝓞 K)} ≠ ⊥) {cc : Ideal (𝓞 K)} (hcc : cc ≠ ⊥) :
    ∃ (k : ℕ) (cc' : Ideal (𝓞 K)), cc = Ideal.span {(p : 𝓞 K) ^ k} * cc' ∧
      Nat.Coprime (Ideal.absNorm cc') p := by
  have hpr : Prime (Ideal.span {(p : 𝓞 K)}) := Ideal.prime_of_isPrime hP0 hP
  obtain ⟨k, cc', hnd, heq⟩ :=
    WfDvdMonoid.max_power_factor (by rwa [Ideal.zero_eq_bot]) hpr.irreducible (a₀ := cc)
  refine ⟨k, cc', by rw [heq, Ideal.span_singleton_pow], ?_⟩
  exact coprime_absNorm_of_not_le hp (hP.isMaximal hP0) (fun h => hnd (Ideal.dvd_iff_le.mpr h))

end Formalism.L2.KerInert.CcGen

namespace Formalism.L2.KerInert

open Formalism.MainNotions

theorem lamOf_span_mul (D : D7) (cc : Ideal (𝓞 D.host.K)) (a : 𝓞 D.host.K) (δ : ℂ) :
    TaylorLogMetric.lamOf D (Ideal.span {a} * cc) δ = TaylorLogMetric.lamOf D cc (δ * D.host.φ₀ ((a : D.host.K) : D.host.E)) := by
  unfold TaylorLogMetric.lamOf
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by simp only [map_mul, MulMemClass.coe_mul]; ring⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨a * z, ⟨z, hz, rfl⟩, by simp only [map_mul, MulMemClass.coe_mul]; ring⟩

theorem lamOf_smul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    TaylorLogMetric.lamOf D cc δ = δ • TaylorLogMetric.lamOf D cc 1 := by
  unfold TaylorLogMetric.lamOf
  change _ = AddSubgroup.map (DistribSMul.toAddMonoidHom ℂ δ) _
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_image, one_mul]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩; exact ⟨c, hc, rfl⟩

theorem discr_smul_eq_inv_pow_twelve_mul (Λ : AddSubgroup ℂ) (c : ℂ) (hc : c ≠ 0) :
    TaylorLogMetric.discr (c • Λ) = (c ^ 12)⁻¹ * TaylorLogMetric.discr Λ :=
  Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discr_smul Λ c hc

theorem curve_ideal_prime : CcPrime := by
  intro D cc δ hcc hδ p hpF hj
  have hp := hpF.out
  have hq := quadK D.host
  have hK2 := PI.UnitaryGroupMassFormula.ClassNumImQInv.finrank_two hq
  have hP : (Ideal.span {(p : 𝓞 D.host.K)}).IsPrime :=
    isPrime_span_of_jacobi_neg_one _ hK2 _ D.host.d p hq.2.2.2.1 hp hj
  have hP0 : Ideal.span {(p : 𝓞 D.host.K)} ≠ ⊥ :=
    PI.ClassNumImQ.ZetaNonvanishing₂.ne_bot_of_absNorm (PI.ClassNumImQ.ZetaNonvanishing₂.absNorm_span_two hK2 p)
      (pow_ne_zero 2 hp.ne_zero)
  obtain ⟨k, cc', heq, hcop⟩ := CcGen.factor_inert hp hP hP0 hcc.1
  have hpk : D.host.φ₀ ((((p : 𝓞 D.host.K) ^ k : 𝓞 D.host.K) : D.host.K) : D.host.E) = (p : ℂ) ^ k := by
    simp
  have hlam : ∀ e : ℂ, TaylorLogMetric.lamOf D cc e = TaylorLogMetric.lamOf D cc' (e * (p : ℂ) ^ k) := by
    intro e; rw [heq, lamOf_span_mul, hpk]
  have hne : cc' ≠ ⊥ := by
    rintro rfl; apply hcc.1; rw [heq, Ideal.mul_bot]
  have hnorm : Ideal.absNorm cc' ∣ Ideal.absNorm cc := by
    rw [heq, map_mul]; exact dvd_mul_left _ _
  refine ⟨cc', δ * (p : ℂ) ^ k, ⟨hne, Nat.Coprime.coprime_dvd_left hnorm hcc.2⟩, ?_, hcop, hlam δ⟩
  have hp0 : ((p : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  unfold TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice at hδ ⊢
  rw [hlam 1, one_mul, lamOf_smul D cc' ((p : ℂ) ^ k), discr_smul_eq_inv_pow_twelve_mul _ _ hp0] at hδ
  rw [mul_pow, hδ]
  field_simp

end Formalism.L2.KerInert
end
end

section

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension omegaK)

namespace FrFix

variable {p : ℕ} [Fact p.Prime]

theorem not_sq (d : ℕ) (hj : jacobiSym (-(d : ℤ)) p = -1) : ¬ ∃ a : ZMod p, a ^ 2 = -(d : ZMod p) := by
  have hleg : legendreSym p (-(d : ℤ)) = -1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hj
  have hns : ¬ IsSquare (((-(d : ℤ)) : ℤ) : ZMod p) := (legendreSym.eq_neg_one_iff (p := p)).1 hleg
  rintro ⟨a, ha⟩
  apply hns
  refine ⟨a, ?_⟩
  push_cast
  rw [← ha]
  ring

theorem fixed_mem_closure (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (hσ : Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ) (z : MaximalUnramifiedExtension p)
    (hz : σ z = z) : (z : ℂ_[p]) ∈ closure (Set.range fun q : ℚ => (q : ℂ_[p])) := by
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖z‖ hp1
  have hpk : ‖((p : MaximalUnramifiedExtension p) ^ k)‖ = ((p : ℝ) ^ k)⁻¹ := by rw [norm_pow, hσ.2.2.1, inv_pow]
  have hpkpos : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  obtain ⟨w, hw⟩ : ∃ w : MaximalUnramifiedExtension p, w = (p : MaximalUnramifiedExtension p) ^ k * z := ⟨_, rfl⟩
  have hw1 : ‖w‖ ≤ 1 := by
    rw [hw, norm_mul, hpk, inv_mul_le_iff₀ hpkpos, mul_one]
    exact hk.le
  have hσw : σ w = w := by rw [hw, map_mul, map_pow, map_natCast, hz]
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hε' : 0 < ε * ((p : ℝ) ^ k)⁻¹ := by positivity
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε' (inv_lt_one_of_one_lt₀ hp1)
  obtain ⟨n, hn⟩ := Formalism.L2.Th1.D.fixedIsLimit (MaximalUnramifiedExtension p) p σ hσ w hw1 hσw j
  refine ⟨((n : ℚ) / (p : ℚ) ^ k : ℚ), ⟨_, rfl⟩, ?_⟩
  have hpk0 : ((p : MaximalUnramifiedExtension p) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hq : ((((n : ℚ) / (p : ℚ) ^ k : ℚ)) : ℂ_[p]) = ((((n : ℚ) / (p : ℚ) ^ k : ℚ) : MaximalUnramifiedExtension p) : ℂ_[p]) :=
    (map_ratCast (MaximalUnramifiedExtension p).subtype _).symm
  have e : z - ((((n : ℚ) / (p : ℚ) ^ k : ℚ)) : MaximalUnramifiedExtension p) = ((p : MaximalUnramifiedExtension p) ^ k)⁻¹ * (w - n) := by
    rw [hw]
    push_cast
    field_simp
  rw [hq, ← Subtype.dist_eq, dist_eq_norm, e, norm_mul, norm_inv, hpk, inv_inv]
  calc (p : ℝ) ^ k * ‖w - n‖ ≤ (p : ℝ) ^ k * ((p : ℝ) ^ j)⁻¹ := by gcongr
    _ = (p : ℝ) ^ k * ((p : ℝ)⁻¹) ^ j := by rw [inv_pow]
    _ < (p : ℝ) ^ k * (ε * ((p : ℝ) ^ k)⁻¹) := by gcongr
    _ = ε := by field_simp

end FrFix

theorem conjugation_fixed_closure : FixConj := by
  intro D p _ h5 hj lam ι hι σ hσ y hy
  have hsq : Squarefree D.host.d := (Nat.prime_iff.mp D.host.hyp.2.1).squarefree
  have h4 : D.host.d % 4 = 3 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discriminant_mod_four D
  obtain ⟨hwm, hws⟩ := Formalism.L2.Th1.D.sqrt_in_unramified_completion D.host.d hsq h4 p h5 (FrFix.not_sq D.host.d hj) ι
  obtain ⟨w, hw⟩ : ∃ w : MaximalUnramifiedExtension p, (w : ℂ_[p]) = ι (omegaK D.host.d) := ⟨⟨_, hwm⟩, rfl⟩
  have hσw : σ w = 1 - w := hws σ hσ w hw
  have hLI := Formalism.L2.KerInert.lamCIota p lam ι hι
  have hlc : ∀ z : D.host.E, lamC lam (D.host.φ₀ z) = ι (D.host.φ₀ z) :=
    fun z => hLI.1 _ (Formalism.MainNotions.Ext.test_vector_mem_schwartz_bruhat D z)
  have hsK : D.host.sqrtMinusD ∈ D.host.K := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_mem D
  have hx2 : (D.host.φ₀ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
    rw [← map_pow, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrtE_sq D, map_neg, map_natCast]
  have hom : (2 * omegaK D.host.d - 1) ^ 2 = -(D.host.d : ℂ) := by
    unfold omegaK
    have hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
    linear_combination (-1 : ℂ) * hsq + (((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2) * Complex.I_sq

  have c2 : ((2 : MaximalUnramifiedExtension p) : ℂ_[p]) = 2 := map_ofNat (MaximalUnramifiedExtension p).subtype 2
  obtain ⟨rK, hrK, hσr⟩ : ∃ rK : MaximalUnramifiedExtension p, (rK : ℂ_[p]) = ι (D.host.φ₀ D.host.sqrtMinusD) ∧ σ rK = -rK := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx2.trans hom.symm) with h | h
    · refine ⟨2 * w - 1, ?_, ?_⟩
      · rw [h, map_sub, map_mul, map_ofNat, map_one, ← hw]; push_cast; rw [c2]
      · rw [map_sub, map_mul, map_ofNat, map_one, hσw]; ring
    · refine ⟨1 - 2 * w, ?_, ?_⟩
      · rw [h, map_neg, map_sub, map_mul, map_ofNat, map_one, ← hw]; push_cast; rw [c2]; ring
      · rw [map_sub, map_mul, map_ofNat, map_one, hσw]; ring
  have hd0 : (D.host.d : ℂ_[p]) ≠ 0 := by exact_mod_cast (D.host.hyp.2.1).ne_zero
  have hr0 : rK ≠ 0 := by
    intro h
    have h' : ((rK : ℂ_[p])) ^ 2 = 0 := by rw [h]; simp
    rw [hrK, ← map_pow, hx2, map_neg, map_natCast, neg_eq_zero] at h'
    exact hd0 h'

  have h2 : (2 : MaximalUnramifiedExtension p) ≠ 0 := two_ne_zero
  obtain ⟨u, hu⟩ : ∃ u : MaximalUnramifiedExtension p, u = (y + σ y) / 2 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : MaximalUnramifiedExtension p, v = (y - σ y) / (2 * rK) := ⟨_, rfl⟩
  have hσu : σ u = u := by rw [hu, map_div₀, map_add (f := _), hy, map_ofNat]; ring
  have hσv : σ v = v := by
    rw [hv, map_div₀, map_sub, map_mul, hy, hσr, map_ofNat]
    field_simp
    ring
  have hyuv : y = u + v * rK := by
    rw [hu, hv]
    field_simp
    ring
  have cu := FrFix.fixed_mem_closure σ hσ u hσu
  have cv := FrFix.fixed_mem_closure σ hσ v hσv
  have hyc : (y : ℂ_[p]) = (u : ℂ_[p]) + (v : ℂ_[p]) * (rK : ℂ_[p]) := by rw [hyuv]; push_cast; rfl
  refine ⟨?_, ?_⟩
  · have hcont : Continuous fun ab : ℂ_[p] × ℂ_[p] => ab.1 + ab.2 * (rK : ℂ_[p]) := by fun_prop
    have hmem : ((u : ℂ_[p]), (v : ℂ_[p])) ∈ closure ((Set.range fun q : ℚ => (q : ℂ_[p])) ×ˢ
        (Set.range fun q : ℚ => (q : ℂ_[p]))) := by
      rw [closure_prod_eq]; exact ⟨cu, cv⟩
    have hmaps : Set.MapsTo (fun ab : ℂ_[p] × ℂ_[p] => ab.1 + ab.2 * (rK : ℂ_[p]))
        ((Set.range fun q : ℚ => (q : ℂ_[p])) ×ˢ (Set.range fun q : ℚ => (q : ℂ_[p])))
        (Set.range fun x : D.host.K => lamC lam (D.host.φ₀ (x : D.host.E))) := by
      rintro ⟨_, _⟩ ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
      refine ⟨(a : D.host.K) + (b : D.host.K) * ⟨D.host.sqrtMinusD, hsK⟩, ?_⟩
      have e : (((a : D.host.K) + (b : D.host.K) * ⟨D.host.sqrtMinusD, hsK⟩ : D.host.K) : D.host.E) =
          (a : D.host.E) + (b : D.host.E) * D.host.sqrtMinusD := by
        push_cast; rfl
      simp only
      rw [e, hlc, hrK, map_add (f := _), map_mul, map_ratCast, map_ratCast, map_add (f := _), map_mul, map_ratCast, map_ratCast]
    have hh := map_mem_closure hcont hmem hmaps
    rw [hyc]
    exact hh
  · intro σp hσp
    have hσc : Continuous σp :=
      AddMonoidHomClass.continuous_of_bound σp 1 (fun z => by rw [hσp.2 z, one_mul])
    have hfixS : closure (Set.range fun q : ℚ => (q : ℂ_[p])) ⊆ {z | σp z = z} :=
      closure_minimal (by rintro _ ⟨q, rfl⟩; exact map_ratCast σp q) (isClosed_eq hσc continuous_id)
    have hu' : σp u = u := hfixS cu
    have hv' : σp v = v := hfixS cv
    have hr' : σp (rK : ℂ_[p]) = -(rK : ℂ_[p]) := by
      have h := hσp.1 ⟨D.host.sqrtMinusD, hsK⟩
      have hc : D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := Formalism.BasicNotions.Examples₂.conj_bE D.host
      change σp (lamC lam (D.host.φ₀ D.host.sqrtMinusD)) =
        lamC lam (D.host.φ₀ (D.host.conj D.host.sqrtMinusD)) at h
      rw [hc, hlc, hlc, map_neg, map_neg, ← hrK] at h
      exact h
    rw [hyc, map_add (f := _), map_mul, hu', hv', hr', hyuv, map_add (f := _), map_mul, hσu, hσv, hσr]
    push_cast
    ring

end Formalism.L2.KerInert
end
end

section

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert

open Formalism.MainNotions Formalism.L2.Ker
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (CmOK cmL matH stdH stdLat pow4 imgLat relIdx StdData Th alphaQ kernel4 tens4 stdChar)
open Formalism.L2.Th1.Top (IsLTNorm)

namespace ReBase

theorem odd_norm {D : D7} {cc : Ideal (𝓞 D.host.K)} (hcc : TaylorLogMetric.IsCurveIdeal D cc) : Odd (Ideal.absNorm cc) := by
  have hc2 : Nat.Coprime (Ideal.absNorm cc) 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 _) hcc.2
  rcases Nat.even_or_odd (Ideal.absNorm cc) with he | ho
  · exact absurd (Nat.Coprime.coprime_dvd_left (even_iff_two_dvd.1 he) hc2) (by decide)
  · exact ho

theorem cm_change_of_base : CmReBase := by
  intro D cc δ B hcc hδ
  obtain ⟨a₀, g, b₀, c₀, ha, hd, hl, hcm, hN, -, hlat⟩ := curve_lattice_compatible D cc δ hcc.1 (odd_norm hcc) hδ
  have hlat' : (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ := hlat.symm
  refine ⟨a₀, g, b₀, c₀, ha, hd, hl, hcm, hN, hlat', KS.isTorsionPoint_standard_CM a₀ b₀ c₀ ha hd _ hl hcm hlat', ?_⟩
  have e : (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = 1 - Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
    rw [KS.theta_val']; ring
  have h := KS.half_period_unique_CM a₀ b₀ c₀ D.host.d ha hd _ hl hcm (B.ω₀ / 2)
    ((KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat' _).1 B.t0.1)
    (by rw [← KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat', KS.theta_val']; exact B.t0.2.1)
    (by rw [← KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat', ← e]; exact B.t0.2.2)
  rw [KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat',
    show (B.ω₀ - (g : ℂ) * δ * a₀) / 2 = B.ω₀ / 2 - (g : ℂ) * δ * a₀ / 2 by ring]
  exact h

theorem isThMM_eq {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B B' : Base D cc δ) (hγ : B'.gC = B.gC)
    (hκ : B'.kappa = B.kappa) (hω : (B.ω₀ - B'.ω₀) / 2 ∈ B'.L.lattice) : B'.IsThMM = B.IsThMM := by
  have h := KS.lattice_eq B B'
  have e : IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa = IsThM B'.L B'.ω₀ B.cq B.lamM B.gC B.kappa := by
    funext θ
    unfold IsThM kernel4 Formalism.L2.Th1.H.F0 Formalism.L2.Th1.H.stdLat
    rw [KS.hOne_congr h, KS.stdH_congr h, KS.thetaNull_congr_lattice h hω (Base.half_not_mem B'), h]
  show IsThM B'.L B'.ω₀ B.cq B.lamM B'.gC B'.kappa = IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa
  rw [hγ, hκ, e]

theorem theta_change_of_base : ThMMReBase := by
  intro D cc δ B hcc
  obtain ⟨a₀, g, b₀, c₀, ha, hd, hl, hcm, hN, hlat, ht, hω⟩ := cm_change_of_base D cc δ B hcc (delta_ne_of_base B)
  have hω' : (B.ω₀ - (g : ℂ) * δ * a₀) / 2 ∈ (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice :=
    (KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat _).1 hω
  refine ⟨a₀, g, b₀, c₀, ha, hd, hl, KS.cmBase B a₀ b₀ c₀ ha hd ((g : ℂ) * δ) hl hcm hlat, hcm, hN,
    KS.cmBase_isCm B a₀ b₀ c₀ ha hd _ hl hcm hlat, KS.lattice_eq _ B, rfl, rfl, rfl,
    (KS.lattice_eq B (KS.cmBase B a₀ b₀ c₀ ha hd ((g : ℂ) * δ) hl hcm hlat)) ▸ hω',
    isThMM_eq B _ rfl rfl hω', (KS.thMM_reBase B _ hlat _ (KS.isTorsionPoint_standard_CM a₀ b₀ c₀ ha hd _ hl hcm hlat) hω').symm⟩

theorem stdLat_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : Type) : stdLat L n = stdLat L' n := by
  unfold Formalism.L2.Th1.H.stdLat; rw [h]

theorem isLTNorm_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 s2 ε : MaximalUnramifiedExtension l) : IsLTNorm l L ι g2 g3 s2 ε ↔ IsLTNorm l L' ι g2 g3 s2 ε := by
  obtain ⟨-, -, -, -, hs, -, -, h2, h3⟩ := Formalism.L2.Th1.F.latticeOnly L L' h
  unfold IsLTNorm
  rw [h2, h3, hs]

theorem th0Char_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) {ω₀ ω₀' : ℂ} (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice)
    {x : ℂ} (hx : x ∈ L'.lattice) : Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ x = Formalism.L2.Th1.F.thetaZeroCharacter L' ω₀' x := by
  obtain ⟨-, -, -, hA, -, -, -, -, -⟩ := Formalism.L2.Th1.F.latticeOnly L L' h
  obtain ⟨k, hk⟩ := Formalism.L2.Th1.F.altEInt L' x ((ω₀ - ω₀') / 2) hx hω
  have e0 : x * (starRingEnd ℂ) ω₀ / (Formalism.L2.Th1.F.area L' : ℂ) = x * (starRingEnd ℂ) ω₀' / (Formalism.L2.Th1.F.area L' : ℂ) +
      2 * (x * (starRingEnd ℂ) ((ω₀ - ω₀') / 2) / (Formalism.L2.Th1.F.area L' : ℂ)) := by
    simp only [map_div₀, map_sub, map_ofNat]; ring
  have e1 : Formalism.L2.Th1.F.altE L x ω₀ = Formalism.L2.Th1.F.altE L' x ω₀' + 2 * Formalism.L2.Th1.F.altE L' x ((ω₀ - ω₀') / 2) := by
    simp only [Formalism.L2.Th1.F.altE, Formalism.L2.Th1.F.herm, hA]
    rw [e0]
    simp [Complex.add_im, Complex.mul_im]
  unfold Formalism.L2.Th1.F.thetaZeroCharacter Formalism.L2.Th1.F.semiChar
  rw [h, e1, hk]
  congr 1
  rw [show ((Formalism.L2.Th1.F.altE L' x ω₀' + 2 * (k : ℝ) : ℝ) : ℂ) = (Formalism.L2.Th1.F.altE L' x ω₀' : ℂ) + (k : ℂ) * 2 by
    push_cast; ring]
  rw [mul_add, Complex.exp_add, show (Real.pi : ℂ) * Complex.I * ((k : ℂ) * 2) = (k : ℂ) * (2 * Real.pi * Complex.I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem stdData_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) {ω₀ ω₀' : ℂ} (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice)
    (hn : ω₀ / 2 ∉ L.lattice) {n : Type} [Fintype n] [DecidableEq n] {hh : Matrix n n ℂ} {Λ : AddSubgroup (n → ℂ)}
    {α : (n → ℂ) → ℂ} {β : (Fin 4 × n → ℂ) → ℂ} {g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)}
    (S : StdData L' ω₀' hh Λ α β g) : StdData L ω₀ hh Λ α β g := by
  have hS := KS.stdH_congr h (Fin 4 × n)
  have hL := stdLat_congr h (Fin 4 × n)
  refine ⟨?_, hn, ?_, S.alpha0, ?_, ?_, S.betaAlpha, ?_, ?_, ?_⟩
  · rw [h, show ω₀ = ω₀' + ((ω₀ - ω₀') / 2 + (ω₀ - ω₀') / 2) by ring]
    exact add_mem S.per (add_mem hω hω)
  · rw [hS]; exact S.isom
  · intro x hx
    have hx' : x ∈ stdLat L' (Fin 4 × n) := hL ▸ hx
    rw [S.betaStd x hx']
    unfold Formalism.L2.Th1.H.stdChar
    exact (Finset.prod_congr rfl fun i _ => th0Char_congr h hω (hx' i (Set.mem_univ i))).symm
  · rw [hS]; exact S.betaSemi
  · rw [hS]; exact S.selfDual
  · rw [hL]; exact S.idx₁
  · rw [hL]; exact S.idx₂

end ReBase

end Formalism.L2.KerInert
end
end
