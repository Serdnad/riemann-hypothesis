module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianLocalOfOrderFunction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1179
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Valuation.Integral
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DiagZEqNegAddY
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.PlaneSkew

variable {E : Type} [Field E] [NumberField E]

def lowLat {n n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n₁ → E) :=
  L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))

theorem mem_lowLat {n n₁ : ℕ} {ι : Matrix (Fin n) (Fin n₁) E} {L : Submodule (𝓞 E) (Fin n → E)} {u : Fin n₁ → E} :
    u ∈ lowLat ι L ↔ ι *ᵥ u ∈ L := Iff.rfl

def PrimAt (𝔓 : HeightOneSpectrum (𝓞 E)) {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E) : Prop :=
  (∀ s : E, s • x ∈ L → 𝔓.valuation E s ≤ 1) ∧ ∃ s : E, s • x ∈ L ∧ 𝔓.valuation E s = 1

end GlobalTheory.PlaneSkew
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

theorem GlobalTheory.adicEmbedding_integral_place (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] v.adicCompletion F) :
    (∀ a : 𝓞 E, Valued.v (τ a) ≤ 1) ∧ ∃ Q : Ideal (𝓞 E), Q.IsMaximal ∧ ∀ a : 𝓞 E, a ∈ Q ↔ Valued.v (τ a) < 1 := by
  set O := v.adicCompletionIntegers F
  have hv : (Valued.v : Valuation (v.adicCompletion F) _).Integers O := by
    have := Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)
    exact this
  have ha : ∀ a : 𝓞 E, Valued.v (τ a) ≤ 1 := by
    intro a
    have h1 : IsIntegral ℤ (τ a) := IsIntegral.map τ (NumberField.RingOfIntegers.isIntegral_coe a)
    have h2 : IsIntegral O (τ a) := h1.tower_top
    exact hv.mem_of_integral h2
  refine ⟨ha, ?_⟩
  let φ : 𝓞 E →+* O :=
    ((τ : E →+* v.adicCompletion F).comp (algebraMap (𝓞 E) E)).codRestrict O.toSubring
      (fun a => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 (ha a))
  have hmem : ∀ a : 𝓞 E, a ∈ (IsLocalRing.maximalIdeal O).comap φ ↔ Valued.v (τ a) < 1 := by
    intro a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one]
    change ¬ Valued.v (τ a) = 1 ↔ _
    exact ⟨fun h => lt_of_le_of_ne (ha a) h, fun h => ne_of_lt h⟩
  refine ⟨(IsLocalRing.maximalIdeal O).comap φ, ?_, hmem⟩
  apply Ideal.IsPrime.isMaximal inferInstance
  intro hbot
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hlt : Valued.v (algebraMap F (v.adicCompletion F) (π : F)) < 1 := by
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v π).2 hπ
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at this
    exact this
  have hne : (algebraMap (𝓞 F) (𝓞 E) π) ≠ 0 := by
    intro h
    apply hπ0
    apply FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)
    simpa using h
  apply hne
  have : algebraMap (𝓞 F) (𝓞 E) π ∈ (IsLocalRing.maximalIdeal O).comap φ := by
    rw [hmem]
    have e : ((algebraMap (𝓞 F) (𝓞 E) π : 𝓞 E) : E) = algebraMap F E (π : F) := by
      exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E π).symm.trans (IsScalarTower.algebraMap_apply (𝓞 F) F E π)
    rw [e, AlgHom.commutes]
    exact hlt
  rw [hbot] at this
  simpa using this
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SepBezout

theorem valuation_le_one_eventually {E : Type} [Field E] [NumberField E] (x : E) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, w.valuation E x ≤ 1 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal (𝓞 E)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  have h1 : w.valuation E (algebraMap (𝓞 E) E b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

theorem bezout_eventually : ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ u v : (w.adicCompletion E)[X],
      (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧ (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * P.map (algebraMap E (w.adicCompletion E)) + v * derivative (P.map (algebraMap E (w.adicCompletion E))) = 1 := by
  intro E _ _ P hP
  obtain ⟨u₀, v₀, h⟩ := hP
  have key : ∀ f : E[X], ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite,
      ∀ i, (f.map (algebraMap E (w.adicCompletion E))).coeff i ∈ w.adicCompletionIntegers E := by
    intro f
    filter_upwards [(Filter.eventually_all_finset f.support).2
      (fun i _ => valuation_le_one_eventually (f.coeff i))] with w hw i
    rw [Polynomial.coeff_map]
    by_cases hi : i ∈ f.support
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have := hw i hi
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
      exact this
    · rw [Polynomial.notMem_support_iff.1 hi, map_zero]
      exact zero_mem _
  filter_upwards [key u₀, key v₀] with w hu hv
  refine ⟨u₀.map (algebraMap E (w.adicCompletion E)), v₀.map (algebraMap E (w.adicCompletion E)), hu, hv, ?_⟩
  rw [Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add (f := _), h,
    Polynomial.map_one]

end GlobalTheory.BCT.SepBezout
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RootOpen


open Classical in
theorem finite_roots (E : Type) [Field E] [NumberField E] :
    {t : Eˣ | ∃ n : ℕ, 0 < n ∧ t ^ n = 1}.Finite := by
  have hF : Finite (NumberField.Units.torsion E) := inferInstance
  have hT : ((NumberField.Units.torsion E : Set (𝓞 E)ˣ)).Finite := Set.finite_coe_iff.1 hF
  refine (hT.image (Units.map (algebraMap (𝓞 E) E).toMonoidHom)).subset ?_
  rintro t ⟨n, hn, ht⟩
  have h1 : IsIntegral ℤ (t : E) := IsIntegral.of_pow hn (by rw [← Units.val_pow_eq_pow_val, ht]; exact isIntegral_one)
  have h2 : IsIntegral ℤ ((t⁻¹ : Eˣ) : E) :=
    IsIntegral.of_pow hn (by rw [← Units.val_pow_eq_pow_val, inv_pow, ht, inv_one]; exact isIntegral_one)
  let u : (𝓞 E)ˣ := ⟨⟨t, h1⟩, ⟨(t⁻¹ : Eˣ), h2⟩,
    NumberField.RingOfIntegers.ext (show (t : E) * ((t⁻¹ : Eˣ) : E) = 1 by simp),
    NumberField.RingOfIntegers.ext (show ((t⁻¹ : Eˣ) : E) * (t : E) = 1 by simp)⟩
  refine ⟨u, ?_, ?_⟩
  · show u ∈ CommGroup.torsion (𝓞 E)ˣ
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, ?_⟩)
    ext
    show ((t ^ n : Eˣ) : E) = 1
    simp [ht]
  · ext; rfl

variable {E : Type} [Field E] [NumberField E]

theorem val_eq_one_of_lt (w : HeightOneSpectrum (𝓞 E)) {z : w.adicCompletion E} (hz : Valued.v (z - 1) < 1) :
    Valued.v z = 1 := by
  have := Valuation.map_add_eq_of_lt_left (Valued.v) (x := (1 : w.adicCompletion E)) (y := z - 1) (by simpa using hz)
  simpa using this

def congOne (w : HeightOneSpectrum (𝓞 E)) (m : ℤ) (hm : m < 0) : Subgroup (w.adicCompletion E)ˣ where
  carrier := {z | Valued.v ((z : w.adicCompletion E) - 1) ≤ WithZero.exp m}
  one_mem' := by simp
  mul_mem' := by
    intro z u hz hu
    have hz' : Valued.v ((z : w.adicCompletion E) - 1) ≤ WithZero.exp m := hz
    have hu' : Valued.v ((u : w.adicCompletion E) - 1) ≤ WithZero.exp m := hu
    have hlt : WithZero.exp m < 1 := by
      rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 hm
    have h1 := val_eq_one_of_lt w (hz'.trans_lt hlt)
    show Valued.v (((z * u : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) ≤ WithZero.exp m
    have e : ((z * u : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        (z : w.adicCompletion E) * ((u : w.adicCompletion E) - 1) + ((z : w.adicCompletion E) - 1) := by
      rw [Units.val_mul]; ring
    rw [e]
    refine Valuation.map_add_le _ ?_ hz'
    rw [map_mul, h1, one_mul]; exact hu'
  inv_mem' := by
    intro z hz
    have hz' : Valued.v ((z : w.adicCompletion E) - 1) ≤ WithZero.exp m := hz
    have hlt : WithZero.exp m < 1 := by
      rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 hm
    have h1 := val_eq_one_of_lt w (hz'.trans_lt hlt)
    show Valued.v (((z⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) ≤ WithZero.exp m
    have e : ((z⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        ((z⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) * (1 - (z : w.adicCompletion E)) := by
      rw [mul_sub, mul_one, Units.inv_mul]
    rw [e, map_mul, Valuation.map_sub_swap, Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one, one_mul]
    exact hz'

theorem isOpen_congOne (w : HeightOneSpectrum (𝓞 E)) (m : ℤ) (hm : m < 0) :
    IsOpen (congOne w m hm : Set (w.adicCompletion E)ˣ) :=
  (GlobalTheory.Mem.UnitOpen.isOpen_val_le w m).preimage (Units.continuous_val.sub continuous_const)

end GlobalTheory.RootOpen

namespace GlobalTheory.RootOpen

theorem exists_open_subgroup_no_roots : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ V : Subgroup (w.adicCompletion E)ˣ,
    IsOpen (V : Set (w.adicCompletion E)ˣ) ∧ ∀ t : Eˣ, (∃ n : ℕ, 0 < n ∧ t ^ n = 1) →
      Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom t ∈ V → t = 1 := by
  intro E _ _ w
  set S := {t : Eˣ | ∃ n : ℕ, 0 < n ∧ t ^ n = 1}
  have hL : ((fun t : Eˣ => WithZero.log (Valued.v ((algebraMap E (w.adicCompletion E) (t : E)) - 1))) ''
      (S \ {1})).Finite := ((finite_roots E).diff).image _
  obtain ⟨b, hb⟩ := hL.bddBelow
  refine ⟨congOne w (min b 0 - 1) (by omega), isOpen_congOne w _ _, fun t ht hV => ?_⟩
  by_contra h1
  have hmem := hb ⟨t, ⟨ht, h1⟩, rfl⟩
  have hne : Valued.v ((algebraMap E (w.adicCompletion E) (t : E)) - 1) ≠ 0 := by
    rw [Ne, map_eq_zero, sub_eq_zero, ← map_one (algebraMap E (w.adicCompletion E))]
    intro e
    exact h1 (Units.ext ((algebraMap E (w.adicCompletion E)).injective e))
  have hV' : Valued.v ((algebraMap E (w.adicCompletion E) (t : E)) - 1) ≤ WithZero.exp (min b 0 - 1) := hV
  rw [← WithZero.exp_log hne, WithZero.exp_le_exp] at hV'
  simp only at hmem
  omega

end GlobalTheory.RootOpen
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

namespace GlobalTheory.NonarchShell

theorem exists_compact_shell_nsmul : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (V : Set (Fin N → v.adicCompletion F)), V ∈ nhds 0 →
      ∃ K : Set (Fin N → v.adicCompletion F), IsCompact K ∧ (0 : Fin N → v.adicCompletion F) ∉ K ∧
        ∀ t, t ∉ V → ∃ n : ℕ, n • t ∈ K := by
  intro F _ _ v N V hV
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  set q : ℕ := Ideal.absNorm v.asIdeal with hqdef
  have hq0 : q ≠ 0 := by
    rw [hqdef, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hq1 : ‖(q : v.adicCompletion F)‖ < 1 := by
    have := (NumberField.FinitePlace.norm_lt_one_iff_mem F v ((q : 𝓞 F))).2 (Ideal.absNorm_mem _)
    rwa [map_natCast, map_natCast] at this
  have hqne : (q : v.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (v.adicCompletion F)) q]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hq0)
  have hqpos : 0 < ‖(q : v.adicCompletion F)‖ := norm_pos_iff.2 hqne
  have hsm : ∀ (m : ℕ) (t : Fin N → v.adicCompletion F), ‖m • t‖ = ‖(m : v.adicCompletion F)‖ * ‖t‖ := by
    intro m t
    rw [← Nat.cast_smul_eq_nsmul (v.adicCompletion F), norm_smul]
  refine ⟨{t | r * ‖(q : v.adicCompletion F)‖ ≤ ‖t‖ ∧ ‖t‖ ≤ r}, ?_, ?_, ?_⟩
  · refine (isCompact_closedBall (0 : Fin N → v.adicCompletion F) r).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    · intro t ht
      simpa [mem_closedBall_zero_iff] using ht.2
  · intro h
    have h1 := h.1
    rw [norm_zero] at h1
    exact absurd h1 (not_le.2 (mul_pos hr hqpos))
  · intro t ht
    have htr : r ≤ ‖t‖ := by
      by_contra hlt
      exact ht (hrV (mem_ball_zero_iff.2 (not_le.1 hlt)))
    have htpos : 0 < ‖t‖ := lt_of_lt_of_le hr htr
    have hex : ∃ k : ℕ, ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ < r := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hr htpos) hq1
      exact ⟨k, (lt_div_iff₀ htpos).1 hk⟩
    classical
    set k := Nat.find hex with hkdef
    have hk : ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ < r := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_mul] at hk
      exact absurd htr (not_le.2 hk)
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hjmin : ¬ ‖(q : v.adicCompletion F)‖ ^ j * ‖t‖ < r :=
      Nat.find_min hex (by omega)
    have hnorm : ‖(q ^ k) • t‖ = ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ := by
      rw [hsm, Nat.cast_pow, norm_pow]
    refine ⟨q ^ k, ?_, ?_⟩
    · show r * ‖(q : v.adicCompletion F)‖ ≤ ‖(q ^ k) • t‖
      rw [hnorm, hj, pow_succ]
      have := not_lt.1 hjmin
      nlinarith
    · show ‖(q ^ k) • t‖ ≤ r
      rw [hnorm]; exact hk.le

end GlobalTheory.NonarchShell
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntCop

theorem lift_of_val_le {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (Q : E[X]) (h : ∀ n, w.valuation E (Q.coeff n) ≤ 1) :
    ∃ Q₀ : (w.adicCompletionIntegers E)[X],
      Q₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) =
        Q.map (algebraMap E (w.adicCompletion E)) := by
  have : Q.map (algebraMap E (w.adicCompletion E)) ∈
      Polynomial.lifts (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    refine ⟨⟨algebraMap E (w.adicCompletion E) (Q.coeff n),
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_⟩, rfl⟩
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (Q.coeff n)).trans_le (h n)
  obtain ⟨Q₀, hQ₀⟩ := (Polynomial.mem_lifts _).1 this
  exact ⟨Q₀, hQ₀⟩

theorem finite_bad {E : Type} [Field E] [NumberField E] (Q : E[X]) :
    {w : HeightOneSpectrum (𝓞 E) | ¬ ∀ n, w.valuation E (Q.coeff n) ≤ 1}.Finite := by
  refine ((Finset.range (Q.natDegree + 1)).finite_toSet.biUnion
    fun n _ => HeightOneSpectrum.Support.finite (𝓞 E) (Q.coeff n)).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq, not_forall, not_le] at hw
  obtain ⟨n, hn⟩ := hw
  have hn' : n < Q.natDegree + 1 := by
    by_contra hc
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero] at hn
    exact (not_lt.2 zero_le') hn
  simp only [Set.mem_iUnion]
  exact ⟨n, by simpa using hn', hn⟩

end GlobalTheory.IntCop

namespace GlobalTheory.IntCop

theorem eventually_integral_coprime : ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ P₀ : (w.adicCompletionIntegers E)[X],
      P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = P.map (algebraMap E (w.adicCompletion E)) ∧
      IsCoprime P₀ (derivative P₀) := by
  intro E _ _ P hP
  obtain ⟨a, b, hab⟩ := hP
  have hfin := ((finite_bad P).union (finite_bad a)).union (finite_bad b)
  refine Filter.eventually_cofinite.2 (hfin.subset ?_)
  intro w hw
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  obtain ⟨⟨hPw, haw⟩, hbw⟩ := hc
  apply hw
  obtain ⟨P₀, hP₀⟩ := lift_of_val_le w P hPw
  obtain ⟨a₀, ha₀⟩ := lift_of_val_le w a haw
  obtain ⟨b₀, hb₀⟩ := lift_of_val_le w b hbw
  refine ⟨P₀, hP₀, a₀, b₀, ?_⟩
  have hinj : Function.Injective
      (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := Subtype.val_injective
  apply Polynomial.map_injective _ hinj
  rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
    ha₀, hb₀, hP₀, Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
    ← Polynomial.map_add, hab, Polynomial.map_one, Polynomial.map_one]

end GlobalTheory.IntCop
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.properGroupScheme_dvr_sections_mulEquiv_generic : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsProper G.hom → IsGrpPullback A G (spMap (algebraMap W L)) φ → ∃ e : (𝟙_ (Over (Sp L)) ⟶ A) ≃* (𝟙_ (Over (Sp W)) ⟶ G), ∀ y, y.left ≫ φ = spMap (algebraMap W L) ≫ (e y).left := by
  first | exact @GlobalTheory.LevExt.sections_generic_mulEquiv | exact GlobalTheory.LevExt.sections_generic_mulEquiv | (intros; apply GlobalTheory.LevExt.sections_generic_mulEquiv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_noetherianLocal_of_orderFunction : ∀ (A B C Ω : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field C] [Field Ω] (f : A →+* B) (ev : B →+* C) (t : B) (i : A →+* Ω), Function.Injective f → Function.Injective i → t ≠ 0 → (∀ b, ev b = 0 ↔ t ∣ b) → (∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (g : A →+* W) (i₀ : W →+* Ω) (i₁ : W →+* C), Function.Injective i₀ ∧ i₀.comp g = i ∧ i₁.comp g = ev.comp f ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ ∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁ := by
  first | exact @GlobalTheory.MBLow.exists_localRing_of_order | exact GlobalTheory.MBLow.exists_localRing_of_order | (intros; apply GlobalTheory.MBLow.exists_localRing_of_order <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isLieBasis_of_compatible_tangentRelation : ∀ (R : Type) [CommRing R] (G H : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (Rel : (epsR R ⟶ G) → (epsR R ⟶ H) → Prop), Rel 1 1 → (∀ y y' x x', Rel y x → Rel y' x' → Rel (y * y') (x * x')) → (∀ (c : R) (y : epsR R ⟶ G) (x : epsR R ⟶ H) (y' : epsR R ⟶ G) (x' : epsR R ⟶ H), y'.left = spMap (epsScaleR c) ≫ y.left → x'.left = spMap (epsScaleR c) ≫ x.left → Rel y x → Rel y' x') → (∀ y, IsTangent y → ∃ x, IsTangent x ∧ Rel y x) → (∀ y y' x, IsTangent y → IsTangent y' → Rel y x → Rel y' x → y = y') → (∀ y x x', Rel y x → Rel y x' → x = x') → ∀ (n : ℕ) (x : Fin n → (epsR R ⟶ H)) (y : Fin n → (epsR R ⟶ G)), IsLieBasis x → (∀ j, IsTangent (y j) ∧ Rel (y j) (x j)) → IsLieBasis y := by
  first | exact @GlobalTheory.LieTransfer.isLieBasis_of_rel | exact GlobalTheory.LieTransfer.isLieBasis_of_rel | (intros; apply GlobalTheory.LieTransfer.isLieBasis_of_rel <;> assumption)
end
