module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassInvariantDescentCoprimeLevelModPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle109
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle341
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle399
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle403
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle017
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.classInvariant_descent_coprimeLevel_modPow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n Ma Mb : ℕ), l.Prime → 0 < Ma → 0 < Mb → 6 * l ∣ Ma → Nat.Coprime Ma Mb → ∀ f : X.Kˣ, Lev X (Ma * Mb) f → (∀ γ ∈ CongruenceSubgroup.Gamma Ma, ∃ g : X.Kˣ, Lev X (Ma * Mb) g ∧ X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ h : X.Kˣ, Lev X Ma ((f : X.K) ^ 4 * (h : X.K) ^ (l ^ n)) := by
  first | exact @GlobalTheory.KZ.ES.CoprimeDescent.descent | exact GlobalTheory.KZ.ES.CoprimeDescent.descent | (intros; apply GlobalTheory.KZ.ES.CoprimeDescent.descent <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne.CycRoots

theorem frob_cycAlg (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : OverL l A) (x : A) (hx : x ∈ cycAlg l A) :
    ∃ y ∈ cycAlg l A, ∃ z : A, x = y ^ l + (l : A) * z := by
  have hp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : Ω) hp.pos
    have hyA : y ∈ A := mem_of_pow_mem A hp.ne_zero (hy ▸ x.2)
    have e : (⟨y, hyA⟩ : A) ^ l = x := Subtype.ext (by simpa using hy)
    refine ⟨⟨y, hyA⟩, mem_cycAlg_of_pow (n := n + 1) ?_, 0, by rw [e]; ring⟩
    rw [pow_succ', pow_mul, e, hn]
  | algebraMap a =>
    obtain ⟨b, z, h⟩ := GlobalTheory.T.fixed_element_lth_power_mod l Ω A hA a
    exact ⟨algebraMap (fixA A) A b, Subalgebra.algebraMap_mem _ b, z, h⟩
  | add a b _ _ iha ihb =>
    obtain ⟨y, hy, z, rfl⟩ := iha
    obtain ⟨y', hy', z', rfl⟩ := ihb
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp y y'
    refine ⟨y + y', Subalgebra.add_mem _ hy hy', z + z' - y * y' * r, ?_⟩
    rw [hr]; ring
  | mul a b _ _ iha ihb =>
    obtain ⟨y, hy, z, rfl⟩ := iha
    obtain ⟨y', hy', z', rfl⟩ := ihb
    refine ⟨y * y', Subalgebra.mul_mem _ hy hy', z * y' ^ l + y ^ l * z' + (l : A) * z * z', ?_⟩
    rw [mul_pow]; ring

theorem approxRoot_fix_ineCyc : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ x ∈ A) →
    0 < v (l : Ω) → v (l : Ω) < 1 → ApproxRoot l v (Fix Ω (ineCyc l A)) := by
  intro l _ hl2 Ω _ _ _ A hA v hv hl0 hl1
  have hp : l.Prime := Fact.out
  have hl3 : 3 ≤ l := by have := hp.two_le; omega
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hF : ∀ x : A, x ∈ cycAlg l A ↔ (x : Ω) ∈ Fix Ω (ineCyc l A) := by
    intro x
    rw [GlobalTheory.T.mem_inertiaInvariantsCyclotomicAlgebra_iff l Ω A hA x]
    exact ⟨fun h g => h g g.2, fun h s hs => h ⟨s, hs⟩⟩
  haveI : NeZero ((l ^ 2 : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos hp.pos 2).ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ 2)
  have hζA : ζ ∈ A := mem_of_pow_mem A (pow_pos hp.pos 2).ne' (by rw [hζ.pow_eq_one]; exact A.one_mem)
  have hζF : ζ ∈ Fix Ω (ineCyc l A) :=
    (hF ⟨ζ, hζA⟩).1 (mem_cycAlg_of_pow (n := 2) (Subtype.ext (by simpa using hζ.pow_eq_one)))
  set c : Ω := ζ - 1 with hc
  have hcF : c ∈ Fix Ω (ineCyc l A) := Subfield.sub_mem _ hζF (Subfield.one_mem _)
  have hequiv : v.IsEquiv A.valuation :=
    Valuation.isEquiv_iff_val_le_one.2 fun {x} => by rw [hv, A.valuation_le_one_iff]
  have hvc : v c ^ (l * (l - 1)) = v (l : Ω) := by
    have h := GlobalTheory.valuation_zeta_sub_one_pow_totient l Ω A 2 ζ (by norm_num) hζ
    rw [Nat.totient_prime_pow hp (by norm_num), ← map_pow] at h
    rw [← map_pow, hequiv.eq_iff]
    simpa using h
  have hN : l * (l - 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hc0 : 0 < v c := by
    rcases (zero_le : 0 ≤ v c).eq_or_lt with h | h
    · rw [← h, zero_pow hN] at hvc; exact absurd hvc hl0.ne
    · exact h
  have hc1 : v c < 1 := by
    by_contra h
    exact absurd (hvc ▸ one_le_pow₀ (not_lt.1 h)) (not_le.2 hl1)
  have hcne : c ≠ 0 := fun h => by rw [h, map_zero] at hc0; exact lt_irrefl _ hc0
  set r : ℝ≥0 := v c ^ l with hr
  have hr0 : 0 < r := pow_pos hc0 l
  have hr1 : r < 1 := pow_lt_one₀ hc0.le hc1 hp.ne_zero
  have hlr : v (l : Ω) ≤ r * r := by
    rw [← hvc, pow_mul, ← hr, ← sq]
    exact pow_le_pow_of_le_one hr0.le hr1.le (by omega)
  refine ⟨r, hr1, fun u hu => ?_⟩
  by_cases hu0 : u = 0
  · refine ⟨0, Subfield.zero_mem _, ?_⟩
    rw [hu0, zero_pow hp.ne_zero, sub_zero, map_zero]; exact zero_le
  have hvu : 0 < v u := (Valuation.pos_iff v).2 hu0
  obtain ⟨k, hk1, hk2⟩ := NNReal.exists_mem_Ioc_zpow hvu.ne' ((one_lt_inv₀ hr0).2 hr1)

  set d : Ω := c ^ (k + 1) with hd
  have hdF : d ∈ Fix Ω (ineCyc l A) := Subfield.zpow_mem _ hcF _
  have hdne : d ≠ 0 := zpow_ne_zero _ hcne
  have hvd : v (d ^ l) = r ^ (k + 1) := by
    rw [map_pow, hd, map_zpow₀, hr, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hrk : 0 < r ^ (k + 1) := zpow_pos hr0 _
  have h1 : v (u * d ^ l) ≤ 1 := by
    rw [map_mul, hvd]
    calc v u * r ^ (k + 1) ≤ r⁻¹ ^ (k + 1) * r ^ (k + 1) := mul_le_mul_of_nonneg_right hk2 zero_le
      _ = 1 := by rw [← mul_zpow, inv_mul_cancel₀ hr0.ne', one_zpow]
  have h2 : r ≤ v (u * d ^ l) := by
    rw [map_mul, hvd]
    calc r = r⁻¹ ^ k * r ^ (k + 1) := by
          rw [zpow_add_one₀ hr0.ne', ← mul_assoc, ← mul_zpow, inv_mul_cancel₀ hr0.ne', one_zpow, one_mul]
      _ ≤ v u * r ^ (k + 1) := mul_le_mul_of_nonneg_right hk1.le zero_le
  have hu'F : u * d ^ l ∈ Fix Ω (ineCyc l A) := Subfield.mul_mem _ hu (Subfield.pow_mem _ hdF _)
  obtain ⟨y, hy, z, e⟩ := frob_cycAlg l Ω A hA ⟨u * d ^ l, (hv _).1 h1⟩ ((hF _).2 hu'F)
  have e' : u * d ^ l = (y : Ω) ^ l + (l : Ω) * (z : Ω) := by
    simpa using congrArg (fun t : A => (t : Ω)) e
  refine ⟨(y : Ω) / d, Subfield.div_mem _ ((hF y).1 hy) hdF, ?_⟩
  have e2 : (u - ((y : Ω) / d) ^ l) * d ^ l = (l : Ω) * (z : Ω) := by
    rw [sub_mul, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hdne), e']; ring
  have h3 : v (u - ((y : Ω) / d) ^ l) * r ^ (k + 1) ≤ r * v u * r ^ (k + 1) := by
    rw [← hvd, mul_assoc, ← map_mul, ← map_mul, e2, map_mul v (l : Ω)]
    calc v (l : Ω) * v (z : Ω) ≤ v (l : Ω) * 1 := mul_le_mul_of_nonneg_left ((hv _).2 z.2) zero_le
      _ = v (l : Ω) := mul_one _
      _ ≤ r * r := hlr
      _ ≤ r * v (u * d ^ l) := mul_le_mul_of_nonneg_left h2 zero_le
  exact le_of_mul_le_mul_right h3 hrk

end GlobalTheory.RecOne.CycRoots
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
theorem _root_.GlobalTheory.T.greenbergWiles_dualSelmer_lower_bound_mod_prime_pow : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (y : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, GwCount.SelN c n S A W (y i)) → (∀ i j, i ≠ j → ¬ Cob1 c n W ⊤ (y i - y j)) → ∃ (N' : ℕ) (z : Fin N' → G ℚ Ω → Fin 2 → Qbar l), N ≤ C * N' ∧ (∀ i, GwCount.SelN c n S A (dual1 W) (z i)) ∧ ∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j) := by
  first | exact @GlobalTheory.Ord2.GwIneq.gw_ineq | exact GlobalTheory.Ord2.GwIneq.gw_ineq | (intros; apply GlobalTheory.Ord2.GwIneq.gw_ineq <;> assumption) | exact @GlobalTheory.Ord2.GwIneq.exists_cc | exact GlobalTheory.Ord2.GwIneq.exists_cc | (intros; apply GlobalTheory.Ord2.GwIneq.exists_cc <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.classSumDenominatorBound_of_cmThetaHypotheses : (∀ D, Inp D) → IntSt := by
  first | exact @GlobalTheory.NormSum.DenomBound.intSt_of_forall_inp | exact GlobalTheory.NormSum.DenomBound.intSt_of_forall_inp | (intros; apply GlobalTheory.NormSum.DenomBound.intSt_of_forall_inp <;> assumption)
end
