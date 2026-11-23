module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CohomologyUnramifiedLift
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerDualVanishesOfStrict
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle369
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle339
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle283
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle399
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle253
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle184
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemGammaOfMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle192
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle171
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.dualSelmer_unbounded_order_nonzero_ordinaryClass : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) → ¬ GrZero (dual1 W) A := by
  first | exact @GlobalTheory.Ord2.gw_limit | exact GlobalTheory.Ord2.gw_limit | (intros; apply GlobalTheory.Ord2.gw_limit <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.cohomology_unramified_lift : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l) (S' : Finset Pl) (n : ℕ), 1 ≤ n → (∀ s i j, mat W s i j ∈ c.O) → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, y s i ∈ c.O) → (∀ s i, z s i ∈ c.O) → Unr W y → (∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c.O) ∧ ∀ s ∈ Ine (F := ℚ) B, z s = mat (dual1 W) s *ᵥ x - x) → (∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c.O) ∧ ∀ s ∈ Dec (F := ℚ) A, z s = mat (dual1 W) s *ᵥ x - x) → (∀ w : Pl, w ∉ S' → l ^ n ∣ normV w - 1 → ∀ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)), KillsMu (normV w) ψ → Function.Surjective ψ → Tame c W y n w ψ) → Continuous u → (∀ s, u s ∈ c.O) → (∀ s, ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cg n (u (s * a)) (u s)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → ∀ σ ∈ ⁅H0g W, H0g W⁆, Cg n ((mat W σ - 1).det * ht W y z u σ) 0 := by
  first | exact @GlobalTheory.Ord2.ht_vanish_commutator | exact GlobalTheory.Ord2.ht_vanish_commutator | (intros; apply GlobalTheory.Ord2.ht_vanish_commutator <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.ordinarySelmer_dual_vanishes_of_strict : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ES W A → StrZero (dual1 W) A → GrZero (dual1 W) A := by
  first | exact @GlobalTheory.Ord2.Upgrade.upgrade | exact GlobalTheory.Ord2.Upgrade.upgrade | (intros; apply GlobalTheory.Ord2.Upgrade.upgrade <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.CycIne

theorem exists_poly_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (m : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ m) → ∀ u ∈ A, (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s u = u) → ∃ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ P.eval ζ = u := by
  intro l _ Ω _ _ _ A hA m ζ hζ u hu hfix
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨Polynomial.C u, ?_, by simp⟩
    intro x hx
    have hxu : x = u := by
      obtain ⟨n, hn, rfl⟩ := Polynomial.mem_coeffs_iff.1 hx
      rw [Polynomial.mem_support_iff, Polynomial.coeff_C] at hn
      rw [Polynomial.coeff_C]
      split_ifs at hn ⊢ with h
      · rfl
      · exact absurd rfl hn
    subst hxu
    haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact ⟨hu, fun s hs => hfix s hs (Units.ext (Subsingleton.elim _ _))⟩
  · obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.exists_poly_in_root_of_inertia_cyclotomic_fixed l Ω A m ζ hζ u hfix
    have hl : A.valuation (l : Ω) < 1 := by
      obtain ⟨v, hv, hlv⟩ := hA
      have := (hv (l : 𝓞 ℚ)).2 hlv
      simpa using this
    let K : Subfield Ω := (IntermediateField.fixedField (Ine (F := ℚ) A)).toSubfield
    have hK : ∀ x, x ∈ K ↔ ∀ s ∈ Ine (F := ℚ) A, s x = x := fun x =>
      IntermediateField.mem_fixedField_iff _ x
    obtain ⟨P, hP, hPe⟩ := GlobalTheory.T.exists_integral_poly_eval_zeta_of_totally_ramified l Ω A hl K
      (fun x hx hx0 => GlobalTheory.T.inertia_fixed_valuation_eq_zpow_prime_valuation l Ω A hA x hx0 ((hK x).1 hx)) m hm ζ hζ
      (GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_charZero l Ω A m hm ζ hζ) u hu ⟨Q, fun x hx => (hK x).2 (hQ x hx), hQe⟩
    exact ⟨P, fun x hx => ⟨(hP x hx).1, (hK x).1 (hP x hx).2⟩, hPe⟩

end GlobalTheory.CycIne
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

theorem _root_.GlobalTheory.T.exists_polynomial_in_primitiveRoot_of_inertia_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ n) → ∀ u ∈ A, (∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) → ∃ Q : Polynomial Ω, (∀ d, Q.coeff d ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s (Q.coeff d) = Q.coeff d) ∧ Q.eval ζ = u := by
  first | exact @GlobalTheory.ZetaPoly.exists_poly | exact GlobalTheory.ZetaPoly.exists_poly | (intros; apply GlobalTheory.ZetaPoly.exists_poly; all_goals assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormVal

def Bd (p : ℕ) [Fact p.Prime] (r : ℝ) (x : ℂ) : Prop :=
  x ∈ Qbar ∧ ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam x‖ ≤ r

variable {p : ℕ} [Fact p.Prime]

lemma lamC_of_mem (lam : Qbar →+* ℂ_[p]) {x : ℂ} (h : x ∈ Qbar) : lamC lam x = lam ⟨x, h⟩ := by
  unfold lamC
  rw [dite_eq_left h]

lemma Bd.zero {r : ℝ} (hr : 0 ≤ r) : Bd p r 0 := by
  refine ⟨zero_mem _, fun lam => ?_⟩
  rw [lamC_of_mem lam (zero_mem _)]
  have : (⟨0, zero_mem _⟩ : Qbar) = 0 := rfl
  rw [this, map_zero, norm_zero]
  exact hr

lemma Bd.add {r : ℝ} {x y : ℂ} (hx : Bd p r x) (hy : Bd p r y) : Bd p r (x + y) := by
  refine ⟨add_mem hx.1 hy.1, fun lam => ?_⟩
  have h1 := hx.2 lam
  have h2 := hy.2 lam
  rw [lamC_of_mem lam hx.1] at h1
  rw [lamC_of_mem lam hy.1] at h2
  rw [lamC_of_mem lam (add_mem hx.1 hy.1)]
  have : (⟨x + y, add_mem hx.1 hy.1⟩ : Qbar) = ⟨x, hx.1⟩ + ⟨y, hy.1⟩ := rfl
  rw [this, map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

lemma Bd.mul {r s : ℝ} {x y : ℂ} (hx : Bd p r x) (hy : Bd p s y) : Bd p (r * s) (x * y) := by
  refine ⟨mul_mem hx.1 hy.1, fun lam => ?_⟩
  have h1 := hx.2 lam
  have h2 := hy.2 lam
  rw [lamC_of_mem lam hx.1] at h1
  rw [lamC_of_mem lam hy.1] at h2
  rw [lamC_of_mem lam (mul_mem hx.1 hy.1)]
  have : (⟨x * y, mul_mem hx.1 hy.1⟩ : Qbar) = ⟨x, hx.1⟩ * ⟨y, hy.1⟩ := rfl
  rw [this, map_mul, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

lemma Bd.mono {r s : ℝ} {x : ℂ} (hx : Bd p r x) (h : r ≤ s) : Bd p s x :=
  ⟨hx.1, fun lam => (hx.2 lam).trans h⟩

lemma conj_mem {x : ℂ} (hx : x ∈ Qbar) : (starRingEnd ℂ) x ∈ Qbar := by
  rw [mem_algebraicClosure_iff] at hx ⊢
  exact hx.algHom ((starRingEnd ℂ).toRatAlgHom)

noncomputable def conjQ : Qbar →+* Qbar :=
  ((starRingEnd ℂ).comp (algebraMap Qbar ℂ)).codRestrict Qbar (fun x => conj_mem x.2)

lemma Bd.conj {r : ℝ} {x : ℂ} (hx : Bd p r x) : Bd p r ((starRingEnd ℂ) x) := by
  refine ⟨conj_mem hx.1, fun lam => ?_⟩
  have h1 := hx.2 (lam.comp conjQ)
  rw [lamC_of_mem _ hx.1] at h1
  rw [lamC_of_mem lam (conj_mem hx.1)]
  exact h1

lemma Bd.inv_nat {n M : ℕ} (hM : M ≠ 0) (h : n ∣ M) :
    Bd p ((p : ℝ) ^ (padicValNat p M : ℝ)) ((n : ℂ)⁻¹) := by
  have hn : n ≠ 0 := fun h0 => hM (by simpa [h0] using h)
  have hm : (n : ℂ)⁻¹ ∈ Qbar := inv_mem (natCast_mem _ n)
  refine ⟨hm, fun lam => ?_⟩
  rw [lamC_of_mem lam hm]
  have : (⟨(n : ℂ)⁻¹, hm⟩ : Qbar) = (n : Qbar)⁻¹ := by
    apply Subtype.ext
    simp
  rw [this, map_inv₀, map_natCast, norm_inv]
  have h2 : ‖(n : ℂ_[p])‖ = ‖(n : ℚ_[p])‖ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) n, norm_algebraMap']
  have hn' : (n : ℚ_[p]) ≠ 0 := by exact_mod_cast hn
  rw [h2, Padic.norm_eq_zpow_neg_valuation hn', Padic.valuation_natCast, zpow_neg, inv_inv,
    zpow_natCast, Real.rpow_natCast]
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  apply pow_le_pow_right₀ hp
  rw [← (by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hM]
  simpa only [_root_.Nat.padicValNat_def] using
    (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat p n)).trans h

lemma order_dvd {f r N : ℕ} (h : r ≤ 2 * N) :
    8 ^ (2 * f * r) * (2 * (2 * f * r)).factorial ∣ 8 ^ (4 * f * N) * (8 * f * N).factorial := by
  have h1 : f * r ≤ f * (2 * N) := Nat.mul_le_mul_left _ h
  apply mul_dvd_mul
  · apply pow_dvd_pow
    nlinarith
  · apply Nat.factorial_dvd_factorial
    nlinarith

theorem norm_mem_and_le : ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → GoodLevel D Q → ∀ (P : Pair D ⊤ δ t0 Q) (N : ℕ) (B : ℝ), P.Small N B → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ((P.norm : ℝ) : ℂ) ∈ Qbar ∧ ‖lamC lam ((P.norm : ℝ) : ℂ)‖ ≤ (p : ℝ) ^ (3 * ((padicValNat p (8 ^ (4 * fF D * N) * (8 * fF D * N).factorial) : ℝ) + 4 * fF D * N * B * (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) + 4 * (N : ℝ) ^ 2 * (padicValNat p Q : ℝ))) := by
  intro D hI S dl hL δ t0 Q hC hT hQ P N B hS p _ lam
  set M : ℕ := 8 ^ (4 * fF D * N) * (8 * fF D * N).factorial with hMdef
  have hM : M ≠ 0 := by positivity
  set c : ℝ := dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ) with hc
  set v : ℝ := (padicValNat p M : ℝ) with hv
  set w : ℝ := (padicValNat p Q : ℝ) with hw
  have hw0 : 0 ≤ w := Nat.cast_nonneg _
  have hv0 : 0 ≤ v := Nat.cast_nonneg _
  have hc0 : 0 ≤ c := by
    have := hL.2.1 p
    have h2 : (0 : ℝ) ≤ (if p = D.host.d then 1 / 4 else 0) := by split_ifs <;> norm_num
    rw [hc]
    linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hp0 : (0 : ℝ) < p := by linarith
  set e : ℝ := ((P.a * ∑ τ, P.n τ : ℕ) : ℝ) * c + ((P.a * P.d : ℕ) : ℝ) * w with he
  have he0 : 0 ≤ e := by positivity
  have ha : P.a ≤ 2 * N := P.a_le.trans hS.1
  have heE : e ≤ 4 * fF D * N * B * c + 4 * (N : ℝ) ^ 2 * w := by
    have hcard := (GlobalTheory.T.derivationDenominators_and_hostField_sizes D hI.g1).2.2.2.2.1
    have h1 : ((∑ τ, P.n τ : ℕ) : ℝ) ≤ fF D * (2 * B) := by
      rw [Nat.cast_sum, ← hcard]
      have := Finset.sum_le_card_nsmul Finset.univ (fun τ => (P.n τ : ℝ)) (2 * B)
        (fun τ _ => hS.2 τ)
      simpa using this
    have haR : (P.a : ℝ) ≤ 2 * N := by exact_mod_cast ha
    have hdR : (P.d : ℝ) ≤ 2 * N := by exact_mod_cast hS.1
    have h2 : ((P.a * ∑ τ, P.n τ : ℕ) : ℝ) ≤ 4 * fF D * N * B := by
      rw [Nat.cast_mul]
      calc (P.a : ℝ) * ((∑ τ, P.n τ : ℕ) : ℝ) ≤ (2 * N) * (fF D * (2 * B)) :=
            mul_le_mul haR h1 (Nat.cast_nonneg _) (by positivity)
        _ = _ := by ring
    have h3 : ((P.a * P.d : ℕ) : ℝ) ≤ 4 * (N : ℝ) ^ 2 := by
      rw [Nat.cast_mul]
      calc (P.a : ℝ) * (P.d : ℝ) ≤ (2 * N) * (2 * N) :=
            mul_le_mul haR hdR (Nat.cast_nonneg _) (by positivity)
        _ = _ := by ring
    exact add_le_add (mul_le_mul_of_nonneg_right h2 hc0) (mul_le_mul_of_nonneg_right h3 hw0)
  obtain ⟨hterm, hsq, -⟩ := GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D hI ⊤ δ t0 Q hC hT P hQ.1
  have hgam : ∀ (r : ℕ), r ≤ 2 * N → ∀ (J : Subgroup (GA D r)), J ≤ intG D r → ∀ g,
      Bd p ((p : ℝ) ^ v) ((gam D J g : ℂ)⁻¹) := fun r hr J hJ g =>
    Bd.inv_nat hM ((GlobalTheory.T.unitaryRationalConjIntersectionCard_dvd_invariant D r J hJ g).2.1.trans (order_dvd hr))
  have hcoord : ∀ (h k' : GA D P.d), k' ∈ intG D P.d →
      TrivAt D p ((h * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ∀ T,
      Bd p ((p : ℝ) ^ v * (p : ℝ) ^ e) (P.coord h T) := by
    intro h k' hk' htr T
    unfold Pair.coord
    refine finsum_induction (Bd p ((p : ℝ) ^ v * (p : ℝ) ^ e)) (Bd.zero (by positivity))
      (fun x y => Bd.add) (fun x => ?_)
    refine Bd.mul (hgam _ ha _ le_rfl _) ?_
    obtain ⟨γ, k, γ', h1, h2, h3⟩ := hI.rep P.a p Fact.out x.out
    rw [← hterm γ (Subgroup.subset_closure ⟨γ', h1⟩) k (Subgroup.subset_closure h2)]
    exact ⟨(GlobalTheory.T.padicValuation_thetaKernelJet_bound D hI S dl hL δ t0 Q hC hT hQ P p lam _ h k' hk' h3 htr T).1,
      fun lam' => (GlobalTheory.T.padicValuation_thetaKernelJet_bound D hI S dl hL δ t0 Q hC hT hQ P p lam' _ h k' hk' h3 htr T).2⟩
  have hsqb : ∀ h : GA D P.d,
      Bd p (((p : ℝ) ^ v * (p : ℝ) ^ e) * ((p : ℝ) ^ v * (p : ℝ) ^ e)) ((P.sq h : ℝ) : ℂ) := by
    intro h
    obtain ⟨γ, k, γ', h1, h2, h3⟩ := hI.rep P.d p Fact.out h
    rw [← hsq γ (Subgroup.subset_closure ⟨γ', h1⟩) 1 (one_mem _) h, mul_one]
    unfold Pair.sq
    rw [Complex.ofReal_sum]
    refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T _ => ?_)
    have hb := hcoord (γ * h) k (Subgroup.subset_closure h2) h3 T
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    exact hb.mul hb.conj
  have hfin : Bd p ((p : ℝ) ^ v * (((p : ℝ) ^ v * (p : ℝ) ^ e) * ((p : ℝ) ^ v * (p : ℝ) ^ e)))
      ((P.norm : ℝ) : ℂ) := by
    unfold Pair.norm
    refine finsum_induction (fun x : ℝ => Bd p ((p : ℝ) ^ v * (((p : ℝ) ^ v * (p : ℝ) ^ e) *
      ((p : ℝ) ^ v * (p : ℝ) ^ e))) (x : ℂ)) ?_ (fun x y hx hy => ?_) (fun x => ?_)
    · rw [Complex.ofReal_zero]
      exact Bd.zero (by positivity)
    · rw [Complex.ofReal_add]
      exact hx.add hy
    · rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
      exact (hgam _ hS.1 _ P.J_le _).mul (hsqb _)
  refine ⟨hfin.1, (hfin.2 lam).trans ?_⟩
  rw [← Real.rpow_add hp0, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
  apply Real.rpow_le_rpow_of_exponent_le hp1
  linarith

end GlobalTheory.NormVal
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.Ues

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem toGQ_mul (m m' : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (h' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have hmm : 0 < (m * m').det := by rw [Matrix.det_mul]; exact mul_pos h h'
  unfold toGQ
  rw [dite_eq_left hmm, dite_eq_left h, dite_eq_left h']
  apply Subtype.ext
  apply Units.ext
  exact Matrix.map_mul (f := Int.castRingHom ℚ)

theorem lev_mul {X : Tower Ω ε} {M : ℕ} {f g : X.K} (hf : Lev X M f) (hg : Lev X M g) : Lev X M (f * g) :=
  fun γ hγ => by rw [map_mul, hf γ hγ, hg γ hγ]

theorem lev_div {X : Tower Ω ε} {M : ℕ} {f g : X.K} (hf : Lev X M f) (hg : Lev X M g) : Lev X M (f / g) :=
  fun γ hγ => by rw [map_div₀, hf γ hγ, hg γ hγ]

theorem lev_pow {X : Tower Ω ε} {M : ℕ} {f : X.K} (hf : Lev X M f) (k : ℕ) : Lev X M (f ^ k) :=
  fun γ hγ => by rw [map_pow, hf γ hγ]

theorem lev_const (X : Tower Ω ε) (M : ℕ) (c : Ω) : Lev X M (algebraMap Ω X.K c) :=
  fun _ _ => AlgEquiv.commutes _ c

theorem lev_sl {X : Tower Ω ε} {M : ℕ} {f : X.K} (hf : Lev X M f) (γ : SL(2, ℤ)) : Lev X M (X.sl (ofSL γ) f) := by
  intro δ hδ
  have e : γ * δ = (γ * δ * γ⁻¹) * γ := by group
  rw [← X.sl_mul, ← map_mul, e, map_mul, X.sl_mul,
    hf _ ((CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ γ)]

theorem lev_gal [IsAlgClosure ℚ Ω] {X : Tower Ω ε} {M : ℕ} (hM : 0 < M) {f : X.K} (hf : Lev X M f)
    (s : Ω ≃ₐ[ℚ] Ω) : Lev X M (X.gal s f) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  intro δ hδ
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := s ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.1 hδ
  have := X.recip M f hM hf ζ hζ s (i : ℤ) (by rw [← hi, zpow_natCast]) 1 δ
    (by simp [en, h00, h01, h10, h11])
  rw [map_one, X.sl_one] at this
  exact this.symm

theorem val_mul_sub_one {K : Type} [Field K] (W : ValuationSubring K) {x y : K} (hx : W.valuation (x - 1) < 1)
    (hy : W.valuation (y - 1) < 1) : W.valuation (x * y - 1) < 1 := by
  have h1 : W.valuation x = 1 := by
    have e : x = 1 + (x - 1) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left _ (by rwa [map_one]), map_one]
  have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [e]
  exact Valuation.map_add_lt _ (by rwa [map_mul, h1, one_mul]) hx

theorem const_mem_un (X : Tower Ω ε) (m : ℕ) {c : Ω} (hc : algebraMap Ω X.K c ≠ 0) :
    Units.mk0 (algebraMap Ω X.K c) hc ∈ X.Un m := by
  intro W hW
  refine ⟨1, ?_⟩
  rw [Units.val_one, one_pow, div_one, Units.val_mk0, KmapA.val_eq_one_iff _ hc]
  exact ⟨hW.1 c, by rw [← map_inv₀]; exact hW.1 _⟩

end GlobalTheory.KZ.ES.Ues


open GlobalTheory.KZ.ES.Ues in
theorem GlobalTheory.KZ.ES.eichlerShimura_unit : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → l ∣ M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ (n k : ℕ) (f : X.Kˣ), f ∈ X.Un (l ^ n) → Lev X (M₀ * l ^ k) f → ∀ γ : SL(2, ℤ), DiagMod (M₀ * l ^ k) q γ → ∃ g : X.Kˣ, Nq X (M₀ * l ^ k) q f * X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL γ) (f : X.K))) ^ q * (g : X.K) ^ (l ^ n) := by
  intro Ω _ _ _ ε X hhol l M₀ hl hM₀ hlM
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.kronecker_congruence_modularFunctionTower_level ε X hhol l M₀ hl hM₀
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.isPow_of_gauss_valuation_congr_one_almost_all_primes ε X hhol l M₀ hl hM₀ hlM
  refine ⟨S₁ ∪ S₂ ∪ M₀.primeFactors, ?_⟩
  intro q hq hqS V s hFrob n k f hf hlev γ hγ
  simp only [Finset.mem_union, not_or] at hqS
  obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hqS
  have hqM₀ : Nat.Coprime q M₀ :=
    (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hq3 (Nat.mem_primeFactors.2 ⟨hq, h, hM₀.ne'⟩)
  have hqM : Nat.Coprime q (M₀ * l ^ k) :=
    Nat.Coprime.mul_right hqM₀ (Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_right hlM hqM₀))
  have hM : 0 < M₀ * l ^ k := Nat.mul_pos hM₀ (pow_pos hl.pos k)
  obtain ⟨W, hDom, hGauss⟩ := GlobalTheory.KZ.ES.exists_dom_gauss ε X V
  have hY := Tower.overY_comap_sl_gal ε X ε.injective hhol
  obtain ⟨hU1, hUmul, hUinv, -, -, hUpow, -⟩ := UnClosure.un_closure ε X ε.injective hhol (l ^ n)
  have hsl : ∀ (g : GQ) (u : X.Kˣ), u ∈ X.Un (l ^ n) → ∃ v ∈ X.Un (l ^ n), (v : X.K) = X.sl g u := fun g u hu =>
    ⟨_, KmapA.un_map X (X.sl g).toRingEquiv (fun W hW => (hY W hW).1 g) _ u hu, rfl⟩
  have hgal : ∀ (t : Ω ≃ₐ[ℚ] Ω) (u : X.Kˣ), u ∈ X.Un (l ^ n) → ∃ v ∈ X.Un (l ^ n), (v : X.K) = X.gal t u :=
    fun t u hu => ⟨_, KmapA.un_map X (X.gal t) (fun W hW => (hY W hW).2 t) _ u hu, rfl⟩
  obtain ⟨f', hf', ef'⟩ := hsl (ofSL γ) f hf
  have hlev' : Lev X (M₀ * l ^ k) (f' : X.K) := ef' ▸ lev_sl hlev γ
  obtain ⟨c₁, hc₁⟩ := (hS₁ q hq hq1 V s hFrob W hDom k f f.ne_zero hlev).1
  obtain ⟨c₂, hc₂⟩ := (hS₁ q hq hq1 V s hFrob W hDom k f' f'.ne_zero hlev').2
  have hc₁0 : c₁ ≠ 0 := by rintro rfl; simp at hc₁
  have hc₂0 : c₂ ≠ 0 := by rintro rfl; simp at hc₂
  have hc : algebraMap Ω X.K (c₁ * c₂) ≠ 0 := (_root_.map_ne_zero _).2 (mul_ne_zero hc₁0 hc₂0)
  have hsplit : X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) =
      X.sl (toGQ !![(q : ℤ), 0; 0, 1]) (f' : X.K) := by
    rw [toGQ_mul _ _ (by rw [γ.det_coe]; exact one_pos) (by simp [Matrix.det_fin_two, hq.pos]), Betti.toGQ_sl,
      X.sl_mul, ef']
  have hnlev := GlobalTheory.KZ.ES.lev_heckeProd ε X _ q f γ hM hq hqM hlev hγ
  obtain ⟨N, hN, eN⟩ : ∃ v ∈ X.Un (l ^ n), (v : X.K) = Nq X (M₀ * l ^ k) q f := by
    unfold Nq
    refine Finset.prod_induction _ (fun x => ∃ v ∈ X.Un (l ^ n), (v : X.K) = x) ?_ ⟨1, hU1, rfl⟩
      (fun j _ => hsl _ f hf)
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, hUmul a b ha hb, rfl⟩
  obtain ⟨T, hT, eT⟩ := hsl (toGQ !![(q : ℤ), 0; 0, 1]) f' hf'
  obtain ⟨A, hA, eA⟩ := hgal s f hf
  obtain ⟨B, hB, eB⟩ := hgal s.symm f' hf'
  have hAl : Lev X (M₀ * l ^ k) (A : X.K) := eA ▸ lev_gal hM hlev s
  have hBl : Lev X (M₀ * l ^ k) (B : X.K) := eB ▸ lev_gal hM hlev' s.symm
  rw [hsplit, ← eN, ← eT] at hnlev
  rw [hsplit, ← eN, ← eT, ← ef', ← eA, ← eB]
  rw [← eN, ← eA] at hc₁
  rw [← eT, ← eB] at hc₂
  have eU : ((Units.mk0 _ hc * (N * T) * (A * B ^ q)⁻¹ : X.Kˣ) : X.K) =
      algebraMap Ω X.K (c₁ * c₂) * (N * T) / (A * B ^ q) := by
    simp [div_eq_mul_inv]
  obtain ⟨g, hg⟩ := hS₂ q hq hq2 V hFrob.1 W hGauss n k (Units.mk0 _ hc * (N * T) * (A * B ^ q)⁻¹)
    (hUmul _ _ (hUmul _ _ (const_mem_un X _ hc) (hUmul _ _ hN hT)) (hUinv _ (hUmul _ _ hA (hUpow q _ hB))))
    (by rw [eU]; exact lev_div (lev_mul (lev_const X _ _) hnlev) (lev_mul hAl (lev_pow hBl q)))
    (by
      rw [eU]
      convert val_mul_sub_one W hc₁ hc₂ using 3
      rw [map_mul]; ring)
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (c₁ * c₂)⁻¹ (pow_pos hl.pos n)
  have hb0 : algebraMap Ω X.K b ≠ 0 := by
    refine (_root_.map_ne_zero _).2 ?_
    rintro rfl
    rw [zero_pow (pow_pos hl.pos n).ne'] at hb
    exact inv_ne_zero (mul_ne_zero hc₁0 hc₂0) hb.symm
  refine ⟨Units.mk0 _ hb0 * g, ?_⟩
  have hg' := congrArg (fun u : X.Kˣ => (u : X.K)) hg
  simp only [eU, Units.val_pow_eq_pow_val] at hg'
  rw [Units.val_mul, Units.val_mk0, mul_pow, ← map_pow, hb, ← hg', map_inv₀]
  have hA0 := A.ne_zero
  have hB0 := B.ne_zero
  field_simp
end
