module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPowOfGaussValuationCongrOneAlmostAllPrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle109
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle396
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle046
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.dualCocycle_coboundary_on_inertia_of_orthogonal : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ), 1 ≤ n → ∀ (S : Finset Pl) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ n)) (GS Ω (S : Set Pl)) M) (hrho : ContAction rho) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (q : Pl), IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ f : Z1 ((twDual μ rho).comp (locHom (S : Set Pl) B)), (∀ a ∈ H1ur (rho.comp (locHom (S : Set Pl) B)) ((Ine (F := ℚ) B).subgroupOf (Dec (F := ℚ) B)), cupH1H1TwistedDual μ rho (locHom (S : Set Pl) B) (hrho.comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∃ m : TDual (ZMod (l ^ n)) M, ∀ s : Dec (F := ℚ) B, (s : G ℚ Ω) ∈ Ine (F := ℚ) B → f.1 s = twDual μ rho (locHom (S : Set Pl) B s) m - m := by
  first | exact @GlobalTheory.Ord2.GwIneq.dual_cocycle_cob_on_inertia | exact GlobalTheory.Ord2.GwIneq.dual_cocycle_cob_on_inertia | (intros; apply GlobalTheory.Ord2.GwIneq.dual_cocycle_cob_on_inertia <;> assumption) | exact @GlobalTheory.Ord2.GwIneq.cob_of_perp_transport | exact GlobalTheory.Ord2.GwIneq.cob_of_perp_transport | (intros; apply GlobalTheory.Ord2.GwIneq.cob_of_perp_transport <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

theorem GlobalTheory.ZetaPoly.exists_poly : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ n) → ∀ u ∈ A, (∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) → ∃ Q : Polynomial Ω, (∀ d, Q.coeff d ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s (Q.coeff d) = Q.coeff d) ∧ Q.eval ζ = u := by
  intro l _ Ω _ _ _ A hA n ζ hζ u hu hfix
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hζ1 : ζ = 1 := by simpa using hζ
    subst hζ1
    refine ⟨Polynomial.C u, fun d => ?_, by simp⟩
    rw [Polynomial.coeff_C]
    split_ifs
    · exact ⟨hu, fun s hs => hfix s hs (map_one s)⟩
    · exact ⟨A.zero_mem, fun s _ => map_zero s⟩
  obtain ⟨P, hPfix, hPev⟩ := GlobalTheory.T.exists_polynomial_eval_eq_of_inertia_fixed Ω A ζ u hfix
  set N := (l ^ n).totient with hN
  have hlpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have hNpos : 0 < N := Nat.totient_pos.2 hlpos
  set Φ := Polynomial.cyclotomic (l ^ n) Ω with hΦ
  have hΦm : Φ.Monic := Polynomial.cyclotomic.monic _ _
  have hΦdeg : Φ.natDegree = N := Polynomial.natDegree_cyclotomic _ _
  have hΦ1 : Φ ≠ 1 := by
    intro h; rw [h, Polynomial.natDegree_one] at hΦdeg; omega
  set P' := P %ₘ Φ with hP'
  have hroot : Φ.eval ζ = 0 := (hζ.isRoot_cyclotomic hlpos)
  have hev : P'.eval ζ = u := by
    rw [← hPev]
    show (P %ₘ Φ).eval ζ = P.eval ζ
    conv_rhs => rw [← Polynomial.modByMonic_add_div P Φ]
    rw [Polynomial.eval_add, Polynomial.eval_mul, hroot, zero_mul, add_zero]
  have hdeg : P'.natDegree < N := hΦdeg ▸ Polynomial.natDegree_modByMonic_lt P hΦm hΦ1
  have hPmap : ∀ s ∈ Ine (F := ℚ) A, P.map (s : Ω →+* Ω) = P := fun s hs =>
    Polynomial.ext fun d => by rw [Polynomial.coeff_map]; exact hPfix s hs d
  have hP'map : ∀ s ∈ Ine (F := ℚ) A, P'.map (s : Ω →+* Ω) = P' := fun s hs => by
    rw [hP', Polynomial.map_modByMonic _ hΦm, hPmap s hs, hΦ, Polynomial.map_cyclotomic]
  set T := Polynomial.taylor (1 : Ω) P' with hT
  have hTmap : ∀ s ∈ Ine (F := ℚ) A, T.map (s : Ω →+* Ω) = T := fun s hs => by
    rw [hT, Polynomial.map_taylor, hP'map s hs, map_one]
  have hTdeg : T.natDegree < N := by rw [hT, Polynomial.natDegree_taylor]; exact hdeg
  have hsum : (∑ i ∈ Finset.range N, T.coeff i * (ζ - 1) ^ i) = u := by
    rw [← Polynomial.eval_eq_sum_range' hTdeg, hT, Polynomial.taylor_eval, sub_add_cancel, hev]
  obtain ⟨v, hv, hlv⟩ := hA
  have hl1 : A.valuation (l : Ω) < 1 := by
    have := (hv ((l : ℕ) : 𝓞 ℚ)).2 hlv
    simpa using this
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hcA : ∀ i < N, T.coeff i ∈ A := by
    refine GlobalTheory.T.coeff_mem_of_sum_mul_pow_mem_of_valuation_zpow Ω A N (ζ - 1) (l : Ω) (fun i => T.coeff i) hNpos hl0 hl1
      (GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_ratAlg l Ω A n ζ hn hζ) (fun i _ hc => ?_) (hsum ▸ hu)
    refine GlobalTheory.T.inertiaFixed_valuation_eq_zpow_prime_ratAlgClosure l Ω A ⟨v, hv, hlv⟩ _ hc (fun s hs => ?_)
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) (hTmap s hs)
    simpa [Polynomial.coeff_map] using this
  have hcA' : ∀ i, T.coeff i ∈ A := fun i => by
    rcases lt_or_ge i N with h | h
    · exact hcA i h
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; exact A.zero_mem
  have hlift : T ∈ Polynomial.lifts (A.subtype) :=
    (Polynomial.lifts_iff_coeff_lifts T).2 fun i => ⟨⟨_, hcA' i⟩, rfl⟩
  obtain ⟨T₀, hT₀⟩ := Polynomial.mem_lifts T |>.1 hlift
  have hback : Polynomial.taylor (-1 : Ω) T = P' := by
    rw [hT, Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]
  refine ⟨P', fun d => ⟨?_, fun s hs => ?_⟩, hev⟩
  · rw [← hback, ← hT₀]
    have : ((-1 : A) : Ω) = -1 := by simp
    rw [← this, show ((-1 : A) : Ω) = A.subtype (-1) from rfl, ← Polynomial.map_taylor, Polynomial.coeff_map]
    exact (Polynomial.taylor (-1 : A) T₀).coeff d |>.2
  · have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p d) (hP'map s hs)
    simpa [Polynomial.coeff_map] using this

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

theorem _root_.GlobalTheory.T.inertia_fixed_valuation_eq_zpow_prime_valuation : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ x : Ω, x ≠ 0 → (∀ s ∈ Ine (F := ℚ) A, s x = x) → ∃ k : ℤ, A.valuation x = A.valuation (l : Ω) ^ k := by
  first | exact @GlobalTheory.InertiaFieldUnram.valuation_eq_zpow | exact GlobalTheory.InertiaFieldUnram.valuation_eq_zpow | (intros; apply GlobalTheory.InertiaFieldUnram.valuation_eq_zpow <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.padicValuation_thetaKernelJet_bound : ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → GoodLevel D Q → ∀ (P : Pair D ⊤ δ t0 Q) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (g : GA D P.a) (g' k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ∀ T, P.term g g' T ∈ Qbar ∧ ‖lamC lam (P.term g g' T)‖ ≤ (p : ℝ) ^ (((P.a * ∑ τ, P.n τ : ℕ) : ℝ) * (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) + ((P.a * P.d : ℕ) : ℝ) * (padicValNat p Q : ℝ)) := by
  first | exact @GlobalTheory.NormSum.Term.term_bound | exact GlobalTheory.NormSum.Term.term_bound | (intros; apply GlobalTheory.NormSum.Term.term_bound <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.isPow_of_gauss_valuation_congr_one_almost_all_primes : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → l ∣ M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ W : ValuationSubring X.K, Gauss X.jK V W → ∀ (n k : ℕ) (U : X.Kˣ), U ∈ X.Un (l ^ n) → Lev X (M₀ * l ^ k) U → W.valuation ((U : X.K) - 1) < 1 → ∃ g : X.Kˣ, U = g ^ (l ^ n) := by
  first | exact @GlobalTheory.KZ.ES.pow_of_gauss_congr_one | exact GlobalTheory.KZ.ES.pow_of_gauss_congr_one | (intros; apply GlobalTheory.KZ.ES.pow_of_gauss_congr_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

theorem _root_.GlobalTheory.T.fixed_element_lth_power_mod : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ a : fixA A, ∃ (b : fixA A) (z : A), (a : A) = (b : A) ^ l + (l : A) * z := by
  first | (exact @GlobalTheory.RecOne.fixA_eq_pow_add_mul) | (exact GlobalTheory.RecOne.fixA_eq_pow_add_mul) | (intros; apply GlobalTheory.RecOne.fixA_eq_pow_add_mul  <;> assumption)
end
