module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsMultiProjPrimeExtTo
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle009
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalNumberZeroOfHorizontalStatement
public import Development.WeilBound.CoreStatements.FlagImmersions.TwoMulThreePowLeFactorial
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle020
public import Development.WeilBound.CoreStatements.IdealCycleValues.GenNumLinearChangeClasses
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle013
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginHeightComparisonTwo
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle003
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle025
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle017
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionSectionRecursion
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.tower_identity_at_cutoff : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ), T.Proportional → FrobShape frob → T.Prop6 II frob → T.ThmBA II hh → ∀ B₀ : ℕ, 2 ≤ B₀ → ∃ A₀ b₀ : ℝ, T.IdentAt II hh frob B₀ A₀ b₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.exists_identAt | exact GlobalTheory.CompanionTheory.Ar.Top.exists_identAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.exists_identAt <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.ZpVert

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K : Type} {ι : K → Type}

theorem nonempty_residue_equiv (p : Nat.Primes) [Fact (p : ℕ).Prime] :
    Nonempty (ZMod (p : ℕ) ≃+* IsLocalRing.ResidueField (ZP p)) := by
  haveI hmax : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero)
  exact ⟨(Int.quotientSpanNatEquivZMod (p : ℕ)).symm.trans
    (IsLocalization.AtPrime.equivQuotMaximalIdeal (Ideal.span {((p : ℕ) : ℤ)}) (ZP p)).toRingEquiv⟩

theorem map_extTo {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (Q : Ideal (MRing ι ℤ)) :
    (extTo R Q).map (MvPolynomial.map g) = extTo S Q := by
  unfold extTo
  rw [Ideal.map_map]
  congr 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp
  · simp

theorem vNumL_extTo [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] (p : Nat.Primes)
    [Fact (p : ℕ).Prime] (Q : Ideal (MRing ι ℤ)) (l : List (K → ℤ)) :
    vNumL (extTo (ZP p) Q) l = intNumL (ZMod (p : ℕ)) (extTo (ZMod (p : ℕ)) Q) l := by
  obtain ⟨e⟩ := nonempty_residue_equiv p
  have h : specialIdeal (extTo (ZP p) Q) =
      (extTo (ZMod (p : ℕ)) Q).map (MvPolynomial.map (e : ZMod (p : ℕ) →+* _)) := by
    unfold specialIdeal
    rw [map_extTo, map_extTo]
  have h2 := intNumL_map_ringEquiv K ι (ZMod (p : ℕ)) (IsLocalRing.ResidueField (ZP p)) e
    (extTo (ZMod (p : ℕ)) Q) l
  rw [← h2, ← h]
  rfl

theorem divCycle_extTo [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] (p : Nat.Primes)
    (P : Ideal (MRing ι ℤ)) (f : MRing ι ℤ) (W' : Ideal (MRing ι (ZP p))) (hW' : W'.IsPrime) :
    divCycle (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) f) W' =
      divCycle P f (W'.comap (MvPolynomial.map (Int.castRingHom (ZP p)))) := by
  have h := divCycle_map_localisation K ι ℤ (ZP p) (Ideal.span {((p : ℕ) : ℤ)}).primeCompl P f W' hW'
  have e : algebraMap ℤ (ZP p) = Int.castRingHom (ZP p) := RingHom.ext_int _ _
  rw [e] at h
  exact h

theorem isPrime_of_ne {R : Type} [CommRing R] {P : Ideal (MRing ι R)} {f : MRing ι R}
    {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) : W.IsPrime := by
  unfold divCycle at h
  split_ifs at h with hc
  · exact hc.1.1.1
  · exact absurd rfl h

theorem disjoint_consts_of_mem (p : Nat.Primes) {W : Ideal (MRing ι ℤ)} (hW : W.IsPrime)
    (hp : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W) :
    Disjoint (ZpModel.consts ι p : Set (MRing ι ℤ)) (W : Set (MRing ι ℤ)) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨s, hs, rfl⟩ hmem
  have hs' : s ∉ Ideal.span {((p : ℕ) : ℤ)} := hs
  have hdvd : ¬ ((p : ℕ) : ℤ) ∣ s := fun h => hs' (Ideal.mem_span_singleton.2 h)
  obtain ⟨u, v, huv⟩ := (Nat.prime_iff_prime_int.1 p.2).irreducible.coprime_iff_not_dvd.2 hdvd
  have h1 : (C (u * ((p : ℕ) : ℤ) + v * s) : MRing ι ℤ) ∈ W := by
    rw [C_add, C_mul, C_mul]
    exact W.add_mem (W.mul_mem_left _ hp) (W.mul_mem_left _ hmem)
  rw [huv, C_1] at h1
  exact hW.ne_top ((Ideal.eq_top_iff_one W).2 h1)

theorem finsum_eq_mem {α : Type*} (g : α → ℤ) (t : Set α) (h : Function.support g ⊆ t) :
    ∑ᶠ x, g x = ∑ᶠ x ∈ t, g x := by
  rw [← finsum_mem_univ g]
  refine finsum_mem_inter_support_eq g _ _ ?_
  rw [Set.univ_inter, Set.inter_eq_right.2 h]

theorem extTo_comap (p : Nat.Primes) (W' : Ideal (MRing ι (ZP p))) :
    extTo (ZP p) (W'.comap (MvPolynomial.map (Int.castRingHom (ZP p)))) = W' := by
  haveI := ZpModel.isLocalization_consts ι p
  rw [ZpModel.extTo_eq, ← ZpModel.algebraMap_eq]
  exact IsLocalization.map_under (ZpModel.consts ι p) (MRing ι (ZP p)) W'

theorem bijOn_comap [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] (p : Nat.Primes)
    (P : Ideal (MRing ι ℤ)) (f : MRing ι ℤ) :
    Set.BijOn (fun W' : Ideal (MRing ι (ZP p)) => W'.comap (MvPolynomial.map (Int.castRingHom (ZP p))))
      {W' | divCycle (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) f) W' ≠ 0 ∧
        (C ((p : ℕ) : ZP p) : MRing ι (ZP p)) ∈ W'}
      {W | divCycle P f W ≠ 0 ∧ (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W} := by
  have hCmap : MvPolynomial.map (Int.castRingHom (ZP p)) (C ((p : ℕ) : ℤ) : MRing ι ℤ) =
      (C ((p : ℕ) : ZP p) : MRing ι (ZP p)) := by
    rw [map_C]
    simp
  haveI := ZpModel.isLocalization_consts ι p
  refine ⟨?_, ?_, ?_⟩
  · rintro W' ⟨hW', hp⟩
    refine ⟨?_, ?_⟩
    · rw [← divCycle_extTo p P f W' (isPrime_of_ne hW')]
      exact hW'
    · show MvPolynomial.map (Int.castRingHom (ZP p)) (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W'
      rwa [hCmap]
  · rintro W₁ - W₂ - h
    calc W₁ = extTo (ZP p) (W₁.comap (MvPolynomial.map (Int.castRingHom (ZP p)))) := (extTo_comap p W₁).symm
      _ = extTo (ZP p) (W₂.comap (MvPolynomial.map (Int.castRingHom (ZP p)))) := congrArg _ h
      _ = W₂ := extTo_comap p W₂
  · rintro W ⟨hW, hp⟩
    have hWp : W.IsPrime := isPrime_of_ne hW
    have hd := disjoint_consts_of_mem p hWp hp
    have hprime : (extTo (ZP p) W).IsPrime := by
      rw [ZpModel.extTo_eq]
      exact IsLocalization.isPrime_of_isPrime_disjoint (ZpModel.consts ι p) _ W hWp hd
    have hcomap : (extTo (ZP p) W).comap (MvPolynomial.map (Int.castRingHom (ZP p))) = W := by
      have h := IsLocalization.under_map_of_isPrime_disjoint (ZpModel.consts ι p) (MRing ι (ZP p)) hWp hd
      rw [ZpModel.extTo_eq, ← ZpModel.algebraMap_eq]
      exact h
    refine ⟨extTo (ZP p) W, ⟨?_, ?_⟩, hcomap⟩
    · rw [divCycle_extTo p P f _ hprime, hcomap]
      exact hW
    · rw [← hCmap]
      exact Ideal.mem_map_of_mem _ hp

end

end GlobalTheory.CompanionTheory.Ar.Num.ZpVert


open GlobalTheory.CompanionTheory.Ar.Num.ZpVert in
theorem GlobalTheory.CompanionTheory.Ar.Num.vertAt_eq_cycList : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (p : Nat.Primes) (a : K → ℕ) (f : MRing ι ℤ), IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = D → vertAt p P f l = cycList (divCycle (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) f)) l := by
  intro K _ _ ι _ P D hP p a f hf hfP l hl
  classical
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  obtain ⟨hirr, hmodel, -⟩ := zp_model K ι P D hP p
  have hfP' : MvPolynomial.map (Int.castRingHom (ZP p)) f ∉ extTo (ZP p) P :=
    fun h => hfP (ZpModel.mem_of_map_mem p hP.2.1.1 hP.2.2.1 h)
  have hf' : IsMultiHomog (MvPolynomial.map (Int.castRingHom (ZP p)) f) a := by
    intro d hd
    refine hf fun h0 => hd ?_
    rw [coeff_map, h0, map_zero]
  unfold vertAt cycList cycEval
  rw [finsum_eq_mem _ {W | divCycle P f W ≠ 0 ∧ (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W},
    finsum_eq_mem _ {W' | divCycle (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) f) W' ≠ 0 ∧
        (C ((p : ℕ) : ZP p) : MRing ι (ZP p)) ∈ W'}]
  · symm
    refine finsum_mem_eq_of_bijOn _ (bijOn_comap p P f) ?_
    rintro W' ⟨hW', hp⟩
    have hWp : W'.IsPrime := isPrime_of_ne hW'
    have hQp : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W'.comap (MvPolynomial.map (Int.castRingHom (ZP p))) := by
      show MvPolynomial.map (Int.castRingHom (ZP p)) (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W'
      rw [map_C]
      simpa using hp
    rw [divCycle_extTo p P f W' hWp]
    beta_reduce
    rw [if_pos hQp]
    congr 1
    have h := vNumL_extTo p (W'.comap (MvPolynomial.map (Int.castRingHom (ZP p)))) l
    rw [extTo_comap] at h
    exact h
  · intro W' hW'
    have h1 := left_ne_zero_of_mul hW'
    refine ⟨h1, ?_⟩
    by_contra hp
    have h0 := GlobalTheory.T.vertical_number_zero_of_horizontal (ZP p) ((p : ℕ) : ZP p) hirr K ι (extTo (ZP p) P) D hmodel a _ hf' hfP' W' h1 hp l hl
    exact right_ne_zero_of_mul hW' h0
  · intro W hW
    have h1 := left_ne_zero_of_mul hW
    refine ⟨h1, ?_⟩
    by_contra hp
    exact right_ne_zero_of_mul hW (if_neg hp)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem restSum_total_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (u : Wt Ψ N) (g : ℝ) (B : ℕ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → WeightHyp j u g → bigB0 u g < B + 1 → IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q → |∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum j bad frob B τ k (Q τ k)| ≤ 2 * (((dimFl Ψ N : ℝ) + 1) * flagDeg u) * ((min j (N - j) : ℕ) * spread u) :=
  RootFieldNumerics.rest_sum_total_bound

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_dvr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (p : ℕ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (τ : Ψ) (Q : MvPolynomial (Ψ × Fin N) ℝ) (Hs : Ψ × Fin N → MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ), Q.IsHomogeneous (d + 1 - k) → (∀ i, (Hs i).IsHomogeneous (d - k)) → (k = d + 1 → ∀ i, Hs i = 0) → ∀ T : LocPair ι O (Ψ × Fin N), T.IsVert P ϖ → FlagChernComparison P d p j φ T → PowerSumsVanish P d (fun i : Fin N => T.x' (τ, i)) → T.val P (fun i => (∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i), rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a))) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q + (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) = cycNum (divCycle P (C (p : O))) T.x (bracket j φ p k τ * Q) [] := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP p Ψ _ _ N j φ k hk1 hkd τ Q Hs hQ hHs hH0 T hT hM hPS
  obtain ⟨hadd, hsmul, -⟩ := GlobalTheory.T.local_pair_value_linear O K ι (Ψ × Fin N) T P
  have hB : T.val P (fun i => (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) = 0 := by
    rcases Nat.lt_or_ge k (d + 1) with hlt | hge
    · exact GlobalTheory.T.vertical_pair_power_sum_vanish O ϖ hϖ K ι P d hP (Ψ × Fin N) T hT N (fun a => (τ, a)) hPS k (d - k) hk1
        (by omega) Hs hHs
    · have hk : k = d + 1 := by omega
      have h0 := hsmul 0 (fun _ => 0)
      simp only [mul_zero, zero_mul] at h0
      have hfun : (fun i => (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) =
          (fun _ => (0 : MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ)) := by
        funext i
        rw [hH0 hk i, mul_zero]
      rw [hfun]
      exact h0
  have hA : T.val P (fun i => (∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i),
        rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a)))
          (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q) =
      cycNum (divCycle P (C (p : O))) T.x (bracket j φ p k τ * Q) [] := by
    rw [GlobalTheory.T.local_pair_power_sum_value O K ι (Ψ × Fin N) T P N k (fun a => (τ, a)) (rename Sum.inl Q),
      support_rename_of_injective Sum.inl_injective,
      Finset.sum_image (Finsupp.mapDomain_injective Sum.inl_injective).injOn,
      GlobalTheory.T.cycle_number_mul_expand O K ι (Ψ × Fin N) (divCycle P (C (p : O))) T.x (bracket j φ p k τ) Q []]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hcl : classList (Sum.elim T.x T.x') (Finsupp.mapDomain Sum.inl μ) = classList T.x μ := by
      have hm : Finsupp.toMultiset (Finsupp.mapDomain (Sum.inl : Ψ × Fin N → (Ψ × Fin N) ⊕ (Ψ × Fin N)) μ) =
          (Finsupp.toMultiset μ).map Sum.inl := (Finsupp.toMultiset_map μ Sum.inl).symm
      unfold classList
      rw [hm, Multiset.map_map]
      rfl
    have hdeg : (classList T.x μ).length + k = d + 1 := by
      have h1 : (classList T.x μ).length = d + 1 - k := by
        have h2 := hQ (mem_support_iff.mp hμ)
        unfold classList
        rw [Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
        rw [Finsupp.weight_apply] at h2
        exact (by simpa using h2 : (μ.sum fun _ c => c) = d + 1 - k)
      omega
    rw [coeff_rename_mapDomain _ Sum.inl_injective, hcl, List.append_nil, hM τ k hk1 _ hdeg]
  exact (hadd _ _).trans (by rw [hA, hB, add_zero])
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem genNum_linear_subst : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime V → ringKrullDim (MRing ι F ⧸ V) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → genNum F V (fun t => ∑ i, M t i • cls i) H Q = genNum F V cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q := by
  exact @BaseChangeColon.genNum_linear_change_classes

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.root_origin_height_comparison_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (M₀ M₁ : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o₀ : RootOrigin Y S₀ M₀ Fx) (o₁ : RootOrigin Y S M₁ Fx) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (κ₀ : M₀.K → K) (v₀ : (Σ k, M₀.ι k) → Σ k, J k) (κ₁ : M₁.K → K) (v₁ : (Σ k, M₁.ι k) → Σ k, J k) (i₀ : M₀.Ω →+* Ω) (i₁ : M₁.Ω →+* Ω) (h₀ : IsBlockMap κ₀ v₀) (h₁ : IsBlockMap κ₁ v₁), (∀ p, y (v₀ p) = i₀ (M₀.y p)) → (∀ p, y (v₁ p) = i₁ (M₁.y p)) → i₀.comp o₀.g = i₁.comp o₁.g → IsArithVar (mCoordIdeal y) (dimFl (CMType H) (D.p + D.q) + 1) → ∃ T : LocPair J ℤ Unit, T.x () = (pullHerm h₀ M₀.A).a ∧ T.x' () = (pullHerm h₁ M₁.A).a ∧ T.IsVertOff (mCoordIdeal y) ∅ ∧ T.IsIsometric (mCoordIdeal y) (fun _ => pullHerm h₀ M₀.A) (fun _ => pullHerm h₁ M₁.A) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.LineUnit.lines_isometric | exact GlobalTheory.CompanionTheory.Ar.Top.LineUnit.lines_isometric | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.LineUnit.lines_isometric <;> assumption)
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Indep

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem pp_monomial (M : Top.RootModel Ψ N) (II : IntersectionSystem) (m : Option (Ψ × Fin N) →₀ ℕ) (a : ℝ) :
    M.PP II (monomial m a) = a * limUnder (𝓝[>] (0:ℝ)) (fun t => M.arMono II t m) := by
  have : (monomial m a : Top.RPA Ψ N) = a • basisMonomials (Option (Ψ × Fin N)) ℝ m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, Top.RootModel.PP, Module.Basis.constr_basis, smul_eq_mul]

end GlobalTheory.CompanionTheory.Ar.Indep

namespace GlobalTheory.CompanionTheory.Ar.Indep

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem pp_toA_eq_of_tendsto (M M' : Top.RootModel Ψ N) (II : IntersectionSystem) (hconv : M.Converges II)
    (h : ∀ m : (Ψ × Fin N) →₀ ℕ, Tendsto (fun t => M.arMono II t (m.mapDomain some) -
      M'.arMono II t (m.mapDomain some)) (𝓝[>] (0:ℝ)) (𝓝 0)) (F : Top.RP Ψ N) :
    M.PP II (Top.toA F) = M'.PP II (Top.toA F) := by
  rw [F.as_sum]

  simp only [Top.toA, map_sum, rename_monomial, pp_monomial]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  obtain ⟨L, hL⟩ := hconv (m.mapDomain some)
  have hL' : Tendsto (fun t => M'.arMono II t (m.mapDomain some)) (𝓝[>] (0:ℝ)) (𝓝 L) := by
    have := hL.sub (h m)
    simpa using this
  rw [hL.limUnder_eq, hL'.limUnder_eq]

end GlobalTheory.CompanionTheory.Ar.Indep

namespace GlobalTheory.CompanionTheory.Ar.Indep

theorem spectrumMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem cst_of_factor {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (A : HodgeCpt Y S y)
    (hβ : Mono (spMap β)) (x : Sp A.Ω₀ ⟶ Xo.XF c) (hx : A.ξ₀ = x ≫ Y.j) :
    spMap A.fn ≫ x ≫ Limits.pullback.snd _ _ = spMap A.cst := by
  rw [← cancel_mono (spMap β), spectrumMap_comp, ← A.cst_over, ← Y.jQ_over]
  have h1 : A.ξ ≫ A.f = spMap A.fn ≫ x ≫ Y.jQ ≫ Limits.pullback.fst _ _ := by
    have := A.fn_over
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at this
    rw [this, hx]; rfl
  have h2 := h1 =≫ Y.s
  simp only [Category.assoc] at h2 ⊢
  rw [← Limits.pullback.condition]
  exact h2.symm

theorem imageCpt_refl_of_genPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y'), Mono (spMap β) → genPt A.ξ₀ = genPt A'.ξ₀ → IsImageCpt (Iso.refl Xo.X) A A' := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω Ω' _ _ K K' _ _ J J' y y' A A' hβ hgen
  obtain ⟨x, hx⟩ := GlobalTheory.T.hodge_component_factor_point E H D l Xo c O β Y S Ω K J y A hβ
  obtain ⟨x', hx'⟩ := GlobalTheory.T.hodge_component_factor_point E H D l Xo c O β Y S Ω' K' J' y' A' hβ
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.generic_point_field_iso Y.X A.Ω₀ A'.Ω₀ A.ξ₀ A'.ξ₀ A.gen₀ A'.gen₀ hgen
  haveI : Mono Y.j := by
    haveI := hβ
    haveI := Y.jQ_open
    unfold Model.j
    infer_instance
  have hxx : spMap ψ.toRingHom ≫ x' = x := by
    rw [← cancel_mono Y.j, Category.assoc, ← hx', ← hx, hψ]
  refine ⟨x, x', ψ, hx, hx', ?_, ?_, cst_of_factor A hβ x hx, cst_of_factor A' hβ x' hx'⟩
  · rw [← Category.assoc, hxx]
    exact (congrArg (x ≫ ·) (Category.comp_id _)).symm
  · rw [← Category.assoc, hxx]

end GlobalTheory.CompanionTheory.Ar.Indep

namespace GlobalTheory.CompanionTheory.Ar.Indep

end GlobalTheory.CompanionTheory.Ar.Indep
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.root_model_comparison_limit : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M₁ M₂ : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (σ : Type) [Fintype σ] [DecidableEq σ] (ℓ₁ : ℝ → σ → HermLine M₁.ι) (ℓ₂ : ℝ → σ → HermLine M₂.ι) (n : Ψ × Fin N → σ → ℤ) (s : Ψ × Fin N → Ψ × Fin N) (e₁ e₂ : ℕ), e₁ ≠ 0 → e₁ * M₁.δ = e₂ * M₂.δ → (∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ a, IsSmoothHerm (ℓ₁ t a) ∧ IsSmoothHerm (ℓ₂ t a)) ∧ (∀ r, (M₁.x t (s r)).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₁ t) (n r)).a ∧ ∀ z ∈ mcPts M₁.P, (M₁.x t (s r)).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₁ t) (n r)).h z) ∧ ∀ r, (M₂.x t r).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₂ t) (n r)).a ∧ ∀ z ∈ mcPts M₂.P, (M₂.x t r).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₂ t) (n r)).h z) → (∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ, Tendsto (fun t => (e₁ : ℝ) * II _ _ M₁.P _ (fun j => ℓ₁ t (w j)) - (e₂ : ℝ) * II _ _ M₂.P _ (fun j => ℓ₂ t (w j))) (𝓝[>] 0) (𝓝 0)) → ∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → Ψ × Fin N, Tendsto (fun t => II _ _ M₁.P _ (fun j => M₁.x t (s (w j))) / M₁.δ - II _ _ M₂.P _ (fun j => M₂.x t (w j)) / M₂.δ) (𝓝[>] 0) (𝓝 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.Root.cmp_root | exact GlobalTheory.CompanionTheory.Ar.Cmp.Root.cmp_root | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.Root.cmp_root <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.arith_intersection_section_recursion : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : Ω), IsArithVar (mCoordIdeal y) (e + 2) → Birational y → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → s ≠ 0 → s ∈ chartLat y A.a 1 → (∀ W, IsArithVar W (e + 1) → mCoordIdeal y ≤ W → 0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1)) → 0 ≤ ptsIntegral (mCoordIdeal y) (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.eff_lat | exact GlobalTheory.CompanionTheory.Ar.Top.eff_lat | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.eff_lat <;> assumption)
end
