module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FaithfullyFlatOfTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle415
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersEqSumZetaPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle444
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle446
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle447
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle445
public import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle448
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

@[expose] public section

section

noncomputable section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions GlobalTheory.EtaleExact TensorProduct

namespace GlobalTheory.EtaleSub

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)


include E in
theorem surjective_of_tie (hfl : Module.Flat O RW) {T' T : LocLat G Qp LL O}
    (hfix : ∀ b, TWmap φR T' b = b → ∃ t : ↥T'.L.T, b = (1 : RW) ⊗ₜ[O] t)
    (hone : Function.Injective fun t : ↥T.L.T => (1 : RW) ⊗ₜ[O] t)
    (ι : LatHom T'.L T.L) (hι : Function.Injective ι.f) (m : ℕ) (hm : (m : LL) ≠ 0)
    (hall : ∀ x : W.DD T, ((m : ℕ) : W.EE) • x ∈ LinearMap.range (W.map ι)) :
    Function.Surjective ι.f := by
  have hU := span_range_map E ι
  have hkill : ∀ y : TW RW T, m • y ∈ LinearMap.range ((latMap ι).baseChange RW) := by
    intro y
    have hy : y ∈ Submodule.span RW (Set.range (E.jD T)) := by
      rw [E.jD_span T]; exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      rw [← hU]
      refine Submodule.subset_span ⟨_, hall x, ?_⟩
      rw [E.jD_smul, map_natCast, Nat.cast_smul_eq_nsmul]
    | zero => simp
    | add z w _ _ hz hw => rw [smul_add]; exact Submodule.add_mem _ hz hw
    | smul r z _ hz => rw [smul_comm]; exact Submodule.smul_mem _ r hz
  have hinj : Function.Injective ((latMap ι).baseChange RW) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := RW) (latMap ι)
      (fun x y hxy => Subtype.ext (hι (congrArg Subtype.val hxy)))
  have hcomm : ∀ c : TW RW T', (latMap ι).baseChange RW (TWmap φR T' c) =
      TWmap φR T ((latMap ι).baseChange RW c) := by
    intro c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul r t => simp [TWmap]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h2 : ∀ t : ↥T.L.T, ∃ t' : ↥T'.L.T, latMap ι t' = m • t := by
    intro t
    obtain ⟨c, hc⟩ := hkill ((1 : RW) ⊗ₜ[O] t)
    rw [← TensorProduct.tmul_smul] at hc
    have hf : TWmap φR T' c = c := by
      apply hinj
      rw [hcomm, hc]
      simp [TWmap]
    obtain ⟨t', rfl⟩ := hfix c hf
    refine ⟨t', hone ?_⟩
    simpa using hc
  have hle : (T.L.T : Set T.V) ⊆ (LinearMap.range ι.f : Submodule LL T.V) := by
    intro t ht
    obtain ⟨t', h'⟩ := h2 ⟨t, ht⟩
    refine ⟨(m : LL)⁻¹ • (t' : T'.V), ?_⟩
    have h3 : ι.f (t' : T'.V) = m • t := congrArg Subtype.val h'
    rw [map_smul, h3, ← Nat.cast_smul_eq_nsmul LL, smul_smul, inv_mul_cancel₀ hm, one_smul]
  have htop : LinearMap.range ι.f = ⊤ :=
    top_le_iff.1 (T.L.span ▸ Submodule.span_le.2 hle)
  exact LinearMap.range_eq_top.1 htop

end Generic

theorem exists_lattice_of_pow_mem : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), InvariantsGenerators.LitSub D HW F := by
  intro D HW F l _ K LL hA T D' hpow hφ hγ
  obtain ⟨T', ι, hι, hr⟩ := exists_sublattice (D.locA l) (HW l) (F l) K 1 LL hA.2.2 T D' hφ hγ
  obtain ⟨a, ha⟩ := hpow
  refine ⟨T', ι, ⟨hι, ?_⟩, hr⟩
  haveI := flat_RW LL
  haveI : CharZero ↥LL.1 := charZero_of_injective_algebraMap (algebraMap ℚ_[l] ↥LL.1).injective
  have hp : (((D.loc l).PD K).p : ℕ) = l := (D.loc l).PD_p K
  refine surjective_of_tie ((F l).E K 1 LL hA.2.2).tie (flat_RW LL)
    (fun b hb => ((GlobalTheory.WittTensorFixed.main l K LL T').2.1 b).1 hb)
    (GlobalTheory.WittTensorFixed.main l K LL T).2.2 ι hι (l ^ a) ?_ ?_
  · exact_mod_cast pow_ne_zero a (Fact.out : l.Prime).ne_zero
  · intro x
    rw [hr]
    have := ha x
    rw [hp] at this
    simpa using this

end GlobalTheory.EtaleSub
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.Cyc.LevelGen

theorem chain_pow {l : ℕ} {M : Type} [Monoid M] (ζ : ℕ → M) (h : ∀ j, ζ (j + 1) ^ l = ζ j)
    (j k : ℕ) : ζ (j + k) ^ (l ^ k) = ζ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc ζ (j + (k + 1)) ^ (l ^ (k + 1)) = (ζ (j + k + 1) ^ l) ^ (l ^ k) := by
          rw [pow_succ', pow_mul, ← add_assoc]
      _ = ζ j := by rw [h, ih]

theorem chain_primitive {l : ℕ} [Fact l.Prime] {M : Type} [CommMonoid M] (ζ : ℕ → M)
    (h0 : ζ 0 = 1) (h1 : ζ 1 ≠ 1) (h : ∀ j, ζ (j + 1) ^ l = ζ j) (j : ℕ) :
    IsPrimitiveRoot (ζ (j + 1)) (l ^ (j + 1)) := by
  have hfin : ζ (j + 1) ^ l ^ (j + 1) = 1 := by
    have := chain_pow ζ h 0 (j + 1)
    rw [zero_add] at this
    rw [this, h0]
  have hnot : ¬ ζ (j + 1) ^ l ^ j = 1 := by
    have := chain_pow ζ h 1 j
    rw [add_comm 1 j] at this
    rw [this]
    exact h1
  rw [← orderOf_eq_prime_pow hnot hfin]
  exact IsPrimitiveRoot.orderOf _

theorem mem_closure_all (l : ℕ) [Fact l.Prime] (K : FinExt l) (ζ : ℕ → Om l) (h0 : ζ 0 = 1)
    (h1 : ζ 1 ≠ 1) (h : ∀ j, ζ (j + 1) ^ l = ζ j) (s : ℕ) :
    ∀ α : Om l, α ∈ Ks K (s + 1) → ‖α‖ ≤ 1 → α ∈ AddSubgroup.closure
      {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (s + 1) ^ n} := by
  induction s with
  | zero =>
    intro α hα hn
    have hp : IsPrimitiveRoot (ζ (0 + 1)) l := by
      simpa using chain_primitive ζ h0 h1 h 0
    obtain ⟨y, hy, rfl⟩ := GlobalTheory.T.exists_integral_eq_sum_zeta_pow_level_one l K (ζ (0 + 1)) hp α hα hn
    refine AddSubgroup.sum_mem _ (fun a _ => AddSubgroup.subset_closure ?_)
    exact ⟨a, y a, (hy a).1, (hy a).2, mul_comm _ _⟩
  | succ s ih =>
    intro α hα hn
    have hp : IsPrimitiveRoot (ζ (s + 1 + 1)) (l ^ (s + 1 + 1)) := chain_primitive ζ h0 h1 h (s + 1)
    have hα' : α ∈ Ks K (s + 1 + 1) := hα
    obtain ⟨y, hy, rfl⟩ := (GlobalTheory.Cyc.integers_eq_sum_zeta_pow l K (s + 1 + 1) (by omega)
      (ζ (s + 1 + 1)) hp).1 α hα' hn
    refine AddSubgroup.sum_mem _ (fun a _ => ?_)
    have hya : y a ∈ Ks K (s + 1) := by simpa using (hy a).1
    have hmem := ih (y a) hya (hy a).2
    have hle : AddSubgroup.closure
        {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (s + 1) ^ n} ≤
        (AddSubgroup.closure
          {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (s + 1 + 1) ^ n}).comap
          (AddMonoidHom.mulLeft (ζ (s + 1 + 1) ^ (a : ℕ))) := by
      rw [AddSubgroup.closure_le]
      rintro x ⟨n, c, hc, hcn, rfl⟩
      apply AddSubgroup.subset_closure
      refine ⟨(a : ℕ) + l * n, c, hc, hcn, ?_⟩
      simp only [AddMonoidHom.coe_mulLeft]
      rw [← h (s + 1), pow_add, pow_mul]
      ring
    exact hle hmem

end GlobalTheory.Cyc.LevelGen


open GlobalTheory.Cyc.LevelGen in
theorem GlobalTheory.Cyc.integers_mem_closure_levels : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ζ : ℕ → Om l), ζ 0 = 1 → ζ 1 ≠ 1 → (∀ j, ζ (j + 1) ^ l = ζ j) → ∀ s : ℕ, 1 ≤ s → ∀ α : Om l, α ∈ Ks K s → ‖α‖ ≤ 1 → α ∈ AddSubgroup.closure {x : Om l | ∃ (j n : ℕ) (c : Om l), 1 ≤ j ∧ j ≤ s ∧ ¬ l ∣ n ∧ c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ j ^ n} := by
  intro l _ K ζ h0 h1 h s hs α hα hn
  set S : AddSubgroup (Om l) := AddSubgroup.closure
    {x : Om l | ∃ (j n : ℕ) (c : Om l), 1 ≤ j ∧ j ≤ s ∧ ¬ l ∣ n ∧ c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧
      x = c * ζ j ^ n} with hS
  have hl : 1 < l := (Fact.out : l.Prime).one_lt

  have hconst : ∀ c : Om l, c ∈ K0 K → ‖c‖ ≤ 1 → c ∈ S := by
    intro c hc hcn
    have hp : IsPrimitiveRoot (ζ 1) l := by simpa using chain_primitive ζ h0 h1 h 0
    have hsum := hp.geom_sum_eq_zero hl
    obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    have hr : Finset.range l = Finset.range (m + 1) := by rw [hm]
    rw [hr, Finset.sum_range_succ', pow_zero] at hsum
    have hc' : c = ∑ i ∈ Finset.range m, (-c) * ζ 1 ^ (i + 1) := by
      rw [← Finset.mul_sum, eq_neg_of_add_eq_zero_left hsum]
      ring
    rw [hc']
    refine AddSubgroup.sum_mem _ (fun i hi => AddSubgroup.subset_closure ?_)
    have hi' := Finset.mem_range.1 hi
    refine ⟨1, i + 1, -c, le_rfl, hs, ?_, neg_mem hc, by rwa [norm_neg], rfl⟩
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hlev : ∀ j, j ≤ s → ∀ (n : ℕ) (c : Om l), c ∈ K0 K → ‖c‖ ≤ 1 → c * ζ j ^ n ∈ S := by
    intro j
    induction j with
    | zero =>
      intro _ n c hc hcn
      rw [h0, one_pow, mul_one]
      exact hconst c hc hcn
    | succ j ih =>
      intro hj n c hc hcn
      by_cases hd : l ∣ n
      · obtain ⟨m, rfl⟩ := hd
        rw [pow_mul, h j]
        exact ih (by omega) m c hc hcn
      · exact AddSubgroup.subset_closure ⟨j + 1, n, c, by omega, hj, hd, hc, hcn, rfl⟩
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hmem := mem_closure_all l K ζ h0 h1 h t α hα hn
  have hle : AddSubgroup.closure
      {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (t + 1) ^ n} ≤ S := by
    rw [AddSubgroup.closure_le]
    rintro x ⟨n, c, hc, hcn, rfl⟩
    exact hlev (t + 1) le_rfl n c hc hcn
  exact hle hmem
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.FiniteRestrictionH1f

theorem mem_H1f_iff_res_mem : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Pr2b D HW F := by
  intro D HW F l _ K s LL h T _ κ
  have hfin := GKs_finiteIndex (D.loc l) K LL _ ((HW l).W K s LL h)
  refine (mem_H1fT_iff_res ((D.loc l).PD K) T ((HW l).W K s LL h).GKs κ).trans ?_
  constructor
  · rintro ⟨c, hx, hc⟩
    exact ⟨c, ⟨c.2, c.2.1, hx⟩, hc⟩
  · rintro ⟨c, ⟨-, -, hx⟩, hc⟩
    exact ⟨c, hx, hc⟩

end GlobalTheory.NL.FiniteRestrictionH1f
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.exists_globalStep_objects_of_cyclotomic_generator_inertia : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.admSS i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → ResSpan i ρ π → π ∈ D.nd.Z i → (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) → D.R.t + 1 < D.nd.l i → ∃ S : IdempotentChoiceData D.nd i, IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S := by
  first | exact @GlobalTheory.UseFive.objects_globalStep_gen | exact GlobalTheory.UseFive.objects_globalStep_gen | (intros; apply GlobalTheory.UseFive.objects_globalStep_gen <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.admissibleAtGoodPoints_of_coefRing_taken_at_live : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (X : KillingConditions.HubData D), GlobalTheory.CoefDuty.TakenAll D → GlobalTheory.PtCore.ResAbsIrr D → GlobalTheory.PtCore.PtFam D X.r X.ρ → ∀ i : D.nd.Loc, ∀ π ∈ D.nd.Zgood i, LargeLevelLemmas.adm51 (D := D) i (X.r i) (X.ρ i) π := by
  first | exact @GlobalTheory.AdmissibleCore.main | exact GlobalTheory.AdmissibleCore.main | (intros; apply GlobalTheory.AdmissibleCore.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.nonPlacePart_localBound_le_middleRange : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (c : ℝ), 1 ≤ c → KillingConditions.DataAD L HW X R → KillingConditions.InvariantsBoundsWithCoarseColumnConstant L X c → KillingConditions.BBLe L X (60 * c) := by
  first | exact @GlobalTheory.NLink.BBSize.main | exact GlobalTheory.NLink.BBSize.main | (intros; apply GlobalTheory.NLink.BBSize.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.RowBLong

theorem logb_le_self {l : ℕ} (hl : 11 ≤ l) {y : ℝ} (hy : 0 < y) : Real.logb l y ≤ y := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hlog : 1 ≤ Real.log l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have h1 := Real.log_le_sub_one_of_pos hy
  unfold Real.logb
  rcases le_or_gt 0 (Real.log y) with h | h
  · calc Real.log y / Real.log l ≤ Real.log y := div_le_self h hlog
      _ ≤ y := by linarith
  · have : Real.log y / Real.log l < 0 := div_neg_of_neg_of_pos h (by linarith)
    linarith

theorem logb_le_split {l : ℕ} (hl : 11 ≤ l) (j : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    Real.logb l H ≤ H / ((l : ℝ) - 1) ^ (j + 1) + ((j : ℝ) + 1) := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hm : 0 < ((l : ℝ) - 1) ^ (j + 1) := pow_pos (by linarith) _
  have hl1 : (1 : ℝ) < l := by linarith
  rcases hH.eq_or_lt with h0 | hpos
  · rw [← h0]; simp; positivity
  have hsplit : Real.logb l H = Real.logb l (H / ((l : ℝ) - 1) ^ (j + 1)) + Real.logb l (((l : ℝ) - 1) ^ (j + 1)) := by
    rw [Real.logb_div hpos.ne' hm.ne']; ring
  have h2 : Real.logb l (((l : ℝ) - 1) ^ (j + 1)) ≤ (j : ℝ) + 1 := by
    rw [Real.logb_pow]
    have h3 : Real.logb l ((l : ℝ) - 1) ≤ 1 := by
      have := Real.logb_le_logb_of_le hl1 (by linarith : (0:ℝ) < l - 1) (by linarith : (l:ℝ) - 1 ≤ l)
      rwa [Real.logb_self_eq_one hl1] at this
    push_cast
    have : (0:ℝ) ≤ (j:ℝ) + 1 := by positivity
    nlinarith
  rw [hsplit]
  have := logb_le_self hl (div_pos hpos hm)
  linarith

theorem bracket_le {l : ℕ} (hl : 11 ≤ l) (j : ℕ) {H G0 hB GP large₂ : ℝ} (hH0 : 0 ≤ H) (hG0 : 0 ≤ G0)
    (hGP : G0 ≤ GP) (hB0 : 0 ≤ hB) (hLg : 0 ≤ large₂) (hH : H ≤ hB ∨ H ≤ G0) :
    H / ((l : ℝ) - 1) ^ (j + 1) + (G0 + 1) * ((j : ℝ) + 1) + Real.logb l H ≤
      3 * (hB / ((l : ℝ) - 1) ^ (j + 1) + (GP + 1) * ((j : ℝ) + 1) + large₂) := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hm1 : 1 ≤ ((l : ℝ) - 1) ^ (j + 1) := one_le_pow₀ (by linarith)
  have hm : 0 < ((l : ℝ) - 1) ^ (j + 1) := by linarith
  have hlog := logb_le_split hl j hH0
  have hj : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  have hBm : 0 ≤ hB / ((l : ℝ) - 1) ^ (j + 1) := div_nonneg hB0 hm.le
  have hGj : (G0 + 1) * ((j : ℝ) + 1) ≤ (GP + 1) * ((j : ℝ) + 1) := by nlinarith
  have hj1 : (j : ℝ) + 1 ≤ (GP + 1) * ((j : ℝ) + 1) := by nlinarith
  rcases hH with h | h
  · have : H / ((l : ℝ) - 1) ^ (j + 1) ≤ hB / ((l : ℝ) - 1) ^ (j + 1) := div_le_div_of_nonneg_right h hm.le
    nlinarith
  · have h1 : H / ((l : ℝ) - 1) ^ (j + 1) ≤ H := div_le_self hH0 hm1
    have h2 : 2 * G0 + (j : ℝ) + 1 ≤ 2 * (G0 + 1) * ((j : ℝ) + 1) := by nlinarith
    nlinarith

end GlobalTheory.RowBLong

namespace GlobalTheory.RowBLong

open Formalism.MainNotions.N in
theorem nLet_eq_nLam {D : D7} {L : SizeData₂ D} {HW : HWOf D.loc} {i : D.nd.Loc}
    {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
    {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL} {Wd : WordDat (nLet i w hw)}
    (hb : WordBase L HW i r ρ π w hw Cx hG Wd) : nLet i w hw = Formalism.MainNotions.TwistedPlaces.nLam D w := by
  have hK : K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.mpr hb.unram
  have h1 : nLet i w hw = Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 :=
    (IntermediateField.equivOfEq hK).toLinearEquiv.finrank_eq
  rw [h1]
  exact hb.deg

end GlobalTheory.RowBLong

namespace GlobalTheory.RowBLong

attribute [local instance] Formalism.MainNotions.N.nLet_neZero

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), WachCoordinates.Conclusion2 D C₂ → 1 ≤ C₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → LocalRepresentationBoundCondition L HW C₂ i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowB L C₂ (D.nd.l i)) := by
  intro D L P HW C₂ i r ρ π dc hA hC _ h11 hJ
  intro w hw _ C hCg
  obtain ⟨hur, hWd⟩ := hJ w hw
  have hg : Good (D.nbr i w hw).Kw 1 C.LL := hCg.good_one (by omega) (le_trans (le_inf le_rfl hur) le_sup_left)
  obtain ⟨Wd, hb, hB⟩ := hWd C hg
  have hrow := GlobalTheory.Survey.InertPlacesGoodSet.rowL_of_wordsB hA h11 hb hB
  refine GlobalTheory.T.rowBound_at_place_of_latticeColengthBound D i r ρ π w hw C _ _ hrow ?_
  have hn : ((nLet i w hw : ℕ) : ℝ) = (Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ) := by
    exact_mod_cast nLet_eq_nLam hb
  have hl' : (11 : ℝ) ≤ D.nd.l i := by exact_mod_cast h11
  have hbr := bracket_le h11 (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i))
    (H := (WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) (G0 := ((Wd.w + Wd.S + Wd.η : ℕ) : ℝ))
    (hB := Formalism.MainNotions.TwistedPlaces.hB L) (GP := Formalism.MainNotions.TwistedPlaces.GP L) (large₂ := Formalism.MainNotions.TwistedPlaces.large₂ L)
    (by positivity) (by positivity)
    (by
      unfold Formalism.MainNotions.TwistedPlaces.GP
      have := hb.w_le; have := hb.S_le; have := hb.η_le
      push_cast; linarith)
    (by linarith [Formalism.MainNotions.TwistedPlaces.one_le_hB L]) (Formalism.MainNotions.TwistedPlaces.Lg_nonneg L)
    (by
      unfold WachCoordinates.hCor
      split_ifs
      · left; have := hb.h_le; push_cast; linarith
      · right; exact le_rfl)
  have key : C₂ * (((nLet i w hw : ℕ) : ℝ) + 1) * D.R.r *
      ((WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ) / ((D.nd.l i : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) + 1) +
        (((Wd.w + Wd.S + Wd.η : ℕ) : ℝ) + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) +
        Real.logb (D.nd.l i) (WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) ≤
      3 * C₂ * coreB L (D.nd.l i) w := by
    unfold coreB
    rw [hn]
    have h0 : 0 ≤ C₂ * ((Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ) + 1) * D.R.r := by
      have : (0:ℝ) ≤ C₂ := by linarith
      positivity
    calc _ ≤ C₂ * ((Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ) + 1) * D.R.r *
          (3 * (Formalism.MainNotions.TwistedPlaces.hB L / ((D.nd.l i : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) + 1) +
            (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) + Formalism.MainNotions.TwistedPlaces.large₂ L)) :=
          mul_le_mul_of_nonneg_left hbr h0
      _ = _ := by ring
  unfold lenRowB ratIn
  split_ifs with hlt
  · have := (exists_rat_btwn hlt).choose_spec
    linarith [this.1]
  · push_neg at hlt
    have hc0 : coreB L (D.nd.l i) w ≤ 0 := by linarith
    have : 3 * C₂ * coreB L (D.nd.l i) w ≤ 0 := by
      have : (0:ℝ) ≤ 3 * C₂ := by linarith
      nlinarith
    simp only [Rat.cast_zero]
    linarith

end GlobalTheory.RowBLong
end
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.decompositionGroup_acts_residues_frobeniusPower : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (_h : IsPlaceOver A w),
    ∀ d ∈ Dec (F := E) A, ∀ y : Ω, ∃ K : IntermediateField E Ω, FiniteDimensional E K ∧ y ∈ K ∧
      ∃ j : ℕ, ∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (d z - z ^ (normV w ^ j)) < 1 := by
  first | exact @GlobalTheory.DecFrobPow.exists_field_cong_pow | exact GlobalTheory.DecFrobPow.exists_field_cong_pow | (intros; apply GlobalTheory.DecFrobPow.exists_field_cong_pow <;> assumption)
end
