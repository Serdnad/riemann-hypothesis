module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle044
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle057
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle005
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle036
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle043
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle033
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle056
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle017
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle055
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle059
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle008
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle060
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualBasisTraceLogNorm
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PeriodGramHermitianSignature
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle007
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PHolomorphicImplicitGraph
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPolyLocalGenerators
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle011
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem lattice_facts_of_normal : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → D.Facts R p w χ φ := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hb hp hn hf hi φ ht h1 h2
  have hleaf := GlobalTheory.T.hodge_annihilator_lattice_holds D R p w χ hc hb hp hn hf hi φ ht h1
  have hseq := GlobalTheory.T.hodge_image_lattice D R p w χ hc hb hp hn hf hi φ ht h1 h2
  obtain ⟨hdx, honto, hinj⟩ := GlobalTheory.T.hodge_divisor_ideal_lattice D R p w χ hc hb hp hn hf hi φ ht h1 h2
  exact
    { le_af := hleaf
      im := fun τ => (hseq τ).1
      ker := fun τ => (hseq τ).2
      dx := hdx
      onto := honto
      inj := hinj }

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.FamLines

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {V : Type} [AddCommGroup V] [Module Ω V]

theorem exists_finset {R : Subalgebra o Ω} {r : ℕ} {L : AddSubgroup V} (h : LocFree R r L) :
    ∃ S : Finset V, L = spanOver R (S : Set V) := by
  classical
  let L' : Submodule R V := { L with smul_mem' := fun a e he => h.1 a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L') (r := r) h
  refine ⟨Finset.univ.image fun i => (v i : V), le_antisymm (fun e he => ?_) ?_⟩
  · rw [← hv e]
    · refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨φ i e, hφ i e he, v i, ?_, rfl⟩
      simp
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, e, he, rfl⟩
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at he
    obtain ⟨i, rfl⟩ := he
    exact h.1 a ha _ (v i).2

theorem ne_bot {R : Subalgebra o Ω} {L : AddSubgroup V} (h : LocFree R 1 L) : L ≠ ⊥ := by
  obtain ⟨-, k, f, c, -, -, hs, hb⟩ := h
  have hex : ∃ l, f l ≠ 0 := by
    by_contra hn
    push Not at hn
    simp [hn] at hs
  obtain ⟨l, hl⟩ := hex
  obtain ⟨b, hli, -, hb⟩ := hb l
  obtain ⟨m, hm⟩ := (hb (b 0)).2 ⟨fun _ => 1, fun _ => ⟨0, by simp⟩, by simp⟩
  rintro rfl
  exact smul_ne_zero (pow_ne_zero m hl) (hli.ne_zero 0) (AddSubgroup.mem_bot.1 hm)

theorem injective {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω} {d : ℕ}
    (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) :
    Function.Injective (algebraMap O Ω) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have h1 : a ∈ (mcIdeal O x).comap (C : O →+* _) := by
    rw [Ideal.mem_comap, mcIdeal, RingHom.mem_ker]
    change GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap O x (algebraMap O _ a) = 0
    rw [AlgHom.commutes, MvPolynomial.algebraMap_apply, ha, map_zero]
  rw [h.2.2.1] at h1
  exact h1

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O (joinCoord x z) u a fun c => (pullFamily O x z D c).xId (fun a => algebraMap O Ω (χ τ a)) i) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hx hfn F _ _ _ n Sg _ r s p hp w χ φ D hD hG
  have hinj := injective hx
  have hchar : ∀ R : Subalgebra O Ω,
      CharData R p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) := by
    intro R
    obtain ⟨hp0, ⟨u, hu, huw⟩, -, h01, hχ⟩ := hD.char
    refine ⟨?_, R.algebraMap_mem _, ?_, h01, fun τ => ⟨?_, ?_, fun a => R.algebraMap_mem _⟩⟩
    · rw [← map_natCast (algebraMap O Ω)]
      exact fun h => hp0 (hinj (h.trans (map_zero _).symm))
    · obtain ⟨u, rfl⟩ := hu
      refine ⟨algebraMap O Ω (↑u⁻¹ * w ^ (p - 2)), R.algebraMap_mem _, ?_⟩
      rw [← map_mul, ← map_natCast (algebraMap O Ω), mul_assoc, ← pow_succ,
        show p - 2 + 1 = p - 1 by have := hp.two_le; omega, huw, Units.inv_mul_cancel_left]
    · simp [(hχ τ).1]
    · simp [(hχ τ).2]
  have hbc := fun c (hc : mseg x c ≠ 0) =>
    GlobalTheory.T.lattice_good_base_change (D c) (chartRing O (mseg x) c) p _ _ (hchar _) (hD.base c hc) (hG c hc)
  have hfam := (GlobalTheory.T.lattice_family_injective_model_facts O Ω K ι x hinj p hp w χ φ D hD).2
  obtain ⟨K', i1, i2, ι', i3, z, hz, hl⟩ := GlobalTheory.T.line_lattice_family_model O Ω K ι x d hx hfn (Sg × Fin n)
    (fun j c => (D c).xId (fun a => algebraMap O Ω (χ j.1 a)) j.2) fun j =>
      ⟨((hfam j.1).2.1 j.2).1, fun c hc =>
        ⟨ne_bot (((hbc c hc).1 j.1).2.2.2 j.2),
          exists_finset (((hbc c hc).1 j.1).2.2.2 j.2)⟩⟩
  refine ⟨K', i1, i2, ι', i3, z, hz, fun τ i => ?_⟩
  obtain ⟨a, ha⟩ := hl (τ, i)
  refine ⟨1, a, one_ne_zero, fun c hc v => ?_⟩
  obtain ⟨hc', hle⟩ := ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.2 K' ι' z).2 c hc
  have h := (((hbc _ hc').2 Ω (chartRing O (mseg (joinCoord x z)) c) fun a ha => hle ha).2 τ).2.2 i
  rw [← ha c hc v]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Set.image_id'] at h
  simp only [pullFamily, h]

end GlobalTheory.CompanionTheory.Ar.FamLines
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem _root_.GlobalTheory.T.lattice_family_injective_model : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), IsLatticeFamily O (joinCoord x z) p w χ φ (pullFamily O x z D) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₁ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) ∧ ((∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg (joinCoord x z)) c) _) ≤ (pullFamily O x z D c).af (chartRing O (mseg (joinCoord x z)) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₂ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))))) ∧ ((∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O (joinCoord x z) u a fun c => (pullFamily O x z D c).xId (fun a => algebraMap O Ω (χ τ a)) i))) ∧ ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → ∃ (Lie' W' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (r τ) (Fin (r τ) → Ω)) (Om' OmHT' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (s τ) (Fin (s τ) → Ω)), HasBundles O (joinCoord x z) (pullFamily O x z D) Lie' W' Om' OmHT' ∧ ∀ τ, IsPull O x z (Lie τ) (Lie' τ) ∧ IsPull O x z (W τ) (W' τ) ∧ IsPull O x z (Om τ) (Om' τ) ∧ IsPull O x z (OmHT τ) (OmHT' τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FamPull.main | exact GlobalTheory.CompanionTheory.Ar.FamPull.main | (intros; apply GlobalTheory.CompanionTheory.Ar.FamPull.main <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.FrobEst

def dotOrth {K : Type} [Field K] {d : ℕ} (X : Submodule K (Fin d → K)) :
    Submodule K (Fin d → K) where
  carrier := {u | ∀ φ ∈ X, u ⬝ᵥ φ = 0}
  add_mem' := fun {a b} ha hb φ hφ => by rw [add_dotProduct, ha φ hφ, hb φ hφ, add_zero]
  zero_mem' := fun φ _ => zero_dotProduct φ
  smul_mem' := fun c u hu φ hφ => by rw [smul_dotProduct, hu φ hφ, smul_zero]

theorem frob_estimate : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (O : Type) [CommRing O] [StarRing O] (d : ℕ) (D : ConjData C p O d), 2 < p →
    0 ≤ deg C (dotDual C D.lie) ∧
      ∀ W : Submodule K (Fin d → K),
        ((p : ℤ) - 2) * subDeg C D.lie W ≤ deg C (dotDual C D.lie) := by
  intro K _ C p _ _ O _ _ d D hp
  obtain ⟨h0, W₀, hW₀⟩ := GlobalTheory.T.sub_degree_bot_and_max_exists K C (Fin d → K) D.lie D.lie_bun
  have hp2 : (0 : ℤ) < (p : ℤ) - 2 := by
    have : (2 : ℤ) < (p : ℤ) := by exact_mod_cast hp
    linarith
  have hf := GlobalTheory.CompanionTheory.Ar.Crv.SubFrob.subDeg_frob K C p d D.lie W₀ D.lie_bun
  have h1 := GlobalTheory.T.sub_degree_mono_injective_hom K C (Fin d → K) ((Fin d → K) × (Fin d → K))
    (frobLat C p D.lie) D.H D.α (frobSub p W₀)
    (GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat K C p d D.lie D.lie_bun).1 D.H_bun D.conj.1
    (fun i x hx => (D.conj.2.2.2.1 i x).1 hx)
  have h2 := GlobalTheory.T.short_exact_sub_degree_bound K C (Fin d → K) ((Fin d → K) × (Fin d → K)) (Fin d → K)
    (dotDual C D.lie) D.H D.lie (LinearMap.inr K (Fin d → K) (Fin d → K))
    (LinearMap.fst K (Fin d → K) (Fin d → K)) (Submodule.map D.α (frobSub p W₀)) D.H_bun D.hodge
  have h3 := GlobalTheory.T.dot_dual_sub_degree_annihilator K C d D.lie
    (dotOrth (Submodule.comap (LinearMap.inr K (Fin d → K) (Fin d → K))
      (Submodule.map D.α (frobSub p W₀))))
    (Submodule.comap (LinearMap.inr K (Fin d → K) (Fin d → K))
      (Submodule.map D.α (frobSub p W₀))) D.lie_bun (fun u => Iff.rfl)
  have h4 := hW₀ (Submodule.map (LinearMap.fst K (Fin d → K) (Fin d → K))
    (Submodule.map D.α (frobSub p W₀)))
  have h5 := hW₀ (dotOrth (Submodule.comap (LinearMap.inr K (Fin d → K) (Fin d → K))
    (Submodule.map D.α (frobSub p W₀))))
  have hr : ((p : ℤ) - 2) * subDeg C D.lie W₀ = (p : ℤ) * subDeg C D.lie W₀ - 2 * subDeg C D.lie W₀ := by
    ring
  have key : ((p : ℤ) - 2) * subDeg C D.lie W₀ ≤ deg C (dotDual C D.lie) := by
    linarith
  have hμ : 0 ≤ subDeg C D.lie W₀ := by
    have := hW₀ ⊥
    linarith
  refine ⟨?_, fun W => ?_⟩
  · have := mul_nonneg hp2.le hμ
    linarith
  · have := mul_le_mul_of_nonneg_left (hW₀ W) hp2.le
    linarith

end GlobalTheory.CompanionTheory.Ar.Crv.FrobEst
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.conjugate_eigen_sub_degree_eq : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ s t : S, (∀ a, χ t a = χ s (star a)) → subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) = subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.ConjEq.subDeg_eig_conj | exact GlobalTheory.CompanionTheory.Ar.Crv.ConjEq.subDeg_eig_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.ConjEq.subDeg_eig_conj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.gram_determinant_log_different : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x : I → D.La) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x).det‖ = -(Fintype.card I : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.GramDet.log_norm_det_gramE | exact GlobalTheory.CompanionTheory.Ar.Fl.GramDet.log_norm_det_gramE | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.GramDet.log_norm_det_gramE <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.dual_basis_trace_log_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : Nat.Primes) (f : ℕ) (b : Fin f → 𝓞 E), IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b → ∃ b' : Fin f → E, (∀ (K : Type) [Field K] (σ σ' : E →+* K), σ (H.rt : E) = σ' (H.rt : E) → (σ = σ' → ∑ k, σ (b' k) * σ' (b k : E) = 1) ∧ (σ ≠ σ' → ∑ k, σ (b' k) * σ' (b k : E) = 0)) ∧ ∀ j : E →+* ℂ_[ℓ], 0 < (⨆ k, ‖j (b' k)‖) ∧ Real.log (⨆ k, ‖j (b' k)‖) = Real.log ‖j (H.rt : E)‖ - logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RelDual.relative_dual | exact GlobalTheory.CompanionTheory.Ar.RelDual.relative_dual | (intros; apply GlobalTheory.CompanionTheory.Ar.RelDual.relative_dual <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (e : I → D.La), Fintype.card I = D.p + D.q → LinearIndependent (𝓞 E) e → (gramE D e).det ≠ 0 ∧ {ℓ : Nat.Primes | ¬ IsLocBasis (𝓞 E) ℓ e}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.Relay.gram_det_ne_zero_local_basis_cofinite | exact GlobalTheory.CompanionTheory.Relay.gram_det_ne_zero_local_basis_cofinite | (intros; apply GlobalTheory.CompanionTheory.Relay.gram_det_ne_zero_local_basis_cofinite <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.period_gram_hermitian_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (p q : ℕ) (X : Fin p ⊕ Fin q → D.La) (τ : E →+* ℂ), IsPeriod D ty P → IsTypeFn H p q ty → LinearIndependent (𝓞 E) X → p + q = D.p + D.q → τ (H.rt : E) = H.rt0 → ((gramE D X).map fun a => Complex.I * τ a).IsHermitian ∧ (∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (C * ((gramE D X).map fun a => Complex.I * τ a) * Cᴴ).PosDef) ∧ ∃ C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ, (-(C * ((gramE D X).map fun a => Complex.I * τ a) * Cᴴ)).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.signature_tau_gram | exact GlobalTheory.CompanionTheory.Ar.Fl.signature_tau_gram | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.signature_tau_gram <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem transition_matrix_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x e : I → D.La), Fintype.card I = D.p + D.q → LinearIndependent (𝓞 E) e → ∃ T : Matrix I I E, IsTransition D x e T ∧ gramE D x = T * gramE D e * (T.map (IsCMField.complexConj E)).transpose ∧ (LinearIndependent (𝓞 E) x → T.det ≠ 0) ∧ ∃ (n : ℕ) (S : Matrix I I (𝓞 E)), 0 < n ∧ (∀ a, n • x a = ∑ b, S a b • e b) ∧ ∀ a b, (S a b : E) = n * T a b :=
  @PositivityTheory.Xgf.exists_transition_matrix_gram

end GlobalTheory.CompanionTheory.Ar.Fl
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem coneArea_inter : ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
  (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
  ∀ (π : Fin m → Fin n → ℂ) (A : Set (EuclideanSpace ℂ (Fin n))), MeasurableSet A →
  ∀ g : EuclideanSpace ℂ (Fin m) → ℝ≥0∞, Measurable g →
    volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ y in coneSet h J ∩ A, g (linProj π y) * ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
      (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ w : EuclideanSpace ℂ (Fin m), cntOver (coneSet h J ∩ A) π w * g w := by
  intro n m h J hJ hm hmn hfin π A hA g hg
  have hCover : ConeGraphCover.Statement := ConeGraphCover.proof ConeFiniteFibreDim.proof
    (ConeTangentDim.proof (ConeKrullDimLe.proof ConeFiniteFibreDim.proof) NullSmaller.full
      (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof))
    (ConeSmoothLocalGraph.proof PolyLocalGenerators.proof HolomorphicImplicitGraph.proof)
  have hArea : GraphAreaFibre.Statement :=
    GraphAreaFibre.proof (GraphAreaIntegral.proof GraphAreaHolomorphic.full) TangentJacComp.proof
      AreaMultiplicityWeight.proof
  obtain ⟨e, Ω, Φ, hpc, hnull⟩ := hCover n m h J hJ hm hmn hfin
  let S : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun i => graphPt (e i) (Φ i) '' Ω i
  let D₀ := disjointed S
  let D : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun i => D₀ i ∩ A
  have hSm : ∀ i, MeasurableSet (S i) := fun i =>
    (hpc i).1.measurableSet.image_of_continuousOn_injOn
      (continuousOn_graphPt _ (hpc i).2.1.continuousOn) (graphPt_injective_of_graphBase _ _).injOn
  have hD₀m : ∀ i, MeasurableSet (D₀ i) := MeasurableSet.disjointed hSm
  have hDm : ∀ i, MeasurableSet (D i) := fun i => (hD₀m i).inter hA
  have hD₀S : ∀ i, D₀ i ⊆ S i := disjointed_subset S
  have hDS : ∀ i, D i ⊆ S i := fun i => Set.inter_subset_left.trans (hD₀S i)
  have hDd : Pairwise (Function.onFun Disjoint D) := fun i j hij =>
    (disjoint_disjointed S hij).mono Set.inter_subset_left Set.inter_subset_left
  have hU₀ : ⋃ i, D₀ i = ⋃ i, S i := iUnion_disjointed
  have hUC₀ : ⋃ i, S i ⊆ coneSet h J := Set.iUnion_subset fun i => (hpc i).2.2.1
  have hUC : ⋃ i, D i ⊆ coneSet h J ∩ A := Set.iUnion_subset fun i y hy =>
    ⟨hUC₀ (hU₀ ▸ Set.mem_iUnion.2 ⟨i, hy.1⟩), hy.2⟩
  have hN : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) ((coneSet h J ∩ A) \ ⋃ i, D i) = 0 := by
    refine measure_mono_null ?_ hnull
    rintro y ⟨⟨hyC, hyA⟩, hyD⟩
    refine ⟨hyC, fun hyS => hyD ?_⟩
    rw [← hU₀] at hyS
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyS
    exact Set.mem_iUnion.2 ⟨i, hi, hyA⟩
  have hCae : (coneSet h J ∩ A : Set (EuclideanSpace ℂ (Fin n))) =ᵐ[Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)] ⋃ i, D i :=
    ae_eq_set.2 ⟨hN, by rw [Set.sdiff_eq_empty.2 hUC]; exact measure_empty⟩
  have hpiece := fun i => hArea m (n - m) n (e i) (Ω i) (Φ i) (hpc i).1 (hpc i).2.1 (D i) (hDS i)
    (hDm i) (coneTangent h J) (fun x hx _ => (hpc i).2.2.2 x hx) π
  have hcount : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℂ (Fin m))),
      cntOver (coneSet h J ∩ A) π w * g w =
        ∑' i, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_linProj_image_null π hN)] with w hw
    rw [ENNReal.tsum_mul_right, cntOver, ptsOver, ← encard_iUnion_disjoint_nat]
    · congr 3
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨hy, rfl⟩
        by_contra hne
        exact hw ⟨y, ⟨hy, fun hyD => hne (by
          obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyD
          exact ⟨i, hi, rfl⟩)⟩, rfl⟩
      · rintro ⟨i, hi, hw'⟩
        exact ⟨hUC (Set.mem_iUnion.2 ⟨i, hi⟩), hw'⟩
    · intro i j hij
      exact (hDd hij).mono (fun y hy => hy.1) (fun y hy => hy.1)
  calc volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ y in coneSet h J ∩ A, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
          ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))
      = ∑' i, volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ y in D i, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
            ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) := by
        rw [Measure.restrict_congr_set hCae, lintegral_iUnion hDm hDd, ENNReal.tsum_mul_left]
    _ = ∑' i, Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w :=
        tsum_congr fun i => (hpiece i).2 g hg
    _ = Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w, cntOver (coneSet h J ∩ A) π w * g w := by
        rw [ENNReal.tsum_mul_left, ← lintegral_tsum
          (f := fun i w => (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w)
          fun i => (hpiece i).1.mul hg.aemeasurable, lintegral_congr_ae hcount]

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix

open scoped ENNReal

theorem chowGroups_le {n e δ : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {g : MvPolynomial (Fin (e + 1) × Fin n) ℂ} (hW : IsProjPrime W) (hg : IsChowForm W (e + 1) g)
    (hδ : IsMultiHomog δ g) : e + 1 ≤ n := by
  by_contra hn
  have hfib := ConeFibreDegree.full n e δ (HermNorm.std n) W g hW hg hδ
  have hpos := ChowDegreePos.proof n (e + 1) δ W g (Nat.succ_pos e) hW hg hδ
  have : (volume : Measure (Fin (e + 1) → Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have : (ae (volume : Measure (Fin (e + 1) → Fin n → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
  have : (ae (volume : Measure (EuclideanSpace ℂ (Fin (e + 1))))).NeBot :=
    ae_neBot.2 (NeZero.ne _)
  obtain ⟨π, hπ⟩ := hfib.exists
  obtain ⟨w, hw1, hw2⟩ := (hπ.and (ae_fibreCount_eq_zero (by omega) (HermNorm.std n) W π)).exists
  rw [hw1] at hw2
  have h0 : δ = 0 := by exact_mod_cast hw2
  omega

theorem isSigmaCompact_cone_inter {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    {A : Set (EuclideanSpace ℂ (Fin n))} (hA : IsOpen A) : IsSigmaCompact (coneSet h J ∩ A) := by
  have hcl : IsClosed (coneSet h J) := isClosed_coneSet h J
  obtain ⟨F, hF, -, hU, -⟩ := hA.exists_iUnion_isClosed
  rw [← hU, Set.inter_iUnion]
  exact isSigmaCompact_iUnion _ fun i =>
    IsSigmaCompact.of_isClosed_subset isSigmaCompact_univ (hcl.inter (hF i)) (Set.subset_univ _)

theorem isScaleStable_coneSet {n : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hJ : IsProjPrime J) : IsScaleStable (coneSet h J) := by
  intro y hy t _ q hq
  rw [HermNorm.pointOf_smul']
  exact PointLine.smul_mem_zeroSet hJ.isHomog hy t q hq

theorem IsScaleStable.inter {n : ℕ} {S T : Set (EuclideanSpace ℂ (Fin n))} (hS : IsScaleStable S)
    (hT : IsScaleStable T) : IsScaleStable (S ∩ T) :=
  fun y hy t ht => ⟨hS y hy.1 t ht, hT y hy.2 t ht⟩

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end
