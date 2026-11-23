module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicProductEquivProductOfPartition
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle237
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle179
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle172
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle060
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle030
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle255
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle260
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.PrimesInAP
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ExistsInfiniteQcmSplitRam
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle004
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.exists_cuspidal_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (π : Irr k 0), ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := by
  first | exact @GlobalTheory.CuspidalSupportZero.exists_isCuspSupport_zero | exact GlobalTheory.CuspidalSupportZero.exists_isCuspSupport_zero | (intros; apply GlobalTheory.CuspidalSupportZero.exists_isCuspSupport_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.parabolicProduct_equiv_product_of_partition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (S : Finset (Fin s)) (r t : ℕ) (e : (Σ a, Fin (d a)) ≃ Fin (r + t)) (e₁ : (Σ a : Fin Sᶜ.card, Fin (d (Sᶜ.orderEmbOfFin rfl a))) ≃ Fin r) (e₂ : (Σ b : Fin S.card, Fin (d (S.orderEmbOfFin rfl b))) ≃ Fin t), (∀ a b, a ∉ S → b ∈ S → ∀ (n : Type) [Fintype n] [DecidableEq n] (f : (Σ i : Fin 2, Fin (d (![a, b] i))) ≃ n) (f' : (Σ i : Fin 2, Fin (d (![a, b] (Equiv.swap 0 1 i)))) ≃ n), Nonempty ((multiProd f fun i => (σ (![a, b] i)).π).Equiv (multiProd f' fun i => (σ (![a, b] (Equiv.swap 0 1 i))).π))) → Nonempty ((multiProd e fun a => (σ a).π).Equiv (prod₂ (multiProd e₁ fun a => (σ (Sᶜ.orderEmbOfFin rfl a)).π) (multiProd e₂ fun b => (σ (S.orderEmbOfFin rfl b)).π))) := by
  first | exact @GlobalTheory.ProdReorder.reorder_split | exact GlobalTheory.ProdReorder.reorder_split | (intros; apply GlobalTheory.ProdReorder.reorder_split <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.CMFam

open IntermediateField

theorem exists_qcm_adjoin (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (p : ℕ) (hp : 0 < p) (δ : Ω) (hδ : δ ^ 2 = -(p : Ω))
    (hn : δ ∉ Set.range (algebraMap E Ω)) :
    ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ} :=
  GlobalTheory.T.exists_cmQuadratic_adjoin_sqrt_neg_nat E Ω p hp δ hδ hn

theorem isSplitAt_of_dvd (L : Type) [Field L] [NumberField L] [IsCMField L] (p q : ℕ) (δ : L) (hp : 0 < p)
    (hδ : δ ^ 2 = -(p : L)) (hq : ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1) (w : HeightOneSpectrum (𝓞 L))
    (hw : (q : 𝓞 L) ∈ w.asIdeal) : GlobalTheory.UnitaryBC.IsSplitAt w :=
  GlobalTheory.T.isSplitPlaceBelowCMField_of_sqrt_neg_prime L p q δ hp hδ hq w hw

theorem not_isUnramifiedAt (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (p : ℕ) (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E) (δ : K) (hδ : δ ^ 2 = -(p : K))
    (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal :=
  GlobalTheory.T.not_isUnramifiedAt_of_sq_eq_neg_prime E K p hp hd δ hδ w hw

theorem exists_unram (E : Type) [Field E] [NumberField E] [IsCMField E] :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra E K]
      (w : HeightOneSpectrum (𝓞 K)), (N : 𝓞 K) ∉ w.asIdeal →
        Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield K)) w.asIdeal :=
  GlobalTheory.T.exists_nat_unramified_over_maximalRealSubfield E

theorem even_finrank (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    (Q : GlobalTheory.RealGal.QCM E Ω) : Even (Module.finrank ℚ (maximalRealSubfield Q.K)) :=
  GlobalTheory.T.finrank_maximal_real_even E Ω Q

end GlobalTheory.CMFam

namespace GlobalTheory.CMFam

theorem dvd_of_mem {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q n : ℕ} (hq : q.Prime)
    (hqw : (q : 𝓞 K) ∈ w.asIdeal) (hn : (n : 𝓞 K) ∈ w.asIdeal) : q ∣ n := by
  by_contra h
  have hc : Nat.gcd q n = 1 := (Nat.Prime.coprime_iff_not_dvd hq).2 h
  have hm : (((Nat.gcd q n : ℕ) : ℤ) : 𝓞 K) ∈ w.asIdeal := by
    rw [Nat.gcd_eq_gcd_ab q n]
    push_cast
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_right _ hqw) (w.asIdeal.mul_mem_right _ hn)
  rw [hc] at hm
  simp only [Nat.cast_one, Int.cast_one] at hm
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hm)

theorem natCast_mem_under {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) : (n : 𝓞 E) ∈ (w.under (𝓞 E)).asIdeal ↔ (n : 𝓞 K) ∈ w.asIdeal := by
  change _ ∈ Ideal.comap _ _ ↔ _
  rw [Ideal.mem_comap, map_natCast]

end GlobalTheory.CMFam


open GlobalTheory.CMFam GlobalTheory.ExSplitCM in
theorem GlobalTheory.GalCut.infinite_qcm_split_good : AutomorphicFormsFiniteGL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ) (π : CuspSub E a) (w₀ : HeightOneSpectrum (𝓞 E)), {Q : GlobalTheory.RealGal.QCM E Ω | (∀ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w₀ → _root_.ReciprocityTheory.Gal.Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range) ∧ (∀ w : HeightOneSpectrum (𝓞 ↥Q.K), w.under (𝓞 E) = w₀ → GlobalTheory.UnitaryBC.IsSplitAt w) ∧ (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) ∧ ∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P}.Infinite := by
  intro hAF E Ω _ _ _ _ _ _ l _ a π w₀
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have halg : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  obtain ⟨q₀, hq₀, hq₀w⟩ := exists_prime_mem w₀
  haveI : Fact q₀.Prime := ⟨hq₀⟩
  obtain ⟨N, hN0, hN⟩ := exists_unram E
  set S : Set (HeightOneSpectrum (𝓞 E)) := {v | ¬ ∃ B, (CG.mk π).HasSat v B} with hSdef
  have hS : S.Finite := Filter.eventually_cofinite.1 (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hAF E a π)
  set T : Finset ℕ := ({2, l, q₀} : Finset ℕ) ∪ N.primeFactors ∪ (discr E).natAbs.primeFactors ∪
    (finite_primes_of_finite hS).toFinset with hTdef
  set M : ℕ := 8 * ∏ q ∈ T, q with hM
  have hT2 : 2 ∈ T := by simp [hTdef]
  have hTl : l ∈ T := by simp [hTdef]
  have hTq₀ : q₀ ∈ T := by simp [hTdef]
  have hTN : ∀ r : ℕ, r.Prime → r ∣ N → r ∈ T := fun r hr hd => by
    simp [hTdef, Nat.mem_primeFactors, hr, hd, hN0]
  have hTd : ∀ r : ℕ, r.Prime → (r : ℤ) ∣ discr E → r ∈ T := fun r hr hd => by
    have : r ∈ (discr E).natAbs.primeFactors :=
      Nat.mem_primeFactors.2 ⟨hr, Int.natCast_dvd.1 hd, Int.natAbs_ne_zero.2 (discr_ne_zero E)⟩
    simp [hTdef, this]
  have hTS : ∀ r : ℕ, r.Prime → ∀ v ∈ S, (r : 𝓞 E) ∈ v.asIdeal → r ∈ T := fun r hr v hv h => by
    have : r ∈ (finite_primes_of_finite hS).toFinset := by simpa using ⟨hr, v, hv, h⟩
    simp [hTdef, this]
  have hM0 : M ≠ 0 := by
    rw [hM]
    refine mul_ne_zero (by norm_num) ?_
    rw [Finset.prod_ne_zero_iff]
    intro q hq h0
    subst h0
    simp [hTdef] at hq
    rcases hq with h | h | h
    · exact (Fact.out : l.Prime).ne_zero h.symm
    · exact hq₀.ne_zero h.symm
    · exact Nat.not_prime_zero h.1
  haveI : NeZero M := ⟨hM0⟩
  have hsq : ∀ p : ℕ, ∃ δ : Ω, δ ^ 2 = -(p : Ω) := fun p =>
    IsAlgClosed.exists_pow_nat_eq (-(p : Ω)) two_pos
  choose δ hδ using hsq
  set Gd : Set ℕ := {p | p.Prime ∧ p ∉ T ∧ (M : ℤ) ∣ (p : ℤ) + 1} with hGd
  have hGood : Gd.Infinite := by
    refine ((Nat.infinite_setOfPred_prime_and_eq_mod (q := M) isUnit_one.neg).diff T.finite_toSet).mono ?_
    rintro p ⟨⟨hp, hpe⟩, hpT⟩
    refine ⟨hp, hpT, ?_⟩
    have : (((p : ℤ) + 1 : ℤ) : ZMod M) = 0 := by push_cast; rw [hpe]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  have h8 : ∀ p ∈ Gd, ∀ q ∈ T, ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1 := fun p hp q hq => by
    refine dvd_trans ?_ hp.2.2
    rw [Int.natCast_dvd_natCast, hM]
    exact Nat.mul_dvd_mul_left 8 (Finset.dvd_prod_of_mem _ hq)
  have hodd : ∀ p ∈ Gd, p ≠ 2 := fun p hp h => hp.2.1 (h ▸ hT2)
  have hdisc : ∀ p ∈ Gd, ¬ (p : ℤ) ∣ discr E := fun p hp h => hp.2.1 (hTd p hp.1 h)
  have hmove : ∀ p ∈ Gd, ∀ (u : HeightOneSpectrum (𝓞 E)) (A' : ValuationSubring Ω), ((p : ℕ) : 𝓞 E) ∈ u.asIdeal →
      _root_.Formalism.ConjugateSelfDual.IsPlaceOver A' u → ∃ s ∈ Ine (F := E) A', s (δ p) ≠ δ p := fun p hp u A' hu hA' =>
    GlobalTheory.SqrtNegRam.sqrt_neg_moved_by_inertia E Ω p hp.1 (hodd p hp) (hdisc p hp) (δ p) (hδ p) u A' hu hA'
  have hnot : ∀ p ∈ Gd, δ p ∉ Set.range (algebraMap E Ω) := by
    rintro p hp ⟨x, hx⟩
    obtain ⟨u, hu⟩ := exists_mem_of_prime (F := E) hp.1
    obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
    obtain ⟨s, -, hs⟩ := hmove p hp u A' hu hA'
    exact hs (by rw [← hx]; exact s.commutes x)
  have hQ : ∀ p ∈ Gd, ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ p} := fun p hp =>
    exists_qcm_adjoin E Ω p hp.1.pos (δ p) (hδ p) (hnot p hp)
  have hmem : ∀ p ∈ Gd, ∀ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ p} →
      Q ∈ {Q : GlobalTheory.RealGal.QCM E Ω | (∀ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w₀ → _root_.ReciprocityTheory.Gal.Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range) ∧ (∀ w : HeightOneSpectrum (𝓞 ↥Q.K), w.under (𝓞 E) = w₀ → GlobalTheory.UnitaryBC.IsSplitAt w) ∧ (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) ∧ ∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P} := by
    intro p hp Q hQK
    have hδK : δ p ∈ Q.K := by rw [hQK]; exact IntermediateField.mem_adjoin_simple_self E (δ p)
    set y : ↥Q.K := ⟨δ p, hδK⟩ with hy
    have hy2 : y ^ 2 = -(p : ↥Q.K) := Subtype.ext (by simpa using hδ p)
    have hsplit : ∀ q ∈ T, ∀ w : HeightOneSpectrum (𝓞 ↥Q.K), (q : 𝓞 ↥Q.K) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w :=
      fun q hq w hw => isSplitAt_of_dvd _ p q y hp.1.pos hy2 (h8 p hp q hq) w hw
    refine ⟨fun A hA s hs => ?_, fun w hw => ?_, ?_, fun P hP => ?_⟩
    · rw [mem_range_res_iff, hQK]
      refine fix_adjoin (halg.isAlgebraic (δ p)).isIntegral s ?_
      exact GlobalTheory.SqFix.sqrt_fixed_of_isSquare_padic E Ω w₀ A hA q₀ hq₀w (-(p : ℤ)) (δ p)
        (by push_cast; exact hδ p)
        (by push_cast; exact GlobalTheory.RealGal.PrimesNegSquare.isSquare_neg_of_dvd q₀ p (h8 p hp q₀ hTq₀)) s hs
    · refine hsplit q₀ hTq₀ w ?_
      rw [← natCast_mem_under (E := E), hw]
      exact hq₀w
    · obtain ⟨w, hw⟩ := exists_mem_of_prime (F := ↥Q.K) hp.1
      refine ⟨w, not_isUnramifiedAt E ↥Q.K p hp.1 (hdisc p hp) y hy2 w hw, ?_⟩
      by_contra hB
      exact hp.2.1 (hTS p hp.1 _ hB ((natCast_mem_under w p).2 hw))
    · refine ⟨⟨y, p, hp.1.pos, by rw [hy2]⟩, even_finrank E Ω Q, fun w hw => ?_⟩
      obtain ⟨q, hq, hqw⟩ := exists_prime_mem w
      have hqT : q ∉ T := fun h => hw (hsplit q h w hqw)
      refine ⟨fun hl => hqT (prime_eq_of_mem w (Fact.out : l.Prime) hq hl hqw ▸ hTl), ?_, ?_⟩
      · refine hN ↥Q.K w fun h => hqT (hTN q hq (dvd_of_mem w hq hqw h))
      · have hB : ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B := by
          by_contra hB
          exact hqT (hTS q hq _ hB ((natCast_mem_under w q).2 hqw))
        obtain ⟨B, hB⟩ := hB
        exact ⟨_, hP.sat w _ B (GlobalTheory.RealGal.AttRes.normV_eq_pow w) hB⟩
  intro hfin
  apply hGood
  refine (hfin.biUnion (t := fun Q : GlobalTheory.RealGal.QCM E Ω => {p : ℕ | p.Prime ∧ ∃ u ∈ {u : HeightOneSpectrum (𝓞 E) |
      ¬ ∀ A' : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A' u → Ine (F := E) A' ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range},
      ((p : ℕ) : 𝓞 E) ∈ u.asIdeal})
    fun Q _ => finite_primes_of_finite (Filter.eventually_cofinite.1 (UpperTheory.cm_inertia_restriction_holds E ↥Q.K Ω))).subset ?_
  intro p hp
  obtain ⟨Q, hQK⟩ := hQ p hp
  refine Set.mem_biUnion (hmem p hp Q hQK) ⟨hp.1, ?_⟩
  obtain ⟨u, hu⟩ := exists_mem_of_prime (F := E) hp.1
  obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
  refine ⟨u, fun hall => ?_, hu⟩
  obtain ⟨s, hs, hne⟩ := hmove p hp u A' hu hA'
  refine hne ((mem_range_res_iff Q.K s).1 (hall A' hA' hs) (δ p) ?_)
  rw [hQK]
  exact IntermediateField.mem_adjoin_simple_self E (δ p)

end
end

section

open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

namespace GlobalTheory.SerSys.BlockLift

open ValuativeRel Formalism.MainNotions.ArithmeticCylinders

section Val

variable {g : ℕ} [Fact g.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

theorem val_lt_one_of_norm_lt_one (e : ℚ_[g] ≃+* F) (he : Continuous e) {z : ℚ_[g]} (hz : ‖z‖ < 1) :
    valuation F (e z) < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => z ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz
  have h2 : Filter.Tendsto (fun n : ℕ => e z ^ n) Filter.atTop (nhds 0) := by
    have := ((he.tendsto 0).comp h1)
    simpa [Function.comp_def, map_pow] using this
  have h3 : {x : F | valuation F x < 1} ∈ nhds (0 : F) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun x hx => by simpa using hx⟩
  obtain ⟨n, hn⟩ := (h2.eventually h3).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ valuation F (e z ^ n) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hn (not_lt.2 this)

theorem val_natCast_le_one (c : ℕ) : valuation F (c : F) ≤ 1 := by
  induction c with
  | zero => simp
  | succ c ih =>
    push_cast
    exact (valuation F).map_add_le ih (by simp)

theorem val_le_one_of_norm_le_one (e : ℚ_[g] ≃+* F) (he : Continuous e) {z : ℚ_[g]} (hz : ‖z‖ ≤ 1) :
    valuation F (e z) ≤ 1 := by
  let zi : ℤ_[g] := ⟨z, hz⟩
  have hm := PadicInt.sub_zmodRepr_mem zi
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at hm
  have hm' : ‖z - (zi.zmodRepr : ℚ_[g])‖ < 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at hm
    exact hm
  have h1 := val_lt_one_of_norm_lt_one e he hm'
  have hz' : e z = e (z - (zi.zmodRepr : ℚ_[g])) + (zi.zmodRepr : F) := by
    rw [map_sub, map_natCast]; ring
  rw [hz']
  exact (valuation F).map_add_le h1.le (val_natCast_le_one _)

theorem norm_lt_one_of_val_lt_one (e : ℚ_[g] ≃+* F) (he : Continuous e) {y : ℚ_[g]}
    (hy : valuation F (e y) < 1) : ‖y‖ < 1 := by
  by_contra hc
  push_neg at hc
  have hy0 : y ≠ 0 := by rintro rfl; simp at hc; exact absurd hc (by norm_num)
  have h1 : ‖y⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hc
  have h2 := val_le_one_of_norm_le_one e he h1
  have h3 : valuation F (e y) * valuation F (e y⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, map_one]
  have h4 : valuation F (e y) * valuation F (e y⁻¹) ≤ valuation F (e y) * 1 := by gcongr
  rw [h3, mul_one] at h4
  exact absurd hy (not_lt.2 h4)

theorem entry_of_val (e : ℚ_[g] ≃+* F) (he : Continuous e) (x : F) (c : ℕ) (hx : valuation F (x - c) < 1) :
    ∃ hA : ‖e.symm x‖ ≤ 1, PadicInt.toZMod (⟨e.symm x, hA⟩ : ℤ_[g]) = c := by
  have h1 : ‖e.symm x - c‖ < 1 :=
    norm_lt_one_of_val_lt_one e he (by rwa [map_sub, map_natCast, e.apply_symm_apply])
  have hc : ‖(c : ℚ_[g])‖ ≤ 1 := by
    have := PadicInt.norm_le_one (c : ℤ_[g])
    rwa [PadicInt.norm_def, PadicInt.coe_natCast] at this
  have hA : ‖e.symm x‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (e.symm x - c) (c : ℚ_[g])
    rw [sub_add_cancel] at this
    exact this.trans (max_le h1.le hc)
  refine ⟨hA, ?_⟩
  let zi : ℤ_[g] := ⟨e.symm x, hA⟩
  have hm : zi - (c : ℤ_[g]) ∈ IsLocalRing.maximalIdeal ℤ_[g] := by
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def]
    simpa using h1
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at hm
  exact hm

end Val

end GlobalTheory.SerSys.BlockLift

namespace GlobalTheory.SerSys.BlockLift

open ValuativeRel Formalism.MainNotions.ArithmeticCylinders

section Mat

variable {g : ℕ} [Fact g.Prime]

def bm (r t : ℕ) (h : Gn g r) : Mt g (r + t) := fun i j =>
  if (i : ℕ) < r ∧ (j : ℕ) < r then entN (h : Mt g r) i j
  else if r ≤ (i : ℕ) ∧ r ≤ (j : ℕ) then entN ((1 : Gn g t) : Mt g t) (i - r) (j - r) else 0

theorem bm_isUnit (r t : ℕ) (h : Gn g r) : IsUnit (bm r t h) := by
  set M := bm r t h with hM
  have h0 : InPar r M := fun i j hj hi => by
    rw [hM]; show bm r t h i j = 0; unfold bm; rw [if_neg (by omega), if_neg (by omega)]
  have h1 : tl r M = h := by
    ext i j
    have hi : (i : ℕ) < r + t := by omega
    have hj : (j : ℕ) < r + t := by omega
    simp [tl, entN, hM, bm, hi, hj]
  have h2 : br r t M = 1 := by
    ext i j
    simp [br, entN, hM, bm]
  have hd := LabelDet.det_inPar r t M h0
  rw [h1, h2, Matrix.det_one, mul_one] at hd
  rw [Matrix.isUnit_iff_isUnit_det, hd]
  exact Matrix.isUnits_det_units h

theorem blk_val (r t : ℕ) (h : Gn g r) : ((blk r t (r + t) h 1 : Gn g (r + t)) : Mt g (r + t)) = bm r t h := by
  show ((toG (bm r t h) : Gn g (r + t)) : Mt g (r + t)) = bm r t h
  unfold toG
  rw [dif_pos (bm_isUnit r t h)]
  exact IsUnit.unit_spec _

theorem bm_apply (r t : ℕ) (h : Gn g r) (a b : Fin (r + t)) : bm r t h a b =
    if hab : (a : ℕ) < r ∧ (b : ℕ) < r then (h : Mt g r) ⟨a, hab.1⟩ ⟨b, hab.2⟩ else if a = b then 1 else 0 := by
  unfold bm
  by_cases hab : (a : ℕ) < r ∧ (b : ℕ) < r
  · rw [if_pos hab, dif_pos hab]; simp [entN, hab]
  · rw [if_neg hab, dite_eq_right hab]
    by_cases h2 : r ≤ (a : ℕ) ∧ r ≤ (b : ℕ)
    · rw [if_pos h2]
      have ha : (a : ℕ) - r < t := by omega
      have hb : (b : ℕ) - r < t := by omega
      simp only [entN, dif_pos (And.intro ha hb), Units.val_one, Matrix.one_apply, Fin.ext_iff]
      congr 1
      apply propext
      omega
    · rw [if_neg h2, if_neg]
      intro e; subst e; omega

end Mat

end GlobalTheory.SerSys.BlockLift

namespace GlobalTheory.SerSys.BlockLift

open ValuativeRel Formalism.MainNotions.ArithmeticCylinders

theorem blockLift_act (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F) (he : Continuous e) (r t : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V)
    (hu : u ∈ fixK1 (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom))) (h : GL (Fin r) (ZMod g))
    (h' : GL (Fin (r + t)) F) (hl : GlobalTheory.PendOf.IsLiftN h h') :
    ρ h' u = ρ (Matrix.GeneralLinearGroup.map e.toRingHom (lift g (r + t) (blk r t (r + t) h 1))) u := by
  classical
  have hent : ∀ a b : Fin (r + t), ∃ hA : ‖e.symm (h'.val a b)‖ ≤ 1,
      PadicInt.toZMod (⟨e.symm (h'.val a b), hA⟩ : ℤ_[g]) = bm r t h a b := by
    intro a b
    have hab := hl a b
    rw [bm_apply]
    by_cases hc : (a : ℕ) < r ∧ (b : ℕ) < r
    · rw [dif_pos hc] at hab ⊢
      obtain ⟨hA, hA'⟩ := entry_of_val e he _ _ hab
      exact ⟨hA, by rw [hA', ZMod.natCast_zmod_val]⟩
    · rw [dite_eq_right hc] at hab ⊢
      obtain ⟨hA, hA'⟩ := entry_of_val e he (h'.val a b) (if a = b then 1 else 0)
        (by rw [hab]; split_ifs <;> simp)
      exact ⟨hA, by rw [hA']; split_ifs <;> simp⟩
  choose hA hA' using hent
  let A : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g] := fun a b => ⟨e.symm (h'.val a b), hA a b⟩
  have hmap : (PadicInt.toZMod (p := g)).mapMatrix A = bm r t h := by
    ext a b
    exact hA' a b
  have hdet : IsUnit A.det := by
    by_contra hn
    have h1 : A.det ∈ IsLocalRing.maximalIdeal ℤ_[g] := hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, RingHom.map_det, hmap] at h1
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (bm_isUnit r t h)).ne_zero h1
  let A' : GL (Fin (r + t)) ℤ_[g] := Matrix.GeneralLinearGroup.mk'' A hdet
  have hred : red g (r + t) A' = blk r t (r + t) h 1 := by
    ext a b
    rw [blk_val]
    exact hA' a b
  have hh' : Matrix.GeneralLinearGroup.map e.toRingHom (inc g (r + t) A') = h' := by
    ext a b
    show e (algebraMap ℤ_[g] ℚ_[g] (A a b)) = h'.val a b
    rw [PadicInt.algebraMap_apply]
    exact e.apply_symm_apply _
  have hx0 : red g (r + t) (Function.invFun (red g (r + t)) (blk r t (r + t) h 1)) = blk r t (r + t) h 1 :=
    Function.invFun_eq ⟨A', hred⟩
  have hk : red g (r + t) ((Function.invFun (red g (r + t)) (blk r t (r + t) h 1))⁻¹ * A') = 1 := by
    rw [map_mul, map_inv, hx0, hred, inv_mul_cancel]
  have hfix := (Submodule.mem_iInf _).1 hu ⟨_, hk⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hfix
  have hsplit : h' = Matrix.GeneralLinearGroup.map e.toRingHom (lift g (r + t) (blk r t (r + t) h 1)) *
      Matrix.GeneralLinearGroup.map e.toRingHom
        (inc g (r + t) ((Function.invFun (red g (r + t)) (blk r t (r + t) h 1))⁻¹ * A')) := by
    rw [← hh', lift, ← map_mul, ← map_mul, mul_inv_cancel_left]
  rw [hsplit, map_mul, Module.End.mul_apply]
  congr 1

end GlobalTheory.SerSys.BlockLift
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.splitLocalComponent_has_fixedVector_of_isotypic : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s τ → ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i → (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp ρ S, f ≠ 0 → (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, NG.rt L n κ f = f) → ∃ a : τ.V, a ≠ 0 ∧ ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n κ)) a = a := by
  first | exact @GlobalTheory.IsoTypFixLoc.main | exact GlobalTheory.IsoTypFixLoc.main | (intros; apply GlobalTheory.IsoTypFixLoc.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.diagUniformiserConj_transposeInv_mem_upperParahoric : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), (∀ x, Valued.v (c x) = Valued.v x) → ∀ (a b : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))), b.val = (a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose → Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t → ∀ ϖ : s.v.adicCompletion (maximalRealSubfield L), Valued.v ϖ = WithZero.exp (-1) → ∀ d : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), d.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) → NG.UniRT s r (d * b * d⁻¹) ∧ Valued.v (NG.supDiag s r (d * b * d⁻¹)) < 1 := by
  first | exact @GlobalTheory.BlockConj.conj_transpose_inv_uniRT | exact GlobalTheory.BlockConj.conj_transpose_inv_uniRT | (intros; apply GlobalTheory.BlockConj.conj_transpose_inv_uniRT <;> assumption)
end
