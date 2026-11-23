module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeOfMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle326
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle198
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle130
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle620
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle621
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

noncomputable section

namespace GlobalTheory.LamTie.TeichEx

section General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.GridChars GlobalTheory.CMVal
open GlobalTheory.LamTie.AuxiliaryPrimeFunction

variable {L : Type} [Field L] [NumberField L]

theorem coprime_absNorm_sub_one (v : HeightOneSpectrum (𝓞 L)) {p : ℕ} (hp : p.Prime) (hv : (p : 𝓞 L) ∈ v.asIdeal) :
    Nat.Coprime p (Ideal.absNorm v.asIdeal - 1) := by
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  haveI := v.isPrime
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 L ⧸ v.asIdeal) = 0 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← nsmul_one, card_nsmul_eq_zero']
  have h1 := GlobalTheory.Mem.WildChar.one_lt_absNorm v
  have hp0 : ((p : ℕ) : 𝓞 L ⧸ v.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem.2 hv]
  refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun ⟨t, ht⟩ => one_ne_zero (α := 𝓞 L ⧸ v.asIdeal) ?_
  have e : Ideal.absNorm v.asIdeal = p * t + 1 := by omega
  rw [e] at hN
  simpa [hp0] using hN

theorem exists_char_teich {F : Type} [Field F] [NumberField F] [Algebra F L] {c : L ≃ₐ[F] L} {I : Type} [Fintype I]
    {φ : I → L →+* ℂ} (hcm : CMData F c φ) (e : I → ℤ) (O : HeightOneSpectrum (𝓞 L) → Prop) (hfin : {w | O w}.Finite)
    (hO : ∀ w w', w.under (𝓞 F) = w'.under (𝓞 F) → O w → O w') (w0 : HeightOneSpectrum (𝓞 L)) (h0 : ¬ O w0)
    (hpr : ∀ w, O w → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ w.asIdeal) {q : ℕ} (hq : q.Prime) (h5 : Units.torsionOrder L + 1 < q)
    (hq0 : (q : 𝓞 L) ∈ w0.asIdeal)
    (hsp : ∀ w, O w ∨ w.under (𝓞 F) = w0.under (𝓞 F) → ¬ ConjPl c.toRingEquiv w w) :
    ∃ χ : Formalism.L2.Host.HChar L, χ.IsUnitary ∧ χ.TrivOn F ∧ χ.HasInf φ (fun i => 2 * e i) ∧
      (∀ w, ¬ O w → w.under (𝓞 F) ≠ w0.under (𝓞 F) → χ.UnrAt w) ∧ (∀ w, O w → ExpAt χ w 2) ∧
      (∀ w, w.under (𝓞 F) = w0.under (𝓞 F) → ExpAt χ w 1) ∧
      ∀ w, O w → ∀ x : (w.adicCompletion L)ˣ, x ^ (Ideal.absNorm w.asIdeal - 1) = 1 → χ.loc w x = 1 := by
  classical
  haveI : Nonempty (HeightOneSpectrum (𝓞 L)) := ⟨w0⟩
  let u : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 F) := fun w => w.under (𝓞 F)
  let r : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 L) := fun w => Function.invFun u (u w)
  have hr : ∀ w, (r w).under (𝓞 F) = w.under (𝓞 F) := fun w => Function.invFun_eq (f := u) ⟨w, rfl⟩
  have hrr : ∀ w w', w.under (𝓞 F) = w'.under (𝓞 F) → r w = r w' := fun w w' h => congrArg (Function.invFun u) h
  set w1 := r w0 with hw1
  have hu1 : w1.under (𝓞 F) = w0.under (𝓞 F) := hr w0
  have h1 : ¬ O w1 := fun h => h0 (hO _ _ hu1 h)
  let S : Finset (HeightOneSpectrum (𝓞 L)) := insert w1 (hfin.toFinset.filter fun w => r w = w)
  have hS : ∀ w, w ∈ S ↔ w = w1 ∨ (O w ∧ r w = w) := fun w => by simp [S]
  have hfix : ∀ w ∈ S, r w = w := fun w hw => by
    rcases (hS w).1 hw with rfl | h
    exacts [hrr _ _ hu1, h.2]
  have hne : ∀ w, O w → w ≠ w1 := fun w hw h => h1 (h ▸ hw)
  have hwild : ∀ w : HeightOneSpectrum (𝓞 L), ∃ θ : (w.adicCompletion L)ˣ →* ℂˣ,
      O w → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ w.asIdeal ∧ (∀ x, θ x ^ p = 1) ∧
        (∀ x, _root_.Formalism.L2.Host.IsUnitAt w x → Valued.v ((x : w.adicCompletion L) - 1) ≤ WithZero.exp (-2 : ℤ) → θ x = 1) ∧
        ∃ k : Lˣ, _root_.Formalism.L2.Host.IsUnitAt w (_root_.Formalism.L2.Host.atFin w k) ∧
          Valued.v (((_root_.Formalism.L2.Host.atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1) ≤
            WithZero.exp (-1 : ℤ) ∧ θ (_root_.Formalism.L2.Host.atFin w k) ≠ 1 := fun w => by
    by_cases hw : O w
    · obtain ⟨p, hp, hp'⟩ := hpr w hw
      obtain ⟨θ, hθ⟩ := exists_wild w hp hp'
      exact ⟨θ, fun _ => ⟨p, hp, hp', hθ⟩⟩
    · exact ⟨1, fun h => absurd h hw⟩
  choose θ1 hθ1 using hwild
  have hw0 : w1 ∈ S := (hS _).2 (Or.inl rfl)
  obtain ⟨θ0, ht0, hθ0, k0, hk0, hk0'⟩ := exists_tame_par w1 hq h5 (natCast_mem_of_under hu1.symm hq0) φ e (S.erase w1) θ1
  let θ : ∀ w : HeightOneSpectrum (𝓞 L), (w.adicCompletion L)ˣ →* ℂˣ := Function.update θ1 w1 θ0
  have e0 : θ w1 = θ0 := Function.update_self _ _ _
  have e1 : ∀ w, w ≠ w1 → θ w = θ1 w := fun w hw => Function.update_of_ne hw _ _
  obtain ⟨χ, hu, ht, hi, hunr, hloc⟩ := exists_hecke_level hcm e S θ
    (fun w hw => by
      rcases (hS w).1 hw with rfl | ⟨h2, -⟩
      · rw [e0]; exact GlobalTheory.ModelChar.continuous_of_tameLoc ht0
      · obtain ⟨p, -, -, -, h, -⟩ := hθ1 w h2
        rw [e1 w (hne w h2)]; exact continuous_of_level h)
    (fun w hw x => by
      rcases (hS w).1 hw with rfl | ⟨h2, -⟩
      · rw [e0]; exact ht0.1 x
      · obtain ⟨p, hp, -, h, -⟩ := hθ1 w h2
        rw [e1 w (hne w h2)]
        exact Complex.norm_eq_one_of_pow_eq_one (by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]) hp.ne_zero)
    (fun w hw w' hcj hw' => by
      have := (under_eq_iff_conjPl c hcm.rank hcm.ne _ _).2 (Or.inr hcj)
      obtain rfl : w' = w := by rw [← hfix w' hw', hrr _ _ this, hfix w hw]
      refine hsp w' ?_ hcj
      rcases (hS w').1 hw with rfl | h
      exacts [Or.inr hu1, Or.inl h.1])
    (fun k hk => by
      have ep : ∏ w ∈ S.erase w1, θ w (_root_.Formalism.L2.Host.atFin w k) = ∏ w ∈ S.erase w1, θ1 w (_root_.Formalism.L2.Host.atFin w k) :=
        Finset.prod_congr rfl fun w hw => by rw [e1 w (Finset.ne_of_mem_erase hw)]
      rw [← Finset.mul_prod_erase _ _ hw0, e0, ep]
      exact hθ0 k hk)
  refine ⟨χ, hu, ht, hi, fun Q hQ hQ' => hunr Q fun w hw h => ?_, fun Q hQ => ?_, fun Q hQ => ?_, fun Q hQ x hx => ?_⟩
  · rcases (hS w).1 hw with rfl | h2
    exacts [hQ' (h.trans hu1), hQ (hO _ _ h.symm h2.1)]
  · have hOr : O (r Q) := hO _ _ (hr Q).symm hQ
    obtain ⟨σ, s1, s2, s3, -, s5⟩ := hloc (r Q) ((hS _).2 (Or.inr ⟨hOr, hrr _ _ (hr Q)⟩)) Q (hr Q).symm
    obtain ⟨p, -, -, -, t2, k, t3, t4, t5⟩ := hθ1 _ hOr
    rw [e1 _ (hne _ hOr)] at s5
    refine expAt_succ (n := 1) (fun x hx hx' => (s5 x hx).2 (t2 _ ((s2 x).2 hx) (by rw [s3]; exact hx'))) fun H => t5 ?_
    obtain ⟨x, hx⟩ := s1 k
    rw [← hx] at t3 t4 ⊢
    rw [s3] at t4
    exact (s5 x ((s2 x).1 t3)).1 (H x ((s2 x).1 t3) t4)
  · obtain ⟨σ, s1, s2, s3, -, s5⟩ := hloc w1 hw0 Q (hQ.trans hu1.symm)
    rw [e0] at s5
    refine expAt_succ (n := 0) (fun x hx hx' => (s5 x hx).2 (ht0.2 _ ((s2 x).2 hx) (by rw [s3]; exact hx'))) fun H => hk0' ?_
    obtain ⟨x, hx⟩ := s1 k0
    rw [← hx] at hk0 ⊢
    exact (s5 x ((s2 x).1 hk0)).1 ((χ.unrAt_iff Q).2 H x ((s2 x).1 hk0))
  · have hOr : O (r Q) := hO _ _ (hr Q).symm hQ
    obtain ⟨σ, -, -, -, s4, s5⟩ := hloc (r Q) ((hS _).2 (Or.inr ⟨hOr, hrr _ _ (hr Q)⟩)) Q (hr Q).symm
    obtain ⟨p, hp, hpm, t1, -⟩ := hθ1 _ hOr
    rw [e1 _ (hne _ hOr)] at s5
    have hpQ : (p : 𝓞 L) ∈ Q.asIdeal := natCast_mem_of_under (hr Q) hpm
    refine (s5 x (GlobalTheory.LamTie.isUnitAt_of_pow_eq_one hx)).2 ?_
    have a2 : θ1 (r Q) (σ x) ^ (Ideal.absNorm Q.asIdeal - 1) = 1 := by rw [← map_pow, s4 x _ hx, map_one]
    have : θ1 (r Q) (σ x) ^ Nat.gcd p (Ideal.absNorm Q.asIdeal - 1) = 1 := by
      rw [pow_gcd_eq_one]; exact ⟨t1 _, a2⟩
    rwa [Nat.Coprime.gcd_eq_one (coprime_absNorm_sub_one Q hp hpQ), pow_one] at this

end General

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
open GlobalTheory.LamTie.AuxiliaryPrimeFunction

theorem exists_auxiliaryHeckeCharacter_trivial_tame_part : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)) (c : R.Psi → ℤ),
    PlacesOk H q0 w0 → Units.torsionOrder H.E + 1 < q0 → ∃ χ, IsAuxiliaryHeckeCharacter H w0 c χ ∧ TeichTriv H χ := by
  intro R H q0 w0 c hP h5
  obtain ⟨cc, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  haveI : IsCMField H.E := H.isCMField_hostE
  have hd := hP.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil] at hd
  have hq := hP.splits q0 (by simp)
  have hpr : ∀ w, Over4 H w → ∃ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p ≠ q0 ∧ (p : 𝓞 H.E) ∈ w.asIdeal := by
    rintro w (⟨k, h⟩ | h | h)
    · fin_cases k
      · exact ⟨H.g 0, by simp, by tauto, h⟩
      · exact ⟨H.g 1, by simp, by tauto, h⟩
    · exact ⟨H.pde, by simp, by tauto, h⟩
    · exact ⟨H.pde', by simp, by tauto, h⟩
  have hsp : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ∀ w : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ w.asIdeal →
      ¬ GlobalTheory.Mem.Chr.ConjPl cc.toRingEquiv w w := fun p hp w hw hc => by
    obtain ⟨h1, -, h2, h3⟩ := hP.splits p hp
    obtain ⟨P, P', hne, hP1, hP2⟩ := GlobalTheory.LamTie.SplitBelow.splits_below_of_absNorm H.E p h1 h2 h3 w hw
    have key : ∀ Q, GlobalTheory.CMVal.Over Q (below w) → Q = w := fun Q hQ => by
      rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl cc hcm.rank hcm.ne w Q).1 (HeightOneSpectrum.ext hQ) with h | h
      · exact h
      · exact (GlobalTheory.Mem.Chr.existsUnique_conjPl cc.toRingEquiv w).unique h hc
    exact hne ((key P hP1).trans (key P' hP2).symm)
  obtain ⟨χ, h1, h2, h3, h4, h5, h6, h7⟩ := exists_char_teich hcm c (Over4 H)
    ((((finite_over (L := H.E) (hP.splits (H.g 0) (by simp)).1).union (finite_over (hP.splits (H.g 1) (by simp)).1)).union
      ((finite_over (hP.splits H.pde (by simp)).1).union (finite_over (hP.splits H.pde' (by simp)).1))).subset (by
        rintro w (⟨k, h⟩ | h | h)
        · fin_cases k
          exacts [Or.inl (Or.inl h), Or.inl (Or.inr h)]
        exacts [Or.inr (Or.inl h), Or.inr (Or.inr h)]))
    (by
      rintro w w' h (⟨k, h'⟩ | h' | h')
      exacts [Or.inl ⟨k, natCast_mem_of_under h h'⟩, Or.inr (Or.inl (natCast_mem_of_under h h')),
        Or.inr (Or.inr (natCast_mem_of_under h h'))])
    w0 (fun h => by
      obtain ⟨p, hp, h1, h2⟩ := hpr w0 h
      exact h1 (prime_eq (hP.splits p hp).1 hq.1 h2 hP.referencePlaceOverPrime))
    (fun w h => by
      obtain ⟨p, hp, -, h2⟩ := hpr w h
      exact ⟨p, (hP.splits p hp).1, h2⟩)
    hq.1 h5 hP.referencePlaceOverPrime
    (by
      rintro w (h | h)
      · obtain ⟨p, hp, -, h2⟩ := hpr w h
        exact hsp p hp w h2
      · exact hsp q0 (by simp) w (natCast_mem_of_under h.symm hP.referencePlaceOverPrime))
  exact ⟨χ, ⟨h1, h2, ⟨fun g => 2 * c g, fun g => by push_cast; rfl, h3⟩, h4, h5, h6⟩, fun w hw => h7 w (Or.inr hw)⟩

end GlobalTheory.LamTie.TeichEx

namespace GlobalTheory.LamTie

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom

end GlobalTheory.LamTie
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RatFinPart

theorem exists_gq_mul_infU (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) :
    ∀ γ ∈ ratU L n, ∃ (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ ∧
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom ∧
      γ * (F.j γQ)⁻¹ ∈ infU L n := by
  intro γ hγ
  obtain ⟨γ₀, hγ₀⟩ := (Subgroup.mem_subgroupOf).1 hγ
  set σ : L →+* L := (IsCMField.complexConj L : L →+* L) with hσ
  have hU := γ.2
  change Formalism.UG.cT (conjAd L) ((γ.1 : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) * 1 *
    ((γ.1 : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) = 1 at hU
  rw [← hγ₀] at hU
  have h2 : Matrix.transpose ((γ₀ : Matrix (Fin n) (Fin n) L).map σ) * (γ₀ : Matrix (Fin n) (Fin n) L) = 1 := by
    have hinj : Function.Injective (algebraMap L (Ad L)) := fun x y h => by
      obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
      have := congrArg (fun z => pInf L z w) h
      simp only [pInf_algebraMap] at this
      exact w.embedding.injective this
    apply Matrix.map_injective hinj
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), ← hU, Matrix.mul_one]
    congr 1
    ext i j
    simp [Formalism.UG.cT, ratGL, conjAd_algebraMap, hσ]
  have hu : (γ₀ : Matrix (Fin n) (Fin n) L) * conjT σ γ₀ = 1 := mul_eq_one_comm.1 h2
  let g : GL (Fin n) (AL L) := Matrix.GeneralLinearGroup.map Algebra.TensorProduct.includeLeftRingHom γ₀
  have hcj : ∀ x : L, conjAL L (x ⊗ₜ[maximalRealSubfield L] (1 : AFplus L)) =
      σ x ⊗ₜ[maximalRealSubfield L] (1 : AFplus L) := fun x => rfl
  have hg : g ∈ ReciprocityTheory.Aut.GA L n := by
    change (g : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (g : Matrix (Fin n) (Fin n) (AL L)) = 1
    have e : conjT (conjAL L) (g : Matrix (Fin n) (Fin n) (AL L)) =
        (conjT σ (γ₀ : Matrix (Fin n) (Fin n) L)).map Algebra.TensorProduct.includeLeftRingHom := by
      ext i j
      simp [conjT, g, hcj]
    rw [e]
    change (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom * _ = 1
    rw [← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hq : (⟨g, hg⟩ : ReciprocityTheory.Aut.GA L n) ∈ GQ L n := by
    rw [GQ, Subgroup.mem_subgroupOf]
    exact ⟨γ₀, hu, rfl⟩
  let x : GAf L n := ⟨g, hg⟩
  refine ⟨⟨x, hq⟩, γ₀, hγ₀.symm, rfl, ?_⟩
  rw [infU, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
  ext s t : 2
  refine FiniteAdeleRing.ext _ fun w => ?_
  have hl := F.loc x w s t
  have e1 : (cLoc w (F.j x) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) s t =
      pFin L (((F.j x).1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w := rfl
  change pFin L ((γ.1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w =
    pFin L (((F.j x).1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w
  rw [← e1, hl, ← hγ₀]
  change pFin L (algebraMap L (Ad L) ((γ₀ : Matrix (Fin n) (Fin n) L) s t)) w =
    F.κ ((γ₀ : Matrix (Fin n) (Fin n) L) s t ⊗ₜ 1) w
  rw [F.left]
  rfl

end GlobalTheory.RatFinPart
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CongOpen

section Lemmas

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem kappa_one_tmul (F : FinIso L n) (a : AFplus L) :
    F.κ (1 ⊗ₜ a) = GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L a := by
  refine FiniteAdeleRing.ext _ fun w ↦ ?_
  obtain ⟨i, hi, hia⟩ := F.right w (w.under (𝓞 (maximalRealSubfield L))) rfl
  rw [hia]
  change i (a (w.under (𝓞 (maximalRealSubfield L)))) =
    GlobalTheory.LFun.complMap rfl (a (w.under (𝓞 (maximalRealSubfield L))))
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L)
    (w.under (𝓞 (maximalRealSubfield L)))).equalizer hi
    (GlobalTheory.LFun.InertChart.continuous_complMap rfl) (funext fun k ↦ ?_)) _
  change i (algebraMap _ _ k) = GlobalTheory.LFun.complMap rfl (algebraMap _ _ k)
  rw [GlobalTheory.LFun.complMap_algebraMap]
  have h1 : (algebraMap (maximalRealSubfield L) (AFplus L) k) (w.under (𝓞 (maximalRealSubfield L))) =
      algebraMap _ (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) (w.under (𝓞 (maximalRealSubfield L)))) k := rfl
  rw [← h1, ← hia, Algebra.algebraMap_eq_smul_one (A := AFplus L) k, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, F.left]
  rfl

theorem kappa_tmul (F : FinIso L n) (x : L) (a : AFplus L) :
    F.κ (x ⊗ₜ a) = algebraMap L _ x * GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L a := by
  rw [← kappa_one_tmul, ← F.left, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem mem_ALint_of_kappa (F : FinIso L n) {y : AL L} (hy : F.κ y ∈ Formalism.UG.intAd L) :
    y ∈ ALint L := by
  have h := GlobalTheory.AdeleBaseChange.mem_int_of_map (F := maximalRealSubfield L) (E := L)
    (ι := F.κ.toRingHom) (fun x a ↦ kappa_tmul F x a) hy
  refine (Subring.closure_le.2 ?_) h
  rintro _ (⟨x, rfl⟩ | ⟨a, rfl⟩)
  · obtain ⟨r, hr⟩ := x.2
    exact Subring.subset_closure (Or.inl ⟨r, by show (x : L) ⊗ₜ _ = _; rw [← hr]⟩)
  · exact Subring.subset_closure (Or.inr ⟨a.1, a.2, rfl⟩)

end Lemmas

theorem exists_open_cong : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (N : ℕ),
    0 < N → ∃ O : Set (finU (E := L) (n := n)), IsOpen O ∧ (1 : finU (E := L) (n := n)) ∈ O ∧
      ∀ k ∈ O, ∀ x : GAf L n, F.j x = (k : UA L n) → NG.Cong L n N x := by
  intro L _ _ _ n F N hN
  set c : Af L := algebraMap L (Af L) (N : L)⁻¹ with hc
  let S : Set (Af L) := {z | z * c ∈ Formalism.UG.intAd L}
  have hI : IsOpen ((Formalism.UG.intAd L : Subring (Af L)) : Set (Af L)) :=
    RestrictedProduct.isOpen_forall_mem (fun v ↦ Valued.isOpen_valuationSubring _)
  have hS : IsOpen S := hI.preimage (continuous_id.mul continuous_const)
  let f : Fin n → Fin n → finU (E := L) (n := n) → Af L := fun s t k ↦
    pFin L ((((k : UA L n) : GlobalTheory.CuspRep.GA L n) : Matrix (Fin n) (Fin n) (Ad L)) s t) -
      pFin L ((1 : Matrix (Fin n) (Fin n) (Ad L)) s t)
  have hm : Continuous (fun k : finU (E := L) (n := n) ↦ (((k : UA L n) : GlobalTheory.CuspRep.GA L n) : Matrix (Fin n) (Fin n) (Ad L))) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hp : Continuous (pFin L) := continuous_snd
  have hf : ∀ s t, Continuous (f s t) := fun s t ↦
    (hp.comp (hm.matrix_elem s t)).sub continuous_const
  refine ⟨{k | ∀ s t, f s t k ∈ S}, ?_, ?_, ?_⟩
  · have e : {k | ∀ s t, f s t k ∈ S} = ⋂ s, ⋂ t, (f s t) ⁻¹' S := by ext; simp
    rw [e]
    exact isOpen_iInter_of_finite fun s ↦ isOpen_iInter_of_finite fun t ↦ hS.preimage (hf s t)
  · intro s t
    have e : f s t 1 = 0 := by simp [f]
    show f s t 1 * c ∈ Formalism.UG.intAd L
    rw [e, zero_mul]
    exact zero_mem _
  · intro k hk x hx
    have hloc : ∀ s t, F.κ (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t) =
        pFin L ((((k : UA L n) : GlobalTheory.CuspRep.GA L n) : Matrix (Fin n) (Fin n) (Ad L)) s t) := by
      intro s t
      refine FiniteAdeleRing.ext _ fun w ↦ ?_
      rw [← F.loc x w s t, hx]
      rfl
    have hone : ∀ s t, F.κ ((1 : Matrix (Fin n) (Fin n) (AL L)) s t) =
        pFin L ((1 : Matrix (Fin n) (Fin n) (Ad L)) s t) := by
      intro s t
      by_cases h : s = t <;> simp [Matrix.one_apply, h]
    have key : ∀ s t, ∃ y ∈ ALint L, ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t -
        (1 : Matrix (Fin n) (Fin n) (AL L)) s t = (N : AL L) * y := by
      intro s t
      have h1 : f s t k * c ∈ Formalism.UG.intAd L := hk s t
      have hz : F.κ (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t -
          (1 : Matrix (Fin n) (Fin n) (AL L)) s t) = f s t k := by
        simp only [f, map_sub, hloc, hone]
      refine ⟨F.κ.symm (f s t k * c), mem_ALint_of_kappa F (by rw [RingEquiv.apply_symm_apply]; exact h1), ?_⟩
      apply F.κ.injective
      rw [hz, map_mul, RingEquiv.apply_symm_apply, map_natCast, mul_comm (f s t k), ← mul_assoc, hc,
        ← map_natCast (algebraMap L (Af L)), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'),
        map_one, one_mul]
    have hU : ∀ s t, ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t ∈ ALint L := by
      intro s t
      obtain ⟨y, hy, e⟩ := key s t
      rw [sub_eq_iff_eq_add] at e
      rw [e]
      refine add_mem (mul_mem (natCast_mem _ N) hy) ?_
      by_cases h : s = t
      · simp [Matrix.one_apply, h, one_mem]
      · simp [Matrix.one_apply, h, zero_mem]
    exact ⟨hU, key⟩

end GlobalTheory.CongOpen
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.conjugate_tuples_conjugate_residue_levels : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), ConjTup R τ t t' → (∀ PP ∈ R.Q t, ∀ x, ((R.xiR t' PP x : ℂˣ) : ℂ) = τ ((R.xiR t PP x : ℂˣ) : ℂ)) ∧ (∀ PP ∈ R.Q t, R.xiR t PP ≠ 1) ∧ (∀ P, (((R.xiH t').val P : ℂˣ) : ℂ) = τ (((R.xiH t).val P : ℂˣ) : ℂ)) ∧ ∀ i : Fin D.R.m, FixBase T R i τ → levJ R i t' = levJ R i t ∧ ∀ k (hk : k ∈ levJ R i t) (hk' : k ∈ levJ R i t'), (((levEnv (Vc D i) (R.βV i) (R.datVt i t')).χ ⟨k, hk'⟩ : ℂˣ) : ℂ) = τ (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨k, hk⟩ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.ConjRes.conj_res | exact GlobalTheory.ConjRes.conj_res | (intros; apply GlobalTheory.ConjRes.conj_res <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt


theorem _root_.GlobalTheory.T.hodge_basis_of_adapted_invariant_family : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (K K' : FinExt l) (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (w : Fin a → Fin a → P.R.BdR) (k : Fin a → ℤ), (∀ i j, w i j ∈ (P.PD K).Fil (k i)) → (∀ j, ∃ u : Fin a → P.R.BdR, (∀ i, u i ∈ (P.PD K).Fil (-k i)) ∧ ∑ i, u i • w i = Pi.single j 1) → (∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → ∀ i, (ρ g).map (algebraMap (Om l) P.R.BdR) *ᵥ (fun j => P.actQdR (g : GQ l) (w i j)) = w i) → ∃ H : Hodge C ξ ρ K', ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = ∑ i, if k i = n then 1 else 0 := by
  first | (exact @GlobalTheory.HodgeAt.hodge_of_adapted) | (exact GlobalTheory.HodgeAt.hodge_of_adapted) | (intros; apply GlobalTheory.HodgeAt.hodge_of_adapted  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinPrismCoproduct_faithfullyFlat_mod_adic_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (t p : B.A) (En : Env bk B t p) (m : ℕ), (qmap En.inl m).FaithfullyFlat := by
  first | exact @GlobalTheory.BSP.envFF | exact GlobalTheory.BSP.envFF | (intros; apply GlobalTheory.BSP.envFF <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.injective_and_range_of_prism_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C), Cover h → Function.Injective (V.v h f) ∧ ∀ z : Fin d → C.A, (∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → (fun i => p.f (z i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (z i)) → ∃ y, V.v h f y = z := by
  first | exact @GlobalTheory.BSP.Eval.effective_of_cover | exact GlobalTheory.BSP.Eval.effective_of_cover | (intros; apply GlobalTheory.BSP.Eval.effective_of_cover <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem _root_.GlobalTheory.T.semistablePeriod_frame_frobenius_isUnit_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (Ψ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Ψ → IsUnit Z → IsUnit (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * (s.X.map (toDisc l (X : bk.S) bk.ρ₀) * Z).map Ψ) := by
  first | (exact @GlobalTheory.BKLim.wseed_F_frob_XZ_isUnit) | (exact GlobalTheory.BKLim.wseed_F_frob_XZ_isUnit) | (intros; apply GlobalTheory.BKLim.wseed_F_frob_XZ_isUnit  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinPrismCoproduct_isPushout_base_change : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B B' : Obj l ↥(OL K)) (t p : B.A) (k : Hom B B') (En : Env bk B t p) (En' : Env bk B' (k.f t) (k.f p)), ∃ k' : Hom En.Q En'.Q, IsPO En.inl k k' En'.inl := by
  first | exact @GlobalTheory.BSP.env_isPO | exact GlobalTheory.BSP.env_isPO | (intros; apply GlobalTheory.BSP.env_isPO <;> assumption)
end
