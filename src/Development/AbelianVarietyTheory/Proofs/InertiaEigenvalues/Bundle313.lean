module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle163
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfAssembleMem
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle286
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle287
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle288
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicExistsIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle193
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

theorem _root_.GlobalTheory.T.teichmuller_roots_act_faithfully_laurent : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → ∃ σ : {z : ℤ_[l] // z ^ (l - 1) = 1} → (k⸨X⸩ →+* k⸨X⸩), (∀ z (b : k⟦X⟧), σ z (b : k⸨X⸩) = ((GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z.1 b : k⟦X⟧) : k⸨X⸩)) ∧ Function.Injective σ ∧ ∀ c, (∀ z, σ z c = c) ↔ ∃ c₀, ι c₀ = c := by
  first | exact @GlobalTheory.DeltaInv.main | exact GlobalTheory.DeltaInv.main | (intros; apply GlobalTheory.DeltaInv.main <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
namespace GlobalTheory.RedPhiProof

theorem ringHom_eq_of_agree {O k : Type} [CommRing O] [CommRing k] (f g : O⟦X⟧ →+* k⟦X⟧)
    (hC : ∀ c : O, f (PowerSeries.C c) = g (PowerSeries.C c))
    (hX : f PowerSeries.X = g PowerSeries.X) (hd : PowerSeries.X ∣ f PowerSeries.X) (a : O⟦X⟧) :
    f a = g a := by

  have hpoly : ∀ p : Polynomial O, f (p : O⟦X⟧) = g (p : O⟦X⟧) := by
    intro p
    have hfg : f.comp (Polynomial.coeToPowerSeries.ringHom) = g.comp (Polynomial.coeToPowerSeries.ringHom) :=
      Polynomial.ringHom_ext (fun c => by simpa [Polynomial.coeToPowerSeries.ringHom_apply] using hC c)
        (by simpa [Polynomial.coeToPowerSeries.ringHom_apply] using hX)
    simpa [Polynomial.coeToPowerSeries.ringHom_apply] using RingHom.congr_fun hfg p
  refine PowerSeries.ext fun n => ?_
  rw [← sub_eq_zero, ← map_sub]

  have htail : PowerSeries.X ^ (n + 1) ∣ a - (PowerSeries.trunc (n + 1) a : O⟦X⟧) := by
    refine PowerSeries.X_pow_dvd_iff.mpr fun m hm => ?_
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]
  obtain ⟨b, hb⟩ := htail
  have ha : a = (PowerSeries.trunc (n + 1) a : O⟦X⟧) + PowerSeries.X ^ (n + 1) * b := by
    rw [← hb]; ring

  have hdiv : PowerSeries.X ^ (n + 1) ∣ f a - g a := by
    have e : f a - g a = f PowerSeries.X ^ (n + 1) * (f b - g b) := by
      conv_lhs => rw [ha]
      rw [map_add (f := _), map_add (f := _), hpoly, map_mul, map_mul, map_pow, map_pow, ← hX]
      ring
    rw [e]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hd _) _
  exact PowerSeries.X_pow_dvd_iff.mp hdiv n (Nat.lt_succ_self n)

theorem red_phi (l : ℕ) [Fact l.Prime] (O k : Type) [CommRing O] [Field k] [Algebra O k] [CharP k l]
    (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧) (h : φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1) (a : O⟦X⟧) :
    ((PowerSeries.map (algebraMap O k) (φ₀ a) : k⟦X⟧) : k⸨X⸩) =
      GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.phiPi k l ((PowerSeries.map (algebraMap O k) a : k⟦X⟧) : k⸨X⸩) := by
  have hc : PowerSeries.constantCoeff ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) = 0 := by simp
  have hs : PowerSeries.HasSubst ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hc

  have key : PowerSeries.map (algebraMap O k) (φ₀ a) =
      (PowerSeries.map (algebraMap O k) a).subst ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) := by
    have e := ringHom_eq_of_agree ((PowerSeries.map (algebraMap O k)).comp φ₀.toRingHom)
      ((PowerSeries.substAlgHom hs).toRingHom.comp (PowerSeries.map (algebraMap O k)))
      (fun c => by
        have h1 : φ₀ (PowerSeries.C c) = PowerSeries.C c := by simpa using φ₀.commutes c
        have h2 := (PowerSeries.substAlgHom hs).commutes (algebraMap O k c)
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, PowerSeries.map_C]
        simpa using h2.symm)
      (by
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h, PowerSeries.map_X,
          PowerSeries.substAlgHom_X]
        simp)
      (by
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h]
        exact PowerSeries.X_dvd_iff.mpr (by simp))
      a
    simpa [PowerSeries.coe_substAlgHom] using e
  rw [key, GlobalTheory.PsiShiftProof.phi_eq_subst, GlobalTheory.PsiLemmaCompare.substHom_coe]

end GlobalTheory.RedPhiProof
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.RedFun

theorem map_pi0 : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) (l : ℕ) [Fact l.Prime] {k : Type} [Field k] [Algebra O k] [CharP k l], PD.p = l → ∀ e : {δ // δ ∈ W.DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, (∀ δ a, PowerSeries.map (algebraMap O k) (W.γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap O k) a)) → PowerSeries.map (algebraMap O k) W.π₀₁ = 1 + ∑ᶠ z : {z : ℤ_[l] // z ^ (l - 1) = 1}, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l z.1 := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l _ k _ _ _ hp e he

  have hsub : ∀ z : ℤ_[l], GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z (1 + PowerSeries.X) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l z := by
    intro z
    have ha : PowerSeries.HasSubst (GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l z - 1) := by
      apply PowerSeries.HasSubst.of_constantCoeff_zero'
      rw [map_sub, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow,
        PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.binomialSeries_constantCoeff, map_one, sub_self]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi
    rw [← PowerSeries.coe_substAlgHom ha, map_add (f := _), map_one, PowerSeries.substAlgHom_X ha]
    ring

  have hl : (l : k⟦X⟧) = 0 := by
    rw [← map_natCast (PowerSeries.C : k →+* k⟦X⟧), CharP.cast_eq_zero, map_zero]
  unfold LocWach.π₀₁

  rw [map_add (f := _), map_sub, map_one, map_natCast, hp, hl, sub_zero, map_sum, ← Finset.sum_coe_sort W.DelF,
  Finset.sum_congr rfl fun δ _ => by rw [he, map_add (f := _), map_one, PowerSeries.map_X, hsub],
  ← finsum_comp_equiv e, finsum_eq_sum_of_fintype]

end GlobalTheory.RedFun
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.blockDet_mem_heckeAlgebra_of_heckeSpan : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ (g : ℕ) (Θ : Fin g → Fin g → X → Matrix (Fin n) (Fin n) O), (∀ p q, InRing T rep (Θ p q)) → (fun x => Matrix.det (Matrix.of fun (pa qb : Fin g × Fin n) => Θ pa.1 qb.1 x pa.2 qb.2)) ∈ T := by
  first | exact @GlobalTheory.SpanRing.blockDet_mem | exact GlobalTheory.SpanRing.blockDet_mem | (intros; apply GlobalTheory.SpanRing.blockDet_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (z : V ⊗[ℚ_[l]] Bst P), monV P ℚ_[l] V z = 0 ↔ ∃ w, crisIncl P ℚ_[l] V w = z := by
  first | exact @GlobalTheory.PMon.monV_eq_zero_iff_exists_crisIncl | exact GlobalTheory.PMon.monV_eq_zero_iff_exists_crisIncl | (intros; apply GlobalTheory.PMon.monV_eq_zero_iff_exists_crisIncl <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.monodromyTensorSemistablePeriodRing_surjective : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V], Function.Surjective (monV P ℚ_[l] V) := by
  first | exact @GlobalTheory.PMon.monV_surjective_onto | exact GlobalTheory.PMon.monV_surjective_onto | (intros; apply GlobalTheory.PMon.monV_surjective_onto <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.Pst GlobalTheory.GalOfCusp

variable (D : D7) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
  (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {w : PlE D.host}
  (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O)

structure IsDeRhamOf : Prop where
  deRham : IsdRAt (D.loc l) Bw (resDec D.nd.plOm.1 r w)
  jumps : ∀ (τ : D.host.E →+* Qbar l) (L : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced Bw τ τ' →
    ∃ J : Multiset ℤ, J.map (fun n : ℤ => (n : ℂ)) =
      (D.naut.infG π (ι.toRingHom.comp τ)).map (fun z => -(z + (s : ℂ)) + ((a : ℂ) - 1) / 2) ∧
      IsJumpsAt (D.loc l) Bw (resDec D.nd.plOm.1 r w) τ J

def FrobMatch {K : Type} [CommRing K] (φ : K →+* ℂ) (M : G D.host.E D.nd.Om →* GL (Fin a) K) (u : ℝ) : Prop :=
  ∀ᶠ w : PlE D.host in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    (M σ : Matrix (Fin a) (Fin a) K).charpoly.map φ =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) u)).map fun α => X - C α).prod

variable {D ι π s r}

end GlobalTheory.TripleLocal

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_linearForm_semistable_extending_trace : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), ∃ lam : Bst P →ₗ[ℚ_[l]] ℚ_[l], (∀ c : ↥(K0 K), lam (phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) = lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) ∧ ∀ c : ↥(K0 K), (∀ c' : ↥(K0 K), lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c') * Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = 0) → c = 0 := by
  first | exact @GlobalTheory.PMon.exists_phiSt_invariant_nondegenerate_linearForm | exact GlobalTheory.PMon.exists_phiSt_invariant_nondegenerate_linearForm | (intros; apply GlobalTheory.PMon.exists_phiSt_invariant_nondegenerate_linearForm <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem levelLe_of_le {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {m m' : ℕ}
    (h : χ.LevelLe w m) (hm : m ≤ m') : χ.LevelLe w m' := by
  intro x hx hv

  refine h x hx (le_trans hv ?_)
  rw [WithZero.exp_le_exp]
  omega

theorem expAt_mul_inv : ∀ (E : Type) [Field E] [NumberField E] (χ χ' : Formalism.L2.Host.HChar E) (w : HeightOneSpectrum (𝓞 E)) (n : ℕ),
    1 ≤ n → ExpAt χ w n → χ'.LevelLe w (n - 1) → ExpAt (χ' * χ⁻¹) w n := by
  intro E _ _ χ χ' w n hn hχ hχ' m
  constructor
  · intro hm

    by_contra hlt
    have h1 : (χ' * χ⁻¹).LevelLe w (n - 1) := levelLe_of_le hm (by omega)
    have h2 : χ.LevelLe w (n - 1) := by
      have h3 := Formalism.L2.Host.HChar.LevelLe.mul (Formalism.L2.Host.HChar.LevelLe.inv h1) hχ'
      have h4 : (χ' * χ⁻¹)⁻¹ * χ' = χ := by group
      rwa [h4] at h3
    have := (hχ (n - 1)).mp h2
    omega
  · intro hm

    have hc : χ.LevelLe w m := (hχ m).mpr hm
    have hc' : χ'.LevelLe w m := levelLe_of_le hχ' (by omega)
    exact Formalism.L2.Host.HChar.LevelLe.mul hc' (Formalism.L2.Host.HChar.LevelLe.inv hc)

end GlobalTheory.LamTie
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem _root_.GlobalTheory.T.cyclotomicLevelSubgroup_mem_wachSubgroups : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))), W.s = s → ∀ g : ↥(GK K), ((g : GQ l) ∈ Gj K s → g ∈ W.GKs) ∧ ((g : GQ l) ∈ Hinf K → W.resΓ g = 1) := by
  first | exact @GlobalTheory.Cyc.Decomp.grp_GKs_H | exact GlobalTheory.Cyc.Decomp.grp_GKs_H | (intros; apply GlobalTheory.Cyc.Decomp.grp_GKs_H <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cyclotomicTower_fixes_epsilonRoots_resGamma_trivial : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l), (∀ g ∈ Hinf K, ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j) ∧ ∀ (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (W : Wach P K LL), ∀ g ∈ Hinf K, ∃ hg : g ∈ GK K, W.resΓ ⟨g, hg⟩ = 1 := by
  first | exact @GlobalTheory.Decompl.hinf_fixes_εroot_and_resΓ_eq_one | exact GlobalTheory.Decompl.hinf_fixes_εroot_and_resΓ_eq_one | (intros; apply GlobalTheory.Decompl.hinf_fixes_εroot_and_resΓ_eq_one <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_step_of_one_le_norm : ∀ r : ℕ, UnitMatch r → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (M : Meas (r + 1) F E) (a : Inv (r + 1) F), Delta a ≠ 0 → 1 ≤ ‖mom (sec a) 0‖ → MatchAt M (unitG (r + 1) F) (unitU (r + 1) F E) a := by
  first | exact @GlobalTheory.JR.Step.unitMatchAt_of_one_le_norm | exact GlobalTheory.JR.Step.unitMatchAt_of_one_le_norm | (intros; apply GlobalTheory.JR.Step.unitMatchAt_of_one_le_norm <;> assumption)
end
