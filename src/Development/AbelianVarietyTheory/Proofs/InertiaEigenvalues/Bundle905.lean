module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodSetupCountEqZeroOffBadPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle319
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle352
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmQAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle893
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle856
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import GroundTheory.AutomorphicForms.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle895
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatFull

theorem baseFrame_one_eq {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (h : Lev.IsBaseFrame V β Λ 1) :
    (Λ : Set (Fin V.rank → D.host.E)) = L0c D V := by
  obtain ⟨-, -, -, h1, h2⟩ := h
  ext x
  constructor
  · intro hx
    simpa using h2 x hx
  · intro hx
    simpa using h1 x hx

theorem latAt_isFullLattice : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (h : GA D (Vc D j)), Submodule.IsFullLattice D.host.E ((ρ.B i j b).latAt (finPt (Vc D j) h)) := by
  intro D ρ hρ i j b h
  open Matrix in
  have heq : (ρ.B i j b).latAt (finPt (Vc D j) h) = Bridge.hLat (Vc D j) (finPt (Vc D j) h) := by
    have hΛ := baseFrame_one_eq _ _ _ (hρ.latS i j b)
    have e : Bridge.hLat (Vc D j) (finPt (Vc D j) h) = Submodule.span (𝓞 D.host.E) {x : Fin (Vc D j).rank → D.host.E |
        Matrix.mulVec ((finPt (Vc D j) h).1⁻¹).1 (fun i => (1 : Formalism.L2.Herm.Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
          GlobalTheory.AdLat.hat D.host.F ((ρ.B i j b).F.ΛS : Set (Fin (Vc D j).rank → D.host.E))} := by
      unfold Bridge.hLat
      rw [hΛ]
      rfl
    rw [e, ← Submodule.span_eq ((ρ.B i j b).latAt (finPt (Vc D j) h))]
    congr 1
    ext x
    have e : ((Formalism.UG.bc (Lev.swapAE D) (finPt (Vc D j) h).1)⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) =
        fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E ((((finPt (Vc D j) h).1⁻¹).1 *ᵥ (fun i => (1 : Formalism.L2.Herm.Af D.host.F) ⊗ₜ[D.host.F] x i)) i) := by
      rw [← map_inv]
      funext i
      change _ = Lev.swapAE D _
      rw [RingHom.map_mulVec (Lev.swapAE D)]
      rfl
    change ((Formalism.UG.bc (Lev.swapAE D) (finPt (Vc D j) h).1)⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (ρ.B i j b).F.ΛS ↔ _
    rw [e]
    constructor
    · intro hz
      have := GlobalTheory.PrincInLevel.swap_symm_mem_hat (ρ.B i j b).F.ΛS _ hz
      simpa only [Set.mem_setOf_eq, AlgEquiv.symm_apply_apply] using this
    · intro hz
      exact GlobalTheory.PrincInLevel.swap_mem_hatL (ρ.B i j b).F.ΛS _ hz
  rw [heq]
  obtain ⟨-, -, hfg, hspan, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D (Vc D j)
  obtain ⟨Λ, hΛ, hΛfg, hΛspan, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E
    (Vc D j).rank (GlobalTheory.Member.latC (Vc D j)) (finPt (Vc D j) h).1 hfg hspan
  rw [SetLike.coe_injective ((GlobalTheory.RepsCompare.coe_hLat _ _).trans hΛ.symm)]
  exact { toIsLattice := Submodule.IsLattice.of_fg D.host.E hΛfg, span_eq_top := hΛspan }

theorem latAt_isLattice (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (h : GA D (Vc D j)) : Submodule.IsLattice D.host.E ((ρ.B i j b).latAt (finPt (Vc D j) h)) :=
  (latAt_isFullLattice D ρ hρ i j b h).toIsLattice

end GlobalTheory.LatFull
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormUnit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem coprime_absNorm {K : Type} [Field K] [NumberField K] (l : ℕ) (hl : l.Prime)
    (P : HeightOneSpectrum (𝓞 K)) (hP : ((l : ℕ) : 𝓞 K) ∉ P.asIdeal) :
    Nat.Coprime l (Ideal.absNorm P.asIdeal) := by
  rw [Nat.Prime.coprime_iff_not_dvd hl]
  intro hd
  haveI : Fact l.Prime := ⟨hl⟩
  letI : Field (𝓞 K ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  have hfin : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  haveI := Fintype.ofFinite (𝓞 K ⧸ P.asIdeal)
  have hc : l ∣ Fintype.card (𝓞 K ⧸ P.asIdeal) := by
    rw [Fintype.card_eq_nat_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]; exact hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card l hc
  have h1 : (l : 𝓞 K ⧸ P.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [addOrderOf_zero] at hx; exact hl.one_lt.ne hx
  have h2 : (l : 𝓞 K ⧸ P.asIdeal) = 0 := (mul_eq_zero.1 h1).resolve_right hx0
  apply hP
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact h2

theorem isUnit_natCast_of_coprime {R : Type} [CommRing R] [IsLocalRing R] {l n : ℕ}
    (hl : ((l : ℕ) : R) ∈ IsLocalRing.maximalIdeal R) (h : Nat.Coprime l n) : IsUnit ((n : ℕ) : R) := by
  by_contra hn
  have hn' : ((n : ℕ) : R) ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hn
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 h : IsCoprime (l : ℤ) (n : ℤ))
  have e : (1 : R) = (a : R) * (l : R) + (b : R) * (n : R) := by
    have := congrArg (Int.cast : ℤ → R) hab
    push_cast at this
    exact this.symm
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [e]; exact add_mem (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hn')
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem normProd_inv_mem (D : D7) (ρ : Setup D.ntw) (i : D.ntw.Tw) (b : Bool) (Q : Finset (Pl D.host.E))
    (hQ : Disjoint Q (D.ntw.S0 i)) : ((normProd Q : ℕ) : ℂ)⁻¹ ∈ (ρ.eO i b).range := by
  have hcop : Nat.Coprime (D.ntw.l i) (normProd Q) := by
    unfold normProd
    refine Nat.Coprime.prod_right fun P hP => coprime_absNorm _ (D.ntw.lPrime i).out P fun hl => ?_
    exact Finset.disjoint_left.1 hQ hP (D.ntw.twistExcludedPlaces_contains_residueChar i hl)
  obtain ⟨u, hu⟩ := isUnit_natCast_of_coprime (D.ntw.O_l i) hcop
  refine ⟨(u⁻¹ : (D.ntw.O i)ˣ), ?_⟩
  have h1 : ρ.eO i b (u : D.ntw.O i) = ((normProd Q : ℕ) : ℂ) := by rw [hu, map_natCast]
  rw [← h1]
  exact map_units_inv (ρ.eO i b) u

end GlobalTheory.NormUnit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.SuppIntCong



theorem cong_one_of_suppAt : ∀ (D : D7) (V : HSp D) (Q : Finset (Pl D.host.E)) (hQ : GA D V) (a : ℕ), 0 < a → SplitSet Q → SuppAt (idem Q) V hQ → ∃ c : ℕ, ∀ i j, (∃ w ∈ intAE D, ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * ((finHom V hQ).val i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) = ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * w) ∧ (∃ w ∈ intAE D, ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * ((finHom V hQ)⁻¹.val i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) = ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * w) := by
  intro D V Q hQ a ha hQs hs
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨hid, hcj⟩ := GlobalTheory.ConjVal.components_and_conj_valuation D ι h1 h2 h4
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ P : HeightOneSpectrum (𝓞 D.host.E), AE D →+* P.adicCompletion D.host.E,
      ∀ P z, ev P z = ι (finPart D z) P :=
    ⟨fun P => ((GlobalTheory.CharLocProd.evalAt P).comp ι.toRingHom).comp (finPart D), fun _ _ => rfl⟩
  obtain ⟨evf, hevf⟩ : ∃ evf : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      (Af D.host.F ⊗[D.host.F] D.host.E) →+* P.adicCompletion D.host.E, ∀ P y, evf P y = ι y P :=
    ⟨fun P => (GlobalTheory.CharLocProd.evalAt P).comp ι.toRingHom, fun _ _ => rfl⟩
  simp only [← hev] at hid hcj
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hQs.isIdemSum
  have e2 : ∀ P, P ∉ Q → ev P (idem Q) = 0 := fun P hP => by

    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q' h' => (hid _ _ (hes Q' h')).2.2 P fun hh => hP (hh ▸ h')
  have hA1 : ∀ P, P ∉ Q → GlobalTheory.IdemSupport.cP P ∉ Q → (ev P).mapMatrix (mt V hQ) = 1 := fun P hP hP' => by
    have hc := hcj (idem Q) (GlobalTheory.IdemSupport.cP P)
    rw [e2 _ hP', map_zero, GlobalTheory.ClassScalarValue.cP_cP, map_eq_zero] at hc
    have hu : ev P (idem Q + cA D (idem Q)) = 0 := by rw [map_add (f := _), e2 P hP, hc, add_zero]
    have : (ev P).mapMatrix (mt V hQ - 1) = 0 := by
      refine Matrix.ext fun i j => ?_
      change ev P ((mt V hQ - 1) i j) = 0
      rw [← hs i j, map_mul, hu, zero_mul]
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this
  have hinv : ∀ P, (ev P).mapMatrix (mt V hQ) * (ev P).mapMatrix (mt V hQ⁻¹) = 1 := fun P => by
    rw [← map_mul, show mt V hQ * mt V hQ⁻¹ = 1 by unfold Formalism.L2.Theta.mt; rw [map_inv]; exact Units.mul_inv _, map_one]
  have hB1 : ∀ P, P ∉ Q → GlobalTheory.IdemSupport.cP P ∉ Q → (ev P).mapMatrix (mt V hQ⁻¹) = 1 := fun P hP hP' => by
    have := hinv P
    rwa [hA1 P hP hP', one_mul] at this
  set S := Q ∪ Q.image GlobalTheory.IdemSupport.cP with hS
  have hout : ∀ P, P ∉ S → P ∉ Q ∧ GlobalTheory.IdemSupport.cP P ∉ Q := fun P hP =>
    ⟨fun h' => hP (Finset.mem_union_left _ h'), fun h' => hP (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨_, h', GlobalTheory.ClassScalarValue.cP_cP P⟩))⟩

  have hN : ∀ P ∈ S, ((normProd Q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have key : ∀ P' ∈ Q, ((normProd Q : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal := fun P' hP' => by
      show ((∏ v ∈ Q, Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal
      obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 D.host.E) => Ideal.absNorm v.asIdeal) hP'
      rw [hr, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    intro P hP
    rcases Finset.mem_union.1 hP with h | h
    · exact key P h
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      rw [GlobalTheory.IdemSupport.mem_cP, map_natCast]
      exact key P' hP'
  have hvN : ∀ P ∈ S, ∀ c : ℕ, Valued.v (evf P ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E)) ≤
      WithZero.exp (-(c : ℤ)) := by
    intro P hP c
    have he : evf P ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) = algebraMap D.host.E (P.adicCompletion D.host.E)
        (algebraMap (𝓞 D.host.E) D.host.E (((normProd Q : ℕ) : 𝓞 D.host.E) ^ c)) := by
      simp only [map_natCast, map_pow, Nat.cast_pow]
    rw [he, GlobalTheory.CharLocProd.val_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 (Ideal.pow_mem_pow (hN P hP) c)
  have hlog : ∀ x : WithZero (Multiplicative ℤ), ∃ n : ℕ, x ≤ WithZero.exp (n : ℤ) := fun x => by
    by_cases hx : x = 0
    · exact ⟨0, hx ▸ zero_le'⟩
    · exact ⟨(WithZero.log x).toNat, by
        rw [← WithZero.exp_log hx]; exact WithZero.exp_le_exp.2 (by rw [WithZero.log_exp]; exact Int.self_le_toNat _)⟩
  choose fn hfn using hlog
  have ha0 : (a : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'

  have hgen : ∀ y : Af D.host.F ⊗[D.host.F] D.host.E, (∀ P, P ∉ S → evf P y = 0) → ∃ c0 : ℕ, ∀ c, c0 ≤ c →
      ∃ w ∈ intAE D, ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * y =
        ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * w := by
    intro y hy
    set u : Af D.host.F ⊗[D.host.F] D.host.E :=
      Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F) (B := D.host.E) ((a : D.host.E)⁻¹ ^ 2) with hu
    have hau : ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * u = 1 := by
      rw [hu, ← map_natCast (Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F) (B := D.host.E)),
        ← map_mul, Nat.cast_pow, ← mul_pow, mul_inv_cancel₀ ha0, one_pow, map_one]
    let f : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun P => fn (Valued.v (evf P u)) + fn (Valued.v (evf P y))
    refine ⟨S.sup f, fun c hc => ⟨u * ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * y, ?_, ?_⟩⟩
    · refine (h2 _).2 fun P => ?_
      rw [← hevf, map_mul, map_mul, map_mul, map_mul]
      by_cases hP : P ∈ S
      · have hle : f P ≤ c := (Finset.le_sup hP).trans hc
        calc _ ≤ WithZero.exp (fn (Valued.v (evf P u)) : ℤ) * WithZero.exp (-(c : ℤ)) *
              WithZero.exp (fn (Valued.v (evf P y)) : ℤ) :=
              mul_le_mul' (mul_le_mul' (hfn _) (hvN P hP c)) (hfn _)
          _ = WithZero.exp ((fn (Valued.v (evf P u)) : ℤ) + -(c : ℤ) + fn (Valued.v (evf P y))) := by
              rw [← WithZero.exp_add, ← WithZero.exp_add]
          _ ≤ 1 := by
              rw [← WithZero.exp_zero]
              exact WithZero.exp_le_exp.2 (by simp only [f] at hle; omega)
      · rw [hy P hP, map_zero, mul_zero]; exact zero_le'
    · rw [← mul_assoc, ← mul_assoc, hau, one_mul]
  have hone : ∀ P i j, evf P ((1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) i j := fun P i j => by
    rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  have hy1 : ∀ i j P, P ∉ S → evf P ((finHom V hQ).val i j -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) = 0 := by
    intro i j P hP
    obtain ⟨o1, o2⟩ := hout P hP
    have h' := congrFun (congrFun (hA1 P o1 o2) i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h'
    have hk : (finHom V hQ).val i j = finPart D (mt V hQ i j) := rfl
    rw [map_sub, hone, hk, hevf, ← hev, h', sub_self]
  have hy2 : ∀ i j P, P ∉ S → evf P ((finHom V hQ)⁻¹.val i j -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) = 0 := by
    intro i j P hP
    obtain ⟨o1, o2⟩ := hout P hP
    have h' := congrFun (congrFun (hB1 P o1 o2) i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h'
    have hk : (finHom V hQ)⁻¹.val i j = finPart D (mt V hQ⁻¹ i j) := by rw [← map_inv]; rfl
    rw [map_sub, hone, hk, hevf, ← hev, h', sub_self]
  choose c1 hc1 using fun i j => hgen _ (hy1 i j)
  choose c2 hc2 using fun i j => hgen _ (hy2 i j)
  let g : Fin V.rank × Fin V.rank → ℕ := fun p => c1 p.1 p.2 + c2 p.1 p.2
  refine ⟨Finset.univ.sup g, fun i j => ⟨hc1 i j _ ?_, hc2 i j _ ?_⟩⟩
  · exact le_trans (Nat.le_add_right _ _) (Finset.le_sup (f := g) (Finset.mem_univ (i, j)))
  · exact le_trans (Nat.le_add_left _ _) (Finset.le_sup (f := g) (Finset.mem_univ (i, j)))

end GlobalTheory.SuppIntCong
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RankReps



theorem exists_rep_split_levJ : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ h ∈ GfC (Vc D j), ∃ (γ : GQ (Vc D j)) (s : Finset (Pl D.host.E)) (h' : GA D (Vc D j)) (k : (ρ.B i j b).levJ (ρ.tw i b 0 ∅ 1)), SplitSet s ∧ (∀ v ∈ s, ((ρ.bad i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) ∧ h' ∈ GfC (Vc D j) ∧ SuppAt (idem s) (Vc D j) h' ∧ finPt (Vc D j) h = Bridge.ratF (Vc D j) γ * finPt (Vc D j) h' * (k : Bridge.Gf (Vc D j)) := by
  intro D ρ hρ i j b h hh
  obtain ⟨N₀, hN₀, hK⟩ := GlobalTheory.LevFinCong.exists_finCong_lev D (Vc D j) (ρ.B i j b).F.βS
    ((ρ.B i j b).levS (ρ.tw i b 0 ∅ 1))
  have hbad : 0 < ρ.bad i := Nat.pos_of_ne_zero (hρ.bad_ne i)
  have hK' : ∀ k ∈ GfC (Vc D j), GlobalTheory.Member.FinCong (Vc D j) N₀ k → FWT.fin (Vc D j) k ∈ (ρ.B i j b).levJ (ρ.tw i b 0 ∅ 1) :=
    fun k hk hc => ((ρ.B i j b).finPt_mem_levJ _ hk).2 (hK k hk hc).1
  obtain ⟨h', ⟨hh', hs⟩, γ, k, e⟩ := GlobalTheory.SplitReps.exists_split_rep (Vc D j) hN₀ hK' hbad (finPt (Vc D j) h)
  have hsb := GlobalTheory.SplitReps.splitOffBad_of_suppSplit (Vc D j) (ρ.bad i) h' hh' hs
  obtain ⟨-, e', P, hP, hoff, hsupp⟩ := hsb
  refine ⟨γ, P, h', k, ⟨e', hP⟩, hoff, hh', ?_, e⟩
  rw [idem_eq hP]
  exact hsupp

end GlobalTheory.RankReps
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section



namespace GlobalTheory.ResTwist

theorem res_twist_spec : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) →
    ∀ (PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) (x : (kP PP.1)ˣ),
      (((ρ.tw i b k Q (χ.comp (Y.delU i Q M))).resC PP.1 x : ℂˣ) : ℂ) =
        ρ.eOk i b k ((χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i)
          (Pi.single PP (Multiplicative.toAdd ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1 x))))) : (X.Ok i k)ˣ) : X.Ok i k) := by
  intro D N X ρ hρ Y hY i b k Q M χ hT PP x
  let χc : Multiplicative (↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) →* Circle :=
    unitPart.comp ((Units.map (ρ.eOk i b k).toMonoidHom).comp (χ.comp (AddMonoidHom.toMultiplicative (spread Y i Q M (ρ.ch i)))))
  have hgood := GlobalTheory.UnivGood.univOf_good D N X ρ hρ Y i Q M

  have hchar : charOf ρ.rc (ρ.eOk i b k) (χ.comp (Y.delU i Q M)) = χc.comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) := by
    ext1 y
    obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym y
    have hψ : IsOpen ((χ.comp (Y.delU i Q M)).ker : Set (G D.host.E N.Om)) :=
      Subgroup.isOpen_mono (H₁ := (Y.delU i Q M).ker) (fun g hg => by simp [MonoidHom.mem_ker.1 hg]) (Y.delU_open i Q M)
    have hco : ∀ P : Pl D.host.E, IsOpen ((coord Y i (admissibleConjugatePairPlaces X i Q M) M P).ker : Set (G D.host.E N.Om)) := by
      intro P
      by_cases hP : P ∈ admissibleConjugatePairPlaces X i Q M
      · refine Subgroup.isOpen_mono (H₁ := (Y.delU i (admissibleConjugatePairPlaces X i Q M) M).ker) (fun g hg => ?_) (Y.delU_open i (admissibleConjugatePairPlaces X i Q M) M)
        refine MonoidHom.mem_ker.2 (Multiplicative.toAdd.injective ?_)
        rw [coord_apply Y i (admissibleConjugatePairPlaces X i Q M) M hP, MonoidHom.mem_ker.1 hg]
        rfl
      · rw [coord, dite_eq_right hP]
        simp
    have e1 : (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) y = Multiplicative.ofAdd fun P : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ) := by
      change Multiplicative.ofAdd (fun PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => Multiplicative.toAdd (ρ.rc.pull (coord Y i (admissibleConjugatePairPlaces X i Q M) M PP.1) y)) = _
      congr 1
      funext P
      exact congrArg Multiplicative.toAdd (ρ.rc.pull_eq (hco P.1) hσ)
    have e2 : Y.delU i Q M σ = AddMonoidHom.toMultiplicative (spread Y i Q M (ρ.ch i))
        (Multiplicative.ofAdd fun P : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ)) :=
      Multiplicative.toAdd.injective (delU_eq_spread hY (twSet_of_twOK hT) (hρ.ch i) σ)
    simp only [charOf, MonoidHom.comp_apply]
    rw [ρ.rc.pull_eq hψ hσ, e1, MonoidHom.comp_apply, e2]
    rfl
  have hspec := GlobalTheory.ExportSeries.SpecGood.spec_good D (ZMod (X.l i ^ M)) Circle (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc hgood
  have hres : IsResAt (χc.comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)))) PP.1 (((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).spec (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc).res PP.1) := hspec.res PP.1 PP.2
  have hidem := hgood.1.isIdemAt PP.2
  have htres : (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).res PP.1 = ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).spec (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc).res PP.1 := by
    change resOf (charOf ρ.rc (ρ.eOk i b k) (χ.comp (Y.delU i Q M))) PP.1 = _
    rw [hchar]
    exact GlobalTheory.ConjTwist.isResAt_unique hidem (isResAt_resOf ⟨_, hres⟩) hres
  have hs : ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).spec (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc).res PP.1 = χc.comp ((AddMonoidHom.toMultiplicative
      (AddMonoidHom.single (fun _ : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => ZMod (X.l i ^ M)) ⟨PP.1, PP.2⟩)).comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1)) := dif_pos PP.2
  have hz : ∀ z : Multiplicative (DelQM D.host (X.l i) Q M), z ^ (X.l i ^ M) = 1 := by
    intro z
    rw [← ofAdd_toAdd z, ← ofAdd_nsmul]
    refine congrArg Multiplicative.ofAdd (funext fun v => ?_)
    simp [nsmul_eq_mul, ZMod.natCast_self]
  change (((ρ.tw i b k Q (χ.comp (Y.delU i Q M))).res PP.1 x : Circle) : ℂ) = _
  rw [htres, hs]
  simp only [χc, MonoidHom.comp_apply]
  rw [unitPart_of_pow (n := X.l i ^ M) (pow_ne_zero _ (X.lPrime i).out.ne_zero)
    (by rw [← map_pow, ← map_pow, hz, map_one, map_one])]
  rfl

end GlobalTheory.ResTwist
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SeriesTie

noncomputable section

namespace GlobalTheory.SeriesTie

theorem Recip.pull_locUnif : ∀ (D : D7) (Ω : Type) [Field Ω] [Algebra D.host.E Ω] (A : Type) [CommGroup A] (a : Recip D Ω), a.Good → ∀ φ : G D.host.E Ω →* A, IsOpen (φ.ker : Set (G D.host.E Ω)) → ∀ (P : Pl D.host.E) (e : AE D), IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → ∀ B : ValuationSubring Ω, IsPlaceOver B P → (∀ τ ∈ Ine (F := D.host.E) B, φ τ = 1) → ∀ σ : G D.host.E Ω, IsFrob (F := D.host.E) B (normV P) σ → a.pull φ x = (φ σ)⁻¹ := by
  intro D Ω _ _ A _ a ha φ hφ P e he ϖ hϖP hϖP2 x hx B hB hine σ hσ
  have hv := GlobalTheory.HeckeDetChar.val_unif hϖP hϖP2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact WithZero.exp_ne_zero hv.symm
  let ϖU : D.host.Eˣ := Units.mk0 (ϖ : D.host.E) hϖ0
  have hκ : a.κ (x : AE D) = ((Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P ϖU) : Neutral.B1.Ideles D.host.E) :
      AdeleRing (𝓞 D.host.E) D.host.E) := by
    rw [← ha.loc P e (GlobalTheory.HeckeDetChar.isPlIdem he) ϖU, hx, Formalism.L2.JoinChr.locE]
    congr 1
    show _ = 1 + e * (incA D (ϖ : D.host.E) - 1)
    ring
  have hsym : a.sym x = a.art (Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P ϖU)) := by
    rw [Recip.sym, MonoidHom.comp_apply]
    congr 1
    exact Units.ext hκ
  have hunif : Valued.v ((Formalism.L2.Host.atFin P ϖU : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) =
      WithZero.exp (-1 : ℤ) := by
    show Valued.v (((ϖ : D.host.E) : P.adicCompletion D.host.E)) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hv]
  obtain ⟨y, hy, hyσ⟩ := (ha.artin.frob P B hB _).mpr ⟨σ, hσ, rfl⟩
  have hu : Valued.v (((Formalism.L2.Host.atFin P ϖU * y⁻¹ : (P.adicCompletion D.host.E)ˣ)) : P.adicCompletion D.host.E) = 1 := by
    have hy' : Valued.v ((y : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) = WithZero.exp (-1 : ℤ) := hy
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hunif, hy']
    exact mul_inv_cancel₀ WithZero.exp_ne_zero
  obtain ⟨τ, hτ, hτu⟩ := (ha.artin.ine P B hB _).mp ⟨_, hu, rfl⟩
  have hs : a.sym x = GlobalTheory.HeckeGal.toAb D.host.E Ω (τ * σ⁻¹) := by
    rw [hsym, show Formalism.L2.Host.atFin P ϖU = (Formalism.L2.Host.atFin P ϖU * y⁻¹) * y by group, map_mul, map_mul, hyσ,
      ← hτu, map_mul]
  rw [a.pull_eq hφ hs, map_mul, hine τ hτ, map_inv, one_mul]

end GlobalTheory.SeriesTie

end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

theorem _root_.GlobalTheory.T.unfoldedIntegrand_measurable_invariant_bounded : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (φ φ' : GA E (m + 1) → ℂ)
    (Φ : (Fin (m + 1) → Cinf E) → ℂ) (N : ℕ) (x : ℝ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    Continuous Φ → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    Measurable (GlobalTheory.ZEul.uInt φ φ' Φ N x) ∧
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, GlobalTheory.ZEul.uInt φ φ' Φ N x (u * g) = GlobalTheory.ZEul.uInt φ φ' Φ N x g) ∧
    ∀ g, ‖GlobalTheory.ZEul.uInt φ φ' Φ N x g‖ ≤ (‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ + ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖) / 2 := by
  first | exact @GlobalTheory.ZEulProps.uInt_props | exact GlobalTheory.ZEulProps.uInt_props | (intros; apply GlobalTheory.ZEulProps.uInt_props <;> assumption)
end
