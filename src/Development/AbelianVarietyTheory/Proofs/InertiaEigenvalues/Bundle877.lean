module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle859
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle850
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle863
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle861
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle862
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle864
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle014
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle312
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

namespace GlobalTheory.FlipCharFormula

variable {D : D7}

theorem fa_mul (a b : FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (a * b) Q = a Q * b Q := rfl
theorem fa_add (a b : FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (a + b) Q = a Q + b Q := rfl
theorem fa_sub (a b : FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (a - b) Q = a Q - b Q := rfl
theorem fa_one (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (1 : FiniteAdeleRing (𝓞 D.host.E) D.host.E) Q = 1 := rfl
theorem fa_natCast (n : ℕ) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (n : FiniteAdeleRing (𝓞 D.host.E) D.host.E) Q = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.cast_succ, fa_add, ih, fa_one, Nat.cast_succ]
theorem fa_sum {α : Type*} (s : Finset α) (g : α → FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) : (∑ a ∈ s, g a) Q = ∑ a ∈ s, g a Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, fa_add, ih, Finset.sum_insert ha]

theorem finPart_incA (k : D.host.E) : finPart D (incA D k) = 1 ⊗ₜ k := rfl

theorem comp_of_isIdemAt (ι : Af ↥D.host.F ⊗[↥D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ (x : D.host.E), ι (1 ⊗ₜ[↥D.host.F] x) = (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) x)
    (h2 : ∀ (y : Af ↥D.host.F ⊗[↥D.host.F] D.host.E),
      y ∈ intAE D ↔ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)), Valued.v ((ι y) P) ≤ 1)
    {e : AE D} {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ι (finPart D e) P = if P = PP then 1 else 0 := by
  obtain ⟨⟨hee, -, -⟩, hP⟩ := he
  have hidem : ∀ Q, ι (finPart D e) Q = 0 ∨ ι (finPart D e) Q = 1 := by
    intro Q
    apply IsIdempotentElem.iff_eq_zero_or_one.mp
    show ι (finPart D e) Q * ι (finPart D e) Q = ι (finPart D e) Q
    rw [← fa_mul, ← map_mul, ← map_mul, hee]
  have key : ∀ x : 𝓞 D.host.E, x ≠ 0 →
      (x ∈ PP.asIdeal ↔ ∃ Q, ι (finPart D e) Q = 1 ∧ x ∈ Q.asIdeal) := by
    intro x hx
    rw [hP x hx, h2, map_mul, finPart_incA, map_mul, h1]
    have hQ : ∀ Q, (Valued.v ((ι (finPart D e) * algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)
        ((x : D.host.E))⁻¹) Q) ≤ 1 ↔ ¬ (ι (finPart D e) Q = 1 ∧ x ∈ Q.asIdeal)) := by
      intro Q
      rw [fa_mul]
      rcases hidem Q with h | h
      · rw [h, zero_mul]; simp
      · rw [h, one_mul]
        have hv : Valued.v ((algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((x : D.host.E))⁻¹) Q)
            = HeightOneSpectrum.valuation D.host.E Q ((x : D.host.E))⁻¹ :=
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q _
        have hx0 : HeightOneSpectrum.valuation D.host.E Q (x : D.host.E) ≠ 0 := by
          simpa using hx
        rw [hv, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hx0), ← not_lt,
          HeightOneSpectrum.valuation_lt_one_iff_mem]
        simp
    simp only [hQ, not_forall, not_not]
  have hne : ∀ Q, Q ≠ PP → ι (finPart D e) Q = 0 := by
    intro Q hQ
    rcases hidem Q with h | h
    · exact h
    · exfalso
      have hnle : ¬ Q.asIdeal ≤ PP.asIdeal := by
        intro hle
        apply hQ
        exact HeightOneSpectrum.ext (Q.isMaximal.eq_of_le PP.isPrime.ne_top hle)
      obtain ⟨x, hxQ, hxP⟩ := Set.not_subset.mp hnle
      have hx0 : x ≠ 0 := by rintro rfl; exact hxP PP.asIdeal.zero_mem
      exact hxP ((key x hx0).mpr ⟨Q, h, hxQ⟩)
  have hPP : ι (finPart D e) PP = 1 := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot PP.ne_bot
    obtain ⟨Q, hQ1, -⟩ := (key x hx0).mp hx
    by_cases hQ : Q = PP
    · rwa [hQ] at hQ1
    · rw [hne Q hQ] at hQ1; exact absurd hQ1 zero_ne_one
  split_ifs with h
  · rw [h, hPP]
  · exact hne P h

theorem infPart_of_isIdemAt {e : AE D} {PP : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e PP) : infPart D e = 0 := by
  obtain ⟨⟨hee, hec, v, ε, ⟨α, rfl, -, -⟩, hsum⟩, -⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id (↥D.host.F) D.host.E)) ((pairA D.host.F 0 α : AF D.host.F) ⊗ₜ[↥D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    have : (fstA D.host.F) (pairA D.host.F 0 α) = 0 := rfl
    rw [this]
    exact TensorProduct.zero_tmul _ _
  have hs := congrArg (infPart D) hsum
  have hm := congrArg (infPart D) hec
  have hi := congrArg (infPart D) hee
  rw [map_add (f := _), h0] at hs
  rw [map_mul, map_zero] at hm
  rw [map_mul] at hi
  have hc : infPart D (cA D e) = - infPart D e :=
    eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hs)
  rw [hc, mul_neg, hi, neg_eq_zero] at hm
  exact hm



theorem char_inv_eq_prod_locK_of_flip : ∀ (D : D7) (V : HSp D) (χW : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (M₀ : ℕ) (u : D.host.Eˣ) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (x : (AE D)ˣ), ChrEq χW χ → (u : D.host.E) = ((M₀ : ℕ) : D.host.E) → IsIdemSum eT T → IsFlipDet V eT M₀ x → ((χW x : Circle) : ℂ)⁻¹ = ∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ V.rank := by
  intro D V χW χ M₀ u T eT x hχ hu hT hx
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) χW χ hχ
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hT
  unfold IsFlipDet at hx
  have heT : ∀ P, ι (finPart D (∑ PP ∈ T, es PP)) P = if P ∈ T then 1 else 0 := by
    intro P

    rw [map_sum, map_sum, fa_sum,
    Finset.sum_congr rfl (fun PP hPP => comp_of_isIdemAt ι h1 h2 (hes PP hPP) P)]
    exact Finset.sum_ite_eq T P (fun _ => (1 : HeightOneSpectrum.adicCompletion D.host.E P))
  have hinfT : infPart D (∑ PP ∈ T, es PP) = 0 := by

    rw [map_sum]
    exact Finset.sum_eq_zero (fun PP hPP => infPart_of_isIdemAt (hes PP hPP))
  have hinf : infPart D (x : AE D) = 1 := by
    have := congrArg (infPart D) hx
    rw [map_mul, map_add (f := _), map_mul, map_sub, hinfT, map_one, zero_mul, zero_add, sub_zero, mul_one] at this
    exact this
  have hcomp : ∀ P, ι (finPart D (x : AE D)) P *
      ((if P ∈ T then 1 else 0) * (((M₀ ^ V.rank : ℕ) : HeightOneSpectrum.adicCompletion D.host.E P))
        + (1 - if P ∈ T then 1 else 0)) = 1 := by
    intro P
    have h0 : ι (finPart D ((x : AE D) * ((∑ PP ∈ T, es PP) * ((M₀ ^ V.rank : ℕ) : AE D)
        + (1 - ∑ PP ∈ T, es PP)))) P = ι (finPart D 1) P := by
      rw [Nat.cast_pow, hx]
    simp only [map_mul, map_add (f := _), map_sub, map_one, map_natCast] at h0
    rw [fa_mul, fa_add, fa_mul, fa_sub, fa_one, fa_natCast, heT] at h0
    exact h0
  let k : HeightOneSpectrum (𝓞 D.host.E) → D.host.Eˣ := fun P => if P ∈ T then (u⁻¹) ^ V.rank else 1
  have hxk : ∀ P, ι (finPart D (x : AE D)) P =
      algebraMap D.host.E (HeightOneSpectrum.adicCompletion D.host.E P) (k P : D.host.E) := by
    intro P
    have hc := hcomp P
    by_cases hP : P ∈ T
    · rw [if_pos hP, one_mul, sub_self, add_zero] at hc
      rw [show k P = (u⁻¹) ^ V.rank from if_pos hP, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hu,
        map_pow, map_inv₀, map_natCast, eq_inv_of_mul_eq_one_left hc, Nat.cast_pow, inv_pow]
    · rw [if_neg hP, zero_mul, sub_zero, zero_add, mul_one] at hc
      rw [show k P = 1 from if_neg hP, Units.val_one, map_one]
      exact hc
  have hI : Ideal.span {((N : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have key := hprod x hinf (T ∪ (Ideal.finite_factors hI).toFinset) k
    (fun P _ => by
      rw [hxk P, sub_self, map_zero]
      exact ⟨HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _, zero_le'⟩)
    (fun P hP => by
      have hPT : P ∉ T := fun h => hP (Finset.mem_union_left _ h)
      refine ⟨?_, ?_⟩
      · rw [hxk P, show k P = 1 from if_neg hPT, Units.val_one, map_one, map_one]
      · intro hNP
        apply hP
        apply Finset.mem_union_right
        rw [Set.Finite.mem_toFinset]
        exact Ideal.dvd_span_singleton.mpr hNP)
  rw [key, ← Finset.prod_subset (Finset.subset_union_left)
    (fun P _ hPT => by rw [show k P = 1 from if_neg hPT, map_one, Units.val_one])]
  rw [Finset.prod_congr rfl (fun P hP => by
    rw [show k P = (u⁻¹) ^ V.rank from if_pos hP, map_pow, map_inv, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val, inv_pow])]
  rw [Finset.prod_inv_distrib, inv_inv]

end GlobalTheory.FlipCharFormula
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section

namespace GlobalTheory.WtDescent

open _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.CoefModel

theorem weight_descends : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', (fun t => e.comp (emb t)) t ≠ ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t')) → (∀ σ : L →+* ℂ, ∃ t, σ = (fun t => e.comp (emb t)) t ∨ σ = ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t)) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W), ρ.IsIrreducible → ∀ lam0 : ι → Fin n → ℤ, (∀ t, NX.HWAtF c ρ.dual (emb t) (lam0 t)) → ∃ lam : ι → DomWeight n, (∀ t, (lam t).w = lam0 t) ∧ ∃ T : W ≃ₗ[K] VV K lam, ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L), (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → ∀ x, T (ρ γ x) = rhoVr emb lam γ₀ (T x) := by
  intro L _ _ _ n ι _ K _ e emb hinj hcm hcov c hc W _ _ _ ρ hρ lam0 hw
  classical
  obtain ⟨σ⟩ : Nonempty (L →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (S := L) (M := ℂ)).toRingHom⟩
  obtain ⟨t₀, -⟩ := hcov σ
  let N := Module.finrank K W
  let b : Module.Basis (Fin N) K W := Module.finBasis K W
  let A : ReciprocityTheory.Aut.GQ L n → Matrix (Fin N) (Fin N) K := fun γ => LinearMap.toMatrix b b (ρ γ)
  let ρC : Representation ℂ (ReciprocityTheory.Aut.GQ L n) (Fin N → ℂ) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin N) (Fin N) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin N → ℂ)) :
        Matrix (Fin N) (Fin N) ℂ →* Module.End ℂ (Fin N → ℂ)).comp
      (((e.mapMatrix : Matrix (Fin N) (Fin N) K →+* Matrix (Fin N) (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) K →* Matrix (Fin N) (Fin N) ℂ).comp
        (((LinearMap.toMatrixAlgEquiv b : Module.End K W ≃ₐ[K] Matrix (Fin N) (Fin N) K) :
          Module.End K W →* Matrix (Fin N) (Fin N) K).comp ρ))
  have hρC : ∀ γ, LinearMap.toMatrix' (ρC γ) = (LinearMap.toMatrix b b (ρ γ)).map e := by
    intro γ
    show LinearMap.toMatrix' (Matrix.toLin' ((LinearMap.toMatrix b b (ρ γ)).map e)) = _
    rw [LinearMap.toMatrix'_toLin']
  have halg : Formalism.AUTREP.IsAlgWeight L n ρC :=
    GlobalTheory.T.isAlgWeight_of_contragredient_highestWeight L n K e c hc W ρ (Fin N) b ρC hρC (emb t₀) (lam0 t₀) (hw t₀)
  haveI : Nontrivial W := GlobalTheory.PiIsotypic.nontrivial_of_isIrreducible ρ hρ
  have hN : 0 < N := Module.finrank_pos
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨a, j, hj, hjρ⟩ := GlobalTheory.T.exists_irreducible_algebraicWeight_subrep L n (Fin N → ℂ) ρC halg
  obtain ⟨lam, Tc, hTc⟩ := GlobalTheory.T.algebraic_weight_dominant_iso_exists L n ι (fun t => e.comp (emb t)) hinj hcm hcov a
  have hmatch : ∀ γ : ReciprocityTheory.Aut.GQ L n, (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) :
      Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
      ((mtwRat (L := L) (n := n) γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
    intro γ
    exact (congrArg (fun g : GL (Fin n) (ReciprocityTheory.Aut.AL L) => (g : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)))
      (mtwInc_mtwRatFun γ)).symm
  let bK := bVV K lam
  let bC : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) :=
    Module.Basis.mk (linearIndependent_mapVV e lam) (span_mapVV e lam).ge
  have hbC : ∀ i, bC i = mapVV e lam (bK i) := fun i => Module.Basis.mk_apply _ _ _
  have hrepr : ∀ x i, bC.repr (mapVV e lam x) i = e (bK.repr x i) := by
    intro x i
    have hx : mapVV e lam x = bC.equivFun.symm (fun i => e (bK.repr x i)) := by
      rw [Module.Basis.equivFun_symm_apply]
      conv_lhs => rw [← bK.sum_repr x]

      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LinearMap.map_smulₛₗ, hbC]
    rw [hx, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  let B : ReciprocityTheory.Aut.GQ L n → Matrix (VVIdx lam) (VVIdx lam) K :=
    fun γ => LinearMap.toMatrix bK bK (rhoVr emb lam (mtwRat (L := L) (n := n) γ))
  have hB : ∀ γ, LinearMap.toMatrix bC bC (rhoVr (fun t => e.comp (emb t)) lam (mtwRat (L := L) (n := n) γ)) = (B γ).map e := by
    intro γ
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.map_apply]
    show _ = e (LinearMap.toMatrix bK bK (rhoVr emb lam (mtwRat (L := L) (n := n) γ)) i k)
    rw [LinearMap.toMatrix_apply, hbC, ← GlobalTheory.ConjTwist.mapVV_rhoVr, hrepr]
  let M : VV ℂ lam →ₗ[ℂ] (Fin N → ℂ) := j ∘ₗ Tc.symm.toLinearMap
  have hM : ∀ γ y, M (rhoVr (fun t => e.comp (emb t)) lam (mtwRat (L := L) (n := n) γ) y) = ρC γ (M y) := by
    intro γ y
    have h1 : Tc.symm (rhoVr (fun t => e.comp (emb t)) lam (mtwRat (L := L) (n := n) γ) y) = a.ρ γ (Tc.symm y) := by
      apply Tc.injective
      rw [hTc γ (mtwRat (L := L) (n := n) γ) (hmatch γ), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simp only [M, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, hjρ]
  let X : Matrix (Fin N) (VVIdx lam) ℂ := LinearMap.toMatrix bC (Pi.basisFun ℂ (Fin N)) M
  have hX0 : X ≠ 0 := by
    intro h
    have hM0 : M = 0 := by
      have := congrArg (Matrix.toLin bC (Pi.basisFun ℂ (Fin N))) h
      simpa [X] using this
    haveI := GlobalTheory.PiIsotypic.nontrivial_of_isIrreducible a.ρ a.irr
    obtain ⟨x, hx⟩ := exists_ne (0 : a.W)
    apply hx
    apply hj
    have : M (Tc x) = j x := by simp [M]
    rw [← this, hM0, LinearMap.zero_apply, map_zero]
  have hXrel : ∀ γ, X * (B γ).map e = (A γ).map e * X := by
    intro γ
    rw [← hB, show (A γ).map e = LinearMap.toMatrix' (ρC γ) from (hρC γ).symm,
      ← LinearMap.toMatrix_eq_toMatrix', ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    congr 1
    exact LinearMap.ext fun y => hM γ y
  obtain ⟨XK, hXK0, hXK⟩ := GlobalTheory.T.nonzero_matrix_intertwiner_descends_to_subfield K e (ReciprocityTheory.Aut.GQ L n) (VVIdx lam) (Fin N) B A ⟨X, hX0, hXrel⟩
  let Φ : VV K lam →ₗ[K] W := Matrix.toLin bK b XK
  have hΦ : ∀ γ x, Φ (rhoVr emb lam (mtwRat (L := L) (n := n) γ) x) = ρ γ (Φ x) := by
    intro γ x
    have h : Φ ∘ₗ rhoVr emb lam (mtwRat (L := L) (n := n) γ) = ρ γ ∘ₗ Φ := by
      apply (LinearMap.toMatrix bK b).injective
      rw [LinearMap.toMatrix_comp bK bK b, LinearMap.toMatrix_comp bK b b, LinearMap.toMatrix_toLin]
      exact hXK γ
    exact LinearMap.congr_fun h x
  have hsurj : Function.Surjective Φ := by
    let S : Subrepresentation ρ := ⟨LinearMap.range Φ, by
      rintro γ _ ⟨x, rfl⟩
      exact ⟨_, hΦ γ x⟩⟩
    rcases hρ.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hXK0
      have hr : LinearMap.range Φ = ⊥ := congrArg Subrepresentation.toSubmodule h
      have hΦ0 : Φ = 0 := LinearMap.range_eq_bot.1 hr
      have := congrArg (LinearMap.toMatrix bK b) hΦ0
      simpa [Φ] using this
    · have hr : LinearMap.range Φ = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.range_eq_top.1 hr
  haveI : FiniteDimensional ℂ a.W := a.alg.1
  haveI : FiniteDimensional K (VV K lam) := Module.Finite.of_basis bK
  have hdimC : Module.finrank ℂ a.W ≤ N := by
    have := LinearMap.finrank_le_finrank_of_injective hj
    simpa using this
  have hdimA : Module.finrank ℂ a.W = Fintype.card (VVIdx lam) := by
    rw [Tc.finrank_eq, Module.finrank_eq_card_basis bC]
  have hdimK : Module.finrank K (VV K lam) = Fintype.card (VVIdx lam) := Module.finrank_eq_card_basis bK
  have hle : N ≤ Module.finrank K (VV K lam) := by
    have := LinearMap.finrank_range_le Φ
    rwa [LinearMap.range_eq_top.2 hsurj, finrank_top] at this
  have heq : Module.finrank K (VV K lam) = Module.finrank K W := by
    show Module.finrank K (VV K lam) = N
    omega
  have hinjΦ : Function.Injective Φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).2 hsurj
  let Φb : VV K lam ≃ₗ[K] W := LinearEquiv.ofBijective Φ ⟨hinjΦ, hsurj⟩
  have h1 : ∀ y, Φb y = Φ y := fun y => rfl
  have hT : ∀ γ x, Φb.symm (ρ γ x) = rhoVr emb lam (mtwRat (L := L) (n := n) γ) (Φb.symm x) := by
    intro γ x
    apply Φb.injective
    rw [Φb.apply_symm_apply, h1, hΦ, ← h1, Φb.apply_symm_apply]
  have hten : Formalism.L2.Col.TenIrr (fun t => e.comp (emb t)) lam := by
    refine GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv a.ρ _ Tc (fun γ v => ?_) a.irr
    rw [hTc γ (mtwRat (L := L) (n := n) γ) (hmatch γ)]
    rfl
  refine ⟨lam, fun t => (GlobalTheory.mtRatDual_hw L n ι K e emb hinj hcm c hc lam hten W ρ Φb.symm hT t (lam0 t) (hw t)).symm,
    Φb.symm, fun γ γ₀ hm x => ?_⟩
  obtain rfl := mtwRat_eq_of_match γ γ₀ hm
  exact hT γ x

end GlobalTheory.WtDescent
end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

namespace GlobalTheory.IdemFlip

theorem idemSum_sub_and_flip : ∀ (D : D7) (e : AE D) (P T : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → T ⊆ P →
    (∃ eT : AE D, IsIdemSum eT T) ∧ ∃ e' : AE D, IsIdemSum e' ((P \ T) ∪ T.image Formalism.L2.DIV.conjPl) := by
  intro D e P T he hT
  have hnc := GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he
  obtain ⟨⟨es, hes, hsum⟩, h0⟩ := he
  have hmul : ∀ S R : Finset (Formalism.L2.DIV.Pl D.host.E), S ⊆ R → R ⊆ P →
      (∑ a ∈ S, es a) * (∑ b ∈ R, es b) = ∑ a ∈ S, es a := by
    intro S R hSR hRP
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single a]
    · exact (hes a (hRP (hSR ha))).1.1
    · intro b hb hba
      exact Formalism.IndefR.Fin.idem_orth (hnc a (hRP (hSR ha)) a (hRP (hSR ha))) (hes a (hRP (hSR ha))) (hes b (hRP hb))
        (Ne.symm hba)
    · intro h; exact absurd (hSR ha) h
  have h1 : (∑ a ∈ T, es a) * e = ∑ a ∈ T, es a := by rw [hsum]; exact hmul T P hT subset_rfl
  have h2 : (∑ a ∈ T, es a) * (∑ a ∈ T, es a) = ∑ a ∈ T, es a := hmul T T subset_rfl hT
  have hTT : (∑ a ∈ T, es a) * cA D (∑ a ∈ T, es a) = 0 := by
    calc (∑ a ∈ T, es a) * cA D (∑ a ∈ T, es a)
        = ((∑ a ∈ T, es a) * e) * cA D ((∑ a ∈ T, es a) * e) := by rw [h1]
      _ = ((∑ a ∈ T, es a) * cA D (∑ a ∈ T, es a)) * (e * cA D e) := by rw [map_mul]; ring
      _ = 0 := by rw [h0, mul_zero]
  have hIT : IsIdemSum (∑ a ∈ T, es a) T := ⟨⟨es, fun a ha => hes a (hT ha), rfl⟩, hTT⟩
  refine ⟨⟨_, hIT⟩, ?_⟩
  obtain ⟨⟨es2, hes2, hsum2⟩, -⟩ := Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj hIT
  have hdisj : Disjoint (P \ T) (T.image Formalism.L2.DIV.conjPl) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha'
    exact hnc b (hT hb) _ (Finset.mem_sdiff.1 ha).1 (fun c hc => ⟨Formalism.L2.DIV.starO c,
      (Formalism.L2.DIV.isConjPl_conjPl b c _ (by rw [Formalism.L2.DIV.starO_coe])).1 hc, by rw [Formalism.L2.DIV.starO_coe]⟩)
  have hf : ∑ a ∈ P \ T, es a = e - ∑ a ∈ T, es a := by
    rw [eq_sub_iff_add_eq, Finset.sum_sdiff hT, hsum]
  refine ⟨(e - ∑ a ∈ T, es a) + cA D (∑ a ∈ T, es a),
    ⟨⟨fun a => if a ∈ P \ T then es a else es2 a, ?_, ?_⟩, ?_⟩⟩
  · intro a ha
    rcases Finset.mem_union.1 ha with h | h
    · simp only [if_pos h]; exact hes a (Finset.mem_sdiff.1 h).1
    · simp only [if_neg (Finset.disjoint_right.1 hdisj h)]; exact hes2 a h
  · rw [Finset.sum_union hdisj, ← hf, hsum2]
    congr 1
    · exact Finset.sum_congr rfl fun a ha => (if_pos ha).symm
    · exact Finset.sum_congr rfl fun a ha => (if_neg (Finset.disjoint_right.1 hdisj ha)).symm
  · generalize (∑ a ∈ T, es a) = t at h1 h2 hTT ⊢
    have h4 : cA D t * cA D e = cA D t := by rw [← map_mul, h1]
    have h5 : cA D t * cA D t = cA D t := by rw [← map_mul, h2]
    rw [map_add (f := _), map_sub, Formalism.L2.Theta.cA_cA]
    linear_combination h0 - (-(e) * h4 + cA D t * h0) + h1 - (-(cA D e) * h1 + t * h0)
      + 2 * hTT - h2 + h4 - h5

end GlobalTheory.IdemFlip
end
