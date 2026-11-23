module

public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle001
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle114
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankJointEigenspaceCoefficientFieldComplex
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle004
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle112
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle117
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.AlgebraicWeights.IsAlgWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_pow_valuation_lt_of_integral_algClosure_place : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → ∀ x c : Ω, IsIntegral ℤ x → IsIntegral ℤ c → c ≠ 0 → A.valuation x < 1 → ∃ k : ℕ, A.valuation x ^ k < A.valuation c := by
  first | exact @GlobalTheory.MaxIdealPow.exists_pow_lt_valuation | exact GlobalTheory.MaxIdealPow.exists_pow_lt_valuation | (intros; apply GlobalTheory.MaxIdealPow.exists_pow_lt_valuation <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

theorem _root_.GlobalTheory.T.inertSatakeParameters_eq_of_iso : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n), π.Iso π' → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), (∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0}) → NG.SatAt π Dv α → NG.SatAt π' Dv α := by
  first | exact @GlobalTheory.SatIso.satAt_of_iso | exact GlobalTheory.SatIso.satAt_of_iso | (intros; apply GlobalTheory.SatIso.satAt_of_iso <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.algWeight_contragredient_exists_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n), ∃ b : NG.AlgWt L n, a.IsDual b ∧ (∀ b', a.IsDual b' ↔ b.Iso b') ∧ ∀ a' : NG.AlgWt L n, a.Iso a' → a'.IsDual b ∧ ∀ τ lam, a.HWAt τ lam → a'.HWAt τ lam := by
  first | exact @GlobalTheory.algWt_contragredient | exact GlobalTheory.algWt_contragredient | (intros; apply GlobalTheory.algWt_contragredient <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.automorphic_multiplicity_eq_of_iso : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n),
    π.Iso π' → π.mult = π'.mult := by
  first | exact @GlobalTheory.MultIso.mult_eq_of_iso | exact GlobalTheory.MultIso.mult_eq_of_iso | (intros; apply GlobalTheory.MultIso.mult_eq_of_iso <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.inf_typeSpace_ne_bot_of_isotypicPart : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (S : Submodule ℂ (GAf L n → W)), Formalism.L2.NG.IsSubrep ρ S → Formalism.L2.NG.isoTyp ρ S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ → S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ := by
  first | exact @GlobalTheory.MoveTyped.typed_of_isoTyp | exact GlobalTheory.MoveTyped.typed_of_isoTyp | (intros; apply GlobalTheory.MoveTyped.typed_of_isoTyp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.finite_exceptional_places_over_prime : ∀ (D : D7) (l : ℕ), l.Prime → ∃ F : Finset (PlE D.host), ∀ v, v ∉ F → v ∉ placesOver D.host.E l ∧ v ∉ placesS D l := by
  first | exact @GlobalTheory.PlacesExc.finite_exceptional | exact GlobalTheory.PlacesExc.finite_exceptional | (intros; apply GlobalTheory.PlacesExc.finite_exceptional <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.finrank_jointEigenspace_coefficientField_complex : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (E : Submodule ℂ (D.what₂.Mt μ j)), (∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → ∀ (c : ℂ) (f f' : GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • NG.tN (M μ j h1 h2).J s ϖ k f + NG.tN (M μ j h1 h2).J s ϖ k f') → (∀ y, y ∈ E ↔ ∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → Module.finrank (FractionRing (B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k), Module.End.eigenspace (B.hK j w v k) (κ v k)) = Module.finrank ℂ E := by
  first | exact @GlobalTheory.PtLocalEig.eig_dim | exact GlobalTheory.PtLocalEig.eig_dim | (intros; apply GlobalTheory.PtLocalEig.eig_dim <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.muZeroChar_locK_congruent_rational_integer : ∀ {R : Ranks} {H : Host R} (P : PiBar H) (W : Omg H) (e : ↥(R.Psi) → ℚ) (j : ℕ) (χ : HChar H.E), IsMu0 P W e j χ → ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (u : 𝓞 H.E) (hu : (u : H.E) ≠ 0) (a : ℕ) (ha : a.Coprime (H.g k)), u - (a : 𝓞 H.E) ∈ w.asIdeal → χ.locK w (Units.mk0 (u : H.E) hu) = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹ := by
  first | exact @GlobalTheory.MuZeroCong.locK_eq_of_sub_mem | exact GlobalTheory.MuZeroCong.locK_eq_of_sub_mem | (intros; apply GlobalTheory.MuZeroCong.locK_eq_of_sub_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem valuation_le_one_of_valuation_one_sub_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    {a : Ω} (ha : A.valuation (1 - a) < 1) : A.valuation a ≤ 1 := by
  have e : a = 1 - (1 - a) := by ring
  rw [e]
  refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ha.le)
  rw [map_one]

theorem valuation_one_sub_mul_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω}
    (ha : A.valuation (1 - a) < 1) (hb : A.valuation (1 - b) < 1) :
    A.valuation (1 - a * b) < 1 := by
  have e : 1 - a * b = (1 - a) + a * (1 - b) := by ring
  rw [e]
  refine Valuation.map_add_lt _ ha ?_
  rw [map_mul]
  calc A.valuation a * A.valuation (1 - b) ≤ 1 * A.valuation (1 - b) :=
        by gcongr; exact valuation_le_one_of_valuation_one_sub_lt A ha
    _ = A.valuation (1 - b) := one_mul _
    _ < 1 := hb

theorem exists_fixed_of_separating :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (σ : G E Ω), σ ∈ Ine (F := E) A' → ∀ (e₀ c : Ω), IsIntegral ℤ e₀ → A.valuation e₀ < A.valuation c → A'.valuation (1 - e₀) < 1 → ∃ e : Ω, IsIntegral ℤ e ∧ σ e = e ∧ A.valuation e < A.valuation c ∧ A'.valuation (1 - e) < 1 := by
  intro E Ω _ _ _ _ _ A A' σ hσ e₀ c hint hA hA'
  obtain ⟨k, hk, hfix⟩ := galAlgClosure_exists_pos_pow_apply_eq E Ω σ e₀
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set f : ℕ → Ω := fun i => (σ ^ i) e₀ with hf
  have hfint : ∀ i, IsIntegral ℤ (f i) := fun i =>
    hint.map ((σ ^ i : Ω ≃ₐ[E] Ω).toRingEquiv.toRingHom.toIntAlgHom)
  have hshift : ∀ i, σ (f i) = f (i + 1) := by
    intro i
    simp only [hf, pow_succ', AlgEquiv.mul_apply]

  have hcong : ∀ i, A'.valuation (1 - f i) < 1 := by
    intro i
    induction i with
    | zero => simpa [hf] using hA'
    | succ i ih =>
      have hy : A'.valuation (f i) ≤ 1 := valuation_le_one_of_valuation_one_sub_lt A' ih
      have hmove := hσ.2 (f i) hy
      have e : 1 - f (i + 1) = (1 - f i) + -(σ (f i) - f i) := by
        rw [← hshift i]; ring
      rw [e]
      refine Valuation.map_add_lt _ ih ?_
      rw [Valuation.map_neg]
      exact hmove
  refine ⟨∏ i ∈ Finset.range (m + 1), f i, ?_, ?_, ?_, ?_⟩
  · exact IsIntegral.prod _ (fun i _ => hfint i)
  · rw [map_prod]
    simp only [hshift]
    rw [Finset.prod_range_succ (fun i => f (i + 1)), Finset.prod_range_succ' f]
    have h0 : f (m + 1) = f 0 := by simpa [hf] using hfix
    rw [h0]
  · rw [Finset.prod_range_succ']
    have hP : IsIntegral ℤ (∏ i ∈ Finset.range m, f (i + 1)) :=
      IsIntegral.prod _ (fun i _ => hfint (i + 1))
    have hPle : A.valuation (∏ i ∈ Finset.range m, f (i + 1)) ≤ 1 :=
      (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A hP)
    rw [map_mul]
    calc A.valuation (∏ i ∈ Finset.range m, f (i + 1)) * A.valuation (f 0)
        ≤ 1 * A.valuation (f 0) := by gcongr
      _ = A.valuation e₀ := by simp [hf]
      _ < A.valuation c := hA
  · refine Finset.prod_induction f (fun x => A'.valuation (1 - x) < 1)
      (fun a b ha hb => valuation_one_sub_mul_lt A' ha hb) ?_ (fun i _ => hcong i)
    simp

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_inertia_fixed_roots_perturbed_polynomial : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A' : ValuationSubring Ω) (σ : G E Ω), σ ∈ Ine (F := E) A' → ∀ (b e : Ω) (m : ℕ) (f : Polynomial ℤ), IsIntegral ℤ e → σ e = e → A'.valuation (1 - e) < 1 → A'.valuation (m : Ω) = 1 → f.Monic → f.natDegree = m → Polynomial.aeval b f = 0 → ∃ ys : Multiset Ω, Multiset.card ys = m ∧ (∀ y ∈ ys, IsIntegral ℤ y ∧ σ y = y) ∧ e * (b ^ m - 1) = (ys.map (fun y => b - y)).prod := by
  first | exact @GlobalTheory.exists_roots_fixed_of_mem_Ine | exact GlobalTheory.exists_roots_fixed_of_mem_Ine | (intros; apply GlobalTheory.exists_roots_fixed_of_mem_Ine <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.iwasawaDecomposition_fact : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (σ : G E Ω), σ ∈ Dec (F := E) A → ∀ t : Ω, A.valuation (σ t) = A.valuation t := by
  first | exact @GlobalTheory.Dec_valuation_apply_eq | exact GlobalTheory.Dec_valuation_apply_eq | (intros; apply GlobalTheory.Dec_valuation_apply_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

theorem _root_.GlobalTheory.T.inertia_wild_of_trivial_tame_characters : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ τ ∈ Ine (F := E) A, (∀ d, 0 < d → ∃ y : Ω, y ^ (g ^ d - 1) = ((g : ℕ) : Ω) ∧ A.valuation (τ y / y - 1) < 1) → ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1 := by
  first | exact @GlobalTheory.TameWild.cob_lt_one_of_tame | exact GlobalTheory.TameWild.cob_lt_one_of_tame | (intros; apply GlobalTheory.TameWild.cob_lt_one_of_tame <;> assumption)
end
