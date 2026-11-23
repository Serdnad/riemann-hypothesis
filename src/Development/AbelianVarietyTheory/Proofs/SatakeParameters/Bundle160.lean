module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle155
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle994
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DetOfColSpanEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RelIndexMatrixHomLatticeRatioEqResiduePow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle713
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle189
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodPrimes

theorem isConjPl_iff {D : D7} {P P' : Pl D.host.E} : Formalism.IndefR.Lev.IsConjPl P P' ↔ P' = Formalism.DivisionValues.conjPl P := by
  constructor
  · intro h
    apply HeightOneSpectrum.ext
    refine ((Formalism.DivisionValues.conjPl P).isMaximal.eq_of_le P'.isPrime.ne_top ?_).symm
    refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
    obtain ⟨c', h1, h2⟩ := h c hc
    have : Formalism.DivisionValues.cO _ c = c' := RingOfIntegers.ext h2.symm
    show Formalism.DivisionValues.cO _ c ∈ P'.asIdeal
    rwa [this]
  · rintro rfl
    exact fun c hc => ⟨Formalism.DivisionValues.cO _ c, Ideal.mem_map_of_mem _ hc, rfl⟩

theorem eq_or_conj_of_under_eq {D : D7} {P Q : Pl D.host.E} (h : Q.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) :
    Q = P ∨ Q = Formalism.DivisionValues.conjPl P := by
  have hsub : (Q.asIdeal : Set (𝓞 D.host.E)) ⊆ P.asIdeal ∪ (Formalism.DivisionValues.conjPl P).asIdeal := by
    intro x hx
    have hfix : star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E) := by
      rw [star_mul', star_star, mul_comm]
    obtain ⟨y, hy⟩ := (D.sp.cm.fixed ((x : D.host.E) * star (x : D.host.E))).1 hfix
    have hint : IsIntegral ℤ y := by
      rw [← isIntegral_algebraMap_iff (B := D.host.E)]
      have e : algebraMap D.host.F D.host.E y = ((x * Formalism.DivisionValues.cO _ x : 𝓞 D.host.E) : D.host.E) := hy
      rw [e]
      exact (x * Formalism.DivisionValues.cO _ x).isIntegral_coe
    have hn : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨y, hint⟩ = x * Formalism.DivisionValues.cO _ x := RingOfIntegers.ext hy
    have h1 : (⟨y, hint⟩ : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ Q.asIdeal
      rw [hn]
      exact Ideal.mul_mem_right _ _ hx
    rw [h] at h1
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨y, hint⟩ ∈ P.asIdeal := h1
    rw [hn] at h2
    refine (P.isPrime.mem_or_mem h2).imp id fun h3 => ?_
    have h4 : Formalism.DivisionValues.cO _ (Formalism.DivisionValues.cO _ x) ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ h3
    have e : Formalism.DivisionValues.cO _ (Formalism.DivisionValues.cO _ x) = x := RingOfIntegers.ext (star_star (x : D.host.E))
    rw [e] at h4
    exact h4
  exact (Ideal.subset_union.1 hsub).imp
    (fun h => HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h))
    (fun h => HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (Formalism.DivisionValues.conjPl P).isPrime.ne_top h))

theorem offS_iff {D : D7} (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : Pl D.host.E) :
    OffS D S P ↔ P.under (𝓞 D.host.F) ∉ S := by
  constructor
  · intro h hP
    obtain ⟨x, hx, hy⟩ := h _ hP
    exact hy (algebraMap _ _ x) rfl hx
  · intro h v hv
    by_contra hc
    push Not at hc
    apply h
    have : v = P.under (𝓞 D.host.F) := by
      refine HeightOneSpectrum.ext (v.isMaximal.eq_of_le (P.under (𝓞 D.host.F)).isPrime.ne_top fun x hx => ?_)
      obtain ⟨y, h1, h2⟩ := hc x hx
      have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x = y := RingOfIntegers.ext h1.symm
      show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P.asIdeal
      rwa [e]
    rwa [← this]

theorem good_primes : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.Q A.μ0 = ∅ ∧ (∀ t P, Good R t P → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ Good R t (Formalism.DivisionValues.conjPl P) ∧ Good R A.μ0 P) ∧ (∀ SF, IsSF R SF → ∀ P, OffS D SF P ↔ Good R A.μ0 P) ∧ (R.IsFam → ∀ t, ∀ P ∈ A.ok t, Good R t (R.pl P) ∧ Formalism.DivisionValues.conjPl (R.pl P) ≠ R.pl P ∧ A.q P = Ideal.absNorm (R.pl P).asIdeal) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL
  have hQ : R.Q A.μ0 = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP h => ?_
    refine (hL.Q_ram A.μ0 PP).2 (Or.inl h) ?_
    rw [hL.xi_base]
    exact fun x _ => rfl
  have hcc := fun w : Pl D.host.E => Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl w
  refine ⟨hQ, fun t P hP => ⟨fun hg => ?_, fun PP h => ?_, fun PP h => ?_⟩, fun SF hSF P => ?_, fun hF t P hP => ?_⟩
  · have hk : ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
      rw [Nat.cast_mul] at hg
      rcases P.isPrime.mem_or_mem hg with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    obtain ⟨k, hk⟩ := hk
    rcases GlobalTheory.ConjOverQuad.div_or_conj_div D R.C.P k P hk with h | ⟨w', h, hw⟩
    · exact (hP P (Or.inl ((hL.Pg P).2 ⟨k, h⟩))).1 rfl
    · refine (hP w' (Or.inl ((hL.Pg w').2 ⟨k, h⟩))).2 (isConjPl_iff.2 ?_)
      rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at hw
      rw [HeightOneSpectrum.ext hw, hcc]
  · obtain ⟨h1, h2⟩ := hP PP h
    rw [isConjPl_iff] at h2 ⊢
    refine ⟨fun e => h2 (by rw [e, hcc]), fun e => h1 ?_⟩
    rw [← hcc PP, ← e, hcc]
  · rw [hQ] at h
    exact hP PP (Or.inl (h.resolve_right (Finset.notMem_empty _)))
  · rw [offS_iff]
    constructor
    · intro h PP hPP
      rw [hQ] at hPP
      have hPP' := hPP.resolve_right (Finset.notMem_empty _)
      have key : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F) := fun e =>
        h ((hSF _).2 ⟨PP, hPP', by rw [← e]; rfl⟩)
      exact ⟨fun e => key (by rw [e]), fun e => key (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e)⟩
    · intro h hm
      obtain ⟨PP, hPP, e⟩ := (hSF _).1 hm
      obtain ⟨h1, h2⟩ := h PP (Or.inl hPP)
      have e' : P.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := HeightOneSpectrum.ext e.symm
      rcases eq_or_conj_of_under_eq e' with h3 | h3
      · exact h1 h3.symm
      · exact h2 (isConjPl_iff.2 h3)
  · obtain ⟨gramR, c0R, c0L, hT⟩ := hF.tie
    obtain ⟨h1, h2, h3⟩ := (hT.ok t P).1 hP
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at h1 h3
    refine ⟨fun PP h => ?_, fun e => h1 (by rw [e]), ?_⟩
    · have hm : PP ∈ (R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E)) :=
        h.imp (fun h => hF.Sb h) id
      refine ⟨fun e => h2 (e ▸ hm), fun hc => h3 PP hm ?_⟩
      rw [isConjPl_iff.1 hc, hcc]
    · rw [hT.q P, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.GoodPrimes
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.wordConditions_at_place_of_frobeniusOrbit : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (hG : Good (D.nbr i w hw).Kw 1 C.LL) r ρ π (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) → ∃ g, IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ C.WordBase r ρ π L HW hG (recWord L (liftIdx D i) ε g) := by
  first | exact @GlobalTheory.HTW.Rec.wordBase_of_jumpIn | exact GlobalTheory.HTW.Rec.wordBase_of_jumpIn | (intros; apply GlobalTheory.HTW.Rec.wordBase_of_jumpIn <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.hodgeTateJumps_coefExt_of_roomy_adm7 : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw), Roomy L C₀ → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.PtIn i r ρ π → ∃ (ε : ℤˣ) (κ : D.host.E →+* ↥Cx.LL.1), JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x)) (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π)) := by
  first | exact @GlobalTheory.HTW.Rec.hodgeTateJumps_coefficientExtension | exact GlobalTheory.HTW.Rec.hodgeTateJumps_coefficientExtension | (intros; apply GlobalTheory.HTW.Rec.hodgeTateJumps_coefficientExtension <;> assumption)
end

section

open Matrix

noncomputable section

namespace GlobalTheory.Hk3.VacPhase

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem cT_mul' (σ : L →+* L) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) L) (B : Matrix (Fin b) (Fin c) L) :
    Formalism.UG.cT σ (A * B) = Formalism.UG.cT σ B * Formalism.UG.cT σ A := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one' (σ : L →+* L) {a : ℕ} : Formalism.UG.cT σ (1 : Matrix (Fin a) (Fin a) L) = 1 := by
  simp [Formalism.UG.cT, Matrix.map_one]

theorem cT_sub' (σ : L →+* L) {a b : ℕ} (A B : Matrix (Fin a) (Fin b) L) :
    Formalism.UG.cT σ (A - B) = Formalism.UG.cT σ A - Formalism.UG.cT σ B := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_add' (σ : L →+* L) {a b : ℕ} (A B : Matrix (Fin a) (Fin b) L) :
    Formalism.UG.cT σ (A + B) = Formalism.UG.cT σ A + Formalism.UG.cT σ B := by
  ext i j; simp [Formalism.UG.cT]

theorem mul_int {a b c : ℕ} {A : Matrix (Fin a) (Fin b) L} {B : Matrix (Fin b) (Fin c) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) (i : Fin a) (j : Fin c) :
    (A * B) i j ∈ Formalism.UG.intL L := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem cT_int (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {a b : ℕ} {A : Matrix (Fin a) (Fin b) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (i : Fin b) (j : Fin a) : Formalism.UG.cT σ A i j ∈ Formalism.UG.intL L := by
  have h := hA j i
  change Valued.v (σ (A j i)) ≤ 1
  rw [hσ]; exact h

theorem locH_sub_trace_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L), (∀ x, Valued.v (σ x) = Valued.v x) → δ ∈ Formalism.UG.intL L →
  ∀ (n n' : ℕ) (JS a k : GL (Fin n) L) (JT : GL (Fin n') L) (E : Matrix (Fin n) (Fin n) L) (y : Matrix (Fin n') (Fin n) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → (∀ i j, ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  Formalism.UG.cT σ E * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * E) →
  (∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * E) i j ∈ Formalism.UG.intL L) → (∀ i j, (E * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (k : Matrix (Fin n) (Fin n) L) = 1 + E → (∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.locH σ δ JS JT y (y * (((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1)) -
    δ * Matrix.trace (E * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) ∈ Formalism.UG.intL L := by
  intro L _ _ σ δ hσ hδ n n' JS a k JT E y hJ hP hT hSD hE hAiE hEA hk hKi hyA
  set J : Matrix (Fin n) (Fin n) L := (JS : Matrix (Fin n) (Fin n) L) with hJdef
  set P : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef
  set T : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hTdef
  set K : Matrix (Fin n) (Fin n) L := (k : Matrix (Fin n) (Fin n) L) with hKdef
  set Ki : Matrix (Fin n) (Fin n) L := ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hKidef
  set A : Matrix (Fin n) (Fin n) L := (a : Matrix (Fin n) (Fin n) L) with hAdef
  set Ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAidef
  have hPJ : P * J = 1 := by rw [hPdef, hJdef]; exact JS.inv_mul
  have hJP : J * P = 1 := by rw [hPdef, hJdef]; exact JS.mul_inv
  have hKKi : K * Ki = 1 := by rw [hKdef, hKidef]; exact k.mul_inv
  have hAAi : A * Ai = 1 := by rw [hAdef, hAidef]; exact a.mul_inv
  set R : Matrix (Fin n) (Fin n) L := P * Formalism.UG.cT σ Ki * J with hRdef
  set Z : Matrix (Fin n) (Fin n) L := P * Formalism.UG.cT σ y * T * y with hZdef

  have h1 : GlobalTheory.Hk3.locH σ δ JS JT y (y * (Ki - 1)) = δ * Matrix.trace ((R - 1) * Z) := by
    unfold GlobalTheory.Hk3.locH
    have : ((y * (Ki - 1)).map σ)ᵀ = Formalism.UG.cT σ (Ki - 1) * Formalism.UG.cT σ y := cT_mul' σ y (Ki - 1)
    rw [← hPdef, ← hTdef, this, cT_sub', cT_one']
    congr 1
    rw [hRdef, hZdef]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc J P, hJP, Matrix.one_mul]
  have h2 : δ * Matrix.trace (E * P * Formalism.UG.cT σ y * T * y) = δ * Matrix.trace (E * Z) := by
    rw [hZdef]; simp only [Matrix.mul_assoc]

  have hR : R * (1 - E) = 1 := by
    have hcK : Formalism.UG.cT σ K * J = J * (1 - E) := by
      rw [hk, cT_add', cT_one', Matrix.add_mul, hE, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, sub_eq_add_neg]
    rw [hRdef, Matrix.mul_assoc, ← hcK, ← Matrix.mul_assoc, Matrix.mul_assoc P, ← cT_mul', hKKi, cT_one', Matrix.mul_one, hPJ]
  have hR' : (1 - E) * R = 1 := mul_eq_one_comm.mp hR
  have hRE : R - 1 - E = E * R * E := by
    have e1 : R - 1 = R * E := by
      have := hR; rw [Matrix.mul_sub, Matrix.mul_one] at this
      rw [← this]; abel
    have e2 : R - 1 = E * R := by
      have := hR'; rw [Matrix.sub_mul, Matrix.one_mul] at this
      rw [← this]; abel
    calc R - 1 - E = (R - 1) * E := by rw [Matrix.sub_mul, Matrix.one_mul, e1]
      _ = E * R * E := by rw [e2]
  have h3 : GlobalTheory.Hk3.locH σ δ JS JT y (y * (Ki - 1)) - δ * Matrix.trace (E * P * Formalism.UG.cT σ y * T * y) =
      δ * Matrix.trace (R * (E * Z * E)) := by
    rw [h1, h2, ← mul_sub, ← Matrix.trace_sub, ← Matrix.sub_mul, hRE]
    congr 1
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm E]
    simp only [Matrix.mul_assoc]
  rw [h3]

  have hRint : ∀ i j, R i j ∈ Formalism.UG.intL L :=
    mul_int (mul_int hP (cT_int σ hσ hKi)) hJ
  have hy' : Formalism.UG.cT σ y = Formalism.UG.cT σ Ai * Formalism.UG.cT σ (y * A) := by
    rw [← cT_mul', Matrix.mul_assoc, hAAi, Matrix.mul_one]
  have hW : E * Z * E = ((E * A) * (Ai * P * Formalism.UG.cT σ Ai) * Formalism.UG.cT σ (y * A)) * T * ((y * A) * (Ai * E)) := by
    rw [hZdef, hy']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A Ai, hAAi, Matrix.one_mul, ← Matrix.mul_assoc A Ai E, hAAi, Matrix.one_mul]
  have hWint : ∀ i j, (E * Z * E) i j ∈ Formalism.UG.intL L := by
    rw [hW]
    exact mul_int (mul_int (mul_int (mul_int hEA hSD.2) (cT_int σ hσ hyA)) hT) (mul_int hyA hAiE)
  refine Subring.mul_mem _ hδ ?_
  exact Subring.sum_mem _ fun i _ => mul_int hRint hWint i i

end GlobalTheory.Hk3.VacPhase

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt

theorem _root_.GlobalTheory.T.relIndex_matrixHomLattice_ratio_eq_residue_pow : ∀ {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p n' : ℕ) (hp : Irreducible (p : W)) (hcard : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') {k k' : ℕ} (a₀ a₁ : Matrix (Fin k) (Fin k) Qq) (b₀ b₁ : Matrix (Fin k') (Fin k') Qq) (ha₀ : IsUnit a₀.det) (ha₁ : IsUnit a₁.det) (hb₀ : IsUnit b₀.det) (hb₁ : IsUnit b₁.det), (((homLat W (colSpan W a₀) (colSpan W b₀)).toAddSubgroup.relIndex (homLat W (colSpan W a₁) (colSpan W b₁)).toAddSubgroup : ℕ) : ℝ) / (((homLat W (colSpan W a₁) (colSpan W b₁)).toAddSubgroup.relIndex (homLat W (colSpan W a₀) (colSpan W b₀)).toAddSubgroup : ℕ) : ℝ) = (p : ℝ) ^ ((n' : ℤ) * ((k : ℤ) * (ordP W p b₀.det - ordP W p b₁.det) - (k' : ℤ) * (ordP W p a₀.det - ordP W p a₁.det))) := by
  first | exact @GlobalTheory.HomLatIndex.relIndex_homLat_ratio | exact GlobalTheory.HomLatIndex.relIndex_homLat_ratio | (intros; apply GlobalTheory.HomLatIndex.relIndex_homLat_ratio <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj finiteCompletionMap)

namespace GlobalTheory.HeckeFinTriv

theorem valued_natCast_le_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v (n : v.adicCompletion K) ≤ 1 := by
  induction n with
  | zero => rw [Nat.cast_zero, map_zero]; exact zero_le
  | succ n ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le _ ih (by rw [map_one])

theorem valued_natCast_le_of_dvd {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {M N : ℕ}
    (h : M ∣ N) : Valued.v (N : v.adicCompletion K) ≤ Valued.v (M : v.adicCompletion K) := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_le_of_le_one_right' (valued_natCast_le_one v k)

theorem finPart_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ψ : HChar (maximalRealSubfield E)) (M : ℕ), (∀ a : Ideles (maximalRealSubfield E), a ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) → (∀ w, (a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Valued.v ((a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 P - 1) ≤ Valued.v ((M : maximalRealSubfield E) : P.adicCompletion (maximalRealSubfield E))) → ψ.1 a = 1) → (∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → ψ.UnrAt (w.under (𝓞 (maximalRealSubfield E)))) → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (N : ℕ), M ∣ N → ∀ b : Ideles (maximalRealSubfield E), ideleMap (maximalRealSubfield E) E b ∈ levT E {w | GlobalTheory.UnitaryBC.IsSplitAt w ∧ w ≠ w₀} N → ψ.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b) = 1 := by
  intro E _ _ _ ψ M hlev hns w₀ N hMN b hb
  have he : ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal ≠ 0 := fun w =>
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 (maximalRealSubfield E))).ne_bot
  have hc : ∀ w : HeightOneSpectrum (𝓞 E), (ideleMap (maximalRealSubfield E) E b).val.2 w =
      finiteCompletionMap (maximalRealSubfield E) E w (b.val.2 (w.under (𝓞 (maximalRealSubfield E)))) := fun w => rfl
  have hs : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) = v := fun v => by
    haveI := v.isPrime
    obtain ⟨⟨P, hP, hP'⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
    exact ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, HeightOneSpectrum.ext hP'.over.symm⟩

  have hunit : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Valued.v (b.val.2 v) = 1 := fun v => by
    obtain ⟨w, rfl⟩ := hs v
    have h := hb.1 w
    change Valued.v ((ideleMap (maximalRealSubfield E) E b).val.2 w) = 1 at h
    rw [hc, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, pow_eq_one_iff_of_nonneg zero_le (he w)] at h
    exact h

  have hcong : ∀ w : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w → w ≠ w₀ →
      Valued.v (b.val.2 (w.under (𝓞 (maximalRealSubfield E))) - 1) ≤ Valued.v (N : (w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := fun w h1 h2 => by
    have h := hb.2 w ⟨h1, h2⟩
    change Valued.v ((ideleMap (maximalRealSubfield E) E b).val.2 w - 1) ≤ _ at h
    rwa [hc, ← map_one (finiteCompletionMap (maximalRealSubfield E) E w), ← map_sub, ← map_natCast (finiteCompletionMap (maximalRealSubfield E) E w),
      GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap,
      pow_le_pow_iff_left₀ zero_le zero_le (he w)] at h
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local (maximalRealSubfield E) ψ.1 ψ.2.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b)
    (GlobalTheory.Mem.Chr.finPartI_mem_unitIdl.2 hunit) (fun w => by rw [GlobalTheory.Mem.Chr.finPartI_fst]; rfl) ?_
  intro v x hx
  rw [GlobalTheory.Mem.Chr.finPartI_snd] at hx
  have hxu : Valued.v (x : v.adicCompletion (maximalRealSubfield E)) = 1 := by rw [hx]; exact hunit v
  by_cases hu : ψ.UnrAt v
  · exact hu x hxu
  obtain ⟨w, hw⟩ := hs v
  have hsp : GlobalTheory.UnitaryBC.IsSplitAt w := by
    by_contra hn
    exact hu (hw ▸ hns w hn)
  obtain ⟨u, hu1, hu2⟩ := hsp
  have hsp' : ∃ w' : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w' ∧ w' ≠ w₀ ∧ w'.under (𝓞 (maximalRealSubfield E)) = v := by
    by_cases h0 : w = w₀
    · refine ⟨u, ⟨w, fun e => hu1 e.symm, hu2.symm⟩, h0 ▸ hu1, hu2.trans hw⟩
    · exact ⟨w, ⟨u, hu1, hu2⟩, h0, hw⟩
  obtain ⟨w', hw'1, hw'2, rfl⟩ := hsp'
  have hxc : Valued.v ((x : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) - 1) ≤
      Valued.v ((M : (maximalRealSubfield E)) : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := by
    rw [hx]
    refine (hcong w' hw'1 hw'2).trans ?_
    have e : ((M : (maximalRealSubfield E)) : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) = (M : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := by
      rw [← map_natCast (algebraMap (maximalRealSubfield E) ((w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E))) M]; rfl
    rw [e]
    exact valued_natCast_le_of_dvd _ hMN
  apply hlev
  · intro P
    by_cases hP : P = w'.under (𝓞 (maximalRealSubfield E))
    · subst hP
      rw [GlobalTheory.HeckeProduct.localIdele_snd_self]
      exact hxu
    · rw [GlobalTheory.HeckeProduct.localIdele_snd_ne (maximalRealSubfield E) _ _ hP]
      exact map_one _
  · intro w
    rw [GlobalTheory.HeckeProduct.localIdele_fst]
    rfl
  · intro P
    by_cases hP : P = w'.under (𝓞 (maximalRealSubfield E))
    · subst hP
      rw [GlobalTheory.HeckeProduct.localIdele_snd_self]
      exact hxc
    · rw [GlobalTheory.HeckeProduct.localIdele_snd_ne (maximalRealSubfield E) _ _ hP, sub_self, map_zero]
      exact zero_le

end GlobalTheory.HeckeFinTriv
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem cg_hasSat_unique : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (a : ℕ) (π : CG K a) (w : HeightOneSpectrum (𝓞 K)) (B B' : Multiset ℂˣ), π.HasSat w B → π.HasSat w B' → B = B' :=
  fun _ _ _ _ _ _ _ _ _ h h' => CG.HasSat.unique h h'

end GlobalTheory.AboveL
end

section

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical
open Formalism.L2.Ker GlobalTheory.TopStep GlobalTheory.TopLaw GlobalTheory.MatLaw

noncomputable section

namespace GlobalTheory.FiLaw

theorem xiEntry_stab : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → Ch.Ok → cst.sharp = true → R.m ≤ cst.A → (∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) → ∀ (u : Pr.Word) (i : ℕ), i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) (a : FrmG (L.levG (i + 1) be) (L.levQ (i + 1) be)), a • p' = p' → ∀ x, XiEntry Ch sel mu cst L i al be p p' (a.1.1.toLinearMap ∘ₗ x) * ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst i P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = (((L.levG (i + 1) be).chr a.2.1 * (L.levQ (i + 1) be).chr a.2.2 : X.Kˣ) : X.K) * XiEntry Ch sel mu cst L i al be p p' x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hg hT hL _ _ _ _ u i hi al be p p' a ha x
  have hd := (tilOk_of_avoid (mu := mu) hPr hsel u ⟨hT u, hg⟩).2.2
  obtain ⟨κ, c, hκ, hc, ec⟩ := exists_pass hd (1 : FrmG (L.levG i al) (L.levQ i al)) p
  obtain ⟨κ', c', hκ', hc', ec'⟩ := exists_pass hd a p'
  have key := xiEntry_law hX hPr hsel hL hi hκ hκ' hc hc' x (phiT_act _ _ _ _ _ _ _)
  have e1 : x ∘ₗ ((1 : FrmG (L.levG i al) (L.levQ i al)).1.1.symm.toLinearMap) = x := LinearMap.ext fun v => rfl
  rw [one_smul, ha, e1, ec, ec'] at key
  simp only [Prod.snd_one, Prod.fst_one, map_one, mul_one, inv_one] at key
  rw [← key]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have h1 : ((κ P)⁻¹).1 = 1 := by
    have h := hκ P
    rw [one_smul] at h
    simpa using h
  have h2 : LinearEquiv.det (κ' P).1 = LinearEquiv.det a.1.1 := by
    have h := congrArg LinearEquiv.det (hκ' P)
    rw [ha, map_mul, map_mul, Subgroup.coe_inv, map_inv] at h
    rw [mul_left_comm] at h
    have h' := mul_left_cancel (h.symm.trans (mul_one _).symm)
    exact (mul_inv_eq_one.1 h').symm
  rw [Pi.inv_apply, Pi.inv_apply, h1, map_one, Units.val_one, rhoT_inv, ← muAt_det, h2]
  unfold rhoS
  rw [GlobalTheory.Mem.Col2.IdxEx.Cong.unitV_one, one_mul]

end GlobalTheory.FiLaw
end
end
