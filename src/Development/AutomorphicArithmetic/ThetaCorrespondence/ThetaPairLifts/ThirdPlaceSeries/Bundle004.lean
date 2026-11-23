module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle230
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.OptInEqSome
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle012
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle149
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle322
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle059
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section



section
noncomputable section
namespace GlobalTheory.StringRepresentationDecomposition
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal
def CentredStringDecompositionAlt : Prop :=
  ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa →
    ∀ r, GoodR D.nd i r →
    ∃ R : ∀ k : Fin Pa.length, Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i)),
      (∀ k, _root_.UpperTheory.GalS.IsStringRepN D i (Pa.get k) (R k)) ∧
      ∀ g, ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
        ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
          (((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))).charpoly).scaleRoots
            ((epsQ D i g)⁻¹ ^ a)
def PurityStringWeight' : Prop :=
  ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa →
    ∀ (k : Fin Pa.length) (R : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))),
      _root_.UpperTheory.GalS.IsStringRepN D i (Pa.get k) R → ∀ a < (Pa.get k).d,
      (∃ v : Fin (Pa.get k).a → Qbar (D.nd.l i), v ≠ 0 ∧ ∀ g,
        ((epsQ D i g)⁻¹ ^ a) • ((R g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a)
          (Qbar (D.nd.l i))).mulVec v = iotaOQ D.nd D.naut i (chi1 D.nd i g) • v) →
      ((Pa.get k).d : ℤ) - 1 - 2 * a = (D.R.t : ℤ) - 1
def HeckeCharEqOfLAdicRealisation' : Prop :=
  ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → ∀ (i : D.nd.Loc) (χ χ' : D.naut.CG 1) (s : ℝ)
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))),
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s) →
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ' w) s) →
    χ = χ'
def MuCharacterCondition : Prop :=
  ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → ∀ (i : D.nd.Loc), HG D.nd D.naut i →
    ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i)),
    (∀ g, ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
      iotaOQ D.nd D.naut i (chi1 D.nd i g)) →
    ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)
        (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2)
def ResidueCount : Prop :=
  ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → ∀ (i : D.nd.Loc), HG D.nd D.naut i →
    ∀ (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (x : D.nd.X i)
    (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))),
    (∀ k, _root_.UpperTheory.GalS.IsStringRepN D i (Pa.get k) (R k)) →
    (∀ g, ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
        ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
          (((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))).charpoly).scaleRoots
            ((epsQ D i g)⁻¹ ^ a)) →
    ∃ Ak : Fin Pa.length → Multiset ℕ, (∀ k, (Ak k).sum = (Pa.get k).a ∧ ∀ a ∈ Ak k, 1 ≤ a) ∧
      ∑ k, (Pa.get k).d • Ak k = D.R.r ::ₘ Multiset.replicate D.R.t 1
def LocalGlobalCompatible (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ w : PlE D.host, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → _root_.UpperTheory.GalS.LGCatN D.nd r D.naut w
end GlobalTheory.StringRepresentationDecomposition
end
end
end

section



section
noncomputable section
namespace Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open NumberField IsDedekindDomain
theorem galois_condition_one_of_alt (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (h32 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (hr : Formalism.MainNotions.N.GoodR D.nd i r) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG1 (D := D) i r := by
  intro g k
  obtain ⟨f, hf⟩ := ((h32 i).2.2 r hr).1 g k
  have e : (fun x : D.nd.X i => ((Formalism.MainNotions.N.rO D.nd i r x g).charpolyRev).coeff k) =
      (f : D.nd.X i → D.nd.O i) := funext fun x => (hf x).symm
  rw [e]
  exact f.2
theorem admG4_of_goodR (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (h32 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (hr : Formalism.MainNotions.N.GoodR D.nd i r) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG4 (D := D) i r := by
  intro x v hl hS hQ g hg
  exact ((h32 i).2.2 r hr).2.2.2 x v hl hS hQ (D.nd.plOm.1 v) (D.nd.plOm.2 v) g hg
end Formalism.MainNotions.N
end
end
end

section



section
noncomputable section
namespace Formalism.MainNotions.PairedCharacterCondition
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Module Polynomial
variable {D : D7}
def PairedCharacterConditionAlt (C : ℝ) (CT : ℕ) : Prop :=
  ∀ (i : D.nd.Loc) (k k' : Fin 2), k ≠ k' → D.nd.l i = D.host.g k →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
    GoodR D.nd i r → (∀ π ∈ D.nd.Z i, Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) →
  ∀ (eta s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool)
    (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ),
    eta + D.R.t + 1 < s →
    Real.log (D.host.g k' : ℝ) ≤ 2 * Real.log (D.host.g k : ℝ) →
    CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k →
    SignOK i sg → HostJ i r eta s S sg U → (∀ π ∈ D.nd.Zgood i, Br.sFin D.loc D.nbr i ρ π) →
    (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
    (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ) * rhs C eta i ρ π
def GaloisFamilyConditions' : Prop :=
  ∀ i r, GoodR D.nd i r →
    Formalism.MainNotions.SumRepresentations.At.G1 D.nd i r ∧ _root_.UpperTheory.GalS.G2a D.nd D.naut i r ∧ _root_.UpperTheory.GalS.G3 D.nd i r ∧
      Formalism.MainNotions.SumRepresentations.At.G4 D.nd i r
def LocalGlobalCompatibility' : Prop := _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D
section Pending
end Pending
end Formalism.MainNotions.PairedCharacterCondition
end
end
end

section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
noncomputable section
namespace GlobalTheory.BCPerm
abbrev _root_.GlobalTheory.BCPerm.mainTheorem : Prop :=  ∀ D : D7, SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i)
    (P0 PI : D.naut.AV i) (Pa0 Pa : List (Part D.naut.CG)), D.naut.ptV i P0 = some x →
    D.naut.ptV i PI = some x → IsBCV D.nd D.naut i P0 Pa0 → IsBCV D.nd D.naut i PI Pa → Pa0.Perm Pa
end GlobalTheory.BCPerm
end
end
end

section



section
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Classical
variable {D : D7}
theorem jumpLemma_a_of_admissible_alt_alt {L : SizeData₂ D} (hP : AdmPar L) (hG2 : _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D) (hCr : CrysIffWD D.nd D.naut)
    (hG2g : _root_.UpperTheory.GalS.DeRhamJumpsDistinctCondition D) (hDi : AdmDict D) (hRd : AdmRead D) : ConclusionJa D := by
  obtain ⟨ep, hdict⟩ := hDi
  refine ⟨ep, ?_⟩
  intro i r hr w hw C τ
  obtain ⟨hInd, ⟨g, hg⟩, hread⟩ := hRd i r hr w hw C τ
  obtain ⟨ρ, hρ⟩ := exists_placeOf (D := D) g
  have hRA : ReadAt D i (gEmb C τ) g ρ := ⟨hg, hρ⟩
  obtain ⟨sg, cτ, hsU, hsD, hJ0, hchi⟩ := hdict i (gEmb C τ) g ρ hRA
  obtain ⟨hχdR, hχJ⟩ := hchi w hInd
  rw [Multiset.map_eq_singleton] at hχJ
  obtain ⟨c, hc, hcq⟩ := hχJ
  have hjr := D.nd.j_range i
  have hF := jFacts_of hP (D.nd.j i) hjr.1 hjr.2 ρ
  set up := decide (TypeU D ep g) with hup
  have hsU' : up = true → sg = 1 := fun h => hsU (by simpa [hup] using h)
  have hsD' : up = false → sg = -1 := fun h => hsD (by simpa [hup] using h)
  have hx : ∀ x, D.naut.IsdRW i (rQ D i r x) w ∧
      D.naut.jumpsW i (rQ D i r x) (gEmb C τ) = D.naut.locAutHodgeTateWeightsLevelZero i (gEmb C τ) := by
    intro x
    by_cases hl : D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1
    · have h := _root_.UpperTheory.GalS.g2g' hG2g i r hr hl w hw x
      exact ⟨h.1, h.2 _ hInd⟩
    · push Not at hl
      have h := _root_.UpperTheory.GalS.g2a' (hG2 i r hr) w hw hl.1 hl.2 x
      have hcont := SumRepresentations.contQ_of_continuous D.nd D.naut i (r x) (hr x).1
      exact ⟨((hCr i _ _ w hw hcont).1 h.1).1, h.2 _ hInd⟩
  have hkey : ∀ a : ℤ, (((D.naut.locAutHodgeTateWeightsLevelZero i (gEmb C τ)).count (a + c) : ℕ) : ℤ) =
      if (a : ℚ) ∈ JJ D up (D.nd.j i) ρ then 1 else 0 :=
    count_key hF _ sg cτ c up hsU' hsD' hJ0 hcq
  have hTw : ∀ x (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a =
      if (a : ℚ) ∈ JJ D up (D.nd.j i) ρ then 1 else 0 := by
    intro x a
    obtain ⟨h1, h2, h3⟩ := hread x (hx x).1 hχdR c hc
    rw [(h1 a).1, (hx x).2, hkey]
  have hDu : ∀ x (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) τ a =
      if (a : ℚ) ∈ dualS (JJ D up (D.nd.j i) ρ) then 1 else 0 := by
    intro x a
    obtain ⟨h1, h2, h3⟩ := hread x (hx x).1 hχdR c hc
    rw [(h1 a).2, (hx x).2, dualS_int, ← hkey]
    congr 3; ring
  refine ⟨g, ρ, hRA, ?_, ?_⟩
  · intro x a
    obtain ⟨h1, h2, h3⟩ := hread x (hx x).1 hχdR c hc
    refine ⟨?_, hTw x a, ?_, hDu x a⟩
    · rw [h2 _ (Or.inl rfl) a, hTw x a]; exact ite_ne_zero_iff' _
    · rw [h2 _ (Or.inr rfl) a, hDu x a]; exact ite_ne_zero_iff' _
  · intro ρπ π hπ hdec a
    obtain ⟨h1, h2, h3⟩ := hread π (hx π).1 hχdR c hc
    have hW : ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ π))) τ a =
        if (a : ℚ) ∈ JW D up (D.nd.j i) ρ then 1 else 0 := by
      intro a
      rw [(h3 ρπ hπ hdec a).1, hTw π a]
      by_cases hb : (a : ℚ) ∈ blockJ D
      · have hb' := (block_mem_iff (D := D) a).1 hb
        rw [if_pos (block_sub_JJ up _ ρ _ hb), if_pos hb', if_neg (block_not_mem_JW hF up _ hb)]
        simp
      · have hb' : ¬ (0 ≤ a ∧ a < (D.R.t : ℤ)) := fun h => hb ((block_mem_iff a).2 h)
        rw [if_neg hb', sub_zero]
        simp only [JJ_iff_JW hF up _ hb]
    have hT : ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ π))) τ a =
        if (a : ℚ) ∈ dualS (JW D up (D.nd.j i) ρ) then 1 else 0 := by
      intro a
      rw [(h3 ρπ hπ hdec a).2.1, hW, dualS_int]
    refine ⟨?_, hW a, ?_, hT a⟩
    · rw [(h3 ρπ hπ hdec a).2.2.1, hW a]; exact ite_ne_zero_iff' _
    · rw [(h3 ρπ hπ hdec a).2.2.2, hT a]; exact ite_ne_zero_iff' _
end GlobalTheory.JumpSets
end
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
noncomputable section
namespace GlobalTheory.GaloisFromAdm
theorem main_alt_alt_alt : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → GlobalTheory.BlockComplement.GaloisRepsCusp D := by
  intro D h i a ha π hc hr
  obtain ⟨ρ, hcont, hss, haway, -⟩ := (_root_.UpperTheory.GalS.weak' h i).1 a ha π hc hr
  refine ⟨ρ, hcont, hss, ?_⟩
  have hfin := placesOver_finite D (D.nd.l i) (Fact.out : (D.nd.l i).Prime).ne_zero
  filter_upwards [D.naut.locG_unr_ae π, hfin.eventually_cofinite_notMem] with w hu hw B φ hB hφ
  rw [D.naut.wdOf_frob i ρ w hw hcont (by rw [(haway w hw).eq_of_unr ((D.naut.unr_tw _ _).2 hu)]; exact (D.naut.unr_tw _ _).2 hu) B φ hB hφ,
    (haway w hw).eq_of_unr ((D.naut.unr_tw _ _).2 hu)]
  rfl
end GlobalTheory.GaloisFromAdm
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.PartUnitary
theorem frobEig_openB_and_norm_one_of_isBCV : ∀ (D : D7), SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → ∀ (i : D.nd.Loc) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), IsBCV D.nd D.naut i P Pa → ∀ p ∈ Pa, ∀ w : PlE D.host,
    D.naut.unr (D.naut.locG p.π w) → ∀ α ∈ D.naut.frobEig (D.naut.locG p.π w), UpperTheory.GalN.OpenB (Formalism.ConjugateSelfDual.normV w) α ∧ (p.a = 1 → ‖α‖ = 1) := by
  intro D ht hT i P Pa hB p hp w hu α hα
  have hW := GlobalTheory.LocalInv.weightRegular_of_ext D.nd D.naut D.nbc
  have hAut := ht.2.1
  obtain ⟨ha1, hd1, hcsd⟩ := hB.1 p hp
  have hle : ∀ τ, (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤
      D.naut.infWt i τ := by
    intro τ
    rw [← hB.2.2.2.2.2 τ]
    unfold isoInf
    refine le_trans ?_ (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
    refine List.single_le_sum (fun _ _ => Multiset.zero_le _) _
      (List.mem_map_of_mem (f := fun k : ℂ => (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - k))) ?_)
    rw [GlobalTheory.LocalInv.list_coe]
    exact List.mem_map_of_mem (List.mem_range.mpr hd1)
  have hnd : ∀ τ, (D.naut.infG p.π τ).Nodup := fun τ =>
    Multiset.Nodup.of_map _ (Multiset.nodup_of_le (hle τ) (hW i P τ).1)
  have hint : ∀ τ, ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ,
      z + ((p.d : ℂ) - 1) / 2 = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
    intro τ z hz
    obtain ⟨k, hk⟩ := (hW i P τ).2 _ (Multiset.mem_of_le (hle τ) (Multiset.mem_map_of_mem _ hz))
    exact ⟨k, by rw [← hk]; push_cast; ring⟩
  rcases Int.even_or_odd ((D.R.nV : ℤ) - p.d - p.a + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hr : D.naut.ralg p.π := (D.naut.ralg_def _).2 fun τ => ⟨hnd τ, fun z hz => by
      obtain ⟨k, hk⟩ := hint τ z hz
      refine ⟨k + m, ?_⟩
      have hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = (m : ℂ) + m := by
        exact_mod_cast hm
      push_cast at hm' ⊢
      linear_combination hk + (1 / 2 : ℂ) * hm'⟩
    exact (_root_.UpperTheory.GalN.tempo' hT p.a p.π ha1 hcsd hr w).part hu α hα
  · have hr : D.naut.ralg (D.naut.tw p.π D.naut.etaT) := (D.naut.ralg_def _).2 fun τ => by
      obtain ⟨s, hs, k0, hk0⟩ : ∃ s : ℂ, D.naut.infG D.naut.etaT τ = {s} ∧ ∃ k0 : ℤ, s = (k0 : ℂ) + 1 / 2 := by
        rcases (hAut.2.1 τ).1 with h | h
        · exact ⟨1 / 2, h, 0, by simp⟩
        · exact ⟨-(1 / 2), h, -1, by push_cast; ring⟩
      rw [D.naut.infG_tw _ _ τ s hs]
      refine ⟨(hnd τ).map (add_left_injective s), fun z hz => ?_⟩
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨k, hk⟩ := hint τ y hy
      refine ⟨k + k0 + m + 1, ?_⟩
      have hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = 2 * (m : ℂ) + 1 := by
        exact_mod_cast hm
      push_cast at hm' ⊢
      rw [hk0]
      linear_combination hk + (1 / 2 : ℂ) * hm'
    exact (_root_.UpperTheory.GalN.tempo' hT p.a _ ha1 (D.naut.csd_tw _ _ hAut.1.1 hcsd) hr w).part_tw hAut hu α hα
end GlobalTheory.PartUnitary
end
end

section



section
namespace UpperTheory.GalC.Tr
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
theorem no_g4_restrict_alt {D : D7} {c : CutD D} (_ : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (_ : ∀ i, UpperTheory.GalS.UnusedSlot55 D.nd D.naut i) :
    ∀ i, UpperTheory.GalS.UnusedSlot55 (cut D c).nd (cut D c).naut i := fun _ => trivial
end UpperTheory.GalC.Tr
end
end

section



section
noncomputable section
namespace Formalism.MainNotions.TypePrimeCongruences
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
def TypePrimeHypothesesAlt (D : D7) : Prop := SumRepresentations.adm5 D ∧ _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D ∧ TypePrimeWildIdempotentChoice D
def TypePrimeLemmasStatement (D : D7) : Prop := _root_.Formalism.MainNotions.TypePrimeCongruences.TypePrimeHypothesesAlt D → TypePrimeChoiceConclusions D
end Formalism.MainNotions.TypePrimeCongruences
end
end
end

section



section
noncomputable section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
end GlobalTheory.CrysFromGTwo
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.DualTwistCrys
end GlobalTheory.DualTwistCrys
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.CrysChiOne
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}
end GlobalTheory.CrysChiOne
end
section
namespace Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open NumberField IsDedekindDomain
theorem galois_condition_three_of_alt_alt (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (h32 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (hr : GoodR D.nd i r)
    (hdec : Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hcont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))))
    (hHG : HG D.nd D.naut i) (hN9 : ResidualIrreducibleRankR D) (hB : LitBurnside (GE D.nd))
    (hc : AbsIrreducibleDistinct D i r) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG3 (D := D) i r ρ π := by
  have h2 : ∀ x (g : GE D.nd), (mapM (IsLocalRing.residue (D.nd.O i)) (rO D.nd i r x) g).charpoly =
      (mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π) g).charpoly *
        ∏ c ∈ Finset.Icc 1 D.R.t,
          (X - C (IsLocalRing.residue (D.nd.O i) ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))) := by
    intro x g
    have e1 := (_root_.UpperTheory.GalS.g3' ((h32 i).2.2 r hr).2.2.1).2 x π g
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i))) (charpoly_of_decomp D i r ρ π hdec g)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    refine e1.trans (e2.trans ?_)
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  refine ⟨hc, h2, ?_⟩
  have hrb : IsRhoBar D.nd i (redRep D.nd i (ρ π)) := by
    refine ⟨isOpen_ker_redRep D i _ hcont, ?_⟩
    intro x w hw B σ hB' hσ
    rw [← (hr x).2.2 w hw B σ hB' hσ, ← Matrix.charpoly_map]
    exact (h2 x σ).symm
  have h3 := hB (D.nd.l i) D.R.r _ (hN9 i hHG _ hrb).1
  exact span_descent (D.naut.kFbar i) (fun g => mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π) g) h3
end Formalism.MainNotions.N
end
section
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
end

section



section
noncomputable section
namespace GlobalTheory.GoodDepthZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
theorem main_alt_alt : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D →
    (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) → Formalism.MainNotions.N.GlobalDatumDepthZeroCondition D := by
  intro D hT hA h41 _ a x hx Sig hSig k v
  obtain ⟨-, Sig', hSig', hgood⟩ := hx
  have hc : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b := hA.2.2
  have hL := charSum_of_tie D hT.1 hc
  obtain ⟨P, hP, hB⟩ := hSig
  obtain ⟨P', hP', hB'⟩ := id hSig'
  have hperm := ((h41 a).2.1 P P' (by rw [hP]; simp) (hP.trans hP'.symm)).1 _ _ hB hB'
  have e1 := GlobalTheory.RowTie.isoLoc_perm D.nd D.naut hperm (D.naut.plGw k v)
  rw [GlobalTheory.LocCongrRoad.isoLoc_twist _ _ hL, GlobalTheory.LocCongrRoad.isoLoc_twist _ _ hL] at e1
  have e2 := congrArg (fun b => D.naut.lpChar b (D.naut.locG D.naut.etaT (D.naut.plGw k v))) e1
  simp only [lpChar_eta_back D hT.1] at e2
  rw [GlobalTheory.LocCongrRoad.isoLoc_append_singleton, GlobalTheory.LocCongrRoad.isoLoc_append_singleton] at e2
  rw [hc _ _ _ _ e2]
  exact GlobalTheory.PointIrredCompare.fullLabels_of_good D.nd D.naut hSig' hgood k v
end GlobalTheory.GoodDepthZero
end
end
end
