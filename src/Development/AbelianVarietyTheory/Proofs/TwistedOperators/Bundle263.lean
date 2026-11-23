module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusElementCharpolyRegularCentralizer
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle246
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle256
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle249
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupCongruentOfTwoLatticeMoves
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.torusElement_charpoly_regular_centralizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : Type) [CommRing k] [Algebra F k], ∀ (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ), (GlobalTheory.AdelicU.matHom k σ J (gam h)).1.charpoly = P.1.map (inclR k) ∧ IsRegSS (GlobalTheory.AdelicU.matHom k σ J (gam h)).1 ∧ Function.Injective (torEmb h) ∧ cent (gam h) = (torEmb h).range := by
  first | exact @GlobalTheory.TrEll.gam_charpoly_regular_cent | exact GlobalTheory.TrEll.gam_charpoly_regular_cent | (intros; apply GlobalTheory.TrEll.gam_charpoly_regular_cent <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ PP ∈ Z, compFin D.host.F D.host.E ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (e + cA D e) = 1 := by
  first | exact @GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one | exact GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one | (intros; apply GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localHeckeChar_det_doubleCoset_splitPlace : ∀ (D : D7) (T : HSp D) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), UnrAt χ w → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), ((locChar χ w (Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂)))) : ℂˣ) : ℂ) = ((val χ w : ℂˣ) : ℂ) ^ (∑ i, d i) := by
  first | exact @GlobalTheory.DetVal.locChar_det_doubleCoset | exact GlobalTheory.DetVal.locChar_det_doubleCoset | (intros; apply GlobalTheory.DetVal.locChar_det_doubleCoset <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

namespace GlobalTheory.HalfUnit

theorem cc_star (D : D7) (x : D.host.E) : cc (star x) = x := by
  first
  | exact star_star x
  | rfl
  | simp [cc]

theorem mem_conjI_of (D : D7) (P : Ideal (𝓞 D.host.E)) (s : 𝓞 D.host.E)
    (h : Formalism.L2.Col.cO D.host.E s ∈ P) : s ∈ conjI P :=
  Ideal.subset_span ⟨_, h, (cc_star D (s : D.host.E)).symm⟩

theorem exists_int_inv_half : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∉ conjI PP.asIdeal) →
    ∃ t : AE D, finPart D t ∈ intAE D ∧ t * incA D (s : D.host.E) * cA D e = cA D e := by
  intro D P e he s hs
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  by_cases hP : P = ∅
  · subst hP
    refine ⟨0, by rw [map_zero]; exact zero_mem _, ?_⟩
    simp
  obtain ⟨tableDegreeThreeBase, hPP0⟩ := Finset.nonempty_iff_ne_empty.2 hP
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs tableDegreeThreeBase hPP0 (zero_mem _)
  have hsE : (s : D.host.E) ≠ 0 := by
    intro h; apply hs0; exact RingOfIntegers.ext (by simpa using h)
  refine ⟨cA D (∑ PP ∈ P, es PP) * incA D ((s : D.host.E)⁻¹), ?_, ?_⟩

  · rw [map_sum, Finset.sum_mul, map_sum]
    refine sum_mem fun PP hPP => ?_
    have hc0 : Formalism.L2.Col.cO D.host.E s ≠ 0 := by
      intro h0; apply hs0
      rw [← Formalism.L2.Col.cO_cO s, h0, map_zero]
    have hnot : Formalism.L2.Col.cO D.host.E s ∉ PP.asIdeal := fun hm => hs PP hPP (mem_conjI_of D _ s hm)
    have hint := not_not.1 (mt ((hes PP hPP).2 _ hc0).2 hnot)
    have := GlobalTheory.MovedIdem.finPart_conj_mem hint
    have hst : star (((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E)⁻¹) = (s : D.host.E)⁻¹ := by
      rw [star_inv₀]
      congr 1
      exact star_star (s : D.host.E)
    rwa [hst] at this
  · have h1 : incA D ((s : D.host.E)⁻¹) * incA D (s : D.host.E) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hsE, map_one]
    calc cA D (∑ PP ∈ P, es PP) * incA D ((s : D.host.E)⁻¹) * incA D (s : D.host.E) * cA D (∑ PP ∈ P, es PP)
        = cA D ((∑ PP ∈ P, es PP) * (∑ PP ∈ P, es PP)) := by
          rw [mul_assoc (cA D _), h1, mul_one, map_mul]
      _ = cA D (∑ PP ∈ P, es PP) := by rw [hee]

end GlobalTheory.HalfUnit
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

namespace GlobalTheory

theorem primeProd_conjI_eq_map {E : Type} [Field E] [NumberField E] [IsCMField E] (I : Ideal (𝓞 E)) :
    conjI I = I.map (RingOfIntegers.mapRingHom ((IsCMField.complexConj E).toRingEquiv.toRingHom)) := by
  unfold conjI
  show _ = Ideal.span _
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, ?_⟩
    apply RingOfIntegers.ext
    rw [h]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩

theorem primeProd_squarefree_le_conj : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), Squarefree (∏ PP ∈ P, PP.asIdeal) ∧ (∀ PP' : Formalism.L2.DIV.Pl D.host.E, (∏ PP ∈ P, PP.asIdeal) ≤ PP'.asIdeal ↔ PP' ∈ P) ∧ conjI (∏ PP ∈ P, PP.asIdeal) = ∏ PP ∈ P, conjI PP.asIdeal := by
  intro D P
  refine ⟨?_, ?_, ?_⟩
  · have hprod : (∏ PP ∈ P, PP.asIdeal) = (P.val.map (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal)).prod := by
      rw [Finset.prod_eq_multiset_prod]
    have hprime : ∀ p ∈ P.val.map (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal), Prime p := by
      intro p hp
      obtain ⟨PP, -, rfl⟩ := Multiset.mem_map.1 hp
      exact PP.prime
    have hne : (∏ PP ∈ P, PP.asIdeal) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro PP _
      exact PP.ne_bot
    rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hne, hprod,
      UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hprime]
    exact (Multiset.nodup_map_iff_of_injective (fun a b h => HeightOneSpectrum.ext h)).2 P.nodup
  · intro PP'
    constructor
    · intro hle
      obtain ⟨PP, hPP, hle'⟩ := (Ideal.IsPrime.prod_le PP'.isPrime).1 hle
      have : PP.asIdeal = PP'.asIdeal := PP.isMaximal.eq_of_le PP'.isPrime.ne_top hle'
      have h2 : PP = PP' := HeightOneSpectrum.ext this
      exact h2 ▸ hPP
    · intro h
      exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ h)
  · simp only [primeProd_conjI_eq_map]
    exact map_prod (Ideal.mapHom _) _ _

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_conjugatePlace_cmField : ∀ (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E), ∃ PP' : Formalism.L2.DIV.Pl D.host.E, PP'.asIdeal = conjI PP.asIdeal ∧ Formalism.IndefR.Lev.IsConjPl PP' PP := by
  first | exact @GlobalTheory.ConjPlace.exists_conj_place | exact GlobalTheory.ConjPlace.exists_conj_place | (intros; apply GlobalTheory.ConjPlace.exists_conj_place <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

noncomputable section

namespace GlobalTheory.HatScalar

theorem smul_mem_tens_of {E : Type} [Field E] [NumberField E] {n r : ℕ} {Λ : Lt E n} {L L' : Lt E r} (c : E)
    (h : ∀ u ∈ L, c • u ∈ L') {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ L) :
    c • y ∈ tens Λ L' := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨v, hv, u, hu, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨v, hv, c • u, h u hu, ?_⟩
    rw [Matrix.vecMulVec_smul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem incA_smul_mem_hatA (D : D7) (S T : HSp D) (Λ : Lt D.host.E S.rank) (L1 L2 : Lt D.host.E T.rank)
    (c : D.host.E) (h : ∀ v ∈ L1, c • v ∈ L2) :
    ∀ u ∈ hatA S T (tens Λ L1), incA D c • u ∈ hatA S T (tens Λ L2) := by
  intro u hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, c • y, smul_mem_tens_of c h hy, ?_⟩
    ext a k
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    show (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] AF D.host.F ⊗[D.host.F] D.host.E) c *
      _ = _
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.HatScalar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.LevMove.Rat

section Core

open Formalism.MainNotions.StandardLattice (latHat intAf)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_of_loc (L : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (h𝔪 : 𝔪 ≠ ⊥)
    {x : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hx : x ∈ latHat F E (L : Set (Fin n → E)))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal →
      ∀ α : FiniteAdeleRing (𝓞 F) F, evalV F v α = 1 → (∀ w, w ≠ v → evalV F w α = 0) →
        (α ⊗ₜ[F] (1 : E)) • x ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E))) :
    x ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  set N := Ideal.absNorm 𝔪 with hNdef
  have hN0 : N ≠ 0 := fun h => h𝔪 (Ideal.absNorm_eq_zero_iff.1 h)
  have hNE : ((N : 𝓞 E)) ∈ 𝔪 := Ideal.absNorm_mem 𝔪
  set c₁ : 𝓞 F := (N : 𝓞 F) with hc₁
  have hc₁0 : c₁ ≠ 0 := Nat.cast_ne_zero.2 hN0
  have hc₁m : algebraMap (𝓞 F) (𝓞 E) c₁ ∈ 𝔪 := by rw [hc₁, map_natCast]; exact hNE
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {c₁}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  set P := hfin.toFinset with hP
  have hmemP : ∀ v, v ∈ P ↔ c₁ ∈ v.asIdeal := fun v => by
    rw [hP, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  choose ind hind1 hind0 using (exists_ind (F := F))
  set e₁ : FiniteAdeleRing (𝓞 F) F := ∑ v ∈ P, ind v with he₁
  have hev : ∀ w, evalV F w e₁ = if w ∈ P then 1 else 0 := fun w => by

    rw [he₁, map_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single w (fun b _ hb => hind0 b w (Ne.symm hb)) (fun h => absurd hw h), hind1]
    · exact Finset.sum_eq_zero fun b hb => hind0 b w (fun h => hw (h ▸ hb))
  have hsplit : x = ((1 - e₁) ⊗ₜ[F] (1 : E)) • x + ∑ v ∈ P, (ind v ⊗ₜ[F] (1 : E)) • x := by
    rw [← Finset.sum_smul, ← TensorProduct.sum_tmul, ← he₁, ← add_smul, ← TensorProduct.add_tmul, sub_add_cancel,
      Algebra.TensorProduct.one_def.symm, one_smul]
  rw [hsplit]
  refine add_mem ?_ (sum_mem fun v hv => ?_)
  · refine vanish_smul_mem L 𝔪 hc₁0 hc₁m (fun w => ?_) (fun w hw => ?_) hx
    · rw [map_sub, map_one, hev]; split_ifs
      · rw [sub_self]; exact zero_mem _
      · rw [sub_zero]; exact one_mem _
    · rw [map_sub, map_one, hev, if_pos ((hmemP w).2 hw), sub_self]
  · by_cases hI : 𝔪.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal
    · exact hloc v hI (ind v) (hind1 v) (hind0 v)
    · obtain ⟨c, hc, hcv⟩ := SetLike.not_le_iff_exists.1 hI
      have hc0 : c ≠ 0 := fun h => hcv (h ▸ zero_mem _)
      refine vanish_smul_mem L 𝔪 hc0 hc (ind_int (hind1 v) (hind0 v)) (fun w hw => hind0 v w ?_) hx
      rintro rfl; exact hcv hw

end Core

variable {D : D7}

theorem mov_comp {k : ℕ} {m m₂ : Matrix (Fin k) (Fin k) (AfE D)} {L L' L'' : Lt D.host.E k}
    (h : IsMov m L L') (h₂ : IsMov m₂ L' L'') : IsMov (m₂ * m) L L'' := by
  intro u
  rw [h₂ u]
  constructor
  · rintro ⟨u₁, hu₁, rfl⟩
    obtain ⟨u₀, hu₀, rfl⟩ := (h u₁).1 hu₁
    exact ⟨u₀, hu₀, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨u₀, hu₀, rfl⟩
    exact ⟨m *ᵥ u₀, (h _).2 ⟨u₀, hu₀, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩

theorem smul_sandwich {R : Type} [CommRing R] {k : ℕ} (P : R) (A A' G B : Matrix (Fin k) (Fin k) R)
    (hA : P • A = P • 1) (hB : P • B = P • 1) (e : A * A' = 1) : P • (A' * G * B) = P • G := by
  have h' : P • A' = P • 1 := by
    calc P • A' = (P • 1) * A' := by rw [Matrix.smul_mul, one_mul]
      _ = (P • A) * A' := by rw [hA]
      _ = P • 1 := by rw [Matrix.smul_mul, e]
  rw [← Matrix.smul_mul, ← Matrix.smul_mul, h', Matrix.smul_mul, one_mul, Matrix.smul_mul, ← Matrix.mul_smul, hB,
    Matrix.mul_smul, mul_one]

theorem map_mulVec_toAf {k : ℕ} (M : Matrix (Fin k) (Fin k) D.host.E) (u : Fin k → D.host.E) :
    (M.map fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) *ᵥ toAf u = toAf (M *ᵥ u) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, toAf, Matrix.map_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    TensorProduct.tmul_sum]

theorem toAf_smul {k : ℕ} (c : 𝓞 D.host.E) (u : Fin k → D.host.E) :
    toAf (c • u) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E) : AfE D) • toAf u := by
  funext i
  simp only [toAf, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rfl

theorem smul_step {R : Type} [CommRing R] {k : ℕ} (P : R) (K G : Matrix (Fin k) (Fin k) R) (u w : Fin k → R)
    (h : P • K = P • G) : P • (K *ᵥ u - w) = P • (G *ᵥ u - w) := by
  rw [smul_sub, smul_sub, ← Matrix.smul_mulVec, h, Matrix.smul_mulVec]

theorem toAf_sub {k : ℕ} (u w : Fin k → D.host.E) : (toAf (u - w) : Fin k → AfE D) = toAf u - toAf w := by
  funext i
  simp only [toAf, Pi.sub_apply, TensorProduct.tmul_sub]

theorem toAf_mem {k : ℕ} {L : Lt D.host.E k} {u : Fin k → D.host.E} (hu : u ∈ L) : toAf u ∈ hatV L :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, u, hu, rfl⟩

end GlobalTheory.Ker.LevMove.Rat



theorem GlobalTheory.Ker.LevMove.levK_of_rat_moves : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (γ : GL (Fin T.rank) D.host.E) (κ : Lv.J), Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) κ → ∀ (a f g₁ g₂ : GA D T) (L : Lt D.host.E T.rank), a ∈ GinfC T → f ∈ GfC T → IsRatOf T γ (a * f) → g₁ ∈ GfC T → g₂ ∈ GfC T → TrivAt T (C.under Lv) g₁ → TrivAt T (C.under Lv) g₂ → L.FG → Submodule.span D.host.E (L : Set (Fin T.rank → D.host.E)) = ⊤ → (mapL γ L).FG → IsMov (fmt T g₁) C.X.Λ L → IsMov (fmt T g₂) C.X.Λ (mapL γ L) → C.LevK Lv (g₂⁻¹ * f * g₁) κ := by
  intro D S T C Lv γ κ hred a f g₁ g₂ L ha hf hrat h1 h2 t1 t2 hLfg hLs hMfg m1 m2
  set G : Matrix (Fin T.rank) (Fin T.rank) (AfE D) :=
    (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x with hGdef
  have hfa : fmt T a = 1 := (((GlobalTheory.Ker.Grp.rational_points_and_parts D S T C).2.2.2 T).2.2.2.1 a ha).1
  have hff : fmt T f = G := by
    have e : fmt T (a * f) = G := by
      rw [fmt, hrat, Matrix.map_map]; rfl
    rw [← e, GlobalTheory.Ker.LevMove.fmt_mul', hfa, one_mul]
  have hfull : C.X.Λ.FG ∧ Submodule.span D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ :=
    ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have e1 : fmt T g₁ * fmt T g₁⁻¹ = 1 := by
    rw [← GlobalTheory.Ker.LevMove.fmt_mul', mul_inv_cancel, GlobalTheory.Ker.LevMove.fmt_one']
  have e2 : fmt T g₂ * fmt T g₂⁻¹ = 1 := by
    rw [← GlobalTheory.Ker.LevMove.fmt_mul', mul_inv_cancel, GlobalTheory.Ker.LevMove.fmt_one']
  obtain ⟨hto, -, -, lawsΛ⟩ := GlobalTheory.Ker.isMov_laws D T.rank C.X.Λ hfull
  obtain ⟨-, -, hG, -⟩ := GlobalTheory.Ker.isMov_laws D T.rank L ⟨hLfg, hLs⟩
  obtain ⟨-, hinv2, -, -, -⟩ := (lawsΛ _ _ e2).2 (mapL γ L) hMfg m2
  have hk : IsMov (fmt T (g₂⁻¹ * f * g₁)) C.X.Λ C.X.Λ := by
    rw [GlobalTheory.Ker.LevMove.fmt_mul', GlobalTheory.Ker.LevMove.fmt_mul', hff]
    exact GlobalTheory.Ker.LevMove.Rat.mov_comp m1 (GlobalTheory.Ker.LevMove.Rat.mov_comp (hG γ) hinv2)
  obtain ⟨κ', hκ', hcong⟩ := hred
  refine ⟨mul_mem (mul_mem (inv_mem h2) hf) h1, hk, κ', hκ', fun i => ?_⟩
  have hb : toAf (Lv.β i) ∈ hatV C.X.Λ := GlobalTheory.Ker.LevMove.Rat.toAf_mem (Lv.β_mem i)
  have hw : toAf (∑ j, κ' j i • Lv.β j) ∈ hatV C.X.Λ :=
    GlobalTheory.Ker.LevMove.Rat.toAf_mem (sum_mem fun j _ => Submodule.smul_mem _ _ (Lv.β_mem j))
  refine GlobalTheory.Ker.LevMove.Rat.mem_of_loc (F := D.host.F) C.X.Λ Lv.𝔪 Lv.ne_bot
    (sub_mem ((hk _).2 ⟨_, hb, rfl⟩) hw) ?_
  intro v hv α a1 a0
  have P1 := GlobalTheory.Ker.LevMove.smul_fmt_sub_one t1 hv a1 a0
  have P2 := GlobalTheory.Ker.LevMove.smul_fmt_sub_one t2 hv a1 a0
  set P : AfE D := α ⊗ₜ[D.host.F] (1 : D.host.E) with hPdef
  have hPint : α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := GlobalTheory.Ker.LevMove.ind_int a1 a0
  have q1 : P • fmt T g₁ = P • 1 := by rw [smul_sub] at P1; exact sub_eq_zero.1 P1
  have q2 : P • fmt T g₂ = P • 1 := by rw [smul_sub] at P2; exact sub_eq_zero.1 P2
  have qk : P • fmt T (g₂⁻¹ * f * g₁) = P • G := by
    rw [GlobalTheory.Ker.LevMove.fmt_mul', GlobalTheory.Ker.LevMove.fmt_mul', hff]
    exact GlobalTheory.Ker.LevMove.Rat.smul_sandwich P _ _ _ _ q2 q1 e2
  obtain ⟨d, hd⟩ : ∃ d : Fin T.rank → D.host.E, d = (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i -
    ∑ j, κ' j i • Lv.β j := ⟨_, rfl⟩
  have hx : P • (fmt T (g₂⁻¹ * f * g₁) *ᵥ toAf (Lv.β i) - toAf (∑ j, κ' j i • Lv.β j)) = P • toAf d := by
    rw [GlobalTheory.Ker.LevMove.Rat.smul_step P _ _ _ _ qk, GlobalTheory.Ker.LevMove.Rat.map_mulVec_toAf,
      ← GlobalTheory.Ker.LevMove.Rat.toAf_sub, hd]
  have hPd : P • toAf d ∈ hatV C.X.Λ := by
    rw [← hx]
    exact GlobalTheory.Ker.LevMove.int_smul_mem C.X.Λ hPint (sub_mem ((hk _).2 ⟨_, hb, rfl⟩) hw)
  change P • _ ∈ hatV (Lv.𝔪 • C.X.Λ)
  rw [hx]
  obtain ⟨s, hs, hsd⟩ := hcong i
  rw [← hd] at hsd
  obtain ⟨u, hu, m, hm, hum⟩ := Ideal.isCoprime_iff_exists.1 hs
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have hsplit : P • toAf d = P • toAf ((t * s) • d) +
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((m : 𝓞 D.host.E) : D.host.E) : AfE D) • (P • toAf d) := by
    have hum' : ((t * s : 𝓞 D.host.E) : D.host.E) + ((m : 𝓞 D.host.E) : D.host.E) = 1 := by
      have := congrArg (algebraMap (𝓞 D.host.E) D.host.E) hum
      simpa using this
    rw [GlobalTheory.Ker.LevMove.Rat.toAf_smul, smul_comm P, ← add_smul, ← TensorProduct.tmul_add, hum',
      Algebra.TensorProduct.one_def.symm, one_smul]
  rw [hsplit]
  refine add_mem ?_ (GlobalTheory.Ker.LevMove.ideal_smul_mem C.X.Λ Lv.𝔪 hm hPd)
  refine GlobalTheory.Ker.LevMove.int_smul_mem _ hPint (GlobalTheory.Ker.LevMove.Rat.toAf_mem ?_)
  rw [mul_smul]
  exact Submodule.smul_mem _ t hsd
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.domain_frame_eq_real_translate_mul_borel : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ x ∈ C.X.dom, ∃ a ∈ GinfC T, ∃ b ∈ Bor C.X.Ψ T.rank, x = rmul (C.xB (C.mvB a B)) b := by
  first | exact @GlobalTheory.FrameDecomp.frame_decomp | exact GlobalTheory.FrameDecomp.frame_decomp | (intros; apply GlobalTheory.FrameDecomp.frame_decomp <;> assumption)
end
