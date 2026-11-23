module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle001
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsAddEquiv
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle035
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle002
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle002
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphIdealArithmeticVarietyImage
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnitRatioDivisorSupportEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Mathlib.FieldTheory.Extension
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPCProof
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

section

noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem one_comp_monHom {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    [IsMonHom f] : (1 : T ⟶ G) ≫ f = 1 := by
  simp [Hom.one_def]

theorem sub_abelianScheme : QuotientByFiniteFlatStatement → ZarhinStatement →
    HodgeTateDatumStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R →
    v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R →
    ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left), IsAbelianScheme A →
    L.IsLB → Out.RelAmple A L → ∀ (T : TorsRep A p) (N : Type) [AddCommGroup N] [Fintype N]
    [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ A)), IsTorsPts A p pt →
    ∀ K : AddSubgroup N, GenAF p (torsFun C T pt) K := by
  intro hQ hZ hD p _ C _ _ _ v R _ _ hint hp hc A _ L hA hL hamp T N _ _ _ pt hpt K
  haveI : IsCommMonObj A := hA.comm
  have hsub := GlobalTheory.T.torsion_points_finite_flat_subgroup p C v R hint hp A T N pt hpt K
  obtain ⟨A', _, L', q, hA', hL', hamp', hq, -, -, -, hker⟩ := hQ R A L hA hL hamp _ _ hsub
  obtain ⟨P, i, r, hi, hr, hir⟩ := hZ C v R hint A' L' hA' hL' hamp'
  haveI : IsCommMonObj P.A := P.isAb.comm
  haveI := hq
  haveI := hi
  haveI := hr
  have hj : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A),
      z ≫ (q ≫ i) = 1 ↔ ∃ φ : (T.A ⧸ vanIdeal T pt K) →ₐ[R] S,
        spMap φ ≫ (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) = z := by
    intro S _ _ z
    rw [← hker S z]
    constructor
    · intro h
      have h1 : (z ≫ q ≫ i) ≫ r = z ≫ q := by simp [hir]
      rw [← h1, h, one_comp_monHom]
    · intro h
      rw [← Category.assoc, h, one_comp_monHom]
  letI : Algebra ℤ_[p] R := (Av.zpLift p R hc).toAlgebra
  obtain ⟨⟨T'⟩, cp, -, -, pt', hpt', -⟩ := hD p C v R hint hp hc P
  have hjm : IsMonHom (q ≫ i) := inferInstance
  obtain ⟨jN, -, hjN, -, hpull⟩ := GlobalTheory.T.torsion_points_isogeny_hopf_order p C v R hint hp A P.A T N pt hpt T' _ pt' hpt'
    (q ≫ i) hjm
  obtain ⟨hK, hid⟩ := GlobalTheory.T.torsion_points_homomorphism_compatible p C v R hint hp A P.A T N pt hpt T' _ pt' hpt' (q ≫ i) hjm K
    hj jN hjN
  obtain ⟨⟨AA, hAA⟩, -⟩ := GlobalTheory.T.torsion_points_hopf_order p C v R hint hp A T N pt hpt
  obtain ⟨⟨AP, hAP⟩, -⟩ := GlobalTheory.T.torsion_points_hopf_order p C v R hint hp P.A T' _ pt' hpt'
  have hinv := GlobalTheory.T.hopf_order_pullback_along_hom p C v R hint hp N AA _ AP jN
    (by rw [hAA, hAP]; exact hpull) (by rw [hAA, hAP]; exact hid)
  rw [hAA, hAP, hK] at hinv
  exact GlobalTheory.T.generation_along_invariants p C R N _ _ _ jN K hinv (gp_polAV hD p C v R hint hp hc P T' _ pt' hpt').1

end GlobalTheory.CompanionTheory.Ar.GR
end
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullFlagPair

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K → ℤ) (f g : Fin N → MRing ι O), IsFlagPair ϖ x E E' w w' b b' f g → (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → IsFlagPair ϖ (joinCoord x z) EB E'B w w' (fun i => pullDeg (K' := K') (b i)) (fun i => pullDeg (K' := K') (b' i)) (fun i => rename (liftVar ι') (f i)) (fun i => rename (liftVar ι') (g i))) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁) (w₁ w₁' : Module.Basis (Fin N) Ω₁ V₁), (∀ i, w₁ i = bc (w i)) → (∀ i, w₁' i = bc (w' i)) → ∀ EB E'B : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB → IsPullBC O x z bc E' E'B → IsFlagPair ϖ (bcCoord x z) EB E'B w₁ w₁' (fun i => pullDeg (K' := K') (b i)) (fun i => pullDeg (K' := K') (b' i)) (fun i => rename (liftVar ι') (f i)) (fun i => rename (liftVar ι') (g i)) :=
  PositivityTheory.Xgn.t_pull_flagpair

end GlobalTheory.CompanionTheory.Ar.Num.PullFlagPair
end

section

namespace GlobalTheory.CompanionTheory.Segre

theorem numericalSegre_closed : GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.full

end GlobalTheory.CompanionTheory.Segre
end

section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.FieldNumbers

open GroundTheory.Heights₂.Heights.FieldNumbers GroundTheory.Heights₂.Heights.NumbersDVR

theorem projectionFormulaDegree :
    GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.Statement.{0} :=
  ProjectionFormulaDegree.of_divPushForward
    (DivPushForward.proof ContractRelDimLe.proof DivPushForwardLocalZero)

end GlobalTheory.CompanionTheory.FieldNumbers
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.CompanionTheory.Relay.complete_dvr_dominating_valuation : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (l : Type) [Field l] [Algebra (IsLocalRing.ResidueField V) l] [FiniteDimensional (IsLocalRing.ResidueField V) l], ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (f : V →+* R) (_ : IsLocalHom f) (s : l →+* IsLocalRing.ResidueField R), IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧ Function.Injective f ∧ s.comp (algebraMap _ l) = IsLocalRing.ResidueField.map f := by
  intro V _ _ _ l _ _ _
  obtain ⟨n, b⟩ : ∃ n, Nonempty (Module.Basis (Fin n) (IsLocalRing.ResidueField V) l) :=
    ⟨_, ⟨Module.finBasis (IsLocalRing.ResidueField V) l⟩⟩
  obtain ⟨b⟩ := b
  have hne : ∀ i, minpoly (IsLocalRing.ResidueField V) (b i) ≠ 0 := fun i =>
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral (b i))
  obtain ⟨R1, _, _, _, f1, _, hinj1, hsplit⟩ := PositivityTheory.HtPt.Pdvr.exists_splits _ V
    (∏ i, minpoly (IsLocalRing.ResidueField V) (b i)) rfl
  letI : Algebra (IsLocalRing.ResidueField V) (IsLocalRing.ResidueField R1) :=
    (IsLocalRing.ResidueField.map f1).toAlgebra
  have hS : IntermediateField.adjoin (IsLocalRing.ResidueField V) (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hspan : Submodule.span (IsLocalRing.ResidueField V) (Set.range b) ≤
        (IntermediateField.adjoin (IsLocalRing.ResidueField V) (Set.range b)).toSubalgebra.toSubmodule :=
      Submodule.span_le.mpr (IntermediateField.subset_adjoin _ _)
    exact hspan (b.span_eq ▸ Submodule.mem_top)
  have hK : ∀ s ∈ Set.range b, IsIntegral (IsLocalRing.ResidueField V) s ∧
      ((minpoly (IsLocalRing.ResidueField V) s).map
        (algebraMap (IsLocalRing.ResidueField V) (IsLocalRing.ResidueField R1))).Splits := by
    rintro s ⟨i, rfl⟩
    refine ⟨Algebra.IsIntegral.isIntegral (b i), ?_⟩
    refine Polynomial.Splits.of_dvd hsplit ?_ ?_
    · exact Polynomial.map_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => hne j)
    · exact Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  obtain ⟨φ⟩ := IntermediateField.nonempty_algHom_of_adjoin_splits hK hS
  obtain ⟨R, _, _, _, f2, _, hcomp, hinj2⟩ := PositivityTheory.HtPt.Pdvr.exists_complete R1
  refine ⟨R, inferInstance, inferInstance, inferInstance, f2.comp f1, inferInstance,
    (IsLocalRing.ResidueField.map f2).comp φ.toRingHom, hcomp, hinj2.comp hinj1, ?_⟩
  ext x
  rw [IsLocalRing.ResidueField.map_comp]
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem _root_.GlobalTheory.T.graph_ideal_arithmetic_variety_image : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (P : Ideal (MRing ι)) (d : ℕ) (g : (Σ k, ι₂ k) → MRing ι) (δ : K₂ → K → ℕ), IsArithVar P d → (∀ q, IsMultiHomog (g q) (δ q.1)) → (∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P) → IsArithVar (graphIdeal P g) d ∧ imageZ inlV (graphIdeal P g) = P := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.graphIdeal_isArithVar | exact GlobalTheory.CompanionTheory.Ar.Giv.graphIdeal_isArithVar | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.graphIdeal_isArithVar <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

abbrev redMap (ι : K → Type*) (p : ℕ) : MRing ι →+* MRingOver (ZMod p) ι :=
  MvPolynomial.map (Int.castRingHom (ZMod p))

theorem redMap_surjective (p : ℕ) : Function.Surjective (redMap ι p) := by
  exact MvPolynomial.map_surjective _ ZMod.intCast_surjective

theorem natCast_charOf_mem (W : Ideal (MRing ι)) : ((charOf W : ℕ) : MRing ι) ∈ W := by
  have hc : charOf W = (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs := rfl
  rw [hc]
  set g := Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) with hgdef
  have hg : C g ∈ W := Ideal.mem_comap.mp (Submodule.IsPrincipal.generator_mem _)
  have h : C (g.natAbs : ℤ) ∈ W := by
    rcases Int.natAbs_eq g with h | h
    · rw [← h]; exact hg
    · have e : (g.natAbs : ℤ) = -g := by linarith
      rw [e, map_neg]; exact W.neg_mem hg
  rw [← map_natCast (C : ℤ →+* MRing ι) g.natAbs]
  exact h

theorem ker_redMap_le {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W) :
    RingHom.ker (redMap ι p) ≤ W := by
  rw [redMap, MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
    Ideal.span_le, Set.singleton_subset_iff]
  simpa using hp

theorem comap_map_redMap {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W) :
    (W.map (redMap ι p)).comap (redMap ι p) = W := by
  rw [Ideal.comap_map_of_surjective _ (redMap_surjective p), ← RingHom.ker_eq_comap_bot,
    sup_eq_left.mpr (ker_redMap_le hp)]

theorem isMultiHomog_redMap {p : ℕ} {s : MRing ι} {a : K → ℕ} (h : IsMultiHomog s a) :
    IsMultiHomog (redMap ι p s) a := by
  intro m hm k
  refine h m ?_ k
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  intro h0
  apply hm
  simp [redMap, MvPolynomial.coeff_map, h0]

theorem isMultiHomogIdeal_map_redMap {p : ℕ} {W : Ideal (MRing ι)} (h : IsMultiHomogIdeal W) :
    IsMultiHomogIdeal (W.map (redMap ι p)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine ⟨redMap ι p '' S, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, isMultiHomog_redMap ha⟩

theorem isRelevant_map_redMap {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W)
    (h : IsRelevant W) : IsRelevant (W.map (redMap ι p)) := by
  intro k
  obtain ⟨i, hi⟩ := h k
  refine ⟨i, fun hx => hi ?_⟩
  rw [← comap_map_redMap hp, Ideal.mem_comap]
  simpa [redMap] using hx

def quotRedEquiv {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W) :
    (MRing ι ⧸ W) ≃+* (MRingOver (ZMod p) ι ⧸ W.map (redMap ι p)) :=
  (Ideal.quotEquivOfEq (by
      rw [← RingHom.comap_ker, Ideal.mk_ker, comap_map_redMap hp])).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (Ideal.Quotient.mk (W.map (redMap ι p))).comp (redMap ι p))
      (Ideal.Quotient.mk_surjective.comp (redMap_surjective p)))

theorem isProjVarF_map_redMap {p : ℕ} [Fact p.Prime] {W : Ideal (MRing ι)} {n : ℕ}
    (hp : ((p : ℕ) : MRing ι) ∈ W) (hW : IsMultiProjPrime W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (W.map (redMap ι p)) n := by
  obtain ⟨hWp, hWh, hWr⟩ := hW
  refine ⟨⟨?_, isMultiHomogIdeal_map_redMap hWh, isRelevant_map_redMap hp hWr⟩, ?_⟩
  · exact Ideal.map_isPrime_of_surjective (redMap_surjective p) (ker_redMap_le hp)
  · rw [← ringKrullDim_eq_of_ringEquiv (quotRedEquiv hp)]
    exact hdim

theorem fibreComp : ReciprocityTheory.ChartRestriction.G.AI.I2.FibreCompStatement := by
  intro K _ ι _ P n A s W hP hs hW hv
  obtain ⟨hK, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
  obtain ⟨a, -, hsa, hsP⟩ := hs
  obtain ⟨hWmin, hWrel⟩ := hW
  have hWp : W.IsPrime := hWmin.1.1
  have hWmh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hPh hsa hWmin
  have hmp : IsMultiProjPrime W := ⟨hWp, hWmh, hWrel⟩
  have hp := charOf_prime hWp hv
  have := hPp
  have h1 := dim_quot_minimal_add_one P W s hsP hWmin
  rw [hPdim] at h1
  have hdim : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    withBot_eq_of_add_one (by rw [h1, show n + 1 + Fintype.card K = n + Fintype.card K + 1 by omega])
  refine ⟨hp, natCast_charOf_mem W, hmp, ?_⟩
  haveI : Fact (charOf W).Prime := ⟨hp⟩
  exact isProjVarF_map_redMap (natCast_charOf_mem W) hmp hdim

end GlobalTheory.CompanionTheory.Ar.Pub
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

theorem _root_.GlobalTheory.T.unit_ratio_divisor_support_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (d : K → ℕ) (f g : MRing ι) (θ : Ω), IsArithVar (mCoordIdeal y) (D + 1) → IsMultiHomog f d → IsMultiHomog g d → aeval y g ≠ 0 → θ ≠ 0 → IsIntegral ℤ θ → IsIntegral ℤ θ⁻¹ → aeval y f = θ * aeval y g → divSupp (mCoordIdeal y) f = divSupp (mCoordIdeal y) g ∧ ∀ W ∈ divSupp (mCoordIdeal y) g, multAt ((mCoordIdeal y) ⊔ Ideal.span {f}) W = multAt ((mCoordIdeal y) ⊔ Ideal.span {g}) W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.divCycle_eq_of_unit_ratio | exact GlobalTheory.CompanionTheory.Ar.Giv.divCycle_eq_of_unit_ratio | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.divCycle_eq_of_unit_ratio <;> assumption)
end
