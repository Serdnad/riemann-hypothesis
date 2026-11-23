module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKtypeKilledByCompactRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandInvariantsActByScalarsHighestWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKtypeHolomorphicKilledByLoweringRoots
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem semiPosReg_of_eqOn_charts {E E' : LB X} (χ : Weight p σ E) {χ' : Weight p σ E'}
    (h : χ'.SemiPosReg D) (j : E.ι → E'.ι)
    (hj : ∀ i y, y ∈ ptsIn p σ (E.U i) → y ∈ ptsIn p σ (E'.U (j i)))
    (he : ∀ i y, y ∈ ptsIn p σ (E.U i) → χ.φ i y = χ'.φ (j i) y) : χ.SemiPosReg D := fun i c y hy ξ => by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (E.U i))
  have e : (fun v => (χ.φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] fun v => (χ'.φ (j i) (c.e.symm v) : ℂ) :=
    eventually_of_mem (ho.mem_nhds (mem_over c.e hy.1 hy.2)) fun v hv => by
      simp only [he i _ hv.2]
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e]
  exact h (j i) c y ⟨hy.1, hj i y hy.2⟩ ξ

theorem exists_generating_secs_tens_lbPow {H L : LB X} (hH : H.IsLB) (hL : L.IsLB) {N : ℕ}
    {s : Fin (N + 1) → H.Sec} (hs : AbLaw.VeryAmpleBy p H s) :
    ∃ (m n : ℕ) (u : Fin n → (CechPic.tens L (lbPow H m)).Sec), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  obtain ⟨t₀, ht⟩ := GlobalTheory.TwistGen.twist_generated k X p H _ s hH hs L hL
  obtain ⟨m, hm⟩ : ∃ m : ℕ, t₀ ≤ m := ⟨t₀.toNat, by omega⟩
  obtain ⟨n, u, hu⟩ := ht m hm
  have hP : (lbPow H m).IsLB := DVR.linComb_isLB H hH _ _
  have hT : (CechPic.tens L (lbPow H m)).IsLB := isLB_tens hL hP
  have e : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) =
      cls L hL - cls (AbLaw.pw H (-(m : ℤ))) (AbLaw.isLB_pw hH _) :=
    cls_div hL (AbLaw.isLB_pw hH _) (AbLaw.isLB_tw hL hH _)
  have e' : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) = cls _ hT := by
    rw [e, GlobalTheory.AmpleStabFinite.cls_pw hH, cls_tens hL hP, cls_lbPow hH, neg_zsmul, natCast_zsmul, sub_neg_eq_add]
  obtain ⟨v, hv⟩ := exists_generating_secs_of_cls_eq _ _ _ _ hT e' _ u hu
  exact ⟨m, _, v, hv⟩

theorem exists_semiPosReg_tens : ∀ (F : Type) [Field F] (X : Scheme.{0}) (p : X ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → ∀ (D : ℕ) (A : MLine p σ), ∃ Q : MLine p σ, Q.φ.SemiPosReg D ∧ (A.tens Q).φ.SemiPosReg D := by
  rintro F _ X p σ ⟨N, ι, hι, hp⟩ D A
  let O : MLine (PSpace.str F N) σ := MLine.ofHerm (ProjSpace.hermitianTwistingSheaf F N) σ
  have hO : O.φ.SemiPosReg N := Weight.semiPosReg_fsBasis (ProjSpace.O1_isLB F N) _
    (ProjSpace.iSup_nonzeroLocus_coord F N) 1 (by simp)
  have hsm : SmoothOfRelativeDimension N (PSpace.str F N) := inferInstance
  let H : MLine p σ := O.pull ι hp
  have hH : H.φ.SemiPosReg D := GlobalTheory.Weight.semiPosReg_pull F _ _ _ _ σ ι hp N D hsm _ _ O.cInf hO
  have hpow (m : ℕ) : (H.φ.pow m).SemiPosReg D :=
    Weight.SemiPosReg.of_mul _ H.cInf hH ((m : ℤ) : ℝ) (by positivity) (fun j => j PUnit.unit)
      (fun _ _ h => mem_pow_iff.1 h) fun j y => H.φ.zpow_φ (m : ℤ) j y
  have hva : ∃ s : Fin (N + 1) → H.B.Sec, AbLaw.VeryAmpleBy p H.B s := by
    dsimp [H, O, MLine.pull, MLine.ofHerm, ProjSpace.hermitianTwistingSheaf, HermLB.fs]
    subst hp
    exact ⟨_, ProjSpace.veryAmpleBy_secPull_coord ι⟩
  obtain ⟨s, hs⟩ := hva
  obtain ⟨m, hgen⟩ := exists_generating_secs_tens_lbPow H.φ.isLB A.φ.isLB hs
  obtain ⟨φ₁, hφ₁, hφ₁'⟩ := GlobalTheory.weight_cInf_semiPos_of_generated F X p σ _ (A.φ.tens (H.φ.pow m)).isLB hgen
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.smooth_weights_differ_by_smooth_function F X p σ _ φ₁ (A.φ.tens (H.φ.pow m)) hφ₁ (A.cInf.tens (H.cInf.zpow m))
  obtain ⟨v, hv, hv'⟩ := GlobalTheory.ClosedExt.exists_extension F _ X (PSpace.str F N) p σ ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩ ι hp u hu
  obtain ⟨m', hm'⟩ := GlobalTheory.T.exists_semiPos_fubiniStudy_power_add_smooth_fn F σ N v hv
  have hwc : ((O.φ.pow m').addFn v).IsCInf := (O.cInf.zpow m').addFn hv
  have hw : (((O.φ.pow m').addFn v).pull ι hp).SemiPosReg D :=
    GlobalTheory.Weight.semiPosReg_pull F _ _ _ _ σ ι hp N D hsm _ _ hwc (hm' m' le_rfl)
  refine ⟨⟨_, (H.φ.pow m).tens (H.φ.pow m'), (H.cInf.zpow m).tens (H.cInf.zpow m')⟩,
    Weight.SemiPosReg.tens (H.cInf.zpow m) (H.cInf.zpow m') (hpow m) (hpow m'), ?_⟩
  refine semiPosReg_of_eqOn_charts (A.φ.tens ((H.φ.pow m).tens (H.φ.pow m')))
    (Weight.SemiPosReg.tens hφ₁ (hwc.pull ι hp) (hφ₁' D) hw)
    (fun i => ((i.1, i.2.1), i.2.2)) (fun i y hy => ?_) fun i y hy => ?_
  · obtain ⟨h₁, h₂⟩ := mem_ptsIn_inf.1 hy
    obtain ⟨h₂, h₃⟩ := mem_ptsIn_inf.1 h₂
    refine mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨h₁, h₂⟩, ?_⟩
    have h₄ := mem_pow_iff.1 h₃
    exact mem_ptsIn.2 (Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun b => Set.mem_iInter.1 (mem_ptsIn.1 h₄) b)
  · obtain ⟨h₁, h₂⟩ := mem_ptsIn_inf.1 hy
    obtain ⟨h₂, h₃⟩ := mem_ptsIn_inf.1 h₂
    have e₁ : A.φ.φ i.1 y + (H.φ.pow m).φ i.2.1 y = φ₁.φ (i.1, i.2.1) y + u y :=
      hu' (i.1, i.2.1) y (mem_ptsIn_inf.2 ⟨h₁, h₂⟩)
    have e₂ : (H.φ.pow m').φ i.2.2 y = (O.φ.pow m').φ (i.2.2 PUnit.unit) (ptMap ι hp σ y) :=
      (H.φ.zpow_φ m' i.2.2 y).trans ((congrArg (_ * ·) (O.φ.pull_φ ι hp (i.2.2 PUnit.unit) y)).trans
        (O.φ.zpow_φ m' (i.2.2 PUnit.unit) _).symm)
    have e₃ : (((O.φ.pow m').addFn v).pull ι hp).φ i.2.2 y =
        (O.φ.pow m').φ (i.2.2 PUnit.unit) (ptMap ι hp σ y) + v (ptMap ι hp σ y) :=
      ((O.φ.pow m').addFn v).pull_φ ι hp i.2.2 y
    change A.φ.φ i.1 y + ((H.φ.pow m).φ i.2.1 y + (H.φ.pow m').φ i.2.2 y) =
      φ₁.φ (i.1, i.2.1) y + (((O.φ.pow m').addFn v).pull ι hp).φ i.2.2 y
    rw [e₃, hv', e₂, ← add_assoc, e₁]
    ring

end GlobalTheory.Mix
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (D : ℕ) (A : FinHolAtlas D (CxPts p σ)), IsAlgAtlas A → ∀ (L : Fin D → MLine p σ) (g : CxPts p σ → ℝ), Measurable g → (Intg L g ↔ MIntegrable A (fun i => (L i).φ.locPot) g) ∧ (Intg L g → Mix.int L g = mInt A (fun i => (L i).φ.locPot) g) := by
  first | exact @GlobalTheory.Mix.int_eq_mInt | exact GlobalTheory.Mix.int_eq_mInt | (intros; apply GlobalTheory.Mix.int_eq_mInt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.firstJetTerms_gauge_unit_mul_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C] (N : NumD C) (ν : NumOf D C N) (gm₀ : GtPt D (epsR R)) (gm : GtPt D (TE R C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF R C))) gm₀ gm → ∀ (k : ℕ) (J : (Sp (DualNumber R) ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → ∃ T : (DualNumber C)ˣ, GlobalTheory.MBLow.TanExp.rigValD D (J gm₀.b.left) ≠ 0 ∧ (T : DualNumber C).fst * toF R C (GlobalTheory.MBLow.TanExp.rigValD D (J gm₀.b.left)) ^ k = ν.rg ^ k ∧ ∀ (s : Fam D C k) (n : ℕ) (c : Fin n → C) (f : Fin n → ∀ α : D.X, D.SecB k α), (∀ α, GeneratorPullback.SecLin D.P.L (DegPre.famφ D C α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D C).left (fun i => scal (fst (TF (R := R) C) D.P.A).left (c i))) → ∀ α, jc ν s gm α = (T : DualNumber C) * ∑ i, TrivSqZeroExt.inl (c i) * dualMap (toF R C) (GlobalTheory.MBLow.TanExp.termV J gm₀ (f i (ν.eX α))) := by
  first | exact @GlobalTheory.MBLow.TanGauge.jc_eq_unit_mul | exact GlobalTheory.MBLow.TanGauge.jc_eq_unit_mul | (intros; apply GlobalTheory.MBLow.TanGauge.jc_eq_unit_mul <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_open_complexPoints_covering_generic_degree : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ (∀ y ∈ ptsIn p σ U, (ptMap π hπ σ ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ z : CxPts q σ, ptMap π hπ σ z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, ptMap π hπ σ z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, ptMap π hπ σ w ∈ c.e.source ∧ c'.e w = c.e (ptMap π hπ σ w)) := by
  first | exact @GlobalTheory.CoverDegProj.exists_open_covering_charts | exact GlobalTheory.CoverDegProj.exists_open_covering_charts | (intros; apply GlobalTheory.CoverDegProj.exists_open_covering_charts <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.reducedClosureOfPoint_properties : ∀ (X : Scheme.{0}) (z : X), ∃ _ : IsIntegral (clos z), closι z (genericPoint (clos z)) = z ∧ topologicalKrullDim (clos z) = topologicalKrullDim (closure ({z} : Set X)) ∧ ∀ (Y : Scheme.{0}) [IsIntegral Y] (π : Y ⟶ X), π (genericPoint Y) = z → ∃ g : Y ⟶ clos z, g ≫ closι z = π ∧ g (genericPoint Y) = genericPoint (clos z) ∧ g.residueDegree (genericPoint Y) = π.residueDegree (genericPoint Y) ∧ (IsClosedImmersion π → IsIso g) := by
  first | exact @GlobalTheory.ClosFacts.clos_facts | exact GlobalTheory.ClosFacts.clos_facts | (intros; apply GlobalTheory.ClosFacts.clos_facts <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.lieBasis_torusExtension_of_lifts_and_duals : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (H : Over (Sp R)) [GrpObj H] [IsCommMonObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ → ∀ (r : ℕ) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (bX : Module.Basis (Fin r) ℤ D.X) (x : Fin D.P.g ⊕ Fin r → (epsR R ⟶ H)), IsLieBasis vB → (∀ j, GtTan (Φ _ (x j))) → (∀ i, (Φ _ (x (Sum.inl i))).b = vB i) → (∀ l, (Φ _ (x (Sum.inr l))).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (x (Sum.inr l))).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr ((bX.repr χ l : ℤ) : R)))) → ∀ (n : ℕ) (σ : Fin n ≃ Fin D.P.g ⊕ Fin r), IsLieBasis (fun k => x (σ k)) := by
  first | exact @GlobalTheory.GtBasis.main | exact GlobalTheory.GtBasis.main | (intros; apply GlobalTheory.GtBasis.main <;> assumption) | exact @GlobalTheory.GtBasis.dn_inj | exact GlobalTheory.GtBasis.dn_inj | (intros; apply GlobalTheory.GtBasis.dn_inj <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

theorem GlobalTheory.VolBr.Pair.exists_rep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (P : Pair p) (a b : ℤ), ∃ M : HermLB p, P.Rep a b M := by
  intro k _ X _ p P a b
  obtain ⟨hL, hA, -⟩ := Pair.rep_base k X p P
  have cast (x y x' y' : ℤ) (M : HermLB p) (h : P.Rep x y M) (hx : x = x') (hy : y = y') :
      P.Rep x' y' M := by subst hx; subst hy; exact h
  have hLa := Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_pow k X p P _ _ _ a.toNat hL)
    (Pair.rep_dual k X p P _ _ _ (Pair.rep_pow k X p P _ _ _ (-a).toNat hL))
  have hAb := Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_pow k X p P _ _ _ b.toNat hA)
    (Pair.rep_dual k X p P _ _ _ (Pair.rep_pow k X p P _ _ _ (-b).toNat hA))
  refine ⟨_, cast _ _ _ _ _ (Pair.rep_tens k X p P _ _ _ _ _ _ hLa hAb) ?_ ?_⟩
  · have h1 := Int.toNat_sub_toNat_neg a
    simp only [mul_one, mul_zero, neg_zero, add_zero]
    omega
  · have h1 := Int.toNat_sub_toNat_neg b
    simp only [mul_one, mul_zero, neg_zero, zero_add]
    omega
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolRead.KCpt

open GlobalTheory.HolDict GlobalTheory.HolDict.BorelK

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Mt n → (H →L[ℂ] H)}

theorem revNeg_lt {a b : Fin n} (ha : ε a = false) (hb : ε b = false) (h : b < a) : revNeg ε a < revNeg ε b := by
  have ma : a ∈ negS ε := by simp [negS, ha]
  have mb : b ∈ negS ε := by simp [negS, hb]
  have h1 : revNeg ε a = (revOn ε ⟨a, ma⟩ : Fin n) := Equiv.Perm.ofSubtype_apply_of_mem _ ma
  have h2 : revNeg ε b = (revOn ε ⟨b, mb⟩ : Fin n) := Equiv.Perm.ofSubtype_apply_of_mem _ mb
  rw [h1, h2]
  have h3 : (⟨b, mb⟩ : {x // x ∈ negS ε}) < ⟨a, ma⟩ := h
  have h4 := ((negS ε).orderIsoOfFin rfl).symm.strictMono h3
  exact ((negS ε).orderIsoOfFin rfl).strictMono (Fin.rev_lt_rev.2 h4)

theorem isWtOn_root (hσ : IsURepOn (UJset ε) σ) {μ : Fin n → ℝ} {v : H}
    (hs : SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v) (hv : IsWtOn (Formalism.REAL.Kset ε) σ μ v) (a c : Fin n) :
    IsWtOn (Formalism.REAL.Kset ε) σ (μ + Formalism.REAL.root a c) (dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v) := by
  have hh : (Formalism.REAL.Jm ε).IsHermitian := Formalism.REAL.Jm_conjTranspose ε
  have z0 : ∀ x : H, dRepC (Formalism.REAL.Jm ε) σ 0 x = 0 := by
    intro x
    simp [dRepC, conjH, dRep]
  have l1 : ∀ (s : ℂ) Z, dRepC (Formalism.REAL.Jm ε) σ (s • Z) v = s • dRepC (Formalism.REAL.Jm ε) σ Z v := by
    intro s Z
    have := LieAct.dRepC_lin hh det_Jm hσ hs s Z 0
    rwa [add_zero, z0, add_zero] at this
  have l2 : ∀ (s : ℂ) Z, dRepC (Formalism.REAL.Jm ε) σ Z (s • v) = s • dRepC (Formalism.REAL.Jm ε) σ Z v := by
    intro s Z
    have := LieAct.dRepC_vec (π := σ) hh det_Jm hs hs (s - 1) Z
    rw [sub_smul, one_smul, sub_add_cancel, sub_smul, one_smul, sub_add_cancel] at this
    exact this
  intro θ hθ
  have hinv : (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I))⁻¹ =
      diagonal fun a => Complex.exp (-((θ a : ℂ) * Complex.I)) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext b
    rw [← Complex.exp_add]; simp
  have e : (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * Matrix.single a c (1 : ℂ) *
      (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I))⁻¹ =
      Complex.exp ((θ a : ℂ) * Complex.I + -((θ c : ℂ) * Complex.I)) • Matrix.single a c (1 : ℂ) := by
    rw [hinv]
    ext i j
    simp only [mul_diagonal, diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
    by_cases h' : a = i ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h'
      simp [Complex.exp_add]
    · simp [h']
  rw [LieAct.rep_dRepC hh det_Jm hσ hs (kset_uj hθ), e, hv θ hθ, l2, l1, smul_smul, ← Complex.exp_add]
  congr 2
  simp [Formalism.REAL.root, Pi.single_apply, add_mul, Finset.sum_add_distrib, sub_eq_add_neg]

theorem killed {lam : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) {v : H} (hv : v ∈ lowKSub ε lam σ)
    (hs : SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v)
    (hw : IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) v) {a c : Fin n} (hac : ε a = ε c)
    (hlt : revNeg ε a < revNeg ε c) : dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v = 0 := by
  have hε : ∀ b, ε ((revNeg ε).symm b) = ε b := fun b => by
    rw [← eps_revNeg ε ((revNeg ε).symm b), Equiv.apply_symm_apply]
  have h1 := isWtOn_perm hσ (revNeg ε).symm hε (isWtOn_root hσ hs hw a c)
  have e : (fun b => ((fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) + Formalism.REAL.root a c) ((revNeg ε).symm b)) =
      Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.root (revNeg ε a) (revNeg ε c) := by
    funext b
    simp [Formalism.REAL.root, Pi.single_apply, Equiv.symm_apply_eq]
  rw [e] at h1
  have h2 := orth_of_not_cdom hσ h1 (not_cdom _ hlt)
  have hK := pM_mem (revNeg ε).symm hε
  have h3 : ∀ x ∈ lowKSub ε lam σ, ⟪dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v, x⟫_ℂ = 0 := by
    intro x hx
    rw [← inner_rep hσ hK]
    exact h2 _ (stable_sSup _ hK x hx)
  exact inner_self_eq_zero.1 (inner_dRepC stable_sSup h3 hv hac)

theorem extremal_killed_compact : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) π → ∀ v ∈ lowKSub ε lam π, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0} π v → IsWtOn (Formalism.REAL.Kset ε) π (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) v → ∀ a b : Fin n, ((ε a = true ∧ ε b = true ∧ a < b) ∨ (ε a = false ∧ ε b = false ∧ b < a)) → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, ∀ Y ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, X + Complex.I • Y = Matrix.single a b 1 → dRep π X v + Complex.I • dRep π Y v = 0 := by
  intro n H _ _ ε lam π hπ v hv hs hw a b hab X hX Y hY hE
  rw [← LieAct.dRepC_parts (G := Formalism.REAL.Jm ε) det_Jm hX hY, hE]
  rcases hab with ⟨ha, hb, h⟩ | ⟨ha, hb, h⟩
  · exact killed hπ hv hs hw (ha.trans hb.symm) (by rwa [revNeg_of_pos ε ha, revNeg_of_pos ε hb])
  · exact killed hπ hv hs hw (ha.trans hb.symm) (revNeg_lt ha hb h)

end GlobalTheory.HolRead.KCpt
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.extremal_lowest_Ktype_killed_by_compact_roots : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mt n → (H →L[ℂ] H)), IsDS ε lam σ → ∀ v ∈ lowKSub ε lam σ, SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v → IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) v → (∀ a, dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a a 1) v = ((Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a) : ℝ) : ℂ) • v) ∧ ∀ a c : Fin n, ε a = ε c → revNeg ε a < revNeg ε c → dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v = 0 := by
  first | exact @GlobalTheory.HolDict.BorelK.extremal_killed | exact GlobalTheory.HolDict.BorelK.extremal_killed | (intros; apply GlobalTheory.HolDict.BorelK.extremal_killed <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gelfand_invariants_act_by_scalars_highest_weight : ∀ (n : ℕ) (Hm : Mt n) (q : ℕ) (x₀ : Mt n) (w : Fin n → ℤ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mt n → (H →L[ℂ] H)), OrthFr Hm q x₀ → IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → IsIrredOn (Formalism.QuantumDeterminants.UH Hm) σ → ∀ v₀, v₀ ≠ 0 → SmoothVec (lieH Hm) σ v₀ → (∀ a c : Fin n, a ≤ c → dRepC Hm σ (x₀ * Matrix.single a c 1 * x₀⁻¹) v₀ = if a = c then (w a : ℂ) • v₀ else 0) → ∀ k, ∃ c : ℂ, ∀ v, SmoothVec (lieH Hm) σ v → gelfRep Hm σ k v = c • v := by
  first | exact @GlobalTheory.HolDict.GelfScalar.gelfRep_scalar | exact GlobalTheory.HolDict.GelfScalar.gelfRep_scalar | (intros; apply GlobalTheory.HolDict.GelfScalar.gelfRep_scalar <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lowest_Ktype_holomorphic_killed_by_lowering_roots : ∀ (n p : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mt n → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → (∀ a, ε a = decide ((a : ℕ) < p)) → IsDS ε lam σ → ∀ v ∈ lowKSub ε lam σ, SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v → ∀ a c : Fin n, ε a = true → ε c = false → dRepC (Formalism.REAL.Jm ε) σ (Matrix.single c a 1) v = 0 := by
  first | exact @GlobalTheory.HolDict.Lowering.lowK_killed | exact GlobalTheory.HolDict.Lowering.lowK_killed | (intros; apply GlobalTheory.HolDict.Lowering.lowK_killed <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem lc_tendsto_of_rep : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ) (M : HermLB p) (α t₀ : ℝ), P.Rep a b M → M.IsSelfInter α → (M.shift (fun _ => t₀) fun _ => rfl).IsNef D → ∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => P.lc (m * a) (m * b) (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α / (D + 1).factorial + ((D + 1) * gdeg M D / (D + 1).factorial) * t)) := by
  intro hHS hC k _ X _ p D hX P a b M α t₀ hRep hα hN t ht
  have hNt := GlobalTheory.T.hermitianLineBundle_isNef_shift_monotone hC k X p D hX M t₀ t ht hN
  have hSt := hC.arShift k X p D hX M α t hα
  have hT := GlobalTheory.Published.ArithHilbertSamuel.tendsto_of_triv hHS hX hNt hSt
  have hF : ((D + 1).factorial : ℝ) ≠ 0 := by positivity
  have h2 := hT.div_const ((D + 1).factorial : ℝ)
  have e (m : ℕ) : P.lc (m * a) (m * b) (Real.exp (t * m)) =
      Real.log ((((M.shift (fun _ => t) fun _ => rfl).pow m).smallSec.ncard : ℝ)) := by
    rw [Pair.lc, Set.ncard_def, Set.ncard_def, (GlobalTheory.T.smallSections_twistedPower_encard_eq_ball k X p P a b M hRep t m).1]
  convert (preTransparency := .reducible) h2 using 1
  · funext m
    rw [e]
    field_simp
  · field_simp

end GlobalTheory.VolBr
end
