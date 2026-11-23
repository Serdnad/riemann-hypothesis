module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2440
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
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SchurLatticeConjugates
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_short_periodLattice_basis_balanced_slope : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), HasPhi y φ → ∀ (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∃ r : ℕ, r ≤ Module.finrank ℚ E * Dw.q ∧ ShortBasis Q r ((|(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) / (2 * Module.finrank ℚ E) * (r : ℝ) ^ 3 * φ) (2 * Real.sqrt r) := by
  first | exact @GlobalTheory.ShortPhi.exists_shortBasis | exact GlobalTheory.ShortPhi.exists_shortBasis | (intros; apply GlobalTheory.ShortPhi.exists_shortBasis <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

theorem _root_.GlobalTheory.T.integralFramedPoint_restrict_coefficient_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (c' : Coeff l) (hle : c.F ≤ c'.F) (T : CDVR) (io' : c'.F →+* T.Fr) (y' : IntFr Xo c' T io'), y'.IsAlg → ∃ y : IntFr Xo c T (io'.comp (IntermediateField.inclusion hle).toRingHom), y.IsAlg ∧ (∀ φ : ℝ, HasPhi y' φ → HasPhi y φ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, evI y' (GlobalTheory.FieldBC.rulBC hle f) = evI y f := by
  first | exact @GlobalTheory.RefSum.intFr_res_down | exact GlobalTheory.RefSum.intFr_res_down | (intros; apply GlobalTheory.RefSum.intFr_res_down <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.balancedPeriodSlope_mul_ramificationIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io') (r : ℕ), 0 < r → (letI := io.toAlgebra; letI := io'.toAlgebra; ∃ ψ : T.Fr →ₐ[c.F] T'.Fr, (∀ x, x ≠ 0 → vV T'.V (ψ x) = (r : ℤ) * vV T.V x) ∧ FrMap ψ y.1 y'.1) → ∀ φ φ' : ℝ, HasPhi y φ → HasPhi y' φ' → φ' = r * φ := by
  first | exact @GlobalTheory.SlopeRec.phi_eq_mul_of_frMap | exact GlobalTheory.SlopeRec.phi_eq_mul_of_frMap | (intros; apply GlobalTheory.SlopeRec.phi_eq_mul_of_frMap <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem divOver_restrict : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E' : DivOver (f ≫ p), E'.Through y → ∃ E : DivOver p, E.Through (f y) ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  intro M W _ _ _ _ p f _ n _ _ U hf y hy E' hE'
  have e := functionFieldMap_comp_constFn p f
  have hc : ∀ a, functionFieldMap f (Cartier.constFn p a) ∈ E'.ring := fun a => by
    rw [← RingHom.comp_apply, e]; exact E'.const_mem a
  obtain ⟨z, hzy, hz⟩ := GlobalTheory.T.exists_specializes_dominatesStalk_of_regular M E'.ring y hE'
  have hzU : z ∈ U := hzy.mem_open U.isOpen hy
  have hfin := GlobalTheory.T.finiteDimensional_functionField_of_etale_on_open' M W f U hf ⟨y, hy⟩
  have hess' : ((functionFieldMap f).comp (Cartier.constFn p)).codRestrict E'.ring hc =
      (Cartier.constFn (f ≫ p)).codRestrict E'.ring E'.const_mem :=
    RingHom.ext fun a => Subtype.ext (RingHom.congr_fun e a)
  obtain ⟨hdvr, hess⟩ := GlobalTheory.T.dvr_comap_finiteIndex_essFiniteType_complex W.functionField M.functionField (functionFieldMap f)
    (Cartier.constFn p) hfin E'.ring hc (hess' ▸ E'.essFiniteType)
  let E : DivOver p := ⟨E'.ring.comap (functionFieldMap f), hc, hdvr, hess⟩
  haveI : IsDiscreteValuationRing (E'.ring.comap (functionFieldMap f)) := hdvr
  have hun := GlobalTheory.T.etale_restrict_dvr_comap_dominatesStalk M W f U hf z hzU E'.ring hz
  let ψ : E.ring →+* E'.ring := (functionFieldMap f).restrict E.ring E'.ring fun _ hx => hx
  letI := ψ.toAlgebra
  have hψ : ψ.comp E.const = E'.const := RingHom.ext fun a => Subtype.ext (RingHom.congr_fun e a)
  have hft : Algebra.EssFiniteType E.ring E'.ring := by
    have h1 : (ψ.comp E.const).EssFiniteType := hψ ▸ E'.essFiniteType
    exact RingHom.EssFiniteType.of_comp E.const h1
  have hord : ∀ g : W.functionFieldˣ,
      E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := fun g =>
    GlobalTheory.T.log_ordFrac_comap_formallyUnramified_dvr W.functionField M.functionField (functionFieldMap f) E'.ring ⟨hun, hft⟩ g g.ne_zero
  refine ⟨E, fun g ⟨a, ha⟩ => ?_, hord, fun η hη => ?_⟩
  · show functionFieldMap f g ∈ E'.ring
    exact hE' _ ⟨f.stalkMap y a, by rw [← functionFieldMap_algebraMap, ha]⟩
  · haveI := SmoothOfRelativeDimension.smooth n p
    haveI := SmoothOfRelativeDimension.smooth n (f ≫ p)
    have hnW : topologicalKrullDim W = n := NadelApp.topologicalKrullDim_eq_of_smooth W p n
    have hnM : topologicalKrullDim M = n := NadelApp.topologicalKrullDim_eq_of_smooth M (f ≫ p) n
    obtain ⟨ω, hω, g, rfl, hg⟩ := E.isFormOrd_formOrd hnW hη
    have hω' := GlobalTheory.T.isFreeGenerator_topForms_of_formallyUnramified E.const E'.const ψ hψ n hun ω hω (E'.exists_isFreeGen hnM)
    have key : ratPull p f n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ψ hψ ω) := by
      have h1 := formMap_formMap (D := n) E.ring.subtype (functionFieldMap f)
        ((functionFieldMap f).comp E.ring.subtype) rfl rfl e
        (by rw [RingHom.comp_assoc]; exact e) ω
      have h2 := formMap_formMap (D := n) ψ E'.ring.subtype
        ((functionFieldMap f).comp E.ring.subtype) rfl hψ rfl
        (by rw [RingHom.comp_assoc]; exact e) ω
      exact h1.trans h2.symm
    have hpull : ratPull p f n ((g : W.functionField) • E.toRat n ω) =
        ((Units.map (functionFieldMap f).toMonoidHom g : M.functionFieldˣ) : M.functionField) •
          E'.toRat n (TopForm.formMap n ψ hψ ω) := by
      rw [map_smulₛₗ, key]; rfl
    have hne : ratPull p f n ((g : W.functionField) • E.toRat n ω) ≠ 0 := by
      rw [hpull]
      refine smul_ne_zero (Units.ne_zero _) fun h0 => ?_
      have := (E'.isFreeGen_toRat hω').1 (a₁ := 0) (a₂ := 1) (by simp [h0])
      exact zero_ne_one this
    change E'.formOrd (ratPull p f n ((g : W.functionField) • E.toRat n ω)) =
      E.formOrd ((g : W.functionField) • E.toRat n ω)
    rw [← hg, ← hord g]
    exact DivOver.IsFormOrd.formOrd_eq hne ⟨_, hω', _, hpull, rfl⟩

end GlobalTheory.EtaleKlt
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.doubledWeilRep_fixes_vacuum_tensor_siegelParabolic_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
      IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.W v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @GlobalTheory.InertDblPar.parD_fix | exact GlobalTheory.InertDblPar.parD_fix | (intros; apply GlobalTheory.InertDblPar.parD_fix <;> assumption)
end

section

noncomputable section

open scoped TensorProduct Matrix ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.WeilAdmCM

variable {F : Type} [Field F] [NumberField F]

theorem std_fin (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) :=
  GlobalTheory.T.standardTraceAdelicAddChar_finite_rational_eq_exp F ψ hψ x

theorem std_beta (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) :
    ∃ β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ,
      (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
        Complex.exp (2 * Real.pi * Complex.I * β a)) ∧ ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0 :=
  GlobalTheory.T.standardAddChar_archimedean_eq_exp_nondegenerate F ψ hψ

theorem fixed_invariant_compactSupport (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (κ : Type) [Fintype κ]
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)))
    (hM : IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)))) :
    ∃ (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) (K : Set (κ → FiniteAdeleRing (𝓞 F) F)),
      IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsCompact K ∧ ∀ Φ : (κ → AF F) → ℂ, (∀ m ∈ M, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilAdm.finE2 F m) Φ = Φ) →
        (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) ∧ ∀ x, (fun i => (x i).2) ∉ K → Φ x = 0 :=
  GlobalTheory.WeilAdm.fixed_schroedinger_invariant_compactSupport_bounded_annihilator ψ
    (fun O hO => GlobalTheory.ScalarAnnih.exists_compact_annihilator_finiteAdeles_traceChar F ψ hψ.1 (std_fin ψ hψ) O hO) κ M hM

theorem realcont (ps : AddChar (AF F) ℂ) (hψ : IsStd ps) (κ : Type) [Fintype κ]
    (L : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ]
      ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (A : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (hA : ∀ f, ∫⁻ z, ‖A f z‖ₑ ^ 2 ≤ C * ∫⁻ z, ‖f z‖ₑ ^ 2)
    (hI : ∀ v (f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ), ⇑f' = GlobalTheory.WeilAdm.schrInf F ps v ⇑f →
      ⇑(A f') = GlobalTheory.WeilAdm.schrInf F ps (L v) ⇑(A f)) :
    Continuous A := by
  obtain ⟨β, hβ1, hnd⟩ := std_beta ps hψ
  obtain ⟨n, Q, P, hQP⟩ := GlobalTheory.T.exists_linear_model_archimedean_schroedinger_standard F ps β hβ1 hnd κ
  obtain ⟨c, hc⟩ := GlobalTheory.T.lintegral_sq_comp_continuousLinearEquiv_mixedSpace F κ n Q
  let CQ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) Q
  let CQi := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) Q.symm
  have hCQ : ∀ f, ⇑(CQ f) = ⇑f ∘ ⇑Q := fun f => SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ Q f
  have hCQi : ∀ g, ⇑(CQi g) = ⇑g ∘ ⇑Q.symm := fun g => SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ Q.symm g
  have hQQ : ∀ f, CQi (CQ f) = f := fun f => by
    ext z; rw [hCQi, hCQ]; simp
  have hQQ' : ∀ g, CQ (CQi g) = g := fun g => by
    ext z; rw [hCQ, hCQi]; simp
  let A' : GlobalTheory.RealWeil.Sch (Fin n) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin n) := CQ.toLinearMap ∘ₗ A ∘ₗ CQi.toLinearMap
  have hA'apply : ∀ g, A' g = CQ (A (CQi g)) := fun g => rfl
  let L' : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) := P.trans (L.trans P.symm)
  have hbound : ∀ g, ∫⁻ x, ‖A' g x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖g x‖ₑ ^ 2 := by
    intro g
    have e1 : ∫⁻ x, ‖A' g x‖ₑ ^ 2 = c * ∫⁻ z, ‖A (CQi g) z‖ₑ ^ 2 := by
      rw [← hc]
      simp only [hA'apply, hCQ, Function.comp_apply]
    have e2 : ∫⁻ x, ‖g x‖ₑ ^ 2 = c * ∫⁻ z, ‖CQi g z‖ₑ ^ 2 := by
      rw [← hc]
      simp only [hCQi, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [e1, e2, ← mul_assoc, mul_comm C c, mul_assoc]
    exact mul_le_mul' le_rfl (hA _)
  have hint : ∀ w (g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑g →
      ⇑(A' g') = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' g) := by
    intro w g g' hg
    have h1 : ⇑(CQi g') = GlobalTheory.WeilAdm.schrInf F ps (P w) ⇑(CQi g) := by
      have := congrArg (fun u => u ∘ ⇑Q.symm) (hQP w ⇑(CQi g))
      simp only [Function.comp_assoc, ContinuousLinearEquiv.self_comp_symm, Function.comp_id] at this
      rw [this, hCQi, hg, ← hCQ, hQQ']
    have h2 := hI (P w) (CQi g) (CQi g') h1
    have hL' : P (L' w) = L (P w) := P.apply_symm_apply _
    have h3 : ⇑(A (CQi g')) = GlobalTheory.WeilAdm.schrInf F ps (P (L' w)) ⇑(A (CQi g)) := by
      rw [h2]
      exact congrArg (fun v => GlobalTheory.WeilAdm.schrInf F ps v ⇑(A (CQi g))) hL'.symm
    calc ⇑(A' g') = ⇑(A (CQi g')) ∘ ⇑Q := hCQ _
      _ = GlobalTheory.WeilAdm.schrInf F ps (P (L' w)) ⇑(A (CQi g)) ∘ ⇑Q := congrArg (· ∘ ⇑Q) h3
      _ = GlobalTheory.RealWeil.rhoFun (L' w) (⇑(A (CQi g)) ∘ ⇑Q) := hQP _ _
      _ = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' g) := congrArg (GlobalTheory.RealWeil.rhoFun (L' w)) (hCQ _).symm
  have hcont : Continuous A' :=
    GlobalTheory.T.continuous_of_lie_intertwine_l2 (Fin n) L' A' C hC hbound (GlobalTheory.T.derived_action_intertwines_of_group (Fin n) L'.toLinearMap A' C hC hbound hint)
  have hAeq : ⇑A = fun f => CQi (A' (CQ f)) := by
    funext f
    rw [hA'apply, hQQ, hQQ]
  rw [hAeq]
  exact CQi.continuous.comp (hcont.comp CQ.continuous)


open GlobalTheory.WeilAdm in

theorem weilAdmissible_of_heisenberg_unitary (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (κ : Type) [Fintype κ]
    (B : ((κ → AF F) × (κ → AF F)) ≃ₗ[AF F] ((κ → AF F) × (κ → AF F)))
    (O : Module.End ℂ ((κ → AF F) → ℂ))
    (hpres : ∀ φ ∈ GlobalTheory.WeilM.schA F κ, O φ ∈ GlobalTheory.WeilM.schA F κ)
    (himpl : ∀ w, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, O (GlobalTheory.WeilM.schr ψ w φ) = GlobalTheory.WeilM.schr ψ (B w) (O φ))
    (hunit : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ x, ‖O φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) :
    ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, l ∘ₗ O ∈ (GlobalTheory.WeilM.adeleClass F).adm κ := by
  intro l hl g hg
  obtain ⟨M, hMo, hM⟩ := GlobalTheory.WeilAdm.pureA_fixed_fin F ψ hψ.1 κ g hg
  obtain ⟨M', hM'o, hM'⟩ := GlobalTheory.WeilAdm.fintrans F κ B M hMo
  obtain ⟨U, K, hUo, hUc, hK, hfix⟩ := fixed_invariant_compactSupport ψ hψ κ M' hM'o
  obtain ⟨R, hRsb, hdec⟩ := GlobalTheory.WeilAdm.eq_sum_pureA_coset_indicator F κ U K hUo hUc hK
  obtain ⟨L, hL⟩ := GlobalTheory.WeilAdm.infLin_main F κ B
  obtain ⟨μ, hμ, C, c, hC, hc0, hcT, hpure, hslice⟩ := GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds F κ g hg U hUo
  have hpA : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.WeilM.schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hfixed : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ m ∈ M',
      GlobalTheory.WeilM.schr ψ (finE2 F m) (O (GlobalTheory.WeilM.pureA F f g)) = O (GlobalTheory.WeilM.pureA F f g) := by
    intro f m hm
    obtain ⟨m0, hm0, hB⟩ := hM' m hm
    rw [← hB, ← himpl _ _ (hpA f), hM m0 hm0]
  have hs : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (r : κ → FiniteAdeleRing (𝓞 F) F),
      ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ z,
        s z = slice F (O (GlobalTheory.WeilM.pureA F f g)) r z :=
    fun f r => exists_schwartz_slice _ (hpres _ (hpA f)) r
  choose sl hsl using hs
  let A : (κ → FiniteAdeleRing (𝓞 F) F) →
      (SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) :=
    fun r =>
    { toFun := fun f => sl f r
      map_add' := fun f f' => by
        ext z
        rw [SchwartzMap.add_apply, hsl, hsl, hsl, show ⇑(f + f') = ⇑f + ⇑f' from funext fun _ => rfl, pureA_add, map_add (f := _)]
        rfl
      map_smul' := fun a f => by
        ext z
        rw [SchwartzMap.smul_apply, hsl, hsl, show ⇑(a • f) = a • ⇑f from funext fun _ => rfl, pureA_smul, map_smul]
        rfl }
  have hA : ∀ r f, ⇑(A r f) = slice F (O (GlobalTheory.WeilM.pureA F f g)) r := fun r f => funext (hsl f r)
  have hcont : ∀ r, Continuous (A r) := by
    intro r
    refine realcont ψ hψ κ L (A r) (C / c) (ENNReal.div_ne_top hC hc0) (fun f => ?_) (fun v f f' hf => ?_)
    · have h1 := hslice _ (hpres _ (hpA f)) (hfix _ (hfixed f)).1 r
      rw [hunit μ hμ _ (hpA f)] at h1
      have h2 := h1.trans (hpure f)
      rw [hA, ← ENNReal.mul_div_right_comm, ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hcT), mul_comm]
      exact h2
    · rw [hA, hA, hf, pureA_schrInf, himpl _ _ (hpA f), hL, slice_schr]
  have hT : ∀ r ∈ R, ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      l (GlobalTheory.WeilM.pureA F f (Set.indicator {y | y - r ∈ U} fun _ => (1 : ℂ))) = T f :=
    fun r hr => hl _ (hRsb r hr)
  choose T hT using hT
  refine ⟨∑ r ∈ R.attach, (T r.1 r.2).comp ⟨A r.1, hcont r.1⟩, fun f => ?_⟩
  have hΦ := hdec (O (GlobalTheory.WeilM.pureA F f g)) (hfix _ (hfixed f)).1 (hfix _ (hfixed f)).2

  rw [LinearMap.comp_apply, hΦ, map_sum, ContinuousLinearMap.sum_apply, ← Finset.sum_attach R]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← hA, hT r.1 r.2]
  rfl

end GlobalTheory.WeilAdmCM

namespace GlobalTheory.WeilAdmCM

theorem transport_adm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              ∀ p, ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ om p ∈ (adeleClass F).adm κ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξσ χS χT hcS hcT hrS hrT ω hω JA JB ξ hJA hJB κ _ co hco om htr p l hl
  have hP : (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) ∧
      ∀ p w, ∀ φ ∈ schA F κ, om p (co.rho B.ψ w φ) = co.rho B.ψ (actAB (cA σ) p w) (om p φ) :=
    GlobalTheory.T.transportedWeilDatum_CM_preserves_schwartz_heisenberg F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξσ χS χT hcS hcT hrS hrT ω hω JA JB ξ hJA hJB κ co hco om htr
  have hU : IsUnitaryOn (adeleClass F) om :=
    GlobalTheory.T.weilDatumTransport_cmExtension_isUnitaryOn F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξσ χS χT hcS hcT hrS hrT ω hω JA JB ξ hJA hJB κ co hco om htr
  refine weilAdmissible_of_heisenberg_unitary B.ψ hB.std κ (co.e.symm.trans ((GlobalTheory.WeilAdm.actLin _ p).trans co.e)) (om p) (hP.1 p)
    (fun w φ hφ => ?_) (fun μ hμ φ hφ => hU μ hμ p φ hφ) l hl
  have h := hP.2 p (co.e.symm w) φ hφ
  simp only [GlobalTheory.WeilM.Darboux.rho, LinearEquiv.apply_symm_apply] at h
  exact h

end GlobalTheory.WeilAdmCM

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

theorem _root_.GlobalTheory.T.exists_local_finiteDimensional_finite_parts_weil_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ p0, ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
      (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        om p Φ = ∑ i, pureA F (f i) (g i) := by
  first | exact @GlobalTheory.WeilContF.exists_local_finite_parts_F | exact GlobalTheory.WeilContF.exists_local_finite_parts_F | (intros; apply GlobalTheory.WeilContF.exists_local_finite_parts_F <;> assumption)
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact.ReadEx

theorem exists_vac_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∃ e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d), e0 ≠ 0 ∧ ∃ f₀, Reads ψ θ hS hT cc δ r e0 f₀ := GlobalTheory.T.exists_nonzero_standardThetaLine_read_adelic

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} {hS : S.rank = a}
  {hT : T.rank = d} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}

theorem reads_zero : Reads ψ θ hS hT cc δ r 0 0 :=
  ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩

theorem reads_sum {k : ℕ} (G : Fin k → VC D a d → ℂ) (f : Fin k → WO S T → ℂ)
    (h : ∀ i, Reads ψ θ hS hT cc δ r (G i) (f i)) : Reads ψ θ hS hT cc δ r (∑ i, G i) (∑ i, f i) := by
  have key : ∀ s : Finset (Fin k), Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using (reads_zero : Reads ψ θ hS hT cc δ r 0 0)
    · intro i s hi ih
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (h i).add ih
  exact key Finset.univ

theorem exists_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G ∈ TT D (tor0 D cc δ) a d, ∃ f, Reads ψ θ hS hT cc δ r G f := by
  intro D ψ θ S T a d hS hT cc δ r hP G hG
  obtain ⟨e0, he0, hne, f₀, hf₀⟩ := exists_vac_reads ψ θ S T hS hT cc δ r hP
  obtain ⟨k, c, z, rfl⟩ := GlobalTheory.ThetaSpan.theta_span D cc δ hP.crv a d e0 he0 hne G hG
  refine ⟨∑ i, c i • (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) •
    heisO ψ S T (finPt hS hT r (z i)) f₀), reads_sum _ _ fun i => ?_⟩
  have h := ((GlobalTheory.T.heisenbergFinitePoint_reads_classicalTranslation ψ θ S T hS hT cc δ r hP e0 f₀ hf₀ (z i)).smul
    (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)))).smul (c i)
  convert h using 2
  ext x
  simp [Formalism.MainNotions.StandardLatticesGL3.Wd]

end GlobalTheory.NormExact.ReadEx
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.exists_coordinates_logVectorFields_determinant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)) (x₀ : TF.Y.X), x₀ ∈ U.1 → ∃ (x : Fin Dw.dim → Γ(TF.Y.X, U.1)) (U' : TF.Y.X.affineOpens) (hU' : U'.1 ≤ U.1), x₀ ∈ U'.1 ∧ TopForm.IsFrame (TopForm.dOn TF.Y.s fun i => resG TF.Y.X hU' (x i)) ∧ (LogKS.boundary TF.Y).ideal U' = Ideal.span {resG TF.Y.X hU' (logDet (fun j => (b j).1) x)} := by
  first | exact @GlobalTheory.LogPole.exists_coord_logDet | exact GlobalTheory.LogPole.exists_coord_logDet | (intros; apply GlobalTheory.LogPole.exists_coord_logDet <;> assumption)
end
