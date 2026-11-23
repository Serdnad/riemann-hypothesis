module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle243
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle438
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle439
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle440
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenReadsOfUnitAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle224
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle441
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCharRat

variable {D : D7}

theorem symplOH_add_right {S T : HSp D} (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  simp only [symplOH, symplO, hO, Matrix.add_apply, RingHom.map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib,
    LinearMap.map_add]

theorem symplOH_isoPart_midPart (V V' W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (hs : IsIsoSplit V V' C B)
    (q₀ : Matrix (Fin W.rank) (Fin r) D.host.E) (x : WO V' W) :
    symplOH V W (isoPart V W C (q₀.map (incA D))) (midPart V V' W B x) = 0 := by
  set X : Mx D r V.rank := (adj D C * V.gram).map (incA D) with hXdef
  set M : Matrix (Fin V'.rank) (Fin V.rank) D.host.E := V'.gram⁻¹ * adj D B * V.gram with hMdef
  set Y : Mx D V'.rank V.rank := M.map (incA D) with hYdef
  have hM : Mᴴ = V.gram * B * V'.gram⁻¹ := by
    rw [hMdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, GlobalTheory.MixModel.gram_conjTranspose,
      GlobalTheory.MixModel.gramInv_conjTranspose]
    show V.gram * ((Bᴴ)ᴴ * V'.gram⁻¹) = _
    rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hX0 : X * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj Y = 0 := by
    have e : GlobalTheory.MixModel.adj Y = GlobalTheory.MixModel.rat (V.gram * B * V'.gram⁻¹) := by
      rw [hYdef, ← hM]; rfl
    rw [e, hXdef]
    show GlobalTheory.MixModel.rat (adj D C * V.gram) * GlobalTheory.MixModel.rat V.gram⁻¹ * GlobalTheory.MixModel.rat (V.gram * B * V'.gram⁻¹) = 0
    rw [← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (V.gram * B * V'.gram⁻¹) = adj D C * V.gram * B * V'.gram⁻¹ := by
      rw [Matrix.mul_assoc (adj D C * V.gram), ← Matrix.mul_assoc V.gram⁻¹, ← Matrix.mul_assoc V.gram⁻¹,
        Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul, ← Matrix.mul_assoc]
    rw [this, hs.orth, Matrix.zero_mul]
    exact GlobalTheory.MixModel.rat_zero
  rw [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace]
  have e2 : isoPart V W C (q₀.map (incA D)) = q₀.map (incA D) * X := rfl
  have e3 : midPart V V' W B x = x * Y := rfl
  rw [e2, e3, GlobalTheory.MixModel.adj_mul]
  have e4 : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj Y * GlobalTheory.MixModel.adj x * (GlobalTheory.MixModel.gA W * (q₀.map (incA D) * X)))
      = (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj Y * GlobalTheory.MixModel.adj x * GlobalTheory.MixModel.gA W * q₀.map (incA D)) * X := by
    simp only [Matrix.mul_assoc]
  rw [e4, Matrix.trace_mul_comm]
  have e5 : X * (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj Y * GlobalTheory.MixModel.adj x * GlobalTheory.MixModel.gA W * q₀.map (incA D))
      = (X * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj Y) * (GlobalTheory.MixModel.adj x * GlobalTheory.MixModel.gA W * q₀.map (incA D)) := by
    simp only [Matrix.mul_assoc]
  rw [e5, hX0, Matrix.zero_mul, Matrix.trace_zero, map_zero]



theorem res_om_rat {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) {ψ : AddChar (AF D.host.F) ℂ}
    {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hω : IsWeilDatumO ψ V W χS χT ω)
    {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)} (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨)
    {γ : GA D W} (hγ : γ ∈ GQ W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (x : WO V' W) :
    res V V' W C B μ 𝓨 (ω (1, γ) f) x = res V V' W C B μ 𝓨 f (Formalism.L2.Theta.mt W γ⁻¹ * x) := by
  have hrat := GlobalTheory.WeilRat.om_rat_actO D ψ hω.std V W χS χT ω hω 1 (one_mem _) γ hγ f hf
  have hact : ∀ w : WO V W, actO V W 1 γ w = Formalism.L2.Theta.mt W γ * w := by
    intro w
    rw [GlobalTheory.MixModel.actO_eq, inv_one, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have hQP : Formalism.L2.Theta.mt W γ * Formalism.L2.Theta.mt W γ⁻¹ = 1 := GlobalTheory.MixModel.mt_mul_inv W γ
  have hPQ : Formalism.L2.Theta.mt W γ⁻¹ * Formalism.L2.Theta.mt W γ = 1 := GlobalTheory.MixModel.mt_inv_mul W γ
  have hpt : ∀ a, ω (1, γ) f (isoPart V W C a + midPart V V' W B x) =
      f (isoPart V W C (Formalism.L2.Theta.mt W γ⁻¹ * a) + midPart V V' W B (Formalism.L2.Theta.mt W γ⁻¹ * x)) := by
    intro a
    rw [← hrat, hact]
    refine congrArg (ω (1, γ) f) ?_
    show a * (((adj D C * V.gram).map (incA D)) : Mx D r V.rank) +
        x * (((V'.gram⁻¹ * adj D B * V.gram).map (incA D)) : Mx D V'.rank V.rank) =
      Formalism.L2.Theta.mt W γ * (Formalism.L2.Theta.mt W γ⁻¹ * a * (((adj D C * V.gram).map (incA D)) : Mx D r V.rank) +
        Formalism.L2.Theta.mt W γ⁻¹ * x * (((V'.gram⁻¹ * adj D B * V.gram).map (incA D)) : Mx D V'.rank V.rank))
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP,
      Matrix.one_mul, Matrix.one_mul]
  show ∫ a in 𝓨, ω (1, γ) f (isoPart V W C a + midPart V V' W B x) ∂μ =
    ∫ a in 𝓨, f (isoPart V W C a + midPart V V' W B (Formalism.L2.Theta.mt W γ⁻¹ * x)) ∂μ
  simp only [hpt]
  have hper : ∀ q ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ a,
      f (isoPart V W C (q + a) + midPart V V' W B (Formalism.L2.Theta.mt W γ⁻¹ * x)) =
        f (isoPart V W C a + midPart V V' W B (Formalism.L2.Theta.mt W γ⁻¹ * x)) := by
    intro q hq a
    obtain ⟨q₀, rfl⟩ := hq
    have e3 : (incA D).toAddMonoidHom.mapMatrix q₀ = q₀.map (incA D) := rfl
    rw [e3, GlobalTheory.TwistEquiRat.isoPart_add, add_assoc, ← GlobalTheory.TwistEquiRat.ratW_eq_isoPart, hf.quasi,
      GlobalTheory.TwistEquiRat.ratW_eq_isoPart, symplOH_add_right, GlobalTheory.TwistEquiRat.symplOH_isoPart V W C hs.frame,
      symplOH_isoPart_midPart V V' W C B hs, add_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
  have integral_mul_left {m n : ℕ} (μ : Measure (Mx D m n)) (𝓨 : Set (Mx D m n))
      (h : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓨) (P Q : Mx D m m)
      (hP : P ∈ GlobalTheory.MixModel.ratMx D m m) (hQ : Q ∈ GlobalTheory.MixModel.ratMx D m m)
      (hPQ : P * Q = 1) (hQP : Q * P = 1) (φ : Mx D m n → ℂ)
      (hφ : ∀ g ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, φ (g + a) = φ a) :
      ∫ a in 𝓨, φ (P * a) ∂μ = ∫ a in 𝓨, φ a ∂μ := by
    obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
    have : BorelSpace (Mx D m n) := ⟨rfl⟩
    let eA : Mx D m n ≃+ Mx D m n :=
      { toFun := fun a => P * a
        invFun := fun a => Q * a
        left_inv := fun a => by show Q * (P * a) = a; rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
        right_inv := fun a => by show P * (Q * a) = a; rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
        map_add' := fun a b => Matrix.mul_add P a b }
    have hc : Continuous (fun a : Mx D m n => P * a) := continuous_const.matrix_mul continuous_id
    have hc' : Continuous (fun a : Mx D m n => Q * a) := continuous_const.matrix_mul continuous_id
    let eH : Mx D m n ≃ₜ Mx D m n := ⟨eA.toEquiv, hc, hc'⟩
    let eM : Mx D m n ≃ᵐ Mx D m n := eH.toMeasurableEquiv
    have := h.1
    have hHaar : (μ.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ eA hc hc'
    have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
    have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
    let eG : GlobalTheory.MixModel.ratMx D m n → GlobalTheory.MixModel.ratMx D m n :=
      fun g => ⟨P * (g : Mx D m n), GlobalTheory.MixModel.ratMx_mul hP g.2⟩
    have hbij : Function.Bijective eG := by
      refine ⟨fun g g' hg => ?_, fun g => ⟨⟨Q * (g : Mx D m n), GlobalTheory.MixModel.ratMx_mul hQ g.2⟩, ?_⟩⟩
      · have e := congrArg (fun x : GlobalTheory.MixModel.ratMx D m n => Q * (x : Mx D m n)) hg
        simp only [eG, ← Matrix.mul_assoc, hQP, Matrix.one_mul] at e
        exact Subtype.ext e
      · apply Subtype.ext
        show P * (Q * (g : Mx D m n)) = g
        rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
    have hF : IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D m n) (eM.symm ⁻¹' 𝓨) (μ.map eM) := by
      refine h.2.1.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
      show Q * (P * (g : Mx D m n) + x) = (g : Mx D m n) + Q * x
      rw [Matrix.mul_add, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
    have hpre : eM ⁻¹' (eM.symm ⁻¹' 𝓨) = 𝓨 := by
      ext a; simp
    have hvol : (μ.map eM) (eM.symm ⁻¹' 𝓨) = 1 := by
      rw [MeasurableEquiv.map_apply, hpre]; exact h.2.2
    have e1 := hmp.setIntegral_preimage_emb eM.measurableEmbedding φ (eM.symm ⁻¹' 𝓨)
    rw [hpre] at e1
    exact e1.trans (GlobalTheory.MixModel.covolOne_integral_eq h ⟨hHaar, hF, hvol⟩ φ hφ)
  exact integral_mul_left μ 𝓨 hμ _ _ ((GlobalTheory.MixModel.mem_GQ_iff W γ⁻¹).1 (inv_mem hγ))
    ((GlobalTheory.MixModel.mem_GQ_iff W γ).1 hγ) hPQ hQP
    (fun a => f (isoPart V W C a + midPart V V' W B (Formalism.L2.Theta.mt W γ⁻¹ * x))) hper

theorem char_eq_one_of_rat : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χS' χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ c : GA D W →* Circle, (∀ h f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f)) → ∀ γ ∈ GQ W, c γ = 1 := by
  intro D V V' W r C B hs ψ χS χT χS' χT' ω ω' hω hω' μ 𝓨 hμ c hc γ hγ
  obtain ⟨hall, f₀, hf₀, hne⟩ := GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hω.std μ 𝓨 hμ
  obtain ⟨x, hx⟩ : ∃ x, res V V' W C B μ 𝓨 f₀ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hres : IsThetaFunO ψ V' W (res V V' W C B μ 𝓨 f₀) := ((hall f₀ hf₀).2.1)
  have h1 := congrFun (hc γ f₀ hf₀) (actO V' W 1 γ x)
  have hact : actO V' W 1 γ x = Formalism.L2.Theta.mt W γ * x := by
    rw [GlobalTheory.MixModel.actO_eq, inv_one, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have hPQ : Formalism.L2.Theta.mt W γ⁻¹ * Formalism.L2.Theta.mt W γ = 1 := GlobalTheory.MixModel.mt_inv_mul W γ
  have h2 := GlobalTheory.WeilRat.om_rat_actO D ψ hω'.std V' W χS' χT' ω' hω' 1 (one_mem _) γ hγ _ hres x
  rw [Pi.smul_apply, h2, res_om_rat hs hω hμ hγ hf₀, hact, ← Matrix.mul_assoc, hPQ, Matrix.one_mul,
    smul_eq_mul] at h1
  have h3 : (c γ : ℂ) = 1 := by
    have := mul_right_cancel₀ hx (h1.symm.trans (one_mul _).symm)
    exact this
  exact Circle.ext (by simpa using h3)

end GlobalTheory.TwistCharRat

end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.adelicLatticeIsometry_eq_prod_localComponents : ∀ (D : D7) (V V' : HSp D) (j : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Φ₀ : GfC V ≃ₜ* GfC V'), GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsLatIsom V V' (frameLat V) (frameLat V') j → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsConjBy V V' j Φ₀ → ∃ jl : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v, (∀ v, IsLatticeConj (frameLat V) (frameLat V') (jl v)) ∧ ∀ v g, Φ₀ (locFin V v g) = locFin V' v (jl v g) := by
  first | exact @GlobalTheory.TwistPC.isom_locComponents | exact GlobalTheory.TwistPC.isom_locComponents | (intros; apply GlobalTheory.TwistPC.isom_locComponents <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section


theorem _root_.GlobalTheory.T.thetaFunction_orientedModel_eq_of_realAdelicPoints : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (f₁ f₂ : WO S T → ℂ),
    IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ →
    (∀ X : Matrix (Fin T.rank) (Fin S.rank) D.host.E, f₁ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X) = f₂ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X)) →
    f₁ = f₂ := by
  first | exact @GlobalTheory.ThetaUniqReal.eq_of_eq_realPt | exact GlobalTheory.ThetaUniqReal.eq_of_eq_realPt | (intros; apply GlobalTheory.ThetaUniqReal.eq_of_eq_realPt <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section


theorem _root_.GlobalTheory.T.rationalMap_columns_mem_latG_iff_moved_finitePart : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E),
    GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b → ∀ (y : GA D (Wc D i)) (Yr : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E),
      (∀ a, (fun m => ∑ n, Yr m n * b n a) ∈ latG (Wc D i) y) ↔
        actO (Vc D i) (Wc D i) 1 y⁻¹ (ratW (Wc D i) (Vc D i) Yr - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) Yr) ∈
          latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
  first | exact @GlobalTheory.ColSplit.cols_mem_iff | exact GlobalTheory.ColSplit.cols_mem_iff | (intros; apply GlobalTheory.ColSplit.cols_mem_iff <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section


theorem _root_.GlobalTheory.T.thetaDictionary_lattice_of_frameCoordinates : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i),
    ∀ γ ∈ GQ (Wc D i), ∀ (g : GA D (Wc D i)),
      FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ g →
    ∀ v : Fin D.R.r → D.host.E,
      v ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).1).Λ ↔
        (fun m => v (Fin.cast (rank_Wc i) m)) ∈ latG (Wc D i) (γ * g) := by
  first | exact @GlobalTheory.DictLatPin.lat_of_frAt | exact GlobalTheory.DictLatPin.lat_of_frAt | (intros; apply GlobalTheory.DictLatPin.lat_of_frAt <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ArchPhase
open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues Matrix

variable {D : D7}

theorem gram_inv_eq (V : HSp D) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hb : IsONLatBasis V b) :
    (HSpace.gram V)⁻¹ = b * bᴴ := by
  have h1 : bᴴ * (HSpace.gram V * b) = 1 := by
    refine Matrix.ext fun a a' => ?_
    have := hb.1 a a'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Finset.mul_sum] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h2 : (HSpace.gram V * b) * bᴴ = 1 := mul_eq_one_comm.1 h1
  rw [Matrix.mul_assoc] at h2
  exact Matrix.inv_eq_right_inv h2

theorem infPart_realPt (S T : HSp D) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    infPart D (realPt S T X i j) = infPart D (incA D (X i j)) := rfl

theorem sum_two_re_tauE (D : D7) (e : D.host.E) :
    ∑ t, (((2 * (tauE D t e).re : ℝ)) : ℂ) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  classical
  have h1 : ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) = ∑ σ : D.host.E →+* ℂ, σ e := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) ℂ (x := e)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom D.host.E ℂ) _ _ fun _ => rfl).symm
  have hi := GlobalTheory.StdRat.tauE_injective D
  have hcm := GlobalTheory.StdRat.tauE_cm D
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => ComplexEmbedding.conjugate (tauE D t)) := by
    have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      fun σ => star_star σ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (tauE D b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (tauE D a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, tauE D t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h4 := hb.sum_comp fun σ : D.host.E →+* ℂ => σ e
  rw [Fintype.sum_sum_type, ← h1] at h4
  simp only [Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq] at h4
  rw [← h4, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Complex.add_conj]

end GlobalTheory.ArchPhase

namespace GlobalTheory.ArchPhase
open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues Matrix

variable {D : D7}



def hRat (S T : HSp D) (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.E :=
  Matrix.trace ((HSpace.gram S)⁻¹ * Yᴴ * HSpace.gram T * X)

theorem infPart_cA_realPt (S T : HSp D) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (i : Fin T.rank)
    (j : Fin S.rank) : infPart D (cA D (realPt S T X i j)) = infPart D (incA D (star (X i j))) := by
  rw [GlobalTheory.PhaseReal.infPart_cA, infPart_realPt, ← GlobalTheory.PhaseReal.infPart_cA, GlobalTheory.DualPairCheck.cA_incA]

theorem infPart_hO_realPt (S T : HSp D) (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    infPart D (hO S T (realPt S T X) (realPt S T Y)) = infPart D (incA D (hRat S T X Y)) := by
  rw [GlobalTheory.PhaseReal.hO_eq_trace, hRat]

  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply,
  Matrix.transpose_apply, Matrix.conjTranspose_apply, infPart_realPt, infPart_cA_realPt]

theorem finPart_hO_realPt (S T : HSp D) (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finPart D (hO S T (realPt S T X) (realPt S T Y)) = 0 := by
  have h : ∀ i j, finPart D (realPt S T X i j) = 0 := fun i j =>
    congrFun (congrFun (GlobalTheory.FrameConst.realPt_fin S T X) i) j

  simp only [hO, map_sum, map_mul, h, mul_zero, Finset.sum_const_zero]

theorem hermitian_column_sum_neg_mul_rearrange {n : ℕ} (ξ u : D.host.E) (v : Fin n → D.host.E) (G : Matrix (Fin n) (Fin n) D.host.E) (c : Fin n) :
    - -ξ * ∑ x, u * -G x c * ReciprocityTheory.ChartRestriction.G.FD.cc (v x) = -(ξ * ((∑ j, star (v j) * G j c) * u)) := by
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hst : star (v x) = ReciprocityTheory.ChartRestriction.G.FD.cc (v x) := rfl
  rw [hst]
  ring

theorem sum_herm_eq (V W : HSp D) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hb : IsONLatBasis V b) (r : ℕ)
    (hr : W.rank = r) (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (hX : ModelW W hr X)
    (Xm Ym : Matrix (Fin W.rank) (Fin V.rank) D.host.E) :
    ∑ a, (-X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (fun m => ∑ n, Xm (Fin.cast hr.symm m) n * b n a)
        (fun m => ∑ n, Ym (Fin.cast hr.symm m) n * b n a)) = -(D.host.xi0 * hRat V W Xm Ym) := by
  subst hr
  obtain ⟨hG, hξ⟩ := hX
  have e1 : hRat V W Xm Ym = Matrix.trace ((Ym * b)ᴴ * HSpace.gram W * (Xm * b)) := by
    rw [hRat, gram_inv_eq V b hb, Matrix.conjTranspose_mul, Matrix.mul_assoc b, Matrix.mul_assoc b,
      Matrix.mul_assoc b, Matrix.trace_mul_comm b]
    simp only [Matrix.mul_assoc]
  rw [e1, hξ, hG, Matrix.trace, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.neg_apply,
    Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_refl, Equiv.refl_symm,
    Equiv.refl_apply, Fin.cast_eq_self]
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c _
  exact hermitian_column_sum_neg_mul_rearrange (n := W.rank) _ _ (fun j : Fin W.rank => ∑ k : Fin V.rank, Ym j k * b k a) _ c

end GlobalTheory.ArchPhase

namespace GlobalTheory.ArchPhase
open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues Matrix



theorem psi_symplOH_realPt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D)
    (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis V b → ∀ (r : ℕ) (hr : W.rank = r)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r), ModelW W hr X → ∀ (Xm Ym : Matrix (Fin W.rank) (Fin V.rank) D.host.E),
    ψ (symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W Xm) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W Ym)) =
      Complex.exp (Real.pi * Complex.I * ∑ a, ((Algebra.trace ℚ D.host.E (-X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm
        (fun m => ∑ n, Xm (Fin.cast hr.symm m) n * b n a) (fun m => ∑ n, Ym (Fin.cast hr.symm m) n * b n a)) : ℚ) : ℂ)) := by
  intro D ψ hψ V W b hb r hr X hX Xm Ym
  obtain ⟨θ, hθ⟩ := hψ.2.1
  set t := incA D D.host.xi0 * hO V W (realPt V W Xm) (realPt V W Ym) with ht
  have hfin : finPart D t = 0 := by rw [ht, map_mul, finPart_hO_realPt, mul_zero]
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set T := Algebra.trace (AF D.host.F) (AE D) t with hTdef
  have hθt : ∀ ρ, θ ρ (infPart D t) = tauE D ρ (D.host.xi0 * hRat V W Xm Ym) := fun ρ => by
    rw [ht, map_mul (infPart D), infPart_hO_realPt, ← map_mul (infPart D), ← map_mul (incA D)]
    exact (hθ ρ).1 _
  have hL : symplOH V W (realPt V W Xm) (realPt V W Ym) =
      pairA D.host.F (algebraMap D.host.F (Ainf D.host.F) (1 / 2) * fstA D.host.F T) 0 := by
    unfold symplOH symplO
    rw [← ht, ← hTdef, hT]
    exact Prod.ext rfl (mul_zero _)
  have hs : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) (1 / 2) * fstA D.host.F T) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      (1 / 2 : ℂ) * ((2 * (tauE D ρ (D.host.xi0 * hRat V W Xm Ym)).re : ℝ) : ℂ) := fun ρ => by
    rw [show (algebraMap D.host.F (Ainf D.host.F) (1 / 2) * fstA D.host.F T) ⊗ₜ[D.host.F] (1 : D.host.E) =
        ((algebraMap D.host.F (Ainf D.host.F) (1 / 2)) ⊗ₜ[D.host.F] (1 : D.host.E)) *
          ((fstA D.host.F T) ⊗ₜ[D.host.F] (1 : D.host.E)) by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
      map_mul, hTdef, GlobalTheory.PhaseReal.theta_trace θ hθ ρ t, hθt, GlobalTheory.StdRat.tmul_one_eq, (hθ ρ).1]
    congr 1
    simp only [one_div, map_inv₀]
    rw [map_ofNat (algebraMap D.host.F D.host.E) 2, map_ofNat]
  rw [hL]
  change psiInf D.host.F ψ _ = _
  rw [hψ.2.2 θ hθ]
  simp only [hs]

  rw [← Finset.mul_sum, sum_two_re_tauE, ← Rat.cast_sum, ← map_sum, sum_herm_eq V W b hb r hr X hX Xm Ym, map_neg]
  congr 1
  push_cast
  ring

end GlobalTheory.ArchPhase
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.unitary_induction_on_splitPlaceSupport : ∀ {D : D7} (V : HSp D) (N : ℕ) (Q : GA D V → Prop), Q 1 → (∀ x y, Q x → Q y → Q (x * y)) →
    (∀ (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
      ∀ x ∈ GfC V, Formalism.L2.Theta.SuppAt e V x → Q x) →
    ∀ g ∈ GfC V, GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N ((finHom V) g : Matrix (Fin V.rank) (Fin V.rank) _) → Q g := by
  first | exact @GlobalTheory.SplitInduct.induct_suppSplit | exact GlobalTheory.SplitInduct.induct_suppSplit | (intros; apply GlobalTheory.SplitInduct.induct_suppSplit <;> assumption)
end
