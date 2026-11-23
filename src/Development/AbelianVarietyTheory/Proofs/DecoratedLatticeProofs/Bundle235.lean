module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle199
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalTwistDatumRenumberRowsColumns
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle227
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedThetaFamilyVectorsLatticesThetaZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle445
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle203
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

theorem _root_.GlobalTheory.T.zeta_residue_ne_zero_of_simple_pole_lift_L_function : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ (D : D7) (S : Finset (FinPl D)) (r t : ℕ) (c par : GlobalTheory.LFun.Fam D.host.E) (χ : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (S : Set (FinPl D)) r t c par (GlobalTheory.LFun.val (F := D.host.F) χ) (GlobalTheory.LFun.val (F := D.host.F) χ) → ∀ (a b : ℕ) (Z : ℂ → ℂ) (C z : ℂ), C ≠ 0 → EqRight Z (fun s => GlobalTheory.LFun.LSD D S par χ (s + 1 / 2) / GlobalTheory.LFun.dSfun D.host.E (S : Set (FinPl D)) a b s * C) → CoeffAt Z ((t : ℂ) / 2) (-1) z → z ≠ 0 := by
  first | exact @GlobalTheory.Core.Rk.Exh.residue_ne_zero_of_simplePole | exact GlobalTheory.Core.Rk.Exh.residue_ne_zero_of_simplePole | (intros; apply GlobalTheory.Core.Rk.Exh.residue_ne_zero_of_simplePole <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ConjAdjWeil

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.PairLift

variable {D : D7}

theorem dagger_eq (S T : HSp D) (x : WO S T) : dagger S T x = adjO T S x := by
  simp only [dagger, adjO, giA, gA, adj, Matrix.mul_assoc]
  rfl

theorem cj_dagger (S T : HSp D) (f : WO S T → ℂ) : cj (dagger T S) f = dag S T f := by
  funext y; simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dag, dagger_eq]

theorem conjAdjoint_apply {S T : HSp D} (om : Rep S T) (g : GA D T) (h : GA D S) (f : WO T S → ℂ) :
    conjAdjoint om (g, h) f = dag S T (om (h, g) (dag T S f)) := by
  show cj (dagger T S) (om (h, g) (cj (dagger S T) f)) = _
  rw [cj_dagger, cj_dagger]

theorem chi_conj {χ : (AE D)ˣ →* Circle} {n : ℕ} (hR : ResEta D χ n) (y : (AE D)ˣ) :
    χ (Units.map (cA D).toMonoidHom y) = (χ y)⁻¹ := by
  obtain ⟨⟨η, hη⟩, hall⟩ := hR
  have hprod : y * Units.map (cA D).toMonoidHom y =
      idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) y) := by
    apply Units.ext
    rw [GlobalTheory.Mem.EtaTilde.idF_norm]
    rfl
  have h1 : χ y * χ (Units.map (cA D).toMonoidHom y) = 1 := by
    rw [← map_mul, hprod, hall η hη, hη.2.2.1, one_pow]
  exact eq_inv_of_mul_eq_one_right h1

theorem isSplitIdem_conj {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩

theorem suppAt_conj {e : AE D} {V : HSp D} {g : GA D V} (h : SuppAt e V g) : SuppAt (cA D e) V g := by
  intro i j
  rw [cA_cA, add_comm]
  exact h i j

theorem det_inv_eq (V : HSp D) (g : GA D V) : (mt V g⁻¹).det = cA D (mt V g).det := by
  have h1 : (giA V).det * (gA V).det = 1 := by rw [← Matrix.det_mul, giA_mul_gA, Matrix.det_one]
  rw [mt_inv, Matrix.det_mul, Matrix.det_mul, adj, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
  linear_combination ((mt V g).map (cA D)).det * h1

theorem isDetAt_conj {e : AE D} (he : e * e = e) {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hx : IsDetAt e V g x) :
    IsDetAt (cA D e) V g (Units.map (cA D).toMonoidHom x⁻¹) := by
  have hd : (mt V g⁻¹).det * (mt V g).det = 1 := by rw [← Matrix.det_mul, mt_inv_mul, Matrix.det_one]
  have hz : ((x⁻¹ : (AE D)ˣ) : AE D) = e * (mt V g⁻¹).det + (1 - e) := by
    apply Units.inv_eq_of_mul_eq_one_left
    rw [hx]
    linear_combination e * hd + ((mt V g⁻¹).det * (mt V g).det - (mt V g⁻¹).det - (mt V g).det + 1) * he
  show cA D ((x⁻¹ : (AE D)ˣ) : AE D) = cA D e * (mt V g).det + (1 - cA D e)
  rw [hz, map_add (f := _), map_mul, map_sub, map_one, det_inv_eq, cA_cA]

end GlobalTheory.ConjAdjWeil

namespace GlobalTheory.ConjAdjWeil

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.PairLift

theorem isWeilDatumO_conjAdjoint : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ T S χT χS (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint om) := by
  intro D ψ S T χS χT om hw
  have hS : AdjLaw ψ S T := GlobalTheory.AdjLawPf.adjLaw D ψ hw.std S T
  have hT : AdjLaw ψ T S := GlobalTheory.AdjLawPf.adjLaw D ψ hw.std T S
  have thB : ∀ f : WO T S → ℂ, IsThetaFunO ψ T S f → IsThetaFunO ψ S T (dag T S f) := hT.theta
  have thA : ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ T S (dag S T f) := hS.theta
  have key : ∀ (g : GA D T) (h : GA D S) (f : WO T S → ℂ),
      conjAdjoint om (g, h) f = dag S T (om (h, g) (dag T S f)) := fun g h f => conjAdjoint_apply om g h f
  have dd : ∀ f : WO T S → ℂ, dag S T (dag T S f) = f := fun f => by
    funext y; simp only [dag, hT.invol, Complex.conj_conj]
  have d0 : adjO S T 0 = 0 := by
    have := hS.add 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  have d0' : adjO T S 0 = 0 := by
    have := hT.add 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  refine ⟨hw.std, hw.hecT, hw.hecS, hw.resT, hw.resS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨g, h⟩ f hf
    rw [key]
    exact thA _ (hw.om_pres _ _ (thB f hf))
  · intro g h w₀ f hf
    have e1 : dag T S (heisO ψ T S w₀ f) = heisO ψ S T (adjO S T w₀) (dag T S f) := by
      rw [hT.Heisenberg₂, hT.invol]
    rw [key, key, e1, hw.om_heis _ _ _ _ (thB f hf), ← hS.act, ← hS.Heisenberg₂]
  · intro γ hγ γ' hγ' f hf
    rw [key]
    have := hw.om_aut γ' hγ' γ hγ (dag T S f) (thB f hf)
    simp only [dag] at this ⊢
    rw [d0, this, d0', Complex.conj_conj]
  · intro f hf w
    have e : (fun p : GA D T × GA D S => conjAdjoint om p f w) =
        fun p => starRingEnd ℂ (om (Prod.swap p) (dag T S f) (adjO S T w)) := by
      funext p
      obtain ⟨g, h⟩ := p
      rw [key]
      rfl
    rw [e]
    exact Complex.continuous_conj.comp ((hw.om_cont _ (thB f hf) _).comp continuous_swap)
  · intro μ 𝓕 hμ h𝓕 p f hf
    obtain ⟨g, h⟩ := p
    haveI : BorelSpace (WO S T) := ⟨rfl⟩
    haveI : BorelSpace (WO T S) := ⟨rfl⟩
    let dE : WO T S ≃+ WO S T :=
      { toFun := adjO S T, invFun := adjO T S, left_inv := hT.invol, right_inv := hS.invol, map_add' := hS.add }
    let hE : WO S T ≃ₜ WO T S :=
      { toFun := adjO T S, invFun := adjO S T, left_inv := hS.invol, right_inv := hT.invol,
        continuous_toFun := hT.cont, continuous_invFun := hS.cont }
    set ν : Measure (WO S T) := μ.map dE with hν
    have hνH : ν.IsAddHaarMeasure := dE.isAddHaarMeasure_map μ hS.cont hT.cont
    have hfm : Measurable (adjO T S) := hT.cont.measurable
    have hdm : Measurable (adjO S T) := hS.cont.measurable
    have hmp : MeasurePreserving (adjO T S) ν μ := by
      refine ⟨hfm, ?_⟩
      rw [hν, Measure.map_map hfm (show Measurable dE from hdm)]
      have : adjO T S ∘ dE = id := funext fun w => hT.invol w
      rw [this, Measure.map_id]
    have hemb : MeasurableEmbedding (adjO T S) := hE.measurableEmbedding
    have hfd : IsAddFundamentalDomain (ratL T S) (adjO T S ⁻¹' 𝓕) ν := by
      refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving
        (e := fun γ : ratL S T => (⟨adjO S T γ, (hS.rat γ).2 γ.2⟩ : ratL T S)) ⟨?_, ?_⟩ ?_
      · intro a b hab
        have := congrArg (fun z : ratL T S => adjO T S (z : WO S T)) hab
        simp only [hT.invol] at this
        exact Subtype.ext this
      · intro b
        refine ⟨⟨adjO T S b, (hT.rat b).2 b.2⟩, Subtype.ext ?_⟩
        exact hS.invol b
      · intro γ x
        show adjO T S (adjO S T (γ : WO T S) + x) = (γ : WO T S) + adjO T S x
        rw [hT.add, hT.invol]
    calc ∫⁻ w in 𝓕, ‖conjAdjoint om (g, h) f w‖ₑ ^ 2 ∂μ
        = ∫⁻ w in 𝓕, (fun z => ‖om (h, g) (dag T S f) z‖ₑ ^ 2) (adjO S T w) ∂μ := by
          congr 1
          funext w
          rw [key]
          simp [dag]
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, (fun z => ‖om (h, g) (dag T S f) z‖ₑ ^ 2) (adjO S T (adjO T S z)) ∂ν :=
          (hmp.setLIntegral_comp_preimage_emb hemb (fun w => (fun z => ‖om (h, g) (dag T S f) z‖ₑ ^ 2) (adjO S T w)) 𝓕).symm
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, ‖om (h, g) (dag T S f) z‖ₑ ^ 2 ∂ν := by simp only [hS.invol]
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, ‖dag T S f z‖ₑ ^ 2 ∂ν := hw.om_unit ν _ hνH hfd (h, g) _ (thB f hf)
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, (fun w => ‖f w‖ₑ ^ 2) (adjO T S z) ∂ν := by
          congr 1
          funext z
          simp [dag]
      _ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := hmp.setLIntegral_comp_preimage_emb hemb (fun w => ‖f w‖ₑ ^ 2) 𝓕
  · intro e he g h hsg hsh x y hx hy
    obtain ⟨r, hr, hℓ⟩ := hw.om_split (cA D e) (isSplitIdem_conj he) h g (suppAt_conj hsh) (suppAt_conj hsg) _ _
      (isDetAt_conj he.1 hy) (isDetAt_conj he.1 hx)
    refine ⟨r, hr, fun ℓ hinv f hf => ?_⟩
    have dadd : ∀ a b : WO S T → ℂ, dag S T (a + b) = dag S T a + dag S T b := fun a b => by
      funext z; simp [dag]
    have dsmul : ∀ (c : ℂ) (a : WO S T → ℂ), dag S T (c • a) = starRingEnd ℂ c • dag S T a := fun c a => by
      funext z; simp [dag]
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun F => starRingEnd ℂ (ℓ (dag S T F))
        map_add' := fun a b => by simp only [dadd, map_add (f := _)]
        map_smul' := fun c a => by
          simp only [dsmul, map_smul, smul_eq_mul, map_mul, RingHom.id_apply, Complex.conj_conj] }
    have hinv' : ∀ u : WO S T, (∀ i j, cA D (cA D e) * u i j = u i j) → ∀ F, IsThetaFunO ψ S T F →
        ℓ' (heisO ψ S T u F) = ℓ' F := by
      intro u hu F hF
      have hu' : IsHalf e u := fun i j => by have := hu i j; rwa [cA_cA] at this
      have e2 : dag S T (heisO ψ S T u F) = heisO ψ T S (adjO T S u) (dag S T F) := by rw [hS.Heisenberg₂, hS.invol]
      show starRingEnd ℂ (ℓ (dag S T (heisO ψ S T u F))) = starRingEnd ℂ (ℓ (dag S T F))
      rw [e2, hinv _ (hT.half e u hu') _ (thA F hF)]
    have main := hℓ ℓ' hinv' (dag T S f) (thB f hf)
    have m2 : starRingEnd ℂ (ℓ (dag S T (om (h, g) (dag T S f)))) =
        (r : ℂ) * (splitFacO χS χT (Units.map (cA D).toMonoidHom y⁻¹) (Units.map (cA D).toMonoidHom x⁻¹) : ℂ) *
          starRingEnd ℂ (ℓ f) := by
      have := main
      simp only [ℓ', LinearMap.coe_mk, AddHom.coe_mk, dd] at this
      exact this
    have hconj := congrArg (starRingEnd ℂ) m2
    rw [Complex.conj_conj] at hconj
    have hfac : (splitFacO χS χT (Units.map (cA D).toMonoidHom y⁻¹) (Units.map (cA D).toMonoidHom x⁻¹))⁻¹ =
        splitFacO χT χS x y := by
      unfold splitFacO
      rw [chi_conj hw.resT, chi_conj hw.resS, map_inv, map_inv, inv_inv, inv_inv, _root_.mul_inv_rev, inv_inv]
    rw [key, hconj, map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal, ← Circle.coe_inv_eq_conj, hfac]

end GlobalTheory.ConjAdjWeil
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (phiQ linOm)

theorem _root_.GlobalTheory.T.local_twist_datum_renumber_rows_columns : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (r a b : ℕ) (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (ε : Fin r ⊕ A ≃ Fin a) (ε' : Fin r ⊕ B ≃ Fin b), (∀ i, (ε (.inl i) : ℕ) = i) → (∀ i, (ε' (.inl i) : ℕ) = i) → (∀ ξ : (Fv D.host.F v)ˣ →* ℂˣ, (phiQ v r ξ = fun z : Matrix (Fin b) (Fin a) (Fv D.host.F v) => datum ξ (z.submatrix ε' ε)) ∧ (GlobalTheory.SplitWeil.IsTame ξ → datum ξ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin r ⊕ B) (Fin r ⊕ A) (Fv D.host.F v)))) ∧ (∀ u : Matrix (Fin r ⊕ B) (Fin r ⊕ A) (Fv D.host.F v) → ℂ, u ∈ GlobalTheory.SplitWeil.SB _ ↔ (fun z : Matrix (Fin b) (Fin a) (Fv D.host.F v) => u (z.submatrix ε' ε)) ∈ GlobalTheory.SplitWeil.SB _) ∧ (∀ (μS μT : (Fv D.host.F v)ˣ →* ℂˣ) (g : GL (Fin r ⊕ A) (Fv D.host.F v)) (h : GL (Fin r ⊕ B) (Fv D.host.F v)) (u : Matrix (Fin r ⊕ B) (Fin r ⊕ A) (Fv D.host.F v) → ℂ), (u ∈ GlobalTheory.SplitWeil.SB _ → GlobalTheory.ParHecke.omTwo μS μT g h u ∈ GlobalTheory.SplitWeil.SB _) ∧ ∀ (G : GL (Fin a) (Fv D.host.F v)) (H : GL (Fin b) (Fv D.host.F v)), G.1.submatrix ε ε = g.1 → H.1.submatrix ε' ε' = h.1 → (fun z : Matrix (Fin b) (Fin a) (Fv D.host.F v) => GlobalTheory.ParHecke.omTwo μS μT g h u (z.submatrix ε' ε)) = (((μT (GeneralLinearGroup.det G))⁻¹ * μS (GeneralLinearGroup.det H) : ℂˣ) : ℂ) • linOm v G H fun z => u (z.submatrix ε' ε)) ∧ ∀ [MeasurableSpace (Fv D.host.F v)] [BorelSpace (Fv D.host.F v)] (ν : Measure (Fv D.host.F v)), ν.IsAddHaarMeasure → ∀ u u' : Matrix (Fin r ⊕ B) (Fin r ⊕ A) (Fv D.host.F v) → ℂ, GlobalTheory.SplitWeil.ip ν (fun z : Matrix (Fin b) (Fin a) (Fv D.host.F v) => u (z.submatrix ε' ε)) (fun z => u' (z.submatrix ε' ε)) = GlobalTheory.SplitWeil.ip ν u u' := by
  first | exact @GlobalTheory.Reidx.renumber | exact GlobalTheory.Reidx.renumber | (intros; apply GlobalTheory.Reidx.renumber <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
noncomputable section

namespace GlobalTheory.NormIdealUnit

theorem unit_at_split_place : ∀ (D : D7) (PP : Pl D.host.E), ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → ∀ (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ((∃ a : D.host.E, a ∈ D.host.AA ∧ Valued.v (rdQ φ a) = 1) ∧ ∀ a : D.host.E, a ∈ D.host.AA → Valued.v (rdQ φ a) ≤ 1) := by
  intro D PP hPP v φ hφ
  have hq : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun h => hPP (by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun h => hPP (by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
  have unit : ∀ x : 𝓞 D.host.E, x ∉ PP.asIdeal → Valued.v (rdQ φ (x : D.host.E)) = 1 := fun x hx =>
    le_antisymm (GlobalTheory.TameLiftChar.val_rdQ_le_one φ x) (not_lt.1 fun h => hx ((hφ x).2 h))
  refine ⟨⟨_, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D, ?_⟩, ?_⟩
  · have := unit _ hN
    simpa using this
  · have hnot : ¬ D.host.𝔟 ≤ PP.asIdeal :=
      haveI := PP.isPrime; UpperTheory.Ram.half_not_le D.host _ hq
    obtain ⟨z, hz, hzP⟩ := Set.not_subset.1 hnot
    have hz1 := unit z hzP
    have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.2 (Formalism.L2.Pj.b_ne_bot D)
    have hAA0 : ∀ a : D.host.E, a ∈ D.host.AA0 → Valued.v (rdQ φ a) ≤ 1 := by
      intro a ha
      unfold Host.AA0 at ha
      rw [FractionalIdeal.mem_inv_iff hB] at ha
      obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1 (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩))
      have h3 := GlobalTheory.TameLiftChar.val_rdQ_le_one φ w
      rw [RingOfIntegers.coe_eq_algebraMap, hw, ← GlobalTheory.TameLiftChar.rdQHom_apply, map_mul, map_mul,
        GlobalTheory.TameLiftChar.rdQHom_apply, GlobalTheory.TameLiftChar.rdQHom_apply] at h3
      rw [← RingOfIntegers.coe_eq_algebraMap] at h3
      rw [hz1] at h3
      simpa using h3
    have hle : D.host.AA ≤ D.host.AA0 := by
      unfold Host.AA
      calc (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0
          ≤ 1 * D.host.AA0 := by first | exact FractionalIdeal.mul_right_mono _ FractionalIdeal.coeIdeal_le_one | exact mul_le_mul_left FractionalIdeal.coeIdeal_le_one _ | gcongr; exact FractionalIdeal.coeIdeal_le_one
        _ = D.host.AA0 := one_mul _
    exact fun a ha => hAA0 a (hle ha)

end GlobalTheory.NormIdealUnit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

theorem _root_.GlobalTheory.T.twistPlaceChainStepDatum_mem_schwartzBruhat : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ) (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → phiQ (a := a) (b := b) v r mu ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  first | exact @GlobalTheory.SBTwist.phiQ_mem_SB | exact GlobalTheory.SBTwist.phiQ_mem_SB | (intros; apply GlobalTheory.SBTwist.phiQ_mem_SB <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Core.Ht2

theorem family_laws : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws)
    (Z : TC.Later B (I.cols l)), (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).EqP I.chi ∧
      (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).VecP I.chi := by
  intro B X I h _ l Z
  have hcc : TaylorLogMetric.IsCurveIdeal (assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ := ⟨top_ne_bot, by simp⟩
  have hδ := ((I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 h.amb_ok).1
  have hχ : TaylorLogMetric.IsChi (assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi := GlobalTheory.Mem.ChiIdeal.isChi_chiId _ _ I.C.isChi
  exact ⟨GlobalTheory.Mem.NatEqui.eqP _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ,
    (GlobalTheory.NatFamily.family _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ).1⟩

end GlobalTheory.Core.Ht2
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)

theorem _root_.GlobalTheory.T.theta_lattice_vacuum_split_place_vacuum_at_prime : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → Formalism.DivisionValues.conjPl w ≠ w → ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ), VacFin ψ S T v f → IsVacAt ψ S T w f := by
  first | exact @GlobalTheory.VacSplit.isVacAt_of_vacFin | exact GlobalTheory.VacSplit.isVacAt_of_vacFin | (intros; apply GlobalTheory.VacSplit.isVacAt_of_vacFin <;> assumption)
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ T S χT χS (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint om) := by
  first | exact @GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint | exact GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint | (intros; apply GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint <;> assumption)

end
end
