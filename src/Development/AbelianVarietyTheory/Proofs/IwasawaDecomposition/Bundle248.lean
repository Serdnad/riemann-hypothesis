module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthPolynomialRepresentation
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle077
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle242
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle238
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle229
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle246
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFamilyLowLieAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle243
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle089
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle244
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import ReciprocityTheory.GaloisValuations.GlobalB

@[expose] public section

section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

theorem _root_.GlobalTheory.T.mumfordGoodGrowth_polynomialRepresentation : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (c : ℝ) (N : ℕ), ∃ (c' : ℝ) (N' : ℕ), ∀ (n : ℕ) (S : Finset (Fin n)) (G : V n → Mat m ℂ) (v : V n), (∀ τ, MContDiffAt 2 (fun u => G u τ) v) → (∀ τ, (G v τ).det ≠ 0) → 1 ≤ ∑ a ∈ S, |Real.log ‖v a‖| → (∀ τ, GoodBound S c N (fun u => G u τ) v) → GoodBound S c' N' (fun u => ρ.ev (G u)) v := by
  first | exact @GlobalTheory.RepBound.goodBound_ev | exact GlobalTheory.RepBound.goodBound_ev | (intros; apply GlobalTheory.RepBound.goodBound_ev <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealGeo.Half

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}



theorem preChar_updFW {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL Ks (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G)
    (h : PreChar R) : PreChar (updFW R nW FW) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, ?_⟩
  · exact ⟨h5.1, h5.2, h5.3, h5.4, h5.5, h5.6, h5.7, h5.8⟩
  · exact ⟨h6.1, h6.2, h6.3, h6.4, h6.5, h6.6, h6.7, h6.8, h6.9, h6.10, h6.11, h6.12, h6.13, h6.14, h6.15, h6.16, h6.17,
      h6.18, h6.19, h6.20, h6.21⟩
  · exact ⟨h7.1, h7.2, h7.3, h7.4, h7.5, h7.6, h7.7, h7.8, h7.9, h7.10, h7.11⟩
  · exact ⟨h8.1, h8.2, h8.3, h8.4, h8.5, h8.6, h8.7⟩

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

section Upd

variable (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G)



def updO {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) :
    OMDat T.toCore (updFW R nW FW) i Tp tup := { O with }

variable (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))


theorem omPins_upd (i : Fin D.R.m) (h : OMPins T R κ v₀ O i) :
    OMPins T (updFW R nW FW) κ v₀ (fun i => updO T R nW FW (O i)) i := by
  refine ⟨h.1, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h.2
  refine ⟨⟨h1.field, h1.std, ?_, h1.c0, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0


theorem fired_upd (ph : Fin D.R.m → ℂ) (h : Fired T R κ v₀ O ph) :
    Fired T (updFW R nW FW) κ v₀ (fun i => updO T R nW FW (O i)) ph :=
  ⟨fun i => h.1 i, fun i σ hσ hV => h.2 i σ hσ hV⟩

end Upd

variable (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))



def tieGeo (h : TieIn T R κ v₀) : FWTie T (geoR T R κ v₀ O) κ v₀ :=
  let t := tieN T R κ v₀ (nTop T κ) h (hasB_nTop T h.laws κ)
  { alg_eq := t.alg_eq, e := t.e, ks := t.ks, kap := t.kap, pt := t.pt, nrm_eq := t.nrm_eq, laws := t.laws, chiR := t.chiR,
    hv₀ := t.hv₀, x0 := t.x0, ev0 := t.ev0, ev := t.ev }


theorem barTie_tieGeo (h : TieIn T R κ v₀) : BarTie (tieGeo T R κ v₀ O h) :=
  fun i σ hσ hV => barTie_tieN T R κ v₀ (nTop T κ) h (hasB_nTop T h.laws κ) i σ hσ hV


theorem rhoGeo_tieGeo (h : TieIn T R κ v₀) (hp : ∀ i, OMPins T R κ v₀ O i) :
    RhoGeo (tieGeo T R κ v₀ O h) (fun i => updO T R _ _ (O i)) := by
  intro i
  have hb := hasB_nTop T h.laws κ i
  refine ⟨fun hk g f => ?_, fun hk g => ?_⟩
  · have hex := GlobalTheory.LevelRep.exists_cusp_rep T κ i (O i).lev2 h.laws (hp i).2.act.1 hk
    refine ⟨hk g f f.2, ?_⟩
    have e1 : geoRho T R κ O i = rhoB D.what₂.LL hb.some hex.choose := dif_pos ⟨hb, hex⟩
    have e2 : (⟨_, hk g f f.2⟩ : Cu T κ i) = hex.choose g f := Subtype.ext (hex.choose_spec g f).symm
    show crdOr T.Q.c.F D.what₂.LL (Cu T κ i) (nTop T κ i) ⟨_, hk g f f.2⟩ =
      geoRho T R κ O i g (crdOr T.Q.c.F D.what₂.LL (Cu T κ i) (nTop T κ i) f)
    rw [e1, e2, crdOr_eq hb, rhoB_crd]
  · have e1 : geoRho T R κ O i = 1 := dif_neg fun h' => hk fun g f hf => by
      have h1 := h'.2.choose_spec g ⟨f, hf⟩
      have h2 := (h'.2.choose g ⟨f, hf⟩).2
      rw [h1] at h2
      exact h2
    show geoRho T R κ O i g = 1
    rw [e1]
    rfl


theorem chiIs_chiTop_of_tie (hL : R.toLevCh.Is A.μ0) (h : TieIn T R κ v₀) (i : Fin D.R.m) : ChiIs R i (chiTop R i) := by
  choose y ha using GlobalTheory.ChiDetValues.chiC_mem_coeff T R κ v₀ hL h i
  have hne : ∀ g, algebraMap T.Q.c.F D.what₂.LL (y g) ≠ 0 := fun g h0 => (chiC R i g).ne_zero (by rw [← ha, h0, map_zero])
  have hex : ∃ chi, ChiIs R i chi :=
    ⟨MonoidHom.mk' (fun g => Units.mk0 _ (hne g)) fun g g' => Units.ext (D.what₂.embLL.injective (by
      simp only [Units.val_mk0, Units.val_mul, map_mul, ha, chiC_mul])), ha⟩
  rw [chiTop, dif_pos hex]
  exact hex.choose_spec

end GlobalTheory.RealGeo.Half

namespace GlobalTheory.RealGeo



theorem exists_geoHalf_geoR : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), PreChar R → TieIn T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → Fired T R κ v₀ O ph → ∃ B : GeoHalf T (geoR T R κ v₀ O) ph, B.κ = κ ∧ B.v₀ = v₀ ∧ Fired T (geoR T R κ v₀ O) B.κ B.v₀ B.O ph ∧ PreChar (geoR T R κ v₀ O) ∧ (geoR T R κ v₀ O).grp_chiW := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O ph hc ht hp hf
  have hf' := Half.fired_upd T R κ v₀ (nTop T κ) (formsGeo T R κ v₀ O) O ph hf
  refine ⟨⟨κ, v₀, Half.tieGeo T R κ v₀ O ht, Half.barTie_tieGeo T R κ v₀ O ht, fun i => Half.updO T R _ _ (O i),
    fun i => Half.omPins_upd T R κ v₀ _ _ O i (hp i), Half.rhoGeo_tieGeo T R κ v₀ O ht hp,
    fun i σ hσ hV _ => hf'.2 i σ hσ hV, fun i _ => ⟨ph i, hf'.1 i⟩, fun i _ _ => hf'.1 i⟩,
    rfl, rfl, hf', Half.preChar_updFW R _ _ hc, fun i g => ?_⟩
  exact (Half.chiIs_chiTop_of_tie T R κ v₀ hc.lev ht i g).trans (Units.coe_prod _ _)

end GlobalTheory.RealGeo
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo

section Change

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  {K : Type} [Field K] {C : Type} [AddCommGroup C] [Module K C] {σ : K →+* ℂ} {V : HSp D}
  {X : Comp → Data E r} {rd : C →ₛₗ[σ] FDSec X} {dict : GA D V → Σ c, Frame (X c).Ψ r} {mu mu' : GA D V → ℂ}

theorem norm_jFn_eq_of_muUnit (h : MuUnit V dict mu) (h' : MuUnit V dict mu') (f : C) (q : AutQ V) :
    ‖jFn V σ rd dict mu' f q‖ = ‖jFn V σ rd dict mu f q‖ := by
  show ‖mu' q.out * rd f (dict q.out).1 (dict q.out).2‖ = ‖mu q.out * rd f (dict q.out).1 (dict q.out).2‖
  rw [norm_mul, norm_mul, h.2.1, h'.2.1]

theorem jMemL2_of_muUnit (h : MuUnit V dict mu) (h' : MuUnit V dict mu') (hc : Continuous mu)
    (hc' : Continuous mu') (hL : JMemL2 V σ rd dict mu) : JMemL2 V σ rd dict mu' := by
  intro f
  have hne : ∀ g, mu g ≠ 0 := fun g h0 => by
    have := h.2.1 g
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hinv : ∀ γ ∈ GQ V, ∀ g, (fun g => mu' g / mu g) (γ * g) = (fun g => mu' g / mu g) g := by
    intro γ hγ g
    show mu' (γ * g) / mu (γ * g) = mu' g / mu g
    rw [h.1, h'.1, h.2.2.1 γ hγ, h'.2.2.1 γ hγ, one_mul, one_mul]
  have hm : AEStronglyMeasurable (onQ V (fun g => mu' g / mu g)) (muQ1 V) := by
    haveI : BorelSpace (GA D V) := ⟨rfl⟩
    rw [onQ_eq_lift _ hinv]
    refine Measurable.aestronglyMeasurable ?_
    exact measurable_from_quotient.2 (hc'.div hc hne).measurable
  have he : jFn V σ rd dict mu' f = onQ V (fun g => mu' g / mu g) * jFn V σ rd dict mu f := by
    funext q
    show mu' q.out * rd f (dict q.out).1 (dict q.out).2 =
      mu' q.out / mu q.out * (mu q.out * rd f (dict q.out).1 (dict q.out).2)
    rw [← mul_assoc, div_mul_cancel₀ _ (hne _)]
  refine (hL f).congr_norm ?_ (Filter.Eventually.of_forall fun q => (norm_jFn_eq_of_muUnit h h' f q).symm)
  rw [he]
  exact hm.mul (hL f).aestronglyMeasurable

theorem peterson_norm_independent_of_unitary_character (h : MuUnit V dict mu) (h' : MuUnit V dict mu') (hL : JMemL2 V σ rd dict mu)
    (hL' : JMemL2 V σ rd dict mu') (f : C) : l2NormAlt V σ rd dict mu' hL' f = l2NormAlt V σ rd dict mu hL f := by
  show ‖(hL' f).toLp _‖ = ‖(hL f).toLp _‖
  rw [Lp.norm_toLp, Lp.norm_toLp,
    eLpNorm_congr_norm_ae (hL' f).aestronglyMeasurable (hL f).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => norm_jFn_eq_of_muUnit h h' f q)]

end Change

theorem exists_mu_reCore : ∀ (D : D7) (T : CoreJ D) (chiW : ℕ → (T.Q.c.F →+* ℂ) → (AE D)ˣ →* Circle), LawsJ T → LawsCore T.toCore → (∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj T.σ₀ σ (chiW j T.σ₀) (chiW j σ)) → ∃ mu, LawsJ (reCore T T.dict mu chiW T.x₀ T.cE) ∧ LawsCore (reCore T T.dict mu chiW T.x₀ T.cE).toCore := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro D T chiW hJ hC hchi
    have hex : ∀ j σ, ∃ mu : GA D (T.V j σ) → ℂ, InR D j → GoodEmb T.Q.c σ →
        MuVal (T.V j σ) (chiW j σ) mu ∧ MuUnit (T.V j σ) (T.dict j σ) mu ∧ Continuous mu := by
      intro j σ
      by_cases h : InR D j ∧ GoodEmb T.Q.c σ
      · obtain ⟨mu, h1, h2, h3, h4, h5⟩ := GlobalTheory.Member.exists_muVal D (T.V j σ) (chiW j σ) (hchi j h.1 σ h.2).1
          (hchi j h.1 σ h.2).2.1
        exact ⟨mu, fun hj hσ => ⟨h1, ⟨h2, h3, h4, (hJ.muUnit j hj σ hσ).2.2.2⟩, h5⟩⟩
      · exact ⟨fun _ => 1, fun hj hσ => absurd ⟨hj, hσ⟩ h⟩
    choose mu hmu using hex
    have hL : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CuspL2 (T.U j) σ (T.V j σ) (T.dict j σ) (mu j σ) :=
      fun j hj σ hσ a n hd => jMemL2_of_muUnit (hJ.muUnit j hj σ hσ) (hmu j σ hj hσ).2.1 (hJ.muCont j hj σ hσ)
        (hmu j σ hj hσ).2.2 (hJ.cuspidalL2Subspace j hj σ hσ a n hd)
    have hLM : LawsM (reCore T T.dict mu chiW T.x₀ T.cE).toCore :=
      { pins := hJ.pins
        half := hJ.half
        evalWD := hJ.evalWD
        unf := hJ.unf
        unTest := hJ.unTest
        chiTriv := hJ.chiTriv
        dictU := hJ.dictU
        spaceW := hJ.spaceW
        levelK := hJ.levelK
        xiAbs := hJ.xiAbs
        muUnit := fun j hj σ hσ => (hmu j σ hj hσ).2.1
        muCont := fun j hj σ hσ => (hmu j σ hj hσ).2.2
        finVol := hJ.finVol
        cuspFD := hJ.cuspFD
        supDef := hJ.supDef
        cuspidalL2Subspace := hL
        l2Def := fun j hj σ hσ a n hd f h0 => hJ.l2Def j hj σ hσ a n hd f
          ((peterson_norm_independent_of_unitary_character (hJ.muUnit j hj σ hσ) (hmu j σ hj hσ).2.1 (hJ.cuspidalL2Subspace j hj σ hσ a n hd)
            (hL j hj σ hσ a n hd) f).symm.trans h0)
        unitIndep := hJ.unitIndep
        ptNe := hJ.ptNe }
    refine ⟨mu, ?_, ?_⟩
    · exact
        { toLawsM := hLM
          cUnit := hJ.cUnit
          muVal := fun j hj σ hσ => (hmu j σ hj hσ).1
          muConj := fun j hj σ hσ => (hchi j hj σ hσ).2.2
          intAll := hJ.intAll
          modelW := hJ.modelW
          familyUniformisationBasePointOrthogonal := hJ.familyUniformisationBasePointOrthogonal
          kfHalf := hJ.kfHalf
          adPin := hJ.adPin }
    · exact
        { toLawsM := hLM
          cuspMul := hC.cuspMul
          latZ := hC.latZ
          cuNe := hC.cuNe
          expo := hC.expo }

end GlobalTheory.RealGeo
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory

theorem nonempty_hFrame : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ), (∀ k, _root_.GlobalTheory.Mem.Chr.SplitsC H.E (H.g k)) → _root_.GlobalTheory.Mem.Chr.SplitsC H.E H.pde → _root_.GlobalTheory.Mem.Chr.SplitsC H.E H.pde' → (∀ j τ, ∃ z : ℤ, e j τ = z) → (∀ j, UpperTheory.MUQ (_root_.Formalism.L2.Host.embPsi H) (e j)) → Nonempty (_root_.GlobalTheory.Mem.Chr.HFrame H e) := by
  intro R H e hg hp hp' he hs
  obtain ⟨⟨P⟩, ⟨W⟩⟩ := GlobalTheory.nonempty_piBar_and_omg R H
  have hmu : ∀ j : Fin R.m, ∃ χ : _root_.Formalism.L2.Host.HChar H.E, _root_.Formalism.L2.Host.IsMu0 P W (e j) j.1 χ := fun j =>
    GlobalTheory.T.mu0Exists_of_splits_of_integral_of_MUQ R H P W (e j) j.1 hg (he j) (hs j)
  choose mu hmu using hmu
  obtain ⟨eta, heta⟩ := GlobalTheory.T.host_etaTilde_character_exists R H
  obtain ⟨chi, hchi⟩ := GlobalTheory.T.exists_unramified_cmType_heckeChar_on_host R H
  obtain ⟨d, hd⟩ := GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists R H H.pde H.pde_prime H.pde_mod.1 hp
  obtain ⟨d', hd'⟩ := GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists R H H.pde' H.pde'_prime H.pde_mod.2 hp'
  exact ⟨⟨P, W, mu, eta, chi, d, d', hmu, heta, hchi, hd, hd'⟩⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.extend_splitTorus_hom_over_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (G₁ : Over (Sp (FractionRing V))) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left),
    IsGrpPullback G₁ G (spMap (algebraMap V (FractionRing V))) φ₁ → Nonempty (TorusExtension G₁) →
    ∀ (Ω : Type) [Field Ω] (α : FractionRing V →+* Ω) (G' : Over (Sp Ω)) [GrpObj G'] (φ : G'.left ⟶ G.left)
      (h : IsGrpPullback G' G (spMap (α.comp (algebraMap V (FractionRing V)))) φ)
      (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp Ω) X ⟶ G'), IsMonHom i →
      ∃ j : splitTorus (Sp V) X ⟶ G, IsMonHom j ∧ GlobalTheory.TorusPart.pullTorus h j = i := by
  first | exact @GlobalTheory.TorusPart.extend_torus_hom_dvr | exact GlobalTheory.TorusPart.extend_torus_hom_dvr | (intros; apply GlobalTheory.TorusPart.extend_torus_hom_dvr <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open Pointwise

namespace GlobalTheory.TrueGeo.HorizRing

variable {F : Type} [Field F] [NumberField F]

theorem exists_embed (B : Type) [CommRing B] [IsDomain B] [Algebra (𝓞 F) B] [CharZero B] [Algebra.IsAlgebraic ℤ B] :
    ∃ ψ : B →ₐ[𝓞 F] AlgebraicClosure F, Function.Injective ψ := by
  have hinj : Function.Injective (algebraMap (𝓞 F) B) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    change Ideal.comap (algebraMap ℤ (𝓞 F)) (RingHom.ker (algebraMap (𝓞 F) B)) = ⊥
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  haveI : Algebra.IsAlgebraic (𝓞 F) B :=
    Algebra.IsAlgebraic.extendScalars (R := ℤ) (RingHom.injective_int _)
  haveI : Module.IsTorsionFree (𝓞 F) B := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  haveI : Module.IsTorsionFree (𝓞 F) (AlgebraicClosure F) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq (𝓞 F) F (AlgebraicClosure F)]
    exact (algebraMap F _).injective.comp (IsFractionRing.injective (𝓞 F) F)
  let ψ : B →ₐ[𝓞 F] AlgebraicClosure F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ, ?_⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  refine Ideal.comap_ne_bot_of_algebraic_mem (R := ℤ) (I := RingHom.ker ψ.toRingHom) h0 hx
    (Algebra.IsAlgebraic.isAlgebraic x) ?_
  change Ideal.comap (algebraMap ℤ B) (RingHom.ker ψ.toRingHom) = ⊥
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

theorem comap_ne_bot {R : Type} [CommRing R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (𝔪 : Ideal R)
    [h : 𝔪.IsMaximal] : 𝔪.comap (algebraMap (𝓞 F) R) ≠ ⊥ := by
  intro h0
  letI := Ideal.Quotient.field 𝔪
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : IsJacobsonRing (𝓞 F) := isJacobsonRing_of_isIntegral (R := ℤ)
  haveI : Module.Finite (𝓞 F) (R ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing _ _
  have hinj : Function.Injective (algebraMap (𝓞 F) (R ⧸ 𝔪)) := by
    rw [RingHom.injective_iff_ker_eq_bot, IsScalarTower.algebraMap_eq (𝓞 F) R (R ⧸ 𝔪), ← RingHom.comap_ker,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, h0]
  exact RingOfIntegers.not_isField F
    ((Algebra.IsIntegral.isField_iff_isField hinj).2 (Field.toIsField _))

theorem exists_valuationSubring {R K : Type} [CommRing R] [Field K] (ψ : R →+* K) (𝔪 : Ideal R) [h : 𝔪.IsMaximal]
    (hk : RingHom.ker ψ ≤ 𝔪) : ∃ A : ValuationSubring K, (∀ x, ψ x ∈ A) ∧ ∀ x, A.valuation (ψ x) < 1 ↔ x ∈ 𝔪 := by
  have hs := ψ.rangeRestrict_surjective
  have hc : (𝔪.map ψ.rangeRestrict).comap ψ.rangeRestrict = 𝔪 := by
    rw [Ideal.comap_map_of_surjective _ hs, sup_eq_left, ← RingHom.ker_eq_comap_bot, RingHom.ker_rangeRestrict]
    exact hk
  have hne : 𝔪.map ψ.rangeRestrict ≠ ⊤ := fun ht => h.ne_top (by rw [← hc, ht, Ideal.comap_top])
  obtain ⟨A, hA, hI⟩ := Ideal.image_subset_nonunits_valuationSubring (A := ψ.range) _ hne
  have hm : ∀ x, ψ x ∈ A := fun x => hA ⟨x, rfl⟩
  refine ⟨A, hm, ?_⟩
  let φ : R →+* A := ψ.codRestrict A hm
  have hle : 𝔪 ≤ (IsLocalRing.maximalIdeal A).comap φ := fun x hx => by
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    exact hI ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩
  have he := h.eq_of_le (Ideal.comap_ne_top φ (IsLocalRing.maximalIdeal.isMaximal A).ne_top) hle
  intro x
  rw [he, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

theorem main : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] [CharZero R] (𝔪 : Ideal R), 𝔪.IsMaximal → ∀ g : R, g ≠ 0 → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (φ : R →+* e.O), (∀ a : 𝓞 F, ((φ (algebraMap (𝓞 F) R a) : e.O) : AlgebraicClosure F) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a)) ∧ (IsLocalRing.maximalIdeal e.O).comap φ = 𝔪 ∧ φ g ≠ 0 := by
  intro F _ _ R _ _ _ _ _ 𝔪 h𝔪 g hg
  haveI : Algebra.FiniteType ℤ R := Algebra.FiniteType.trans (S := 𝓞 F) inferInstance inferInstance
  obtain ⟨q, hq, hqm, hgq, hc, ha⟩ := GlobalTheory.exists_horizontal_prime_le_of_isMaximal R 𝔪 h𝔪 g hg
  obtain ⟨ψ₀, hψ₀⟩ := @exists_embed F _ _ (R ⧸ q) _ _ _ hc (by convert ha <;> first | rfl | exact Subsingleton.elim _ _)
  let ψ : R →ₐ[𝓞 F] AlgebraicClosure F := ψ₀.comp (Ideal.Quotient.mkₐ (𝓞 F) q)
  have hker : ∀ x, ψ x = 0 ↔ x ∈ q := fun x => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff ψ₀ hψ₀]
    rfl
  have hψ (a : 𝓞 F) : ψ (algebraMap (𝓞 F) R a) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a) := by
    rw [ψ.commutes, ← IsScalarTower.algebraMap_apply]
  obtain ⟨A, hA, hAm⟩ := exists_valuationSubring ψ.toRingHom 𝔪 (fun x hx => hqm ((hker x).1 hx))
  let v : HeightOneSpectrum (𝓞 F) := ⟨𝔪.comap (algebraMap (𝓞 F) R), inferInstance, comap_ne_bot 𝔪⟩
  obtain ⟨e⟩ := (ExtConj.main F).1 v
  have hov (x : 𝓞 F) : A.valuation (algebraMap F (AlgebraicClosure F) (x : F)) < 1 ↔ x ∈ v.asIdeal := by
    have := hAm (algebraMap (𝓞 F) R x)
    rwa [show ψ.toRingHom (algebraMap (𝓞 F) R x) = _ from hψ x] at this
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_over hov (ExtConj.lies_over e)
  have hm (x : R) : σ (ψ x) ∈ e.O := by
    rw [← hσ]
    exact ValuationSubring.smul_mem_pointwise_smul σ _ A (hA x)
  let φ : R →+* e.O := (σ.toRingEquiv.toRingHom.comp ψ.toRingHom).codRestrict e.O hm
  have hφ (x : R) : (φ x : AlgebraicClosure F) = σ (ψ x) := rfl
  refine ⟨v, e, φ, fun a => ?_, ?_, fun h0 => hgq ?_⟩
  · rw [hφ, hψ, σ.commutes]
  · ext x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, hφ, ← hAm]
    have := ReciprocityTheory.Gal.smul_valuation_lt_one_iff σ A (σ (ψ x))
    rw [hσ] at this
    rw [this]
    simp
  · have := hφ g
    rw [h0] at this
    exact (hker g).1 (by simpa using this.symm)

end GlobalTheory.TrueGeo.HorizRing
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_discreteSeries_formalDegree_product : DiscreteSeriesExist → FormalDegreeFormula₂ → ∀ (cd : CDHaar) (R : Ranks) (P : HCParam R), (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)), IsDS (epsSH R) (lamSH R P) σ ∧ IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ (trueDsig R P)) ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)) (d : ℝ), IsDS (epsSH R) (lamSH R P) σ → IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ d → d = trueDsig R P := by
  first | exact @GlobalTheory.Mem.Vol.exists_isDS_isFdeg_trueDsig | exact GlobalTheory.Mem.Vol.exists_isDS_isFdeg_trueDsig | (intros; apply GlobalTheory.Mem.Vol.exists_isDS_isFdeg_trueDsig <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.holomorphic_family_low_lie_action : ∀ (D : D7) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (ϖ : (D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) → Module.End ℂ P), IsHolFam M.ε B ϖ → ∃ m : LowT M →ₗ[ℂ] Module.End ℂ P, (∀ A : Module.End ℂ P, (∀ k, (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → Commute A (ϖ k)) → ∀ x, Commute A (m x)) ∧ (∀ κ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, κ τ ∈ Formalism.REAL.Kset (M.ε τ)) → ∃ v : ∀ τ, lowT M τ, (∀ τ, v τ ≠ 0) ∧ ∀ y, IsBotFam M.ε ϖ (fun τ => -Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) y → m (PiTensorProduct.tprod ℂ v) y = ϖ (fun τ => (κ τ).map star) y) ∧ ∀ y, IsBotFam M.ε ϖ (fun τ => -Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) y → ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ), ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) → m (PiTensorProduct.tprod ℂ (Function.update v τ u)) y = ϖ (Pi.mulSingle τ (k.map star)) (m (PiTensorProduct.tprod ℂ v) y) := by
  first | exact @GlobalTheory.JointHarm.MultiOp.lowest_types_act | exact GlobalTheory.JointHarm.MultiOp.lowest_types_act | (intros; apply GlobalTheory.JointHarm.MultiOp.lowest_types_act <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical


theorem _root_.GlobalTheory.T.fullFlag_common_closedPoint_of_generic : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (L : Type) [Field L] [Algebra R L] [IsFractionRing R L] (v₁ : Sp R ⟶ Y₁.X) (v₂ : Sp R ⟶ Y₂.X), v₁ ≫ f₁ = v₂ ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap (algebraMap R L) ≫ v₁ ≫ f₁) (spMap (algebraMap R L) ≫ v₁) (spMap (algebraMap R L) ≫ v₂) → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap (IsLocalRing.residue R) ≫ v₁ ≫ f₁) (spMap (IsLocalRing.residue R) ≫ v₁) (spMap (IsLocalRing.residue R) ≫ v₂) := by
  first | exact @GlobalTheory.FlagBundle.coBear_closedPoint | exact GlobalTheory.FlagBundle.coBear_closedPoint | (intros; apply GlobalTheory.FlagBundle.coBear_closedPoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical


theorem _root_.GlobalTheory.T.eq_of_bear_common_fullFlag : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (K : Type) [Field K] (p p' : Sp K ⟶ Y₁.X) (q : Sp K ⟶ Y₂.X), p ≫ f₁ = q ≫ f₂ → p' ≫ f₁ = q ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p q → CoBear Eb S₁ φ₁ S₂ φ₂ (p' ≫ f₁) p' q → p = p' := by
  first | exact @GlobalTheory.FlagBundle.eq_of_coBear | exact GlobalTheory.FlagBundle.eq_of_coBear | (intros; apply GlobalTheory.FlagBundle.eq_of_coBear <;> assumption)
end
