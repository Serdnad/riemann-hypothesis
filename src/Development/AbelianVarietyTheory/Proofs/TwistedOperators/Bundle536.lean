module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle530
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle311
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle251
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle516
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle518
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle113
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle366
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle458
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle515
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle517
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransport
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicStripSetMeasurableReadOnRealPart
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
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows



namespace GlobalTheory.InjEigen

theorem label_eigensystem : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ), ∃ h, GlobalTheory.Hk3.IsOpsV R.toRealDat j A3.A.fam.μ0 h ∧ ∃ e : Eig D, ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c, ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P → GlobalTheory.Hk3.IsLab (Vc D j) P d → h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) = e P d • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hch hex hOk hpg j c
  obtain ⟨h, hops, hnf⟩ :=
    (GlobalTheory.DefiniteOps.definite_ops R.toRealDat F.lv2 hch.base.lev hch.base.fam hch.base.models).2 j A3.A.fam.μ0
  have key : ∀ P d, ∃ a : ℂ, GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P →
      GlobalTheory.Hk3.IsLab (Vc D j) P d → ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
        h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) =
          a • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
    intro P d
    by_cases hg : GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P
    · by_cases hl : GlobalTheory.Hk3.IsLab (Vc D j) P d
      · first
          | exact (Classical.em (Formalism.L2.DIV.conjPl P = P)).elim
              (fun hc => (GlobalTheory.InertEigScalar.inert_label_scalar R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
              (fun hc => (GlobalTheory.SplitEigen.label_scalar_split R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
          | exact (Classical.em (Formalism.DivisionValues.conjPl P = P)).elim
              (fun hc => (GlobalTheory.InertEigScalar.inert_label_scalar R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
              (fun hc => (GlobalTheory.SplitEigen.label_scalar_split R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
      · exact ⟨0, fun _ hl' => absurd hl' hl⟩
    · exact ⟨0, fun hg' => absurd hg' hg⟩
  choose e he using key
  exact ⟨h, hops, e, fun x hx P d hg hl => he P d hg hl x hx⟩

theorem inj_eig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → LiftInj R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (x y : (R.toCx3 F).FLC j A3.A.fam.μ0), x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c → (R.toCx3 F).θ' j A3.A.fam.μ0 x ≠ 0 → y ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c ⊓ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j → (R.toCx3 F).θ' j A3.A.fam.μ0 y = 0 → y = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hch hex hinj hOk hpg j c x y hx hθx hy hθy
  obtain ⟨h, hops, e, he⟩ := label_eigensystem R F hok hch hex hOk hpg j c
  have hy' := Submodule.mem_inf.mp hy
  have hgood := GlobalTheory.goodV_of_goodL R F hok hch hex hOk hpg j y hy'.2
  clear hok hch hex hOk hpg hy
  have hθ : ∀ z : (R.toCx3 F).FLC j A3.A.fam.μ0, (R.toCx3 F).θ' j A3.A.fam.μ0 z =
      R.phs j • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j A3.A.fam.μ0) z := fun z => rfl
  have hp : R.phs j ≠ 0 := by
    intro h0
    apply hθx
    rw [hθ, h0]
    exact zero_smul ℂ _
  have hcj : Formalism.IndefR.Links.cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) ≠ 0 := by
    intro h0
    apply hp
    rw [← Formalism.IndefR.Links.cj_cj (twAt D.what₂.embLL A3.A.v0) (R.phs j), h0, map_zero]
  have hx0 : R.thG j A3.A.fam.μ0 (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) ≠ 0 := by
    intro h0
    apply hθx
    rw [hθ]
    have h1 : Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j A3.A.fam.μ0) x = 0 := h0
    rw [h1]
    first
      | exact smul_zero (M := Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j _).H) (R.phs j)
      | exact smul_zero (M := Tw (twAt D.what₂.embLL A3.A.v0) _) (R.phs j)
      | (simp only [smul_zero]; rfl)
  have hy0 : R.thG j A3.A.fam.μ0 (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) = 0 := by
    have h2 : Formalism.IndefR.Links.cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j A3.A.fam.μ0 (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) = 0 := hθy
    exact (smul_eq_zero.mp h2).resolve_left hcj
  exact hinj j h hops e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) (fun P d hg hl => he x hx P d hg hl)
    (fun P d hg hl => he y hy'.1 P d hg hl) hx0 hgood hy0

end GlobalTheory.InjEigen
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.definiteTopSpace_columnValues : TopCols := by
  first | exact @GlobalTheory.CoreOnto.topCols | exact GlobalTheory.CoreOnto.topCols | (intros; apply GlobalTheory.CoreOnto.topCols <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.dualCoefSpace_isTensorOverRealPlaces : CoefTensor := by
  first | exact @GlobalTheory.CoefTensorProof.coefTensor | exact GlobalTheory.CoefTensorProof.coefTensor | (intros; apply GlobalTheory.CoefTensorProof.coefTensor <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChain_unitVacuum_otherLattices_exists : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ (r : ReLat (G.V (.core i))) (r' : ReLat (G.V (.core (i + 1)))) (S S' : D.what₂.Tau → SPar) (M : DSModel r.sp S) (M' : DSModel r'.sp S'), ∃ f₀, IsVacO W.ψ W.θ r.sp r'.sp (cart M) (cart M') (GlobalTheory.AdelicU.frameLat r.sp : Set _) (GlobalTheory.AdelicU.frameLat r'.sp : Set _) f₀ := by
  first | exact @GlobalTheory.CoreVacRe.vacExists_reLat | exact GlobalTheory.CoreVacRe.vacExists_reLat | (intros; apply GlobalTheory.CoreVacRe.vacExists_reLat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adjointExchange_laws_thetaHeisenberg : ∀ D : D7, ExchLaw D := by
  first | exact @GlobalTheory.ExchPf.exchLaw | exact GlobalTheory.ExchPf.exchLaw | (intros; apply GlobalTheory.ExchPf.exchLaw <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coreChain_realParameters_correspond : ParOK := by
  first | exact @GlobalTheory.CoreOntoPar.parOK_core | exact GlobalTheory.CoreOntoPar.parOK_core | (intros; apply GlobalTheory.CoreOntoPar.parOK_core <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.EvenOnto.parBound_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ParBound D := by
  intro hCRD D c hc j hj s hs u B hB
  obtain ⟨hu0, hpar⟩ := hB
  have hex : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu0
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact h v
  obtain ⟨v, hv⟩ := hex
  set f : GA D s.V → ℂ := fun g => conj (PiLocalization₂.val u v g) with hfdef
  have h3 : GlobalTheory.LFun.IsParamFunV s.V c.S f B := hpar v hv
  obtain ⟨h4a, _⟩ := GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj hCRD D c hc j hj s hs
  obtain ⟨hcont, ⟨C, hC⟩, hinv, hlev, _⟩ := h4a u v
  have hsph : SphOff (s.J : Set (GA D s.V)) 1 c.S := hs.sph
  have hfmem : f ∈ GlobalTheory.FinZeta.bddAut s.V := by
    refine ⟨(Complex.continuous_conj).comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [hfdef, hinv γ hγ g]
    · simpa [hfdef] using hC g
  have hf0 : f ≠ 0 := by
    intro h0
    apply hv
    funext g
    have := congrFun h0 g
    simpa [hfdef] using this
  have hlev' : ∀ k ∈ (s.J : Set (GA D s.V)), ∀ g, f (g * k) = (1 : GA D s.V → ℂ) k * f g := by
    intro k hk g
    simp only [hfdef, hlev k hk g, Pi.one_apply, one_mul]
  obtain ⟨a, ha⟩ := GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params D s.V (s.J : Set (GA D s.V)) 1 c.S hsph B
  obtain ⟨B', hB', hbd⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D s.V _ _ c.S hsph f hfmem hf0 hlev' a (fun P d R hR => ha f h3 P d R hR)
  intro w hw
  rw [GlobalTheory.LFun.IsParamVecOff.unique h3 hB' hw]
  exact hbd w hw
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto

theorem val_hecke_of_mem_partFull_one {D : D7} {c : Com D} {s : PiLocalization₂ D} (u : s.CC c)
    (e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ)
    (hu : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (R : Finset (GA D s.V))
    (hR : Hecke₂ s.V (s.J : Set (GA D s.V)) 1 c.S P d R) (v : SmT s.M) :
    heckeLin s.V R (PiLocalization₂.val u v) = e P d • PiLocalization₂.val u v := by
  have h := ((mem_partFull c.θ s.M _ _ c.S e _).1 hu).2 P d R hR
  have key : heckeLin s.V R ∘ₗ (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = e P d • (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) := by
    apply PiTensorProduct.ext
    ext x
    have := h x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply] at this ⊢
    convert congrFun this _ using 2 <;> simp [PiTensorProduct.lift_symm]
  exact congrFun (congrArg DFunLike.coe key) v |>.trans rfl

theorem partPar : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s => ∀ (u : s.CC c) (e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e → (u ≠ 0 → ∃ B, IsPar u B) ∧ ∀ w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → IsPar u B := by
  intro hP D c hc j hj s hs u e hu
  obtain ⟨hval, hconj⟩ := GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj hP D c hc j hj s hs
  have hsph : SphOff (s.J : Set (GA D s.V)) 1 c.S := hs.sph
  have hlev : ∀ v, ∀ k ∈ (s.J : Set (GA D s.V)), ∀ g, (fun g => conj (PiLocalization₂.val u v g)) (g * k) =
      (1 : GA D s.V → ℂ) k * (fun g => conj (PiLocalization₂.val u v g)) g := by
    intro v k hk g
    simp only [(hval u v).2.2.2.1 k hk g, Pi.one_apply, one_mul]
  have hhk : ∀ v P d R, Hecke₂ s.V (s.J : Set (GA D s.V)) 1 c.S P d R →
      heckeLin s.V R (fun g => conj (PiLocalization₂.val u v g)) = (fun P d => conj (e P d)) P d • (fun g => conj (PiLocalization₂.val u v g)) := by
    intro v P d R hR
    rw [hconj, val_hecke_of_mem_partFull_one u e hu P d R hR v]
    funext g
    simp [map_mul]
  have hne : ∀ v, PiLocalization₂.val u v ≠ 0 → (fun g => conj (PiLocalization₂.val u v g)) ≠ 0 := by
    intro v h0 h
    apply h0
    funext g
    simpa using congrFun h g
  have hiff : ∀ v B, PiLocalization₂.val u v ≠ 0 →
      (ParFun c s (PiLocalization₂.val u v) B ↔ GlobalTheory.LFun.IsSysParamD D c.S s.V.rank (fun P d => conj (e P d)) B) := by
    intro v B h0
    exact GlobalTheory.LFun.isParamFunV_iff_isSysParamD_of_level hsph (hne v h0) (hlev v) (hhk v) B
  have second : ∀ w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → IsPar u B := by
    intro w B hw hB
    refine ⟨?_, fun v hv => (hiff v B hv).2 ((hiff w B hw).1 hB)⟩
    rintro rfl
    exact hw (by simp [PiLocalization₂.val])
  refine ⟨fun hu0 => ?_, second⟩
  have hu1 : (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ≠ 0 := fun h => hu0 (Subtype.ext h)
  obtain ⟨v, hv⟩ : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hu1 (LinearMap.ext hh)
  obtain ⟨C, hC⟩ := (hval u v).2.1
  have hbdd : (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.FinZeta.bddAut s.V := by
    refine ⟨(Complex.continuous_conj.comp (hval u v).1), fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [(hval u v).2.2.1 γ hγ g]
    · simpa using hC g
  obtain ⟨B, hB, -⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D s.V (s.J : Set (GA D s.V)) 1 c.S hsph
    _ hbdd (hne v hv) (hlev v) (fun P d => conj (e P d)) (hhk v)
  have hpf : ParFun c s (PiLocalization₂.val u v) B := hB
  exact ⟨B, second v B hv hpf⟩

end GlobalTheory.EvenOnto
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainStage_cartanFrame_conj_values_cuspForms : ∀ D : D7, ForStage D fun c _ s => ∃ (cA : GlobalTheory.Mem.Th.CptF s.V) (a : GL (Fin s.V.rank) (AE D)), GlobalTheory.Cusp.IsCartanFrame s.V cA ∧ (∀ τ, IsCartanInv (gramAt D s.V τ) (cart s.M τ)) ∧ (∀ τ, cA τ * cart s.M τ = Formalism.UG.Jpq (s.V.sig (tauE D τ)).1 (s.V.sig (tauE D τ)).2 * cA τ) ∧ GlobalTheory.Doubling.IsMaj s.V a ∧ (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) ∧ ∀ (u : s.CC c), ∀ v ∈ s.KF, (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := by
  first | exact @GlobalTheory.EvenOnto.conj_stage_val_mem_A0_and_cartan_frame | exact GlobalTheory.EvenOnto.conj_stage_val_mem_A0_and_cartan_frame | (intros; apply GlobalTheory.EvenOnto.conj_stage_val_mem_A0_and_cartan_frame <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaRowGrid_bottom_selfDual_lattices : All fun {D} _ {L} _ {G} _ _ => IsSelfDualC (Yc D 0) (L.ΛY 0) ∧ IsSelfDualC (G.V (.core 0)) (G.Λ (.core 0)) ∧ G.Λ (.core 0) = G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) ∧ zv G.sp.dec0 ∈ G.Λ (.core 0) ∧ (∀ k ∈ GfC (Yc D 0), Lev.finE (G.V (.core 0)) (stabilizerEmbedding G.sp.dec0 k) ∈ G.levCong (.core 0) → k ∈ levRow L) ∧ (Yc D 0).rank = D.R.r ∧ (G.V (.core 0)).rank = D.R.r + 1 ∧ ∀ (A : Fr (Yc D 0)) τ, (Finset.univ.filter fun a => A.ε τ a = false).card ≤ D.R.m := by
  first | exact @GlobalTheory.BottomGrid.bottom | exact GlobalTheory.BottomGrid.bottom | (intros; apply GlobalTheory.BottomGrid.bottom <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelSum

theorem sum_ker_eq_card_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : Sp Ω ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (p n : ℕ) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ ((p : ℤ) ^ 2))) (s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))) (e : Fin n ≃ transKer Xo.univ.t.G Ψ), IsHeckeIsog p (transKer Xo.univ.t.G Ψ) Ψ → IsThGen x' s' → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ p s s' → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ _ β → IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ → ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → (Nat.card {a : Over.mk x ⟶ Xo.univ.t.G // a ∈ transKer Xo.univ.t.G Ψ ∧ a ^ p = 1} : Z.presheaf.stalk z) * sv Xo.univ.t.G Xo.univ.t.PP s' (r ≫ Ψ) z J = ∑ j, ((val β (r ≫ (translT Xo.univ.t.G (e j).1).left) z J)⁻¹).val * sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ (translT Xo.univ.t.G (e j).1).left) z J := by
  intro E _ _ _ H Dw l Xo Ω _ _ x x' Ψ p n s s' β s₁ e hΨ _ hs' hβ hs Z r z J hJ
  have hG := abelianSchemeLaws_all.1.globalFns
  have hA := GlobalTheory.HeckePoint.isAbelianScheme_of_proper Xo.univ.t Xo.univ.proper
  obtain ⟨β', s₂, n', c, hβ', hs₂, hc, hv⟩ := isThetaTrace_iff.1 hs'
  obtain rfl := hs.unique hG hA hs₂
  have hst : ∀ a ∈ transKer Xo.univ.t.G Ψ, a ≫ Xo.univ.t.act.act H.w0 ∈ transKer Xo.univ.t.G Ψ := by
    intro a ha
    have := Xo.univ.t.act.hom H.w0
    refine (hΨ.2.2.2.1 _).1 ?_
    have h1 : (lift (𝟙 (Over.mk x)) a).left ≫ Ψ =
        (lift (𝟙 (Over.mk x')) (1 : Over.mk x' ⟶ Xo.univ.t.G)).left := (hΨ.2.2.2.1 a).2 ha
    show (lift (𝟙 (Over.mk x)) (a ≫ Xo.univ.t.act.act H.w0)).left ≫ Ψ =
      (lift (𝟙 (Over.mk x')) (1 : Over.mk x' ⟶ Xo.univ.t.G)).left
    rw [← lift_whiskerLeft, Over.comp_left, Category.assoc, hΨ.2.1.2.2 H.w0, reassoc_of% h1, ← Over.comp_left,
      lift_whiskerLeft, MonObj.one_comp]
  let Φ : (Over.mk x ⟶ Xo.univ.t.G) → Z.presheaf.stalk z := fun b =>
    ((val β (r ≫ (translT Xo.univ.t.G b).left) z J)⁻¹).val *
      sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ (translT Xo.univ.t.G b).left) z J
  have hΦ : ∀ a ∈ transKer Xo.univ.t.G Ψ, a ^ p = 1 → ∀ b, Φ (a * b) = Φ b := fun a ha hp b =>
    GlobalTheory.ThetaTransport.term_transl hΨ.2.1 hβ.2.1 hs hst r z hJ a ha hp b
  have h1 : sv Xo.univ.t.G Xo.univ.t.PP s' (r ≫ Ψ) z J = ∑ i, Φ (c i) :=
    (hv Z r z J hJ).trans (Finset.sum_congr rfl fun i _ => by
      simp only [Φ]; rw [hβ'.val_unique hG hA hβ _ z hJ])
  have : Finite (transKer Xo.univ.t.G Ψ) := Finite.of_equiv _ e
  letI := Fintype.ofFinite (transKer Xo.univ.t.G Ψ)
  let T := {a : Over.mk x ⟶ Xo.univ.t.G // a ∈ transKer Xo.univ.t.G Ψ ∧ a ^ p = 1}
  have : Finite T := Finite.of_injective (fun q : T => (⟨q.1, q.2.1⟩ : transKer Xo.univ.t.G Ψ))
    (fun a b h => Subtype.ext (congrArg (fun q : transKer Xo.univ.t.G Ψ => q.1) h))
  letI := Fintype.ofFinite T
  have bij : Function.Bijective fun q : T × Fin n' =>
      (⟨q.1.1 * c q.2, (transKer Xo.univ.t.G Ψ).mul_mem q.1.2.1 (hc.1 _)⟩ : transKer Xo.univ.t.G Ψ) := by
    constructor
    · rintro ⟨a, i⟩ ⟨b, j⟩ h
      have h' : a.1 * c i = b.1 * c j := congrArg Subtype.val h
      obtain rfl : i = j := (hc.2 _ ((transKer Xo.univ.t.G Ψ).mul_mem a.2.1 (hc.1 i))).unique
        (by simpa using a.2.2) (by rw [h']; simpa using b.2.2)
      exact Prod.ext (Subtype.ext (mul_right_cancel h')) rfl
    · intro d
      obtain ⟨i, hi, -⟩ := hc.2 d d.2
      exact ⟨(⟨d * (c i)⁻¹, (transKer Xo.univ.t.G Ψ).mul_mem d.2 ((transKer Xo.univ.t.G Ψ).inv_mem (hc.1 i)), hi⟩, i),
        Subtype.ext (by simp)⟩
  have h2 : ∑ j, Φ (e j).1 = ∑ d : transKer Xo.univ.t.G Ψ, Φ d.1 := Equiv.sum_comp e (fun d => Φ d.1)
  have h3 : ∑ d : transKer Xo.univ.t.G Ψ, Φ d.1 = ∑ q : T × Fin n', Φ (q.1.1 * c q.2) :=
    (Fintype.sum_bijective _ bij _ _ fun q => rfl).symm
  have h4 : ∑ q : T × Fin n', Φ (q.1.1 * c q.2) = ∑ q : T × Fin n', Φ (c q.2) :=
    Finset.sum_congr rfl fun q _ => hΦ _ q.1.2.1 q.1.2.2 _
  show _ = ∑ j, Φ (e j).1
  rw [h2, h3, h4, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [h1, Nat.card_eq_fintype_card]

end GlobalTheory.KernelSum
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.adelicStripSet_measurable_read_on_realPart : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ C : Set (GA D W), IsCompact C → C ⊆ GinfC W → MeasurableSet (strip W (Rgrp W (rat x₀)) C) ∧ ∃ S : Set (Mx D W.rank ρ), MeasurableSet S ∧ (∀ z z' : Mx D W.rank ρ, z.map (infPart D) = z'.map (infPart D) → (z ∈ S ↔ z' ∈ S)) ∧ ∀ (h : GA D W) (u : UX D ρ), mt W h⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1) ∈ S ↔ h ∈ strip W (Rgrp W (rat x₀)) C := by
  first | exact @GlobalTheory.StripBorel.strip_measurable | exact GlobalTheory.StripBorel.strip_measurable | (intros; apply GlobalTheory.StripBorel.strip_measurable <;> assumption)
end
