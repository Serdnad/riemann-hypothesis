module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle452
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle240
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle522
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle462
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle439
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle573
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle323
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle043
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle859
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

namespace GlobalTheory.ConjHalfVac

theorem sum_conj_half_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ Y : Finset (WO V W), (∀ y ∈ Y, IsHalf (cA D eT) y) → IsThetaFunO ψ V W (∑ y ∈ Y, heisO ψ V W y f₀) ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW τ)) (∑ y ∈ Y, heisO ψ V W y f₀) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT _ _ _ Y hY
  obtain ⟨hpair, _, _, _, _, _, _, _, hvac⟩ := hP
  have hstd : IsStdChar D ψ (-1) := hvac.1
  have hth0 : IsThetaFunO ψ V W f₀ := GlobalTheory.OneMapRef.isThetaFunO_of_isVacO hvac
  have hinf : infPart D (cA D eT) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hT)
  have hfin : ∀ y ∈ Y, map y ⇑(infPart D) = 0 := fun y hy =>
    GlobalTheory.DatumFock.infPart_of_isHalf hinf (hY y hy)
  refine ⟨?_, fun τ => ?_⟩
  · classical
    induction Y using Finset.induction_on with
    | empty => simpa using GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := V) (T := W)
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact GlobalTheory.OrientedHeis.theta_add
        (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hth0 a)
        (ih (fun y hy => hY y (Finset.mem_insert_of_mem hy)) (fun y hy => hfin y (Finset.mem_insert_of_mem hy)))
  · have hF : IsFockVacAt (heisO ψ V W) θ τ (cplxO (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW τ)) f₀ :=
      hvac.2.fock τ
    have := GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ V W hstd.1 hpair.inf f₀ hth0 τ _ hF
      (WO V W) Y id (fun _ => 1) (fun y hy => hfin y hy)
    simpa using this

end GlobalTheory.ConjHalfVac
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.TargetUnipMean

open GlobalTheory.MixModel (rat)
open scoped GlobalTheory.MixModel

variable {D : D7}

theorem exists_split (W : HSp D) {s : ℕ} (I : Matrix (Fin W.rank) (Fin s) D.host.E) (hI : IsIsoFrame W I) :
    ∃ (W' : HSp D) (ι : W'.V →ₗ[D.host.E] W.V), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit W W' I (frameMat W W' ι) := by
  obtain ⟨e, rfl⟩ := GlobalTheory.BesselCompare.eMat_surj W I
  have he : LinearIndependent D.host.E e :=
    LinearIndependent.of_comp W.frame.equivFun.toLinearMap hI.2.1
  have hiso : ∀ a b, W.hT (e a) (e b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hI.2.2]; rfl
  obtain ⟨W', ι, h1, h2, h3⟩ := GlobalTheory.WittLow.exists_lower Examples₂.star_isIntegral W e he hiso
  refine ⟨W', ι, ⟨hI, ?_, ?_, by omega⟩⟩
  · refine Matrix.ext fun a b => ?_
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]
    exact h2 _ _
  · refine Matrix.ext fun a b => ?_
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul, ← W.herm.eq, h3]
    simp

theorem decomp {W W' : HSp D} {s k : ℕ} {I : Matrix (Fin W.rank) (Fin s) D.host.E}
    {B : Matrix (Fin W.rank) (Fin W'.rank) D.host.E} (hsp : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit W W' I B) (x : Mx D W.rank k)
    (hx : rat (Iᴴ * W.gram) ⬝ x = 0) : ∃ (z : Mx D s k) (w : Mx D W'.rank k), x = rat I ⬝ z + rat B ⬝ w := by
  obtain ⟨d, hde, hdi, -⟩ := GlobalTheory.WittSect.exists_hypDec_mem_NI D W W' s I B hsp
  have h := d.sum_eq_one_rat
  simp only [GlobalTheory.MixModel.HypDec.qX, GlobalTheory.MixModel.HypDec.qY, GlobalTheory.MixModel.HypDec.q0, hde, hdi] at h
  have h1 : rat (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E) ⬝ x = x := by
    rw [GlobalTheory.MixModel.rat_one, Matrix.one_mul]
  rw [← h, GlobalTheory.MixModel.rat_add, GlobalTheory.MixModel.rat_add, Matrix.add_mul, Matrix.add_mul] at h1
  have h2 : rat (d.e' * (Iᴴ * W.gram)) ⬝ x = 0 := by
    rw [GlobalTheory.MixModel.rat_mul, Matrix.mul_assoc, hx, Matrix.mul_zero]
  rw [h2, add_zero] at h1
  rw [GlobalTheory.MixModel.rat_mul I, GlobalTheory.MixModel.rat_mul B, Matrix.mul_assoc (rat I), Matrix.mul_assoc (rat B)] at h1
  exact ⟨_, _, h1.symm⟩

theorem periodic {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {g : WO V W → ℂ} (hg : IsThetaFunO ψ V W g) {s : ℕ}
    (I : Matrix (Fin W.rank) (Fin s) D.host.E) (p : WO V W) (hp : rat (Iᴴ * W.gram) ⬝ p = 0)
    (γ : Matrix (Fin s) (Fin V.rank) D.host.E) : g (rat I ⬝ rat γ + p) = g p := by
  have e1 : rat I ⬝ rat γ = ratW W V (I * γ) := by rw [GlobalTheory.MixModel.ratW_eq, GlobalTheory.MixModel.rat_mul]
  have e2 : GlobalTheory.MixModel.adj p ⬝ rat (W.gram * I) = 0 := by
    have := congrArg GlobalTheory.MixModel.adj hp
    rwa [GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_zero, ← GlobalTheory.MixModel.rat_conjTranspose, conjTranspose_mul,
      GlobalTheory.MixModel.gram_conjTranspose, conjTranspose_conjTranspose] at this
  have e3 : GlobalTheory.MixModel.adj p ⬝ (GlobalTheory.MixModel.gA W ⬝ ratW W V (I * γ)) = 0 := by
    have e2' : GlobalTheory.MixModel.adj p ⬝ (rat W.gram ⬝ rat I) = 0 := by rw [← GlobalTheory.MixModel.rat_mul]; exact e2
    rw [GlobalTheory.MixModel.ratW_eq, GlobalTheory.MixModel.gA, GlobalTheory.MixModel.rat_mul I γ, ← Matrix.mul_assoc (rat W.gram) (rat I) (rat γ),
      ← Matrix.mul_assoc, e2', Matrix.zero_mul]
  rw [e1, hg.quasi, GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, e3, Matrix.mul_zero, Matrix.trace_zero,
    map_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.TargetUnipMean

namespace GlobalTheory.TargetUnipMean

open GlobalTheory.MixModel (rat)
open scoped GlobalTheory.MixModel

theorem mean_unip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → ∀ (ν : Measure (Mx D s V.rank)) (𝓨 : Set (Mx D s V.rank)), IsCovolOne (GlobalTheory.MixModel.ratMx D s V.rank) ν 𝓨 → ∀ n ∈ NI W I, ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ∀ x : WO V W, HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram).map (incA D)) x = (0 : Mx D s V.rank) → ∫ y in 𝓨, om (1, n) f (HMul.hMul (I.map (incA D)) y + x) ∂ν = ∫ y in 𝓨, f (HMul.hMul (I.map (incA D)) y + x) ∂ν := by
  intro D ψ V W χV χW om hom s I hI ν 𝓨 hν n hn f hf x hx
  obtain ⟨W', ι, hsp⟩ := exists_split W I hI
  obtain ⟨omt, hmt, hsw⟩ := GlobalTheory.T.exists_conj_weilDatum_exchangedPair D ψ V W χV χW om hom
  obtain ⟨μ', 𝓖', hμ', he⟩ := (GlobalTheory.T.weilConstantTerm_source_target_conjAdjoint_corr D V W W' s ι I).1 ν 𝓨 hν
  have hlaw := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hom.std V W'
  have hlawW := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hom.std V W
  have hr : GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 (om (1, n) f) = GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 f := by
    have h1 := GlobalTheory.UnipRes.res_unip D W W' V s I (frameMat W W' ι) hsp ψ χW χV omt hmt μ' 𝓖' hμ' ⟨n, hn⟩
      (GlobalTheory.PairLift.dag V W f) (hlawW.theta f hf)
    have h2 : GlobalTheory.PairLift.dag V W' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 (om (1, n) f)) =
        GlobalTheory.PairLift.dag V W' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 f) := by
      rw [← he, ← he, ← hsw]
      exact h1
    funext w
    have h3 := congrFun h2 (GlobalTheory.PairLift.adjO W' V w)
    simp only [GlobalTheory.PairLift.dag, hlaw.invol] at h3
    exact (starRingEnd ℂ).injective h3
  have hII : Iᴴ * W.gram * I = 0 := hI.2.2
  have hIB : Iᴴ * W.gram * frameMat W W' ι = 0 := hsp.orth
  obtain ⟨z, w, hz⟩ := decomp hsp x hx
  have hred : ∀ g, IsThetaFunO ψ V W g → ∫ y in 𝓨, g (HMul.hMul (I.map (incA D)) y + x) ∂ν =
      GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 g w := by
    intro g hg
    have hper : ∀ γ ∈ GlobalTheory.MixModel.ratMx D s V.rank, ∀ a : Mx D s V.rank,
        g (rat I ⬝ (γ + a) + rat (frameMat W W' ι) ⬝ w) = g (rat I ⬝ a + rat (frameMat W W' ι) ⬝ w) := by
      intro γ hγ a
      obtain ⟨γ0, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hγ
      rw [Matrix.mul_add, add_assoc]
      refine periodic hg I _ ?_ γ0
      rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul, hII,
        hIB, GlobalTheory.MixModel.rat_zero, GlobalTheory.MixModel.rat_zero, Matrix.zero_mul, Matrix.zero_mul, add_zero]
    have := GlobalTheory.MixModel.covolOne_integral_add hν (fun a => g (rat I ⬝ a + rat (frameMat W W' ι) ⬝ w)) hper z
    rw [hz]
    calc ∫ y in 𝓨, g (HMul.hMul (I.map (incA D)) y + (rat I ⬝ z + rat (frameMat W W' ι) ⬝ w)) ∂ν
        = ∫ y in 𝓨, g (rat I ⬝ (y + z) + rat (frameMat W W' ι) ⬝ w) ∂ν := by
          congr 1
          funext y
          show g (rat I ⬝ y + _) = _
          rw [Matrix.mul_add, add_assoc]
      _ = _ := this
  rw [hred (om (1, n) f) (hom.om_pres (1, n) f hf), hred f hf, hr]

end GlobalTheory.TargetUnipMean
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead



namespace GlobalTheory.MtRead.Red

section General

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem ALint_eq : ReciprocityTheory.Aut.ALint L = Formalism.L2.Herm.intAf (maximalRealSubfield L) L := by
  apply le_antisymm
  · refine Subring.closure_le.2 ?_
    rintro z (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨(y : L), ⟨y, rfl⟩⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  · refine Subring.closure_le.2 ?_
    rintro x (⟨⟨_, y, rfl⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨y, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨c, hc, rfl⟩)

theorem proj_tmul_one (s : ReciprocityTheory.Aut.SplitPlace L) (y : L) :
    s.proj (y ⊗ₜ[maximalRealSubfield L] (1 : ReciprocityTheory.Aut.AFplus L)) = s.i y := by
  simp [ReciprocityTheory.Aut.SplitPlace.proj, Algebra.TensorProduct.lift_tmul]

theorem proj_mem (s : ReciprocityTheory.Aut.SplitPlace L) {z : ReciprocityTheory.Aut.AL L} (hz : z ∈ ReciprocityTheory.Aut.ALint L) :
    s.proj z ∈ s.v.adicCompletionIntegers (maximalRealSubfield L) := by
  have hle : ReciprocityTheory.Aut.ALint L ≤ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring.comap s.proj := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨y, rfl⟩ | ⟨c, hc, rfl⟩)
    · show s.proj _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield L)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, proj_tmul_one]
      exact s.split_le_one y
    · show s.proj _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield L)
      simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
        map_one, one_mul]
      exact hc s.v
  exact hle hz

theorem proj_lt_one (s : ReciprocityTheory.Aut.SplitPlace L) (z : Formalism.L2.Herm.intAf (maximalRealSubfield L) L)
    (hz : z ∈ Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal) :
    Valued.v (s.proj (z : ReciprocityTheory.Aut.AL L)) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Formalism.L2.DIV.oToS_coe, proj_tmul_one]
    exact hy
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add (f := _)]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul c x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    have hc : Valued.v (s.proj (c : ReciprocityTheory.Aut.AL L)) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (proj_mem s ((ALint_eq (L := L)).ge c.2))
    calc Valued.v (s.proj (c : ReciprocityTheory.Aut.AL L)) * Valued.v (s.proj (x : ReciprocityTheory.Aut.AL L))
        ≤ 1 * Valued.v (s.proj (x : ReciprocityTheory.Aut.AL L)) := by gcongr
      _ < 1 := by rwa [one_mul]

theorem resS_iff (s : ReciprocityTheory.Aut.SplitPlace L) (z : Formalism.L2.Herm.intAf (maximalRealSubfield L) L) (u : 𝓞 L) :
    Valued.v (s.i (u : L) - s.proj (z : ReciprocityTheory.Aut.AL L)) < 1 ↔
      Formalism.L2.DIV.resS (maximalRealSubfield L) s.w z = Ideal.Quotient.mk s.w.asIdeal u := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Formalism.L2.DIV.resS (maximalRealSubfield L) s.w z)
  have e1 : Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal (Formalism.L2.DIV.resS (maximalRealSubfield L) s.w z) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal) z :=
    (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := maximalRealSubfield L) s.w.asIdeal s.w.ne_bot)).apply_symm_apply _
  have e2 : Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal (Ideal.Quotient.mk s.w.asIdeal b) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal) (Formalism.L2.DIV.oToS (maximalRealSubfield L) L b) :=
    Ideal.quotientMap_mk
  have hmem : z - Formalism.L2.DIV.oToS (maximalRealSubfield L) L b ∈ Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal := by
    refine Ideal.Quotient.eq.1 ?_
    exact e1.symm.trans ((congrArg (Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal) hb.symm).trans e2)
  have h1 : Valued.v (s.proj (z : ReciprocityTheory.Aut.AL L) - s.i (algebraMap (𝓞 L) L b)) < 1 := by
    have := proj_lt_one s _ hmem
    rwa [AddSubgroupClass.coe_sub, map_sub, Formalism.L2.DIV.oToS_coe, proj_tmul_one] at this
  rw [← hb, eq_comm (a := Ideal.Quotient.mk s.w.asIdeal b), Ideal.Quotient.eq]
  show _ ↔ Valued.v (s.i ((u - b : 𝓞 L) : L)) < 1
  have e : s.i ((u - b : 𝓞 L) : L) =
      (s.i (u : L) - s.proj (z : ReciprocityTheory.Aut.AL L)) + (s.proj (z : ReciprocityTheory.Aut.AL L) - s.i (algebraMap (𝓞 L) L b)) := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_sub]
    ring
  constructor
  · intro h
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h h1)
  · intro h
    rw [← sub_eq_iff_eq_add] at e
    rw [← e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h h1)

def castE {F : Subfield L} (h : F = maximalRealSubfield L) :
    ReciprocityTheory.Aut.AL L ≃+* L ⊗[F] FiniteAdeleRing (𝓞 F) F :=
  (GlobalTheory.Mem.R3.swapCast h).symm.trans (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) L).toRingEquiv

theorem castE_rfl (x : ReciprocityTheory.Aut.AL L) : castE (L := L) rfl x = x :=
  (Algebra.TensorProduct.comm (maximalRealSubfield L) (ReciprocityTheory.Aut.AFplus L) L).apply_symm_apply x

theorem castE_mem_iff {F : Subfield L} (h : F = maximalRealSubfield L) (x : ReciprocityTheory.Aut.AL L) :
    castE h x ∈ Formalism.L2.Herm.intAf F L ↔ x ∈ ReciprocityTheory.Aut.ALint L := by
  subst h
  rw [castE_rfl, ALint_eq]

theorem resS_castE_iff {F : Subfield L} (h : F = maximalRealSubfield L) (s : ReciprocityTheory.Aut.SplitPlace L) (x : ReciprocityTheory.Aut.AL L)
    (z : Formalism.L2.Herm.intAf F L) (hz : (z : L ⊗[F] FiniteAdeleRing (𝓞 F) F) = castE h x) (u : 𝓞 L) :
    Valued.v (s.i (u : L) - s.proj x) < 1 ↔ Formalism.L2.DIV.resS F s.w z = Ideal.Quotient.mk s.w.asIdeal u := by
  subst h
  rw [castE_rfl] at hz
  rw [← hz]
  exact resS_iff s z u

end General

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}

theorem frGL_one_val (y : GL (Fin m) (Formalism.L2.Herm.intAf F E)) (a c : Fin m) :
    (frGL (1 : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) y).val a c = (y.val a c : E ⊗[F] Formalism.L2.Herm.Af F) := by
  have h : frGL (1 : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) y = intGL F E m y := by
    simp [frGL]
  rw [h]
  rfl

theorem mem_St_one (g : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) (h : ∀ a c, g.val a c ∈ Formalism.L2.Herm.intAf F E)
    (h' : ∀ a c, (g⁻¹).val a c ∈ Formalism.L2.Herm.intAf F E) : g ∈ St (1 : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  have inj : Function.Injective ((Formalism.L2.Herm.intAf F E).subtype.mapMatrix (m := Fin m)) :=
    fun x y hxy => Matrix.ext fun a c => Subtype.ext (congrFun (congrFun hxy a) c)
  refine ⟨⟨Matrix.of fun a c => ⟨_, h a c⟩, Matrix.of fun a c => ⟨_, h' a c⟩, inj ?_, inj ?_⟩, ?_⟩
  · rw [map_mul, map_one]
    exact g.mul_inv
  · rw [map_mul, map_one]
    exact g.inv_mul
  · refine Units.ext (Matrix.ext fun a c => ?_)
    rw [frGL_one_val]
    rfl

end Stab

theorem red_eq_local : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n), IdFrame hF P → ∀ (hn : V.rank = n) (κ : GAf D.host.E n), (κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔ Lev.finE V (P.ψ κ) ∈ St (1 : GL (Fin V.rank) (Lev.EAf D))) ∧ ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, κ ∈ ReciprocityTheory.Aut.Umax D.host.E n → ∀ a c : Fin V.rank, NX.locM s κ (Fin.cast hn a) (Fin.cast hn c) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) ∧ ∀ u : 𝓞 D.host.E, Valued.v (s.i (u : D.host.E) - NX.locM s κ (Fin.cast hn a) (Fin.cast hn c)) < 1 ↔ (redFn (1 : GL (Fin V.rank) (Lev.EAf D)) s.w (Lev.finE V (P.ψ κ))).val a c = Ideal.Quotient.mk s.w.asIdeal u := by
  intro D V n hF P hP hn κ
  obtain ⟨hn', hP⟩ := hP
  have ent : ∀ (κ : GAf D.host.E n) a c, (Lev.finE V (P.ψ κ)).val a c =
      castE hF ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn c)) := fun κ a c =>
    congrArg (Lev.swapAE D) (hP κ a c)
  have toSt : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n → Lev.finE V (P.ψ κ) ∈ St (1 : GL (Fin V.rank) (Lev.EAf D)) := fun hκ => by
    refine mem_St_one _ (fun a c => ?_) (fun a c => ?_)
    · rw [ent]
      exact (castE_mem_iff hF _).2 (hκ _ _)
    · rw [← map_inv, ← map_inv, ent]
      exact (castE_mem_iff hF _).2 (Subgroup.inv_mem _ hκ _ _)
  refine ⟨⟨toSt, ?_⟩, fun s hκ a c => ⟨proj_mem s (hκ _ _), fun u => ?_⟩⟩
  · rintro ⟨y, hy⟩ i j
    have h1 := ent κ (Fin.cast hn.symm i) (Fin.cast hn.symm j)
    rw [← hy, frGL_one_val] at h1
    exact (castE_mem_iff hF _).1 (h1 ▸ (y.val _ _).2)
  · obtain ⟨y, hy⟩ := toSt hκ
    have h1 := ent κ a c
    rw [← hy, frGL_one_val] at h1
    rw [← hy, redFn_frGL]
    exact resS_castE_iff hF s _ (y.val a c) h1 u

end GlobalTheory.MtRead.Red

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead



noncomputable section

namespace GlobalTheory.MtRead.IdFrameStd

variable {D : D7}


open GlobalTheory.StdFrameExist in
theorem exists_idFrame_of (hF : D.host.F = maximalRealSubfield D.host.E) (V : HSp D) (hg : V.gram = 1)
    (hV : Seed.FrmC.StdLat V) (n : ℕ) (hn : V.rank = n) :
    ∃ P : principalLevelFrame.RowPsi V n, IdFrame hF P ∧ GlobalTheory.Mem.R3.StdFrame hF P := by
  subst hn
  have hO : IsOrthF V (1 : GL (Fin V.rank) (Lev.EAf D)) := by
    show Formalism.UG.cT (sgA D) (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) * gA V * 1 = 1
    have : gA V = 1 := by
      show V.gram.map _ = 1
      rw [hg]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [this, Formalism.UG.cT_one, Matrix.mul_one, Matrix.mul_one]
  have hI : IntM (SI D) ((1 : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) := fun i j => by
    rw [Units.val_one, Matrix.one_apply]
    split_ifs
    · exact (SI D).one_mem
    · exact (SI D).zero_mem
  refine ⟨rowPsi V 1 hO, ⟨rfl, fun κ a b => ?_⟩, stdFrame_rowPsi hF hV hO hI (by rw [inv_one]; exact hI)⟩
  rw [← GlobalTheory.HeckeTrans.finE_unswap]
  show (Formalism.IndefR.Lev.finE V (psiF V 1 hO κ)).1.map _ a b = _
  rw [finE_psiF, inv_one, mul_one, one_mul]
  rfl

theorem exists_idFrame : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (j : Fin D.R.m), FWT.VStd D j →
    ∃ P : principalLevelFrame.RowPsi (Vc D j) D.R.nV, IdFrame hF P ∧ GlobalTheory.Mem.R3.StdFrame hF P := by
  intro D hF j hV
  have hL := (GlobalTheory.Equiv.StdSpace.lattice_clause_iff (Vc D j)).1 hV.2
  have hS : Seed.FrmC.StdLat (Vc D j) := fun x => by
    rw [hL]
    exact forall_congr' fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).symm
  exact exists_idFrame_of hF (Vc D j) hV.1 hS D.R.nV (GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne.rank_Vc j).1

end GlobalTheory.MtRead.IdFrameStd

end
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.StdAtPrime

theorem bnd_of_integral_over_prime : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)), (∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal → ∀ i j, Valued.v ((A i j) Q) ≤ 1) → GlobalTheory.StdAtPrime.Bnd p A := by
  intro E _ _ p hp n A hA
  let S : Set (HeightOneSpectrum (𝓞 E)) := {Q | ∃ i j, ¬ Valued.v ((A i j) Q) ≤ 1}
  have hS : S.Finite := by
    have hsub : S ⊆ ⋃ i, ⋃ j, {Q | ¬ (A i j) Q ∈ Q.adicCompletionIntegers E} := by
      rintro Q ⟨i, j, h⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨i, j, fun hm => h ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hm)⟩
    refine Set.Finite.subset (Set.finite_iUnion fun i => Set.finite_iUnion fun j => ?_) hsub
    exact Filter.eventually_cofinite.mp (A i j).2
  refine bnd_of_local p n A S hS (fun Q hQ i j => ?_) (fun Q hQ i j => ?_)
  · have hpQ : (p : 𝓞 E) ∉ Q.asIdeal := by
      obtain ⟨i', j', h⟩ := hQ
      exact fun hm => h (hA Q hm i' j')
    exact exists_coprime_natCast_mul_v_le_one p hp Q hpQ _
  · by_contra h
    exact hQ ⟨i, j, h⟩

end GlobalTheory.StdAtPrime
end
