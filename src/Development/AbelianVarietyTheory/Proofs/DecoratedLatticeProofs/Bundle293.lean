module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle276
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle287
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle282
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle283
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle244
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle285
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsOfPartHavePartParamsFirstChainMember
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle226
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle284
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle254
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm

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
open GlobalTheory.Core.Rk.SumBox

noncomputable section

namespace GlobalTheory.Core.Rk.SumBox

theorem frameLat_selfDual {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V :=
    Submodule.ext fun y => (mem_frameLat V y).trans (GlobalTheory.PlaceModel.mem_latFrame V y).symm
  rw [h]
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem box_sum_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B W H : HSp D) (o : OrthDec B W H) (sA : RealMat A) (sW : RealMat W) (sH : RealMat H), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → ∃ (sB : RealMat B) (LB : Lat B), (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) ∧ IsSelfDualC B LB ∧ (∀ Φ Φ', IsFockVec ψ θ A W sA sW Φ → IsFockVec ψ θ A H sA sH Φ' → IsFockVec ψ θ A B sA sB (o.boxT A Φ Φ')) ∧ ∀ (LA : Lat A) (Sf : Finset (FinPl D)) Φ Φ', IsSphOff ψ A W LA (frameLat W) Sf Φ → IsSphOff ψ A H LA (frameLat H) Sf Φ' → IsSphOff ψ A B LA LB Sf (o.boxT A Φ Φ') := by
  intro D ψ θ A B W H o sA sW sH hψ hθ hW hH
  refine ⟨sumMat o sW sH, sumLatO o (frameLat W) (frameLat H), GlobalTheory.T.isCartanInvolution_orthDecBlockSumRealMat D B W H o sW sH hW hH,
    GlobalTheory.T.orthDecSumLattice_selfDual D B W H o _ _ (frameLat_selfDual W) (frameLat_selfDual H),
    fun Φ Φ' h₁ h₂ => GlobalTheory.T.isPolynomialFockThetaVector_orthogonalBoxProduct D ψ θ A B W H o sA sW sH hψ hθ Φ Φ' h₁ h₂,
    fun LA Sf Φ Φ' h₁ h₂ => GlobalTheory.T.spherical_outside_box_product_orthDecSumLattice D ψ A B W H o LA _ _ Sf Φ Φ' h₁ h₂⟩

end GlobalTheory.Core.Rk.SumBox
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_uniform_isotypic_average_real_centre : ∀ (D : D7), BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k₀ : KerDat A S) (k₀' : KerDat S A'), k₀.Is ψ θ x y → k₀'.Is ψ θ y z → ∀ (χ₁ : GA D A → ℂ) (χ₃ : GA D S → ℂ) (C₁ : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₁ → IsBiSmooth C₁ → (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k₀.om (a, 1) (fun u => C₁ u v) = χ₁ a • fun u => C₁ u v) → (∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ v, k₀.om (1, b) (fun u => C₁ u v) = χ₃ b • fun u => C₁ u v) → ∃ (C₂ : WO A S → WO S A' → ℂ) (χ₂ : GA D S → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₂ ∧ (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k₀.om (a, 1) (fun u => C₂ u v) = χ₁ a • fun u => C₂ u v) ∧ (∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ u, k₀'.om (b, 1) (C₂ u) = χ₂ b • C₂ u) ∧ ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) → (∀ a ∈ GinfC S, ∀ b ∈ GinfC A', ∀ f, IsThetaFunO ψ S A' f → k'.om (a, b) f = k₀'.om (a, b) f) → ∀ φ, IsContAut A φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C₁) = biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C₂) := by
  first | exact @GlobalTheory.AvgMidUnif.exists_isotypic_uniform | exact GlobalTheory.AvgMidUnif.exists_isotypic_uniform | (intros; apply GlobalTheory.AvgMidUnif.exists_isotypic_uniform <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.chainMove_characters_eq_rho_up_to_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (c : {c // A.chOf i c = α}) (c' : {c // A.chOf (i + 1) c = γ}) x y, IsDetRoot _ (A.h i α c) x → IsDetRoot _ (A.h (i + 1) γ c') y → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) = (A.chr (i + 1) (A.xr i α) : ℂ) * (A.chr (i + 1) (A.xr (i + 1) γ) : ℂ)⁻¹ * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) * I.A.chiF (B.R.N i) (B.R.N (i + 1)) ((I.stp u a i).rep c.1).1.1.deco.1.N ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N := by
  first | exact @GlobalTheory.AdForm.TwDat.chr_moves_eq_rho_base | exact GlobalTheory.AdForm.TwDat.chr_moves_eq_rho_base | (intros; apply GlobalTheory.AdForm.TwDat.chr_moves_eq_rho_base <;> assumption)
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

noncomputable section

namespace GlobalTheory.RealMeasOne

variable {D : D7}

theorem ginfC_facts (V : HSp D) : IsTopologicalGroup (GA D V) ∧ LocallyCompactSpace (GA D V) ∧
    SecondCountableTopology (GA D V) ∧ T2Space (GA D V) ∧ BorelSpace (GA D V) ∧ LocallyCompactSpace (GinfC V) ∧
    SecondCountableTopology (GinfC V) ∧ BorelSpace (GinfC V) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  exact ⟨i1, i2, i3, i4, i5, i6.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsInducing.subtypeVal.secondCountableTopology, Subtype.borelSpace _⟩

theorem eq_map_of_lev {V : HSp D} (K : Subgroup (GA D V)) (hK : K ≤ GfC V) (A : Set (GA D V)) (ν : Measure (GA D V))
    (mR : Measure (GinfC V)) (hH : mR.IsHaarMeasure)
    (h : ∀ (f : GinfC V → ℂ) (F : GA D V → ℂ), Integrable f mR → (∀ b : GinfC V, ∀ κ ∈ K, F ((b : GA D V) * κ) = f b) →
      IntegrableOn F A ν ∧ ∫ g in A, F g ∂ν = ∫ b, f b ∂mR) :
    mR = Measure.map (GlobalTheory.AutMult.toInf V) (ν.restrict A) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ginfC_facts V
  haveI := hH
  have hmeas : Measurable (GlobalTheory.AutMult.toInf V) := (GlobalTheory.AutMult.continuous_toInf V).measurable

  have hfin : ∀ G : Set (GinfC V), MeasurableSet G → mR G < ⊤ →
      mR G = Measure.map (GlobalTheory.AutMult.toInf V) (ν.restrict A) G := by
    intro G hG hGf
    have hS : MeasurableSet (GlobalTheory.AutMult.toInf V ⁻¹' G) := hmeas hG
    have hf : Integrable (G.indicator fun _ => (1 : ℂ)) mR :=
      (integrable_indicator_iff hG).2 ((integrableOn_const_iff (by simp)).2 (Or.inr hGf))
    obtain ⟨hi, he⟩ := h (G.indicator fun _ => (1 : ℂ)) ((GlobalTheory.AutMult.toInf V ⁻¹' G).indicator fun _ => (1 : ℂ)) hf
      (fun b κ hκ => by
        have h1 : GlobalTheory.AutMult.toInf V ((b : GA D V) * κ) = b := by
          rw [map_mul, GlobalTheory.AutMult.toInf_coe, (GlobalTheory.ChainOnto.HaarInf.toInf_eq_one_iff V κ).2 (hK hκ), mul_one]
        classical
        rw [Set.indicator_apply, Set.indicator_apply, Set.mem_preimage, h1])
    have hi' : ν.restrict A (GlobalTheory.AutMult.toInf V ⁻¹' G) < ⊤ := by
      have := ((integrable_indicator_iff hS).1 hi)
      rcases (integrableOn_const_iff (by simp)).1 this with h0 | h0
      · simp at h0
      · exact h0
    rw [integral_indicator_const _ hS, integral_indicator_const _ hG] at he
    have he' : (ν.restrict A).real (GlobalTheory.AutMult.toInf V ⁻¹' G) = mR.real G := by
      simpa using he
    rw [Measure.map_apply hmeas hG]
    exact ((ENNReal.toReal_eq_toReal_iff' hGf.ne hi'.ne).1 he'.symm)
  refine Measure.ext fun G hG => ?_
  have hU : ⋃ n, G ∩ spanningSets mR n = G := by rw [← Set.inter_iUnion, iUnion_spanningSets, Set.inter_univ]
  have hmono : Monotone fun n => G ∩ spanningSets mR n := fun a b hab =>
    Set.inter_subset_inter_right _ (monotone_spanningSets mR hab)
  rw [← hU, hmono.measure_iUnion, hmono.measure_iUnion]
  refine iSup_congr fun n => hfin _ (hG.inter (measurableSet_spanningSets mR n)) ?_
  exact (measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top mR n)

end GlobalTheory.RealMeasOne

namespace GlobalTheory.RealMeasOne

variable {D : D7}

theorem infMat_toInf (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    infMat D.sp.cm.sig V.gram φ (GlobalTheory.AutMult.toInf V g : GA D V) = infMat D.sp.cm.sig V.gram φ g := by
  conv_rhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.TensRep.infMat_of_mem_fin V φ (GlobalTheory.AutMult.toFin V g).2, Matrix.mul_one]

theorem eq_of_measLevW {V : HSp D}
    {good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop}
    (hgood : ∀ ρ m, good ρ m → m.IsHaarMeasure)
    {K₁ K₂ : Subgroup (GL (Fin V.rank) (Lev.EAf D))} {ν₁ ν₂ : Measure (GA D V)}
    (h₁ : Lev.IsMeasLevW V K₁ good ν₁) (h₂ : Lev.IsMeasLevW V K₂ good ν₂)
    (m₁ m₂ : Measure (GinfC V)) (hH₁ : m₁.IsHaarMeasure) (hH₂ : m₂.IsHaarMeasure)
    (e₁ : m₁ = Measure.map (GlobalTheory.AutMult.toInf V) (ν₁.restrict {g | Lev.finE V g ∈ K₁}))
    (e₂ : m₂ = Measure.map (GlobalTheory.AutMult.toInf V) (ν₂.restrict {g | Lev.finE V g ∈ K₂})) : m₁ = m₂ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ginfC_facts V
  haveI := hH₁
  haveI := hH₂
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨-, ⟨θ, hθ⟩, h1⟩ := h₁
  obtain ⟨⟨A, hA⟩, h1⟩ := h1 θ hθ
  obtain ⟨⟨m, hm⟩, h1⟩ := h1 A hA
  obtain ⟨-, -, h2⟩ := h₂
  obtain ⟨-, h2⟩ := h2 θ hθ
  obtain ⟨-, h2⟩ := h2 A hA
  have h2 := h2 m hm
  let B : ∀ ρ : D.what₂.Tau, TopologicalSpace.PositiveCompacts (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) :=
    fun ρ => Classical.arbitrary _
  have hB : ∀ ρ, MeasurableSet (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)) := fun ρ =>
    (B ρ).isCompact.measurableSet
  let S : Set (GA D V) := {h | ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h}
  have hSc : IsClosed S := by
    have e : S = ⋂ ρ, (fun h => A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h) ⁻¹'
        ((fun b => UpqT.mat b * A ρ) '' (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2))) := by
      ext h
      simp only [Set.mem_iInter]
      exact Iff.rfl
    rw [e]
    refine isClosed_iInter fun ρ => IsClosed.preimage ?_ ?_
    · exact continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat (σ := D.sp.cm.sig) V.gram (hθ ρ))
    · exact ((B ρ).isCompact.image ((GlobalTheory.UpqTopology.continuous_mat).matrix_mul continuous_const)).isClosed
  have hS : MeasurableSet S := hSc.measurableSet
  let E : Set (GinfC V) := Subtype.val ⁻¹' S
  have hE : MeasurableSet E := measurable_subtype_coe hS
  have hpre : GlobalTheory.AutMult.toInf V ⁻¹' E = S := by
    ext h
    simp only [E, S, Set.mem_preimage, Set.mem_setOf_eq, infMat_toInf]
  have hval : ∀ (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (ν : Measure (GA D V)),
      Measure.map (GlobalTheory.AutMult.toInf V) (ν.restrict {g | Lev.finE V g ∈ K}) E =
        ν {h | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} := by
    intro K ν
    rw [Measure.map_apply (GlobalTheory.AutMult.continuous_toInf V).measurable hE, hpre, Measure.restrict_apply hS]
    congr 1
    ext h
    exact and_comm
  have v1 : m₁ E = ∏ ρ, m ρ (B ρ) := by rw [e₁, hval]; exact h1 m hm (fun ρ => B ρ) hB
  have v2 : m₂ E = ∏ ρ, m ρ (B ρ) := by rw [e₂, hval]; exact h2 (fun ρ => B ρ) hB
  have h0 : ∏ ρ, m ρ (B ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (Measure.measure_pos_of_nonempty_interior (m ρ) (B ρ).interior_nonempty).ne'
  have ht : ∏ ρ, m ρ (B ρ) ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (B ρ).isCompact.measure_lt_top.ne
  have e : m₂ = ((Measure.haarScalarFactor m₂ m₁ : NNReal) : ENNReal) • m₁ := Measure.isMulLeftInvariant_eq_smul m₂ m₁
  have e' := v2
  rw [e, Measure.smul_apply, v1, smul_eq_mul] at e'
  have hc : ((Measure.haarScalarFactor m₂ m₁ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 ht).1 (e'.trans (one_mul _).symm)
  rw [e, hc, one_smul]

end GlobalTheory.RealMeasOne

namespace GlobalTheory.RealMeasOne

theorem models_good {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (j : ℕ)
    (hj : j < D.R.m) :
    ∃ good : ∀ ρ : D.what₂.Tau, Measure (UpqT ((Yc D j).sig (tauE D ρ)).1 ((Yc D j).sig (tauE D ρ)).2) → Prop,
      (∀ ρ m, good ρ m → m.IsHaarMeasure) ∧
      ∀ t, Lev.IsMeasLevW (Yc D j) (lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)) good (R.νY t j) := by
  rcases Nat.lt_or_ge (j + 1) D.R.m with h | h
  · exact ⟨fun _ m => Lev.IsMinf m, fun _ _ hm => hm.1, fun t => (hM.νY t j h).1⟩
  · obtain rfl : j = D.R.m - 1 := by omega
    exact ⟨fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m, fun _ _ hm => hm.1, fun t => (hM.νY' t).1⟩

theorem one_real_measure : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F →
    (∀ h : RangeX R, RChain R h) → RangeX R → RMeas R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hC hR j hj
  by_cases hT : Nonempty T
  swap
  · exact ⟨0, fun t => (hT ⟨t⟩).elim⟩
  obtain ⟨t₀⟩ := hT
  have hlev : ∀ t, ∃ mR, IsLevMeas (stY R t j) mR := fun t =>
    (GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D (comR R t) (twR R t) (hC hR t).1 j hj.le (stY R t j) ((hC hR t).2.1 j hj)).2.2.2.2.2
  choose mR hmR using hlev
  obtain ⟨good, hgood, hW⟩ := models_good R hG.core.models j hj
  have hmap : ∀ t, mR t = Measure.map (GlobalTheory.AutMult.toInf (Yc D j))
      ((R.νY t j).restrict {g | Lev.finE (Yc D j) g ∈ lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)}) := fun t => by
    exact eq_map_of_lev (Lev.levG (Yc D j) (R.βY j) (R.datYt t j R.triv)) inf_le_left _ _ (mR t) (hmR t).1 (hmR t).2
  refine ⟨mR t₀, fun t => ?_⟩
  have e : mR t = mR t₀ := by
    exact eq_of_measLevW hgood (hW t) (hW t₀) (mR t) (mR t₀) (hmR t).1 (hmR t₀).1 (hmap t) (hmap t₀)
  rw [← e]
  exact hmR t

end GlobalTheory.RealMeasOne

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

theorem _root_.GlobalTheory.T.rows_of_part_have_part_params_first_chain_member : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → (∀ h : RangeX R, RChain R h) → RangeX R → RowPar R := by
  first | exact @GlobalTheory.ChainTw.rowPar_of_chain | exact GlobalTheory.ChainTw.rowPar_of_chain | (intros; apply GlobalTheory.ChainTw.rowPar_of_chain <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

open Matrix

variable {D : D7}

theorem Tm_mul_stackRows_gram (A : HSp D) (μ : D.host.E) :
    Tm A μ * stackRows A.gram 0 = stackRows 1 1 := by
  have hG : IsUnit A.gram.det := (gram_det_ne A).isUnit
  rw [Tm, stackRows, submatrix_mul_equiv, fromCols_mul_fromRows, Matrix.mul_zero, add_zero]
  show (stackRows A.gram⁻¹ A.gram⁻¹ * A.gram).submatrix id id = stackRows 1 1
  rw [submatrix_id_id]
  show stkRows A.gram⁻¹ A.gram⁻¹ * A.gram = stkRows 1 1
  rw [stkRows_mul, nonsing_inv_mul _ hG]

theorem mul_stkRows_zero_diag {n : ℕ} (F : Mx D (n + n) (n + n))
    (hF : ∀ i j : Fin n, F (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)) =
      F (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)))
    (X : Mx D n n) :
    ∃ β : Mx D n n, F ⬝ (stkRows X 0 : Mx D (n + n) n) = stkRows β β := by
  refine ⟨(F ⬝ (stkRows X 0 : Mx D (n + n) n)).submatrix (fun i => finSumFinEquiv (Sum.inl i)) id, ?_⟩
  ext a j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective a
  simp only [stkRows, Matrix.submatrix_apply, id, Equiv.symm_apply_apply]
  rcases s with s | s
  · simp only [Matrix.fromRows_apply_inl, Matrix.submatrix_apply, id]
  · simp only [Matrix.fromRows_apply_inr, Matrix.submatrix_apply, id, Matrix.mul_apply]
    rw [← finSumFinEquiv.sum_comp, ← finSumFinEquiv.sum_comp]
    simp only [Fintype.sum_sum_type, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, hF]

theorem exists_siegel_mul_Tm : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ Fr : GL (Fin (A.rank + A.rank)) (AE D), adj Fr.1 * gA (dblSp A) * Fr.1 = incA D μ • rat (Jst D A.rank) → (∀ i j : Fin A.rank, Fr.1 (finSumFinEquiv (Sum.inr i : Fin A.rank ⊕ Fin A.rank)) (finSumFinEquiv (Sum.inl j : Fin A.rank ⊕ Fin A.rank)) = Fr.1 (finSumFinEquiv (Sum.inl i : Fin A.rank ⊕ Fin A.rank)) (finSumFinEquiv (Sum.inl j : Fin A.rank ⊕ Fin A.rank))) → ∃ p : siegel A, mt (dblSp A) p * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) = Fr.1 := by
  intro D A μ hμ Fr hFr hdiag
  obtain ⟨hgram, hdet, -⟩ := GlobalTheory.T.doubledBasisSkewColumnMatrix_gram_inverse D A μ hμ
  have hTT : Tm A μ * (Tm A μ)⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hTT' : (Tm A μ)⁻¹ * Tm A μ = 1 := nonsing_inv_mul _ hdet
  have hU : adj (Fr.1 * rat (Tm A μ)⁻¹) * (gA (dblSp A) * (Fr.1 * rat (Tm A μ)⁻¹)) = gA (dblSp A) := by
    have h1 : rat ((Tm A μ)⁻¹ᴴ * ((Tm A μ)ᴴ * (dblSp A).gram * Tm A μ) * (Tm A μ)⁻¹) = rat (dblSp A).gram := by
      congr 1
      rw [show (Tm A μ)⁻¹ᴴ * ((Tm A μ)ᴴ * (dblSp A).gram * Tm A μ) * (Tm A μ)⁻¹ =
          (Tm A μ * (Tm A μ)⁻¹)ᴴ * (dblSp A).gram * (Tm A μ * (Tm A μ)⁻¹) by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc], hTT, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    rw [hgram, rat_mul, rat_mul, rat_smul, ← hFr, rat_conjTranspose,
      show rat (dblSp A).gram = gA (dblSp A) from rfl] at h1
    rw [adj_mul]
    simp only [Matrix.mul_assoc] at h1 ⊢
    exact h1
  have hS : (Fr.1 * rat (Tm A μ)⁻¹ : Mx D (A.rank + A.rank) (A.rank + A.rank)) ⬝
      (stkRows 1 1 : Mx D (A.rank + A.rank) A.rank) = Fr.1 ⬝ (stkRows (gA A) 0 : Mx D (A.rank + A.rank) A.rank) := by
    rw [show (stkRows 1 1 : Mx D (A.rank + A.rank) A.rank) = rat (stackRows 1 1) by rw [rat_stackRows, rat_one],
      ← Tm_mul_stackRows_gram A μ, rat_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (rat (Tm A μ)⁻¹), ← rat_mul, hTT',
      rat_one, Matrix.one_mul, rat_stackRows, rat_zero]
    rfl
  obtain ⟨β, hβ⟩ := mul_stkRows_zero_diag Fr.1 hdiag (gA A)
  refine ⟨⟨ofMat (dblSp A) _ hU, mem_siegelOf.2 (keepsDiag_of_mul_stkRows_one (β := β) (hS.trans hβ))⟩, ?_⟩
  show (Fr.1 * rat (Tm A μ)⁻¹) * rat (Tm A μ) = Fr.1
  rw [Matrix.mul_assoc, ← rat_mul, hTT', rat_one, Matrix.mul_one]

end GlobalTheory.StdUnn
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainNS
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.chain_each_step_splitPlace_without_excludedParams : ∀ D : D7, ChainNS D := by
  first | exact @GlobalTheory.ChainNS.chainNS_holds | exact GlobalTheory.ChainNS.chainNS_holds | (intros; apply GlobalTheory.ChainNS.chainNS_holds <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_standardUnitaryChart_doubledSpace : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∃ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ := by
  first | exact @GlobalTheory.StdUnn.chart_exists | exact GlobalTheory.StdUnn.chart_exists | (intros; apply GlobalTheory.StdUnn.chart_exists <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

theorem compFin_cA_scal {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (z : AE D) :
    GlobalTheory.AdelicU.compFin D.host.F D.host.E v (cA D z) =
      sigR _ D.sp.cm.sig (GlobalTheory.AdelicU.compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem map_units_inv_eq_scal {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a b : Rˣ) (h : f a = f b) :
    f ((a⁻¹ : Rˣ) : R) = f ((b⁻¹ : Rˣ) : R) := by
  calc f ((a⁻¹ : Rˣ) : R) = f ((a⁻¹ : Rˣ) : R) * (f (b : R) * f ((b⁻¹ : Rˣ) : R)) := by
        rw [← map_mul, Units.mul_inv, map_one, mul_one]
    _ = (f ((a⁻¹ : Rˣ) : R) * f (a : R)) * f ((b⁻¹ : Rˣ) : R) := by rw [h, mul_assoc]
    _ = f ((b⁻¹ : Rˣ) : R) := by rw [← map_mul, Units.inv_mul, map_one, one_mul]

theorem scalData_exists : ∀ D : D7, ∃ μ : D.host.E, IsSkew μ ∧ ∃ u ε : (AE D)ˣ, ScalData μ u ε := by
  intro D
  obtain ⟨μ, hμ, u₀, ε₀, h0, hI, hI'⟩ := GlobalTheory.T.exists_traceZero_localNorm_mul_integralUnit D
  obtain ⟨u, ε, h1, hfin, hinf⟩ := GlobalTheory.T.exists_idele_traceZero_norm_adjust_realComponents D μ hμ u₀
  have key : ∀ v, GlobalTheory.AdelicU.compFin D.host.F D.host.E v (ε : AE D) =
      GlobalTheory.AdelicU.compFin D.host.F D.host.E v (ε₀ : AE D) := by
    intro v
    have e2 : GlobalTheory.AdelicU.compFin D.host.F D.host.E v (cA D (u : AE D)) =
        GlobalTheory.AdelicU.compFin D.host.F D.host.E v (cA D (u₀ : AE D)) := by
      rw [compFin_cA_scal, compFin_cA_scal, hfin v]
    have e := congrArg (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) (h1.trans h0.symm)
    simp only [map_mul] at e
    rw [hfin v, e2, mul_assoc, mul_assoc] at e
    have hu : IsUnit (GlobalTheory.AdelicU.compFin D.host.F D.host.E v (u₀ : AE D) *
        GlobalTheory.AdelicU.compFin D.host.F D.host.E v (cA D (u₀ : AE D))) := by
      refine IsUnit.mul (u₀.isUnit.map _) ?_
      have hc : IsUnit (cA D (u₀ : AE D)) := u₀.isUnit.map (cA D)
      exact hc.map _
    exact hu.mul_left_inj.mp e
  have keyInv : ∀ v, GlobalTheory.AdelicU.compFin D.host.F D.host.E v ((ε⁻¹ : (AE D)ˣ) : AE D) =
      GlobalTheory.AdelicU.compFin D.host.F D.host.E v ((ε₀⁻¹ : (AE D)ˣ) : AE D) := by
    intro v
    exact map_units_inv_eq_scal (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) ε ε₀ (key v)
  refine ⟨μ, hμ, u, ε, h1, ?_, ?_, hinf⟩
  · intro v; rw [key v]; exact hI v
  · intro v; rw [keyInv v]; exact hI' v

end GlobalTheory.StdUnn

end
end
