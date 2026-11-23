module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorHermitianSideLevelPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.MtHeckeLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle457
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle444
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle467
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle456
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle458
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateIntertwinerValuesSobolevContinuous
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle479
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProduct
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle273
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle480
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
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import ReciprocityTheory.Automorphisms.PlaceA
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hermitianUpMove_at_levelPrime_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (c : ((I.rec7 l Z).mem u).C.cls i) (y : Formalism.L2.Herm.Ld (I.rec7 l Z) u i c), ∃ γ, i ≤ (I.rec7 l Z).R.m → ((I.rec7 l Z).fm u).fv i v c (prH (F u).atT (F u).lv i v c y) = 1 → UpCl (F u).atT (F u).lv i v c y γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).up i v c (prH (F u).atT (F u).lv i v c y)) γ v := by
  first | exact @GlobalTheory.Mem.Col2.HAt.UpMove.up_move | exact GlobalTheory.Mem.Col2.HAt.UpMove.up_move | (intros; apply GlobalTheory.Mem.Col2.HAt.UpMove.up_move <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.diamondOperator_hermitian_side_levelPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (a : (((I.rec7 l Z).mem u).A.Fv v)ˣ) (c : ((I.rec7 l Z).mem u).C.cls i), ∃ γ, i ≤ (I.rec7 l Z).R.m → DilCl (F u).atT (F u).lv i v a c γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).dil i v a c) γ v := by
  first | exact @GlobalTheory.Mem.Col2.HAt.Dil.diamond_on_hermitian_side | exact GlobalTheory.Mem.Col2.HAt.Dil.diamond_on_hermitian_side | (intros; apply GlobalTheory.Mem.Col2.HAt.Dil.diamond_on_hermitian_side <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.R3.LiftBrg

theorem eta_isHecke : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (hx1 : 1 ≤ x.2) (hx2 : x.2 ≤ (Vc X.toD7 i).rank) (v : HeightOneSpectrum (𝓞 X.toD7.host.F)) (Pb : HeightOneSpectrum (𝓞 X.toD7.host.E)) (hPb : Formalism.L2.Col.conjPrime₂ Pb = x.1.1.1) (hv : Formalism.L2.Col.IsOver v Pb) (Ut : Formalism.L2.Col.MhlUnif Pb) (g : Bridge.Gf (Vc X.toD7 i)) (hg : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * ((Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2 : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹),
    (envL X I hX U Xg tr L cV i t).isT x g := by
  intro X px I hX U Xg tr L hI hV hL cV i t A k hF x hx1 hx2 v Pb hPb hv Ut g hg
  show x.2 ≤ (Vc X.toD7 i).rank → ∃ α, IsHeckeAt (Vc X.toD7 i) (x.1.1.1 : Pl X.toD7.host.E) x.2 α ∧ (g : GL _ _) = finHom (Vc X.toD7 i) α⁻¹
  intro _
  obtain ⟨α₀, hα₀, hfin⟩ := GlobalTheory.T.exists_adelicPoint_finitePart_eq_realOne (Vc X.toD7 i) g
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_splitIdempotent_at_conjugatePrime Pb Ut
  obtain ⟨h1, h2⟩ := GlobalTheory.T.conj_uniformizer_isUniformizer_conjPrime Pb Ut
  have hβ := hL.is.βV i
  rw [hL.beta.1 i] at hβ
  have hdict := GlobalTheory.T.mem_completedSelfDualLattice_iff_integral_stdFrame (Vc X.toD7 i) (L.ΛV i) hβ
  have heps := GlobalTheory.T.conjPrimeIdempotent_mul_eq_zero_of_vanishing_at_place v Pb e hv he
  have hC : A * k ∈ Formalism.L2.DIV.St 1 := mul_mem hF.2.1 hF.2.2.2.2.1
  have hg' : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) (finHom (Vc X.toD7 i) α₀)) = A * k * ((Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2 : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ := by
    rw [hfin]; exact hg
  have hs := GlobalTheory.T.frameTransport_eta_supported_at_placeIdempotent (Vc X.toD7 i) X.B.R.nV (rkEq X i) v Pb Ut x.2 e (A * k) α₀ hv he hα₀ hg'
  have hl := GlobalTheory.T.heckeElementInv_latticeClauses_of_frameConj (Vc X.toD7 i) X.B.R.nV (rkEq X i) v Pb Ut x.2 e (A * k) α₀ he heps hdict hC hα₀ hg'
  have hd := GlobalTheory.T.heckeElement_uniformizerRatio_determinant (Vc X.toD7 i) X.B.R.nV (rkEq X i) v Pb Ut x.2 e (A * k) α₀ (by rw [rkEq X i]; exact hx2) he heps hα₀ hg'
  rw [← hPb]
  refine ⟨α₀⁻¹, ⟨e, Formalism.L2.Col.cO X.toD7.host.E Ut.π, he, h1, h2, (GfC _).inv_mem hα₀, GlobalTheory.SplitPlace.suppAt_inv hs, hl.1, hl.2, hd⟩, ?_⟩
  rw [inv_inv, hfin]

end GlobalTheory.Mem.R3.LiftBrg
end

section

open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

theorem GlobalTheory.ConjRowCont.conjMap_sobCont_ofIdE : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ (τ : D.what₂.Tau) (v : (MP R).Vec) (x : GA D (D.sp.Y 0)), ∃ ℓ : (MP R).H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt (D.sp.Y 0) τ) ((MP R).rep τ) ℓ ∧ ∀ w : (MP R).sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update v τ w) x := by
  intro _ _ _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hιE _ _ hinf _ _ c hc Φ hΦ _ τ v x
  obtain ⟨hf, -, hat, -⟩ := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h R.θ hinf hιE
  exact GlobalTheory.ConjRowCont.sobCont_conjMap X h R.θ (MP R) t c hinf (fun k hk => (hf k).1 hk)
    (fun τ g hg => ⟨(hat τ g hg).1, (hat τ g hg).2.1⟩) hc Φ hΦ τ v x
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.greenSeriesIdempotent_eq_classFunctionIdempotent : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (hζ : IsGenSys L.gen), t = L.teich → ∀ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t ht L.gen hζ), (∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC t ht L.gen hζ) τ (O.lab d τ)) → ∀ (r : ℕ) (f : (ZMod g)[X]), 1 ≤ r → GlobalTheory.GLq.eSerC L r f = eSerO O r f := by
  first | exact @GlobalTheory.SerCmp.eSerC_eq_eSerO | exact GlobalTheory.SerCmp.eSerC_eq_eSerO | (intros; apply GlobalTheory.SerCmp.eSerC_eq_eSerO <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2

noncomputable section

namespace GlobalTheory.HeckeSplitComp

open ReciprocityTheory.Aut

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-(1 : ℕ) : ℤ) := by
  by_cases hx : x = 0
  · rw [hx]; exact zero_le'
  rw [← WithZero.exp_log hx] at h ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]; push_cast; omega

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (χ : Formalism.L2.Host.HChar L), χ.TameAt s.w → ∃ ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ, NG.IsCompAt χ s ξ ∧ ∀ (u : (s.v.adicCompletion (maximalRealSubfield L))ˣ) (a : 𝓞 L) (k : Lˣ), (k : L) = (a : L) → Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) = 1 → Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - s.i (a : L)) < 1 → ξ u = χ.locK s.w k := by
  intro L _ _ _ s χ hχ
  obtain ⟨c, hc, -, hci⟩ := GlobalTheory.SplitCompl.exists_ringEquiv L s
  have hlt : ∀ y, Valued.v (c y) < 1 ↔ Valued.v y < 1 := GlobalTheory.TypeBlockFix.v_map_lt_one_iff s.v s.w c hc
  have hle : ∀ y, Valued.v (c y) ≤ 1 ↔ Valued.v y ≤ 1 := GlobalTheory.TypeBlockFix.v_map_le_one_iff s.v s.w c hc
  have heq1 : ∀ y, Valued.v y = 1 → Valued.v (c y) = 1 := by
    intro y hy
    refine le_antisymm ((hle y).2 hy.le) (not_lt.1 fun h => ?_)
    have := (hlt y).1 h
    rw [hy] at this
    exact lt_irrefl _ this
  refine ⟨(χ.loc s.w).comp (Units.map c.toRingHom.toMonoidHom), ⟨⟨1, fun u hu => ?_⟩, fun k => ?_⟩, ?_⟩
  · have hu1 : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) < 1 :=
      lt_of_le_of_lt hu (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    have hv : Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) = 1 := by
      have := Valuation.map_eq_of_sub_lt Valued.v (x := 1)
        (y := (u : s.v.adicCompletion (maximalRealSubfield L))) (by rw [map_one]; exact hu1)
      rwa [map_one] at this
    show χ.loc s.w (Units.map c.toRingHom.toMonoidHom u) = 1
    refine hχ _ (heq1 _ hv) ?_
    have e : ((Units.map c.toRingHom.toMonoidHom u : (s.w.adicCompletion L)ˣ) : s.w.adicCompletion L) - 1 =
        c ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) := by
      rw [map_sub, map_one]; rfl
    rw [e]
    exact le_exp_neg_one_of_lt_one ((hlt _).2 hu1)
  · show χ.loc s.w (Units.map c.toRingHom.toMonoidHom (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k)) =
      χ.loc s.w (Formalism.L2.Host.atFin s.w k)
    congr 1
    ext
    simp [Formalism.L2.Host.atFin, hci]
  · intro u a k hka hu hua
    show χ.loc s.w (Units.map c.toRingHom.toMonoidHom u) = χ.locK s.w k
    have hia : Valued.v (s.i (a : L)) = 1 := by
      have := Valuation.map_eq_of_sub_lt Valued.v (x := (u : s.v.adicCompletion (maximalRealSubfield L)))
        (y := s.i (a : L)) (by rw [Valuation.map_sub_swap, hu]; exact hua)
      rw [this, hu]
    have hk : s.w.valuation L (k : L) = 1 := by
      have h1 := heq1 _ hia
      rw [hci, ← hka] at h1
      rwa [Formalism.UG.P.levelaf_valued_algebraMap] at h1
    refine GlobalTheory.LevMuDet.loc_eq_locK hχ hk ?_
    have e : ((Units.map c.toRingHom.toMonoidHom u : (s.w.adicCompletion L)ˣ) : s.w.adicCompletion L) -
        algebraMap L _ (k : L) = c ((u : s.v.adicCompletion (maximalRealSubfield L)) - s.i (a : L)) := by
      rw [map_sub, hci, hka]; rfl
    rw [e]
    exact (hlt _).2 hua

end GlobalTheory.HeckeSplitComp
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.Opn

theorem exists_princ_loc_step : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n T f : ℕ} {J : Matrix (Fin n) (Fin n) E} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)), J = 1 → ∃ M : ℕ, 0 < M ∧ ∀ y ∈ UPts σ J (v.adicCompletion F), (∀ a b, ∃ c ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring, ((y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) a b = (M : E ⊗[F] v.adicCompletion F) * c) → y ∈ S.Uloc v := by
  intro F E _ _ _ _ _ σ n T f J bad S v hJ
  subst hJ
  obtain ⟨M, hM, hMU⟩ := GlobalTheory.Mem.Col2.AdT.Opn.exists_princ σ S.U S.U_open
  refine ⟨M, Nat.pos_of_ne_zero hM, fun y hy hc => ?_⟩
  choose C hC hyC using hc
  have hz := Formalism.UG.P.afsplitU_mem v σ 1 y 1 hy (one_mem _)
  have hzU : Formalism.UG.P.afsplitU v y 1 ∈ S.U := by
    refine hMU _ hz fun a b => ?_
    have hyab : (y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b =
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b + M • C a b := by
      rw [nsmul_eq_mul, ← hyC a b, Matrix.sub_apply, add_sub_cancel]
    have e : (((Formalism.UG.P.afsplitU v y 1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b =
        (M : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * Formalism.UG.P.afsplitIE v (C a b) := by
      rw [Matrix.sub_apply, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_apply, Units.val_one, hyab, map_add (f := _), map_nsmul,
        nsmul_eq_mul]
      by_cases hab : a = b
      · subst hab
        simp only [Matrix.one_apply_eq, Formalism.UG.P.afsplitEps]
        ring
      · simp [Matrix.one_apply_ne hab]
    rw [e, ← mul_assoc, ← map_natCast (Formalism.L2.Col.iA F E), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hM), map_one, one_mul]
    exact Formalism.UG.P.afsplit_IE_int v _ (hC a b)
  have h := ((S.U_eq _).1 hzU).2 v
  rwa [Formalism.UG.P.afsplit_right1] at h

end GlobalTheory.Mem.Col2.AdT.Opn
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.numberFieldGL_dense_in_completionGL_two_sided : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (A : GL (Fin n) (P.adicCompletion E)), ∃ γ : GL (Fin n) E, ∀ r s, Valued.v (((A⁻¹).1 * γ.1.map (algebraMap E (P.adicCompletion E)) - 1) r s) ≤ WithZero.exp (-(N : ℤ)) ∧ Valued.v (((γ⁻¹).1.map (algebraMap E (P.adicCompletion E)) * A.1 - 1) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  first | exact @GlobalTheory.DenseGL.dense_two_sided | exact GlobalTheory.DenseGL.dense_two_sided | (intros; apply GlobalTheory.DenseGL.dense_two_sided <;> assumption)
end
