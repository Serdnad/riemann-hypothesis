module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.ExistsGap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle548
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjMemNilSet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffMulRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagFieldHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorsCommute
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle564
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeHomotopy
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeStructure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceMulConjTranspose
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.CxDataModel
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.GelFlagOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveFinal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PCompat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.TrMulComm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.CasInfOfIm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfFiniteInputs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntryLeOfLg
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.CharacterIntegrability.ConvMul
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.DoubleSumFinprodFactor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private lemma wdVal_map {B C Γ : Type} [CommRing B] [StarRing B] [Algebra ℂ B] [Ring C] [StarRing C] [Algebra ℂ C]
    (f : B →⋆ₐ[ℂ] C) (gen : Γ → B) (w : List (Γ × Bool)) :
    f (wdVal gen w) = wdVal (fun x => f (gen x)) w := by
  induction w with
  | nil => simp [wdVal]
  | cons p w ih =>
    simp only [wdVal, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    split_ifs <;> simp [map_star]

theorem peakAlg : PeakAlg := by
  intro H _ _ _ Q _ Γ op v 𝔄 arch a₀ x ρ ha hv hρ hs
  let gen : {γ // arch γ} → 𝔄.B := fun γ => 𝔄.ι γ
  let A : StarSubalgebra ℂ 𝔄.B := StarAlgebra.adjoin ℂ (Set.range gen)
  have hmem : ∀ γ : {γ // arch γ}, 𝔄.ι γ ∈ A := fun γ =>
    StarAlgebra.subset_adjoin ℂ (Set.range gen) (Set.mem_range_self γ)
  let p : A →⋆ₐ[ℂ] ℂ := 𝔄.P.comp A.subtype
  let a₁ : A := ⟨𝔄.ι a₀, hmem ⟨a₀, ha⟩⟩
  obtain ⟨g, hg, hn⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.peak 𝔄.B Q 𝔄.R A p a₁ (𝔄.ι x) ρ
    (by
      change 𝔄.P (𝔄.ι a₀) = 1
      rw [𝔄.hP, hv])
    hρ
    (fun s hb hsa => hs s hb fun γ hγ => by
      have h1 := hsa ⟨𝔄.ι γ, hmem ⟨γ, hγ⟩⟩
      have h2 : p ⟨𝔄.ι γ, hmem ⟨γ, hγ⟩⟩ = v γ := by
        change 𝔄.P (𝔄.ι γ) = v γ
        exact 𝔄.hP γ
      rw [← h2]
      exact h1)
  obtain ⟨J, hJ, c, w, L, -, hgw, -⟩ := PositivityTheory.Rg.BcB.F.adjWords _ _ gen (g : 𝔄.B) g.2
  refine ⟨J, hJ, c, w, ?_, ?_⟩
  · have hp : 𝔄.P (g : 𝔄.B) = 1 := hg

    rw [hgw, map_sum] at hp
    rw [← hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, wdVal_map, smul_eq_mul]
    congr 2
    funext γ
    exact (𝔄.hP γ).symm
  · have hF : op x * ((∑ j, c j • wdVal (fun γ : {γ // arch γ} => op γ) (w j)) * op a₀) =
        𝔄.F (𝔄.ι x * ((g : 𝔄.B) * 𝔄.ι a₀)) := by

      rw [map_mul, map_mul, 𝔄.hF, 𝔄.hF, hgw, map_sum]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, wdVal_map]
      congr 2
      funext γ
      exact (𝔄.hF γ).symm
    rw [hF]
    have hnorm : ‖𝔄.F (𝔄.ι x * ((g : 𝔄.B) * 𝔄.ι a₀)) ∘L Q.subtypeL‖ =
        ‖𝔄.R (𝔄.ι x * ((g : 𝔄.B) * 𝔄.ι a₀))‖ := by
      refine ContinuousLinearMap.opNorm_ext _ _ fun q => ?_
      change ‖𝔄.F _ (q : H)‖ = ‖(𝔄.R _ q)‖
      rw [← 𝔄.hR]
      rfl
    rw [hnorm]
    exact hn

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.arEx :
    UpperTheory.Zero.ConvolutionTheory.EB.ArEx := by
  intro E _ _ _ a b l₁ l₂ D
  haveI : BorelSpace (G a) := ⟨rfl⟩
  haveI : BorelSpace (G b) := ⟨rfl⟩
  haveI : BorelSpace (Hf E a b) := ⟨rfl⟩
  haveI : LocallyCompactSpace (G a) := lc_G a
  haveI : LocallyCompactSpace (G b) := lc_G b
  let μa : Measure (G a) := Measure.haar
  let μb : Measure (G b) := Measure.haar
  have ha : μa.IsHaarMeasure := inferInstance
  have hb : μb.IsHaarMeasure := inferInstance
  obtain ⟨ν, hν, hν', hcomp⟩ := compatEx E a b D μa μb
  obtain ⟨-, -, ca, hca0, hca⟩ := GlobalTheory.CompanionTheory.Growth.size_facts E a
  obtain ⟨-, -, cb, hcb0, hcb⟩ := GlobalTheory.CompanionTheory.Growth.size_facts E b
  obtain ⟨bump, T, hT, hbump, hone⟩ := PositivityTheory.Rg.BcB.F.F0.bump_one (InfinitePlace E ⊕ InfinitePlace E)
    (Sum.elim (fun v => cas (UpperTheory.Zero.ConvolutionTheory.EB.chi l₁ v)) fun v => cas (UpperTheory.Zero.ConvolutionTheory.EB.chi l₂ v))
    (fun i => by cases i <;> exact PositivityTheory.Rg.BcB.F.F0.cas_infOf_im _)
  obtain ⟨_, hKa⟩ := PositivityTheory.RgBcC.wave_existence_speed_multiplicity.2.2.1 a
  obtain ⟨_, hKb⟩ := PositivityTheory.RgBcC.wave_existence_speed_multiplicity.2.2.1 b
  let Ma := UpperTheory.Zero.ConvolutionTheory.EB.Ml l₁
  let Mb := UpperTheory.Zero.ConvolutionTheory.EB.Ml l₂
  exact ⟨{
    μa := μa
    μb := μb
    ν := ν
    ha := ha
    hb := hb
    hν := hν
    hν' := hν'
    compat := hcomp
    c := max ca cb
    c_nonneg := le_max_of_le_left hca0
    ca := fun g h => (hca g h).trans (by gcongr; exact le_max_left _ _)
    cb := fun g h => (hcb g h).trans (by gcongr; exact le_max_right _ _)
    bump := bump
    T := T
    T_nonneg := hT
    isBump := hbump
    ka := fun w v => ((hKa μa (Ma v)).1 w bump T hbump).choose
    kb := fun w v => ((hKb μb (Mb v)).1 w bump T hbump).choose
    kera := fun w v => ((hKa μa (Ma v)).1 w bump T hbump).choose_spec
    kerb := fun w v => ((hKb μb (Mb v)).1 w bump T hbump).choose_spec
    one := by simpa [Fintype.prod_sum_type] using hone }⟩
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem vcSt_holds : VCSt :=
  VC.vcOf wave_existence_speed_multiplicity.1 wave_existence_speed_multiplicity.2.1 wave_existence_speed_multiplicity.2.2.2 GlobalTheory.CompanionTheory.GelC.gelComm GlobalTheory.CompanionTheory.GelFlagPf.gelFlag_holds
    GlobalTheory.CompanionTheory.FlagHerm.flagField_holds GlobalTheory.CompanionTheory.NilUnimod.nilUni GlobalTheory.CompanionTheory.KerZeroPf.main

private theorem lSt_holds : LSt :=
  LfSt.lOf_of_kChain LfSt.kChain_holds wave_existence_speed_multiplicity.1 wave_existence_speed_multiplicity.2.1 wave_existence_speed_multiplicity.2.2.1 wave_existence_speed_multiplicity.2.2.2
    (LfSt.chainOf'_holds wave_existence_speed_multiplicity.1 wave_existence_speed_multiplicity.2.1 GlobalTheory.CompanionTheory.GelC.gelComm GlobalTheory.CompanionTheory.KerZeroPf.main)
    GlobalTheory.CompanionTheory.ConeHaar.coneSt GlobalTheory.CompanionTheory.SuperHomot.homot GlobalTheory.CompanionTheory.SuppBound.suppSt

abbrev LefConcl {n : ℕ} (lam : Fin n → ℤ) (M : KMod n) (Tθ : M.V →L[ℂ] M.V) : Prop :=
  (∀ k, Tθ * M.ρ k = M.ρ k * Tθ) ∧ (∀ v, ‖Tθ v‖ = ‖v‖) ∧ Tθ * Tθ = 1 ∧
    ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (k : Mat n → (M.V →L[ℂ] M.V))
      (val : Inf n → ℂ) (T : ℝ), IsMult μ M k val T →
      (∀ (d : G n) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ → W₁ ≠ ⊥ →
        (fun v => d.val *ᵥ v) '' perp W₂ = W₁ → (fun v => d.val *ᵥ v) '' perp W₁ = W₂ →
        ∀ (N : Subgroup (G n)), (N : Set (G n)) = nilSet W₁ W₂ → ∀ (ν : Measure N) [ν.IsHaarMeasure],
          ∫ u : N, phiOf M Tθ k (u * d) ∂ν = 0) ∧
      ∀ (d : G n) (z : Fin n → ℂ), d.val = diagonal z → (∀ a, ‖z a‖ = 1) → (Function.Injective fun a => z a ^ 2) →
        Integrable (fun x => phiOf M Tθ k (PositivityTheory.RgTw.tw x d)) μ ∧
          ∫ x, phiOf M Tθ k (PositivityTheory.RgTw.tw x d) ∂μ =
            val (infOf lam) * starRingEnd ℂ (weylChar lam fun a => z a ^ 2)

theorem lefModel (n : ℕ) (lam : Fin n → ℤ) (hlam : Antitone lam) : LefConcl lam (lefE n lam) (lefT n lam) := by
  have h := cxData_model lam hlam
  exact ⟨h.TK, h.Tiso, h.Tsq, fun μ _ k val τ hk =>
    ⟨vcSt_holds n lam _ _ _ _ _ _ _ h μ k val τ hk, lSt_holds n lam _ _ _ _ _ _ _ h μ k val τ hk⟩⟩

theorem lefL : LefL := by
  intro E _ _ _ a b l₁ l₂ D A
  have LA := fun v : InfinitePlace E => lefModel a (l₁ v).w (l₁ v).anti
  have LB := fun v : InfinitePlace E => lefModel b (l₂ v).w (l₂ v).anti
  haveI := A.ha
  haveI := A.hb
  haveI : BorelSpace (G a) := ⟨rfl⟩
  haveI : BorelSpace (G b) := ⟨rfl⟩
  refine ⟨⟨fun v k val T hm => vcBridge a A.μa (Ml l₁ v) (Tl l₁ v) k val T (LA v).1 hm ((LA v).2.2.2 A.μa k val T hm).1,
    fun v k val T hm => vcBridge b A.μb (Ml l₂ v) (Tl l₂ v) k val T (LB v).1 hm ((LB v).2.2.2 A.μb k val T hm).1⟩, ?_⟩
  intro v k k' val val' T hm hm'
  exact lefschetz_pair_holds a b A.μa A.μb (l₁ v) (l₂ v) _ _ _ _
    ⟨(F0.phiOf_cs A.μa (Ml l₁ v) (Tl l₁ v) k val T hm).1, (F0.phiOf_cs A.μa (Ml l₁ v) (Tl l₁ v) k val T hm).2,
      fun d z hd hz hi => ((LA v).2.2.2 A.μa k val T hm).2 d z hd hz hi |>.2⟩
    ⟨(F0.phiOf_cs A.μb (Ml l₂ v) (Tl l₂ v) k' val' T hm').1, (F0.phiOf_cs A.μb (Ml l₂ v) (Tl l₂ v) k' val' T hm').2,
      fun d z hd hz hi => ((LB v).2.2.2 A.μb k' val' T hm').2 d z hd hz hi |>.2⟩

end UpperTheory.Zero.ConvolutionTheory.EB

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH finH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem convMul : ConvMul := by
  intro E _ _ _ B f hf
  haveI := B.ha
  haveI := B.hb
  haveI := B.hν
  haveI : BorelSpace (G B.a) := ⟨rfl⟩
  haveI : BorelSpace (G B.b) := ⟨rfl⟩
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  refine ⟨fun t t' ht ht' => ?_, fun ψ ψ' hψ hψ' => ?_⟩
  · have hT := PositivityTheory.Rg.BcB.F.Op.test B tensTest t ht
    have hT' := PositivityTheory.Rg.BcB.F.Op.test B tensTest t' ht'
    have hm := (tensMul E B.a B.b B.D B.μa B.μb B.ν B.Ma B.Mb B.κ t.ka t'.ka t.kb t'.kb t.va t'.va t.vb t'.vb
      t.T t'.T t.ψ t'.ψ B.compat ht.ka ht.kb ht'.ka ht'.kb ht.ψ ht'.ψ).2
    have e : (t.mul t').Φ = mulM B.D.μ t.Φ t'.Φ := hm.symm
    rw [e]
    exact PositivityTheory.Rg.BcB.F.Rd.B.conv_mulM B.D t.Φ t'.Φ hT hT' f hf
  · have hcf : Continuous fun h : Hf E B.a B.b => finH h :=
      ((continuous_finGL' B.a).comp continuous_fst).prodMk ((continuous_finGL' B.b).comp continuous_snd)
    have hF : ∀ i x, Continuous fun h => f i (x * finH h) := fun i x =>
      (hf i).comp (continuous_const.mul hcf)
    have hI : ∀ (φ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)), IsFinM φ → ∀ y z i x,
        Integrable (fun h => φ y z h * f i (x * finH h)) B.ν := fun φ hφ y z i x =>
      ((hφ y z).1.mul (hF i x)).integrable_of_hasCompactSupport (hφ y z).2.mul_right
    refine ⟨PositivityTheory.Rg.BcB.F.R3.convF_mulF_eq_convF_convF B.ν ψ ψ' hψ hψ' f hF, ?_, fun c => ⟨?_, ?_⟩⟩
    · funext i x
      simp only [convF, Pi.add_apply, Matrix.add_apply, add_mul]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      exact integral_add (hI ψ hψ _ _ _ _) (hI ψ' hψ' _ _ _ _)
    · funext i x
      simp only [convF, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      exact integral_const_mul _ _
    · funext i x
      simp only [convF, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun h => ?_)
      show ψ i.2 z h * (c * f (i.1, z) (x * finH h)) = c * (ψ i.2 z h * f (i.1, z) (x * finH h))
      ring

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem position_off {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {Z : Finset (Pl E)} (L : Lv a b Z)
    {w i : Pl E} (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (hi : i ≠ w) :
    intersection_update_fsHerm_neg_one Z {w} L.ln e i = intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one) i := by
  simp [intersection_update_fsHerm_neg_one, hi]

private theorem position_at {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {Z : Finset (Pl E)} (L : Lv a b Z)
    {w : Pl E} (hZ : w ∉ Z) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) :
    intersection_update_fsHerm_neg_one Z {w} L.ln e w = fn2 a b w (e w) := by
  simp [intersection_update_fsHerm_neg_one, hZ]

private theorem position_cof {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {Z : Finset (Pl E)} (L : Lv a b Z) :
    ∀ᶠ i in cofinite, intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one) i = ((K2 a b i : Subgroup _) : Set _).indicator 1 := by
  filter_upwards [Z.finite_toSet.compl_mem_cofinite] with i hi
  have hi' : i ∉ Z := hi
  simp [intersection_update_fsHerm_neg_one, hi']

private theorem fin_split {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (S : Set (Pl E)) {Z : Finset (Pl E)}
    (L : Lv a b Z) {w : Pl E} (hw : w ∈ S) (hZ : w ∉ Z) (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (y : Gf E a b) :
    finFn S (intersection_update_fsHerm_neg_one Z {w} L.ln e₁) (intersection_update_fsHerm_neg_one Z {w} L.ln e₂) y =
      (fn2 a b w (e₁ w) (atW w y) * if IsSplitAt w then fn2 a b w (e₂ w) (atW w (thP E a b y)) else 1) *
        ∏ᶠ i ∈ S \ ↑({w} : Finset (Pl E)), Fm.fac (intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one)) (intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one)) y i := by
  rw [Fm.finFn_eq, Fm.fp_split S {w} (by simpa using hw) _ _ (fun i hi => ?_)
    (Fm.fac_fin S (position_cof L) (position_cof L) y)]
  · congr 1
    simp [Fm.fac, position_at L hZ]
  · have hi' : i ≠ w := by simpa using hi
    simp only [Fm.fac, position_off L _ hi']

private theorem ex_add {ι G : Type} [Group G] (K : Subgroup G) (g : ι → G → ℂ) (x y : Ex ι) (h : G) :
    (x.add y).fn K g h = x.fn K g h + y.fn K g h := rfl

private theorem ex_smul {ι G : Type} [Group G] (K : Subgroup G) (g : ι → G → ℂ) (c : ℂ) (x : Ex ι) (h : G) :
    (Ex.smul c x).fn K g h = c * x.fn K g h := rfl

theorem hkLin : HkLin := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ' w hw hZ x y z c
  have key : ∀ (e₁ e₂ : Ex (Fin (a + 1) × Fin (b + 1))) (u v : Unit) (h : Hf E a b), A.hk S L {w} (fun _ => e₁) (fun _ => e₂) u v h =
      A.blk.vol⁻¹ * ((fn2 a b w e₁ (atW w h) * if IsSplitAt w then fn2 a b w e₂ (atW w (thP E a b h)) else 1) *
        ∏ᶠ i ∈ S \ ↑({w} : Finset (Pl E)), Fm.fac (intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one)) (intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one)) h i) := by
    intro e₁ e₂ u v h
    exact congrArg _ (fin_split S L hw hZ _ _ h)
  refine ⟨?_, ?_, fun hs => ⟨?_, ?_⟩, fun hs => ?_⟩ <;> funext u v h
  · simp only [Matrix.add_apply, Pi.add_apply, key, fn2, ex_add]; ring
  · simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, key, fn2, ex_smul]; ring
  · simp only [Matrix.add_apply, Pi.add_apply, key, fn2, ex_add, if_pos hs]; ring
  · simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, key, fn2, ex_smul, if_pos hs]; ring
  · simp only [key, if_neg hs]

end UpperTheory.Zero.ConvolutionTheory.EB
end
end
