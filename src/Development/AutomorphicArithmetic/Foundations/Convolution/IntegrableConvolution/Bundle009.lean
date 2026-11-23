module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle008
import GroundTheory.GlobalFields.Bundle001
import GroundTheory.LocalFields.LocalFourierHaar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo

theorem UpperTheory.ConvolutionTheory.L1.matchFin :
    UpperTheory.ConvolutionTheory.L1.MatchFin := by
  intro F E _ _ _ _ _ σ m v D n _ _ _ _ μE μF hE hF
  have hreg : UpperTheory.ConvolutionTheory.L1.RegOk (v.adicCompletion F) n := UpperTheory.ConvolutionTheory.L1.regOkPi.1 _ n
  obtain ⟨c, hc, hμ, hφ⟩ := UpperTheory.ConvolutionTheory.L1.matchSplit (v.adicCompletion F) (CompletionsOver E v)
    (incFin E v) (galFin σ v) m D n μE μF hE hF hreg
  refine ⟨c, hc, hμ, fun φ h1 h2 => (hφ φ h1 h2).2.2, fun φ h => ?_⟩
  obtain ⟨hcomp, hglue, -, hgc, hcc, -⟩ :=
    UpperTheory.ConvolutionTheory.L1.glueBasic (v.adicCompletion F) (CompletionsOver E v) (incFin E v) (galFin σ v) m D n
  let e : (Fin (m + 1) → GL (Fin n) (v.adicCompletion F)) ≃ₜ GL (Fin n) (CompletionsOver E v) :=
    { toFun := D.glue n
      invFun := fun x i => D.comp n i x
      left_inv := fun g => funext fun i => hcomp g i
      right_inv := hglue
      continuous_toFun := hgc
      continuous_invFun := continuous_pi hcc }
  have hΨc : Continuous fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i) :=
    continuous_finsetProd _ fun i _ => (h i).1.comp (continuous_apply i)
  have hΨs : HasCompactSupport fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i) := by
    refine HasCompactSupport.intro' (K := Set.pi Set.univ fun i => tsupport (φ i))
      (isCompact_univ_pi fun i => (h i).2) (isClosed_set_pi fun i _ => isClosed_tsupport _) ?_
    intro g hg
    obtain ⟨i, -, hi⟩ : ∃ i, i ∈ Set.univ ∧ g i ∉ tsupport (φ i) := by
      simpa [Set.mem_pi] using hg
    exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)
  have htens : D.tens n φ = (fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i)) ∘ e.symm :=
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [htens]
    exact hΨc.comp e.symm.continuous
  · rw [htens]
    exact hΨs.comp_isClosedEmbedding e.symm.isClosedEmbedding
  · have hpush := UpperTheory.ConvolutionTheory.L1.pushTens (GL (Fin n) (v.adicCompletion F)) μF m φ
      (fun i => (h i).1) (fun i => (h i).2)
    rw [← hpush]
    unfold UpperTheory.ConvolutionTheory.L1.Split.transfer
    congr 1
    funext g
    rw [htens]
    change (∏ i, φ i ((e.symm (e g)) i)) = _
    rw [e.symm_apply_apply]
end

section

open MeasureTheory NumberField

private theorem UpperTheory.ConvolutionTheory.L1.matchInf_tens (R S : Type) [CommRing R] [CommRing S] [TopologicalSpace R]
    [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] [T2Space S] (ι : R →+* S) (s : S →+* S) (m : ℕ) (D : UpperTheory.ConvolutionTheory.L1.Split ι s m) (n : ℕ)
    [MeasurableSpace (GL (Fin n) R)] [BorelSpace (GL (Fin n) R)] (μ : Measure (GL (Fin n) R)) [μ.IsHaarMeasure]
    (φ : Fin (m + 1) → GL (Fin n) R → ℂ) (hφ : ∀ i, Continuous (φ i) ∧ HasCompactSupport (φ i)) :
    Continuous (D.tens n φ) ∧ HasCompactSupport (D.tens n φ) ∧
      D.transfer n μ (D.tens n φ) = UpperTheory.ConvolutionTheory.L1.cvAll μ m φ := by
  obtain ⟨h1, h2, -, h4, h5, -⟩ := UpperTheory.ConvolutionTheory.L1.glueBasic R S ι s m D n
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (GL (Fin n) R) :=
    (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)).locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin n) R) :=
    (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) R)).secondCountableTopology
  refine ⟨?_, ?_, ?_⟩
  · exact continuous_finsetProd _ fun i _ => (hφ i).1.comp (h5 i)
  · have hK : IsCompact (D.glue n '' Set.pi Set.univ fun i => tsupport (φ i)) :=
      (isCompact_univ_pi fun i => (hφ i).2.isCompact).image h4
    refine HasCompactSupport.intro hK fun x hx => ?_
    by_contra hne
    apply hx
    refine ⟨fun i => D.comp n i x, fun i _ => subset_tsupport _ ?_, h2 x⟩
    intro h0
    exact hne (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  · rw [← UpperTheory.ConvolutionTheory.L1.pushTens (GL (Fin n) R) μ m φ (fun i => (hφ i).1) (fun i => (hφ i).2)]
    unfold UpperTheory.ConvolutionTheory.L1.Split.transfer UpperTheory.ConvolutionTheory.L1.Split.tens
    simp only [h1]

private theorem UpperTheory.ConvolutionTheory.L1.t2Space_infiniteAdeleRing' (F : Type) [Field F] [NumberField F] : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

private theorem UpperTheory.ConvolutionTheory.L1.matchInf_sc (F : Type) [Field F] [NumberField F] :
    SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

theorem UpperTheory.ConvolutionTheory.L1.matchInf :
    UpperTheory.ConvolutionTheory.L1.MatchInf := by
  intro F E _ _ _ _ _ σ m D n _ _ _ _ μE μF hE hF
  haveI := UpperTheory.ConvolutionTheory.L1.t2Space_infiniteAdeleRing' F
  haveI := UpperTheory.ConvolutionTheory.L1.t2Space_infiniteAdeleRing' E
  haveI := UpperTheory.ConvolutionTheory.L1.matchInf_sc F
  obtain ⟨c, hc, hμ, hM⟩ := UpperTheory.ConvolutionTheory.L1.matchSplit _ _ _ _ m D n μE μF hE hF (UpperTheory.ConvolutionTheory.L1.regOkPi.2.2 F n)
  exact ⟨c, hc, hμ, fun φ h1 h2 => (hM φ h1 h2).2.2,
    fun φ hφ => UpperTheory.ConvolutionTheory.L1.matchInf_tens _ _ _ _ m D n μF φ hφ⟩
end
