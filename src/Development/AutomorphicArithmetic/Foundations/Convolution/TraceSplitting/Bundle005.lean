module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle006
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle008
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.BumpEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle005
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PairPosition
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TypedEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitMatch
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
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSpaceR
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Filter

theorem UpperTheory.ConvolutionTheory.T.pickS :
    UpperTheory.ConvolutionTheory.T.PickS := by
  classical
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V Λ t hV hAt v
  obtain ⟨hInf, hUnr, hNe, -, -, -⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨S₀, hS₀, hA⟩ := hAt
  obtain ⟨-, -, h0⟩ := UpperTheory.ConvolutionTheory.Dp.parEx E n hn μ V hV
  have hU := Filter.eventually_cofinite.1 hUnr
  have hfin := ((hS₀.image (fun w => w.under (𝓞 F))).union hU).union (Set.finite_singleton v)
  obtain ⟨q, hq, hqS⟩ := (hInf.diff hfin).nonempty
  have hsub : ∀ w, w.under (𝓞 F) ∉ hfin.toFinset → w ∉ S₀ := fun w hw hw0 =>
    hw (hfin.mem_toFinset.2 (Or.inl (Or.inl ⟨w, hw0, rfl⟩)))
  refine ⟨hfin.toFinset, q, (hNe q).some, hfin.mem_toFinset.2 (Or.inr rfl),
    fun h => hqS (hfin.mem_toFinset.1 h), hq, fun u hu => ?_, fun w hw => ?_, fun S' hS' => ?_⟩
  · by_contra h
    exact hu (hfin.mem_toFinset.2 (Or.inl (Or.inr h)))
  · exact (hA.2 w (hsub w hw)).2.1
  · have hS : ∀ w, w ∉ S' → w ∉ S₀ := fun w hw => hsub w fun h => hw ((hS' w).2 (Or.inl h))
    exact ⟨⟨hA.1, fun w hw => hA.2 w (hS w hw)⟩, fun τ => (hA.1 τ).1,
      fun w hw => ⟨(hA.2 w (hS w hw)).1, h0 w _ (hA.2 w (hS w hw))⟩⟩
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1
open scoped ComplexConjugate

theorem UpperTheory.ConvolutionTheory.T.Port.adj_ne {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (u : H) (hu : star T u ≠ 0) : (T * star T) u ≠ 0 := by
  intro h0
  apply hu
  rw [ContinuousLinearMap.star_eq_adjoint] at h0 ⊢
  have h1 : T (ContinuousLinearMap.adjoint T u) = 0 := h0
  rw [← inner_self_eq_zero (𝕜 := ℂ), ContinuousLinearMap.adjoint_inner_left, h1, inner_zero_right]

theorem UpperTheory.ConvolutionTheory.T.Port.pickInf_of (hInf : UpperTheory.ConvolutionTheory.L1.InfSplit) (hAB : UpperTheory.ConvolutionTheory.L1.ArchBasic)
    (hBump : UpperTheory.ConvolutionTheory.L1.BumpEx) (hPosition : UpperTheory.ConvolutionTheory.L1.ArchSlotEx) (hSq : UpperTheory.ConvolutionTheory.L1.SqOp)
    (hAmp : UpperTheory.ConvolutionTheory.L1.AmpSlot) (hPair : UpperTheory.ConvolutionTheory.L1.PairPosition) : UpperTheory.ConvolutionTheory.T.PickInf := by
  set_option synthInstance.maxHeartbeats 100000 in
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ u hu
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 :=
    ⟨Module.finrank F E - 1, by have := hp.two_le; omega⟩
  obtain ⟨p⟩ := (hInf F E σ hσ m hm).1 inferInstance
  obtain ⟨D, -⟩ := (hInf F E σ hσ m hm).2 p
  obtain ⟨-, -, -, -, -, ⟨s, hsl, hs⟩, -, -⟩ := hAB F E σ m D n
  obtain ⟨νF, hνF⟩ : ∃ νF : Measure (archGroup F n), νF.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨b, hbs, hbf, hbn, hbu⟩ := hBump F n νF (LL μE)
    (((rightRegularRep (rationalGLOne (K := E) (n := n)) μE).compHom (archP E n) continuous_archP).compHom (s 0) (hs 0)) u hu
  obtain ⟨νE, hνE, a, aE, aF, hA⟩ := hPosition F E σ m D n νF b hbs hbf hbn
  obtain ⟨hsq, -, -, -⟩ := hSq F n νF b a aF m hA.sq hA.pow hA.norm (LL μE)
    (((rightRegularRep (rationalGLOne (K := E) (n := n)) μE).compHom (archP E n) continuous_archP).compHom (s 0) (hs 0))
  obtain ⟨hAE, hAF⟩ := hAmp F E σ m D n νE νF b a aE aF hA
  refine ⟨m, hm, D, s, hs, νE, hνE, νF, hνF, b, a, aE, aF, hsl, hA, hAE μE, hAF μF,
    hPair F E σ m hm D n νE νF b a aE aF hA, ?_⟩
  have key := UpperTheory.ConvolutionTheory.T.Port.adj_ne _ u hbu
  rw [← hsq] at key
  exact key

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.T.pickInf :
    UpperTheory.ConvolutionTheory.T.PickInf := UpperTheory.ConvolutionTheory.T.Port.pickInf_of infSplit archBasic bumpEx archPositionEx sqOp ampPosition pairPosition
end
end

section

open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T in
theorem UpperTheory.ConvolutionTheory.T.tyEx :
    UpperTheory.ConvolutionTheory.T.TyEx :=
  tyEx_of splitLev splitStable splitMatch inertData offStable L1.typedEx L1.eigBasic
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published PositivityTheory.RgJS UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T Filter

private theorem above_finite {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {S : Set (HeightOneSpectrum (𝓞 F))} (hS : S.Finite) :
    {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ S}.Finite := by
  refine Set.Finite.preimage' (f := fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F)) hS fun v _ => ?_
  have h := Ideal.finite_factors (R := 𝓞 E) (I := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)))
    (by
      intro h
      exact v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h))
  refine h.subset fun w hw => ?_
  have e : w.under (𝓞 F) = v := hw
  rw [Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

theorem UpperTheory.ConvolutionTheory.T.famParts :
    UpperTheory.ConvolutionTheory.T.FamParts := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hl n hn hL Λ t h
  classical
  simp only [OffAll, OffFam, not_forall, not_and_or, not_not] at h
  obtain ⟨S, hS, h⟩ := h
  have hT := above_finite (E := E) hS
  rcases h with ⟨b, hb⟩ | ⟨b, Λ', t', hb, h⟩
  · obtain ⟨P, hP⟩ := famSat E n b _ hT Λ t hb
    refine ⟨Fin b.r, inferInstance, b.d, P, b.pos, by simpa using b.two, ?_⟩
    exact hT.eventually_cofinite_notMem.mono hP
  · have ht : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ S → t w = bcSat t' w := by
      intro w hw
      by_contra hc
      apply h
      right
      exact ⟨w, hw, hc⟩
    obtain ⟨π, hπ⟩ := famSat F n b S hS Λ' t' hb
    have hlt : ∀ i, b.d i < n := by
      intro i
      haveI : Nontrivial (Fin b.r) := Fin.nontrivial_iff_two_le.2 b.two
      obtain ⟨j, hj⟩ := exists_ne i
      refine lt_of_lt_of_eq ?_ b.sum
      exact Finset.single_lt_sum hj (Finset.mem_univ _) (Finset.mem_univ _) (b.pos j) fun k _ _ => Nat.zero_le _
    choose κ fκ m P hm hne hP using fun i => hL (b.d i) (b.pos i) (hlt i) (π i)
    have hsum := R.liftSum F E hl (Fin b.r) κ b.d (fun a => m a.1 a.2) π (fun a => P a.1 a.2) hP
    refine ⟨Σ i, κ i, inferInstance, fun a => m a.1 a.2, fun a => P a.1 a.2, fun a => hm a.1 a.2, ?_, ?_⟩
    · refine b.two.trans ?_
      have := Fintype.card_le_of_surjective (Sigma.fst : (Σ i, κ i) → Fin b.r) fun i => ⟨⟨i, (hne i).some⟩, rfl⟩
      simpa using this
    · have hN := (places F E hl).2.2.2.2.1
      filter_upwards [hsum, hT.eventually_cofinite_notMem] with w hw hwS
      obtain ⟨B, ⟨B1, hB1, e1⟩, hB'⟩ := hw (resDeg F w) (by
        simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hN w)
      obtain ⟨C, ⟨C1, hC1, e2⟩, e⟩ := hπ _ hwS
      have e3 : B = C := by
        rw [e1, e2]
        exact Finset.sum_congr rfl fun i _ => (hB1 i).unique (hC1 i)
      refine ⟨_, hB', ?_⟩
      rw [ht w hwS, bcSat, e, e3, Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl fun a _ => by simp
end
