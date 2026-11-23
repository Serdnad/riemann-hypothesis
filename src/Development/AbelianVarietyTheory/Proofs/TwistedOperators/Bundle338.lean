module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle299
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle315
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle266
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle263
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle286
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle319
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle320
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle321
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SBCount

theorem countable_compact_open (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    {U : Set X | IsCompact U ∧ IsOpen U}.Countable := by
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis X
  refine ((Set.countable_setOf_finite_subset hbc).image Set.sUnion).mono ?_
  rintro U ⟨hUc, hUo⟩
  obtain ⟨S, hSb, rfl⟩ := hb.open_eq_sUnion hUo
  obtain ⟨t, htS, htf, hcov⟩ := hUc.elim_finite_subcover_image (b := S) (c := id)
    (fun s hs => hb.isOpen (hSb hs)) (by intro x hx; simpa using hx)
  refine ⟨t, ⟨htf, htS.trans hSb⟩, ?_⟩
  refine le_antisymm (Set.sUnion_subset_sUnion htS) ?_
  intro x hx
  simpa using hcov hx

theorem SB_le_span (X : Type) [TopologicalSpace X] :
    GlobalTheory.WeilM.SB X ≤ Submodule.span ℂ
      ((fun U : Set X => U.indicator (fun _ => (1 : ℂ))) '' {U : Set X | IsCompact U ∧ IsOpen U}) := by
  intro f hf
  obtain ⟨hlc, hcs⟩ := hf
  obtain ⟨s, hs⟩ := hcs.isCompact.elim_finite_subcover (fun a : ℂ => f ⁻¹' {a})
    (fun a => hlc.isOpen_fiber a) (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  have hf_eq : f = ∑ a ∈ s, a • (f ⁻¹' {a}).indicator (fun _ => (1 : ℂ)) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Set.indicator, Set.mem_preimage,
      Set.mem_singleton_iff, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_cases hx : x ∈ tsupport f
      · exact absurd (by simpa using hs hx) h
      · exact image_eq_zero_of_notMem_tsupport hx
  rw [hf_eq]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases ha : a = 0
  · simp [ha]
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨f ⁻¹' {a}, ⟨?_, hlc.isOpen_fiber a⟩, rfl⟩)
    refine hcs.isCompact.of_isClosed_subset (hlc.isClosed_fiber a) ?_
    intro x hx
    refine subset_tsupport f ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp [Function.mem_support, hx, ha]

theorem rank_SB_le (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (GlobalTheory.WeilM.SB X) ≤ Cardinal.aleph0 := by
  refine (Submodule.rank_mono (SB_le_span X)).trans ((rank_span_le _).trans ?_)
  exact Cardinal.mk_le_aleph0_iff.2 ((countable_compact_open X).image _).to_subtype

end GlobalTheory.SBCount

namespace GlobalTheory.TripleAssembly

theorem rank_SB_adicCompletion_le : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : HeightOneSpectrum (𝓞 F)),
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ≤ Cardinal.aleph0 := by
  intro F _ _ κ _ v
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    ⟨_, Set.countable_range _, v.denseRange_algebraMap F⟩
  exact GlobalTheory.SBCount.rank_SB_le _

end GlobalTheory.TripleAssembly
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.PrimFrameLeft

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]

theorem row_mul_eq_sum (M : Matrix A A k) (Y : Matrix A D k) (i : A) :
    (M * Y).row i = ∑ l, M i l • Y.row l := by
  funext j
  simp [Matrix.mul_apply, Finset.sum_apply, Matrix.row]

theorem span_O_row_mul_le (M : Matrix A A k) (hM : ∀ i j, M i j ∈ 𝒪[k]) (Y : Matrix A D k) :
    Submodule.span 𝒪[k] (Set.range (M * Y).row) ≤ Submodule.span 𝒪[k] (Set.range Y.row) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [row_mul_eq_sum]
  exact Submodule.sum_mem _ fun l _ =>
    Submodule.smul_mem _ (⟨M i l, hM i l⟩ : 𝒪[k]) (Submodule.subset_span ⟨l, rfl⟩)

theorem span_k_row_mul_le (M : Matrix A A k) (Y : Matrix A D k) :
    Submodule.span k (Set.range (M * Y).row) ≤ Submodule.span k (Set.range Y.row) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [row_mul_eq_sum]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem span_O_row_gl_mul (g : GL A k) (hg : g ∈ KO k A) (Y : Matrix A D k) :
    Submodule.span 𝒪[k] (Set.range (g.val * Y).row) = Submodule.span 𝒪[k] (Set.range Y.row) := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff g).1 hg
  refine le_antisymm (span_O_row_mul_le _ h1 Y) ?_
  have := span_O_row_mul_le _ h2 (g.val * Y)
  rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this

theorem span_k_row_gl_mul (g : GL A k) (Y : Matrix A D k) :
    Submodule.span k (Set.range (g.val * Y).row) = Submodule.span k (Set.range Y.row) := by
  refine le_antisymm (span_k_row_mul_le _ Y) ?_
  have := span_k_row_mul_le (g⁻¹).val (g.val * Y)
  rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this

theorem mem_matLat_iff_span_le (Λ : Submodule 𝒪[k] (D → k)) (Y : Matrix A D k) :
    Y ∈ matLat A Λ ↔ Submodule.span 𝒪[k] (Set.range Y.row) ≤ Λ := by
  rw [Submodule.span_le, mem_matLat]
  exact ⟨fun h => by rintro _ ⟨i, rfl⟩; exact h i, fun h i => h ⟨i, rfl⟩⟩

theorem isPrimFrame_gl_mul_iff (Λ : Submodule 𝒪[k] (D → k)) (g : GL A k) (hg : g ∈ KO k A)
    (Y : Matrix A D k) : IsPrimFrame Λ (g.val * Y) ↔ IsPrimFrame Λ Y := by
  have hrank : (g.val * Y).rank = Y.rank :=
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
  unfold IsPrimFrame
  rw [hrank, mem_matLat_iff_span_le, mem_matLat_iff_span_le, span_O_row_gl_mul g hg, span_k_row_gl_mul]

end GlobalTheory.PrimFrameLeft
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.ResSumInv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mk_eq_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (a b : 𝒪[k]) :
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) a = Ideal.Quotient.mk _ b) ↔
      (((ϖ ^ e)⁻¹ : kˣ) : k) * ((a : k) - b) ∈ 𝒪[k] := by
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hne : ((ϖ : k)) ^ e ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  constructor
  · rintro ⟨c, hc⟩
    have hc' : ((a : k) - b) = (ϖ : k) ^ e * c := by
      have := congrArg (fun x : 𝒪[k] => (x : k)) hc
      simpa using this
    rw [hc']
    have : (((ϖ ^ e)⁻¹ : kˣ) : k) * ((ϖ : k) ^ e * c) = c := by
      rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rw [this]; exact c.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

theorem mul_mem_int {A C B : Type} [Fintype C] {X : Matrix A C k} {Y : Matrix C B k}
    (hX : ∀ i j, X i j ∈ 𝒪[k]) (hY : ∀ i j, Y i j ∈ 𝒪[k]) (i : A) (j : B) : (X * Y) i j ∈ 𝒪[k] := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hX i l) (hY l j)

theorem sum_res_mul_left {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ϖ : kˣ) (e : ℕ) (hϖ : IsUnif ϖ) (f : Matrix A B k → ℂ)
    (hf : ∀ Z Z' : Matrix A B k, (∀ i j, Z' i j ∈ 𝒪[k]) → f (Z + Z') = f Z)
    (M : GL A k) (hM : M ∈ KO k A) :
    ∑ S : A → B → Res k e, f (M.val * ((ϖ ^ e)⁻¹ • liftRes S)) =
      ∑ S : A → B → Res k e, f ((ϖ ^ e)⁻¹ • liftRes S) := by
  obtain ⟨hM1, hM2⟩ := (mem_KO_iff M).1 hM
  set c : k := (((ϖ ^ e)⁻¹ : kˣ) : k) with hc
  have hint : ∀ (S : A → B → Res k e) i j, (M.val * liftRes S) i j ∈ 𝒪[k] :=
    fun S => mul_mem_int hM1 (liftRes_mem S)
  let φ : (A → B → Res k e) → (A → B → Res k e) := fun S i j =>
    Ideal.Quotient.mk _ (⟨(M.val * liftRes S) i j, hint S i j⟩ : 𝒪[k])
  have h1 : ∀ S i j, c * (liftRes (φ S) i j - (M.val * liftRes S) i j) ∈ 𝒪[k] := by
    intro S i j
    have := (mk_eq_iff hϖ e (Quotient.out (φ S i j)) ⟨(M.val * liftRes S) i j, hint S i j⟩).1
      (Ideal.Quotient.mk_out _)
    exact this
  have hinj : Function.Injective φ := by
    intro S S' h
    have hd : ∀ i j, c * ((M.val * liftRes S) i j - (M.val * liftRes S') i j) ∈ 𝒪[k] := fun i j =>
      (mk_eq_iff hϖ e ⟨_, hint S i j⟩ ⟨_, hint S' i j⟩).1 (congrFun (congrFun h i) j)
    have hD : ∀ i j, (c • (M.val * liftRes S - M.val * liftRes S')) i j ∈ 𝒪[k] := fun i j => by
      simpa [mul_sub] using hd i j
    have hL : c • (liftRes S - liftRes S') = (M⁻¹).val * (c • (M.val * liftRes S - M.val * liftRes S')) := by
      rw [Matrix.mul_smul, ← Matrix.mul_sub, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul]
    funext i j
    have hij : c * (((Quotient.out (S i j) : 𝒪[k]) : k) - ((Quotient.out (S' i j) : 𝒪[k]) : k)) ∈ 𝒪[k] := by
      have := mul_mem_int hM2 hD i j
      rw [← hL] at this
      simpa [liftRes, mul_sub] using this
    have := (mk_eq_iff hϖ e (Quotient.out (S i j)) (Quotient.out (S' i j))).2 hij
    rwa [Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] at this
  have hbij : Function.Bijective φ := Finite.injective_iff_bijective.1 hinj
  rw [← Fintype.sum_bijective φ hbij (fun S => f ((ϖ ^ e)⁻¹ • liftRes (φ S))) (fun S => f ((ϖ ^ e)⁻¹ • liftRes S)) (fun _ => rfl)]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hsm : ∀ N : Matrix A B k, (ϖ ^ e)⁻¹ • N = c • N := fun N => rfl
  rw [hsm, hsm, Matrix.mul_smul]
  have : c • liftRes (φ S) = c • (M.val * liftRes S) + c • (liftRes (φ S) - M.val * liftRes S) := by
    rw [← smul_add, add_sub_cancel]
  rw [this, hf]
  intro i j
  simpa [mul_sub] using h1 S i j

end GlobalTheory.ResSumInv
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.ColSubst

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem liftRes_mul_sub {A C : Type} [Fintype C] {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (T : A → C → Res k e)
    (N : Matrix C C 𝒪[k]) (i : A) (j : C) :
    valuation k ((liftRes (Matrix.of T * N.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e)) :
        A → C → Res k e) - liftRes T * N.map (fun x => (x : k))) i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) := by
  set r : 𝒪[k] := Quotient.out ((Matrix.of T * N.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e))) i j) -
    ∑ l, Quotient.out (T i l) * N l j with hr
  have h1 : ((liftRes (Matrix.of T * N.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e)) :
        A → C → Res k e) - liftRes T * N.map (fun x => (x : k))) i j) = (r : k) := by
    simp [hr, liftRes, Matrix.mul_apply]

  rw [h1, ← GlobalTheory.SplitFlip.Model.val_le_iff_mem hϖ, ← Ideal.Quotient.eq_zero_iff_mem, hr, map_sub, map_sum]
  simp [Matrix.mul_apply, Ideal.Quotient.mk_out]

theorem sum_liftRes_mul {A C : Type} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ)
    (N N' : Matrix C C 𝒪[k]) (hN : N * N' = 1) (F : Matrix A C k → ℂ)
    (hF : ∀ T Z : Matrix A C k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) → F (T + Z) = F T) :
    ∑ T : A → C → Res k e, F (liftRes T * N.map (fun x => (x : k))) = ∑ T : A → C → Res k e, F (liftRes T) := by
  classical
  set π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) with hπ
  let φ : (A → C → Res k e) → (A → C → Res k e) := fun T => Matrix.of T * N.map π
  have hinj : Function.Injective φ := by
    intro T T' h
    have h2 := congrArg (fun M : Matrix A C (Res k e) => M * N'.map π) h
    simp only [φ, Matrix.mul_assoc, ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero π) (map_one π),
      Matrix.mul_one] at h2
    exact h2
  have hbij : Function.Bijective φ := Finite.injective_iff_bijective.1 hinj
  rw [← hbij.sum_comp (fun T => F (liftRes T))]
  refine Finset.sum_congr rfl fun T _ => ?_
  symm
  rw [show liftRes (φ T) = liftRes T * N.map (fun x => (x : k)) +
    (liftRes (φ T) - liftRes T * N.map (fun x => (x : k))) by abel]
  exact hF _ _ fun i j => liftRes_mul_sub hϖ e T N i j

end GlobalTheory.ColSubst
end
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

open scoped Pointwise

noncomputable section

namespace GlobalTheory.TrEll

theorem torPt_mul_comm {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k] (a b : HR k (star' P) (one₁ P)) : a * b = b * a := by
  apply Subtype.ext; apply Units.ext; ext i j
  simp [Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0]
  exact mul_comm _ _

theorem eventually_unitLoc_orbCls : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (1 : Cls P (Fv F v)) ∈ XSet P (Fv F v) J ∧ (∀ (γ : GLoc σ J v) q, HasCls P (Fv F v) J γ q → (∃ g, g⁻¹ * γ * g ∈ stabLoc σ J L v) → q = 1) ∧ (∀ (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin r → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), gam h ∈ stabLoc σ J L v → ∀ t, torEmb h t ∈ stabLoc σ J L v ↔ t ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v) ∧ ∀ (μ : Measure (GLoc σ J v)) (dt : Measure (Tor P (Fv F v))), μ.IsHaarMeasure → dt.IsHaarMeasure → μ (stabLoc σ J L v) = 1 → dt (stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v) = 1 → ∀ q : XSet P (Fv F v) J, (q.1 = 1 → orbCls μ dt (unitLoc σ J L v) q = 1) ∧ (q.1 ≠ 1 → orbCls μ dt (unitLoc σ J L v) q = 0) := by
  intro F E _ _ _ _ _ σ hE r P J hJ L _
  have hsep : P.1.Separable := P.2.2.1.separable
  filter_upwards [GlobalTheory.T.eventually_unitClass_realized_by_lattice_isometry F E σ hE r P J hJ L, eventually_conj_of_charpoly_eq hE hJ L hsep] with v hu hc
  obtain ⟨φ₁, h₁, hγ₁, hT₁⟩ := hu
  have hcp : ∀ (x : plusUnits P (Fv F v)) φ (h : IsIsom P (Fv F v) J x.1.1 φ),
      (matHom _ σ J (gam h)).1.charpoly = P.1.map (inclR (Fv F v)) :=
    fun x φ h => (GlobalTheory.T.torusElement_charpoly_regular_centralizer F E σ hE r r P J hJ (Fv F v) x φ h).1
  have hcpc : ∀ g y : GLoc σ J v,
      (matHom _ σ J (y⁻¹ * g * y)).1.charpoly = (matHom _ σ J g).1.charpoly := fun g y => by
    rw [map_mul, map_mul, map_inv, charpoly_conj_GL]
  have hcls : ∀ (γ : GLoc σ J v) q, HasCls P (Fv F v) J γ q → (∃ g, g⁻¹ * γ * g ∈ stabLoc σ J L v) → q = 1 := by
    rintro γ q ⟨x, φ, h, rfl, rfl⟩ ⟨g, hg⟩
    obtain ⟨k, hk, hkg⟩ := hc _ hg _ hγ₁ (by rw [hcpc]; exact hcp x φ h) (hcp 1 φ₁ h₁)
    exact (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hE r r P J hJ (Fv F v) x φ h 1 φ₁ h₁).2.1
      (isConj_iff.2 ⟨(g * k)⁻¹, by rw [← hkg]; group⟩)
  refine ⟨⟨1, φ₁, rfl, h₁⟩, hcls, ?_, ?_⟩
  · intro x φ h hγ t
    obtain ⟨k, hk, hkg⟩ := hc _ hγ _ hγ₁ (hcp x φ h) (hcp 1 φ₁ h₁)
    have ht := (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hE r r P J hJ (Fv F v) x φ h 1 φ₁ h₁).2.2.1 k⁻¹ (by rw [inv_inv, hkg]) t
    rw [← hT₁ t, ht, inv_inv, Subgroup.mul_mem_cancel_right _ hk, Subgroup.mul_mem_cancel_left _ (inv_mem hk)]
  · intro μ dt hμ hdt hμK hdtK q
    have hK := isOpen_stabLoc σ J L v
    have hKc := isCompact_stabLoc σ J L v
    refine ⟨fun hq => ?_, fun hq => ?_⟩
    · have hcont : Continuous (unitLoc σ J L v) :=
        (IsClopen.continuous_indicator ⟨Subgroup.isClosed_of_isOpen _ hK, hK⟩ continuous_const)
      have hcs : HasCompactSupport (unitLoc σ J L v) :=
        HasCompactSupport.intro hKc fun y hy => indicator_of_notMem hy _
      have h1 := ((GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hE r r P J hJ).1 v μ dt (unitLoc σ J L v) hμ hdt hcont hcs).2 1 φ₁ h₁
      have hqe : (⟨QuotientGroup.mk 1, 1, φ₁, rfl, h₁⟩ : XSet P (Fv F v) J) = q := Subtype.ext (by rw [hq]; rfl)
      rw [hqe] at h1
      obtain ⟨e, he1, he2⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure F E σ hE r r P J hJ (Fv F v) 1 φ₁ h₁
      rw [he2] at h1
      haveI := hμ
      haveI := hdt
      haveI : (dt.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map dt e
      have hcomm : ∀ a b : cent (gam h₁), a * b = b * a := fun a b => by
        apply e.symm.injective
        rw [map_mul, map_mul]
        exact torPt_mul_comm P (Fv F v) (e.symm a) (e.symm b)
      haveI : (dt.map e).IsMulRightInvariant := ⟨fun g => by
        have : (fun x : cent (gam h₁) => x * g) = (fun x => g * x) := funext fun x => hcomm x g
        rw [this]; exact map_mul_left_eq_self _ g⟩
      have hset : conjFn (gam h₁) (unitLoc σ J L v) =
          ((cent (gam h₁) : Set (GLoc σ J v)) * (stabLoc σ J L v : Set (GLoc σ J v))).indicator 1 := by
        funext y
        have hmem : y⁻¹ * gam h₁ * y ∈ stabLoc σ J L v ↔
            y ∈ (cent (gam h₁) : Set (GLoc σ J v)) * (stabLoc σ J L v : Set (GLoc σ J v)) := by
          refine ⟨fun hy => ?_, ?_⟩
          · obtain ⟨k, hk, hkg⟩ := hc _ hy _ hγ₁ (by rw [hcpc]; exact hcp 1 φ₁ h₁) (hcp 1 φ₁ h₁)
            refine ⟨y * k, mem_cent.2 ?_, k⁻¹, inv_mem hk, by group⟩
            calc y * k * gam h₁ = y * k * (k⁻¹ * (y⁻¹ * gam h₁ * y) * k) := by rw [hkg]
              _ = gam h₁ * (y * k) := by group
          · rintro ⟨t, ht, k, hk, rfl⟩
            have : (t * k)⁻¹ * gam h₁ * (t * k) = k⁻¹ * (t⁻¹ * (gam h₁ * t)) * k := by group
            rw [this, ← mem_cent.1 ht, inv_mul_cancel_left]
            exact mul_mem (mul_mem (inv_mem hk) hγ₁) hk
        by_cases hy : y ∈ (cent (gam h₁) : Set (GLoc σ J v)) * (stabLoc σ J L v : Set (GLoc σ J v))
        · rw [Set.indicator_of_mem hy]
          exact Set.indicator_of_mem (hmem.2 hy) _
        · rw [Set.indicator_of_notMem hy]
          exact Set.indicator_of_notMem (mt hmem.1 hy) _
      have h2 := hasQuotInt_indicator_mul (dt := dt.map e) (dh := μ) (isClosed_cent (gam h₁)) hK hKc
      rw [HasOrbInt, hset] at h1
      rw [← h1.2, h2.2]
      have hpre : e ⁻¹' ((stabLoc σ J L v).subgroupOf (cent (gam h₁)) : Set (cent (gam h₁))) =
          (stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v : Set (Tor P (Fv F v))) := by
        ext t
        simp [Subgroup.mem_subgroupOf, he1, hT₁]
      have hm : (dt.map e) ((stabLoc σ J L v).subgroupOf (cent (gam h₁))) = 1 := by
        rw [Measure.map_apply (show Measurable e from e.continuous.measurable) (show MeasurableSet ((stabLoc σ J L v).subgroupOf (cent (gam h₁)) : Set (cent (gam h₁))) from
          (hK.preimage continuous_subtype_val).measurableSet), hpre, hdtK]
      simp [Measure.real, hμK, hm]
    · have hrep := q.2.choose_spec.choose_spec
      have h0 : conjFn (gam hrep.2) (unitLoc σ J L v) = 0 := by
        funext y
        by_cases hy : y⁻¹ * gam hrep.2 * y ∈ stabLoc σ J L v
        · exact absurd (hcls _ _ ⟨_, _, hrep.2, hrep.1, rfl⟩ ⟨y, hy⟩) hq
        · exact Set.indicator_of_notMem hy _
      rw [orbCls, orbInt, h0]
      simp [quotInt, descend]
end TrEll
end GlobalTheory
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lintegral_thetaLift_termSum_ne_top : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → ∀ F : GA D W → ℂ, GlobalTheory.Grow.RapidDec W F → ∀ (Sg : GA D V × GA D W → ℝ≥0∞), (∀ n ∈ NI V C, n ∈ GQ V → ∀ a b, Sg (n * a, b) = Sg (a, b)) → (∀ γ ∈ GQ W, ∀ a b, Sg (a, γ * b) = Sg (a, b)) → ∀ (A : ℕ) (c : ℝ), (∀ a b, Sg (a, b) ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V a * GlobalTheory.Grow.height W b) ^ A)) → ∀ g : GA D V, ∫⁻ n in 𝓝, ∫⁻ h in 𝓕, Sg ((n : GA D V) * g, h) * ‖F h‖ₑ ∂ν ∂κ ≠ ⊤ := by
  first | exact @GlobalTheory.ThetaLiftBound.lintegral_ne_top | exact GlobalTheory.ThetaLiftBound.lintegral_ne_top | (intros; apply GlobalTheory.ThetaLiftBound.lintegral_ne_top <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tendsto_moderateGrowthSize_differenceQuotient : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (N : ℕ), ∀ X ∈ lieAt V τ, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V 2 N φ ≠ ⊤ → Filter.Tendsto (fun t : ℝ => GlobalTheory.Size.growthSize V N (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  first | exact @GlobalTheory.Size.DiffQuot.tendsto_growthSize_diffQuot | exact GlobalTheory.Size.DiffQuot.tendsto_growthSize_diffQuot | (intros; apply GlobalTheory.Size.DiffQuot.tendsto_growthSize_diffQuot <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.moderateGrowthSobolevSize_rightTranslate_polyBound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (d N : ℕ), ∃ (C : NNReal) (m : ℕ), ∀ h ∈ GinfC V, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V d N (rTr V h φ) ≤ (C : ENNReal) * ENNReal.ofReal (GlobalTheory.Grow.height V h ^ m) * GlobalTheory.Size.growthSob θ V d N φ := by
  first | exact @GlobalTheory.Size.Translate.growthSob_rTr_le | exact GlobalTheory.Size.Translate.growthSob_rTr_le | (intros; apply GlobalTheory.Size.Translate.growthSob_rTr_le <;> assumption)
end
