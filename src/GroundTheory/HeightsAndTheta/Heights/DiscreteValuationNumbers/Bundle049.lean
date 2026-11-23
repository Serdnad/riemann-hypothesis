module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericCycleCorresp
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle002
public import Mathlib.RingTheory.Ideal.Height
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAB
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

universe u

section PolynomialHeights

variable {σ : Type*} [Finite σ]

theorem ringKrullDim_mvPolynomial_dvr (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] :
    ringKrullDim (MvPolynomial σ O) = ((Nat.card σ + 1 : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one]
  rw [ENat.card_eq_coe_natCard]
  push_cast
  ring

theorem height_mvPolynomial_field_of_isMaximal {k : Type*} [Field k]
    (M : Ideal (MvPolynomial σ k)) (hM : M.IsMaximal) :
    (M.height : WithBot ℕ∞) = (Nat.card σ : WithBot ℕ∞) := by
  have h := DimF.height_eq_ringKrullDim_of_forall
    (DimF.height_eq_of_isMaximal_of_field (k := k)) M hM
  rw [h, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp [ENat.card_eq_coe_natCard]

theorem le_height_of_isMaximal_of_uniformiser_mem {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) (m : Ideal (MvPolynomial σ O))
    (hm : m.IsMaximal) (hϖm : (C ϖ : MvPolynomial σ O) ∈ m) :
    ((Nat.card σ + 1 : ℕ) : ℕ∞) ≤ m.height := by
  set p0 : Ideal (MvPolynomial σ O) := Ideal.map C (IsLocalRing.maximalIdeal O) with hp0def
  have hp0 : p0 = Ideal.span {C ϖ} := by
    rw [hp0def, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  let e : (MvPolynomial σ O ⧸ p0) ≃+* MvPolynomial σ (IsLocalRing.ResidueField O) :=
    (MvPolynomial.quotientEquivQuotientMvPolynomial (IsLocalRing.maximalIdeal O)).symm.toRingEquiv
  have hdom : IsDomain (MvPolynomial σ O ⧸ p0) := Function.Injective.isDomain e.toRingHom (by exact e.injective)
  have hp0p : p0.IsPrime := (Ideal.Quotient.isDomain_iff_prime p0).mp hdom
  have hle : p0 ≤ m := by
    rw [hp0]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hϖm)
  have hmb : (m.map (Ideal.Quotient.mk p0)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hle)
  have h1 : (m.map (Ideal.Quotient.mk p0)).height = Nat.card σ := by
    rw [← e.height_map]
    have := height_mvPolynomial_field_of_isMaximal (k := IsLocalRing.ResidueField O) _
      (Ideal.map_isMaximal_of_equiv e (p := m.map (Ideal.Quotient.mk p0)))
    exact_mod_cast this
  have h0 : 1 ≤ p0.height := by
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot, hp0,
      Ideal.span_singleton_eq_bot, C_eq_zero]
    exact hϖ.ne_zero
  have hfin : FiniteRingKrullDim (MvPolynomial σ O) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top, ringKrullDim_mvPolynomial_dvr]
    exact ⟨by simp, by
      rw [← WithBot.coe_natCast]
      exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))⟩
  have h2 := DimF.height_add_height_map_le (q := p0) (M := m) hle
  rw [h1] at h2
  calc ((Nat.card σ + 1 : ℕ) : ℕ∞) = 1 + (Nat.card σ : ℕ∞) := by push_cast; ring
    _ ≤ p0.height + (Nat.card σ : ℕ∞) := add_le_add h0 le_rfl
    _ ≤ m.height := h2

theorem ringKrullDim_quotient_le_sub_height {A : Type*} [CommRing A] [IsNoetherianRing A]
    [FiniteRingKrullDim A] (P : Ideal A) [P.IsPrime] (N h : ℕ)
    (hmax : ∀ m : Ideal A, m.IsMaximal → m.height ≤ N) (hP : P.height = h) :
    ringKrullDim (A ⧸ P) ≤ ((N - h : ℕ) : WithBot ℕ∞) := by
  refine (ringKrullDim_le_iff_isMaximal_height_le _).mpr fun M hM => ?_
  have hc : (M.comap (Ideal.Quotient.mk P)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have : (M.comap (Ideal.Quotient.mk P)).IsPrime := hc.isPrime
  have hPle : P ≤ M.comap (Ideal.Quotient.mk P) := fun x hx => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact M.zero_mem
  have e : (M.comap (Ideal.Quotient.mk P)).map (Ideal.Quotient.mk P) = M :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective M
  have h2 := DimF.height_add_height_map_le (q := P) (M := M.comap (Ideal.Quotient.mk P)) hPle
  rw [e, hP] at h2
  have h3 := DimF.le_natSub_of_add_le (h2.trans (hmax _ hc))
  calc (M.height : WithBot ℕ∞) ≤ (((N - h : ℕ) : ℕ∞) : WithBot ℕ∞) := WithBot.coe_le_coe.mpr h3
    _ = ((N - h : ℕ) : WithBot ℕ∞) := WithBot.coe_natCast _

theorem withBot_eq_of_le_of_add_one_le {x : WithBot ℕ∞} {c : ℕ} (h1 : (c : WithBot ℕ∞) ≤ x)
    (h2 : x + 1 ≤ ((c + 1 : ℕ) : WithBot ℕ∞)) : x = c :=
  _root_.UpperTheory.Reformulated.B.Ydd3.withBot_eq_of_le_of_add_one_le h1 h2

end PolynomialHeights

theorem ComponentDim.proof : ComponentDim.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a f hfa hfP W hW hϖW
  have hWmin : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  have hWp : W.IsPrime := hWmin.1.1
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hfW : f ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))

  have hup := ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_dim_add_one_le hPW hfW hfP

  have hq : W.map (Ideal.Quotient.mk P) ∈ (Ideal.span {Ideal.Quotient.mk P f}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk P f} = (Ideal.span {f}).map (Ideal.Quotient.mk P) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_comm]
    exact ⟨W, hWmin, rfl⟩
  have : (W.map (Ideal.Quotient.mk P)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk P f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hk : (W.map (Ideal.Quotient.mk P)).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq

  obtain ⟨m, hm, hWm⟩ := Ideal.exists_le_maximal W hWp.ne_top
  have : m.IsPrime := hm.isPrime
  have hmge := le_height_of_isMaximal_of_uniformiser_mem hϖ m hm (hWm hϖW)
  have hdimS := ringKrullDim_mvPolynomial_dvr (σ := Σ k, ι k) O
  have hfin : FiniteRingKrullDim (MRing ι O) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top, hdimS]
    exact ⟨by rw [← WithBot.coe_natCast]; exact WithBot.coe_ne_bot, by
      rw [← WithBot.coe_natCast]
      exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))⟩
  have hmax : ∀ m' : Ideal (MRing ι O), m'.IsMaximal →
      m'.height ≤ ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := by
    intro m' hm'
    have := Ideal.height_le_ringKrullDim_of_ne_top hm'.ne_top
    rw [hdimS] at this
    exact_mod_cast this
  have hmeq : m.height = ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := le_antisymm (hmax m hm) hmge

  have hcat1 := DimF.height_eq_height_add_of_isRegularRing P W hPW
  have hcat2 := DimF.height_eq_height_add_of_isRegularRing W m hWm
  have hsum : P.height + (W.map (Ideal.Quotient.mk P)).height + (m.map (Ideal.Quotient.mk W)).height
      = ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := by
    rw [← hcat1, ← hcat2, hmeq]
  have hPfin : P.height ≠ ⊤ := fun h => by
    simp only [h, top_add] at hsum; exact ENat.top_ne_natCast _ hsum
  have hafin : (W.map (Ideal.Quotient.mk P)).height ≠ ⊤ := fun h => by
    simp only [h, top_add, add_top] at hsum; exact ENat.top_ne_natCast _ hsum
  have hbfin : (m.map (Ideal.Quotient.mk W)).height ≠ ⊤ := fun h => by
    simp only [h, add_top] at hsum; exact ENat.top_ne_natCast _ hsum
  obtain ⟨h0, hh0⟩ : ∃ h0 : ℕ, P.height = h0 := ⟨_, (ENat.natCast_toNat hPfin).symm⟩
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℕ, (W.map (Ideal.Quotient.mk P)).height = a0 :=
    ⟨_, (ENat.natCast_toNat hafin).symm⟩
  obtain ⟨b0, hb0⟩ : ∃ b0 : ℕ, (m.map (Ideal.Quotient.mk W)).height = b0 :=
    ⟨_, (ENat.natCast_toNat hbfin).symm⟩
  rw [hh0, ha0, hb0] at hsum
  rw [ha0] at hk
  have hsum' : h0 + a0 + b0 = Nat.card (Σ k, ι k) + 1 := by exact_mod_cast hsum
  have hk' : a0 ≤ 1 := by exact_mod_cast hk

  have hPdim := ringKrullDim_quotient_le_sub_height P (Nat.card (Σ k, ι k) + 1) h0 hmax hh0
  rw [hP.dim] at hPdim
  have hPdim' : d + 1 + Fintype.card K ≤ Nat.card (Σ k, ι k) + 1 - h0 := by exact_mod_cast hPdim

  have hlow := Ideal.height_le_ringKrullDim_of_ne_top
    (DimF.isPrime_map_mk (A := MRing ι O) (q := W) (M := m) hWm).ne_top
  rw [hb0] at hlow
  have hb' : d + Fintype.card K ≤ b0 := by omega
  have hlow' : ((d + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ W) :=
    le_trans (by exact_mod_cast hb') hlow
  rw [hP.dim] at hup
  exact withBot_eq_of_le_of_add_one_le hlow' (by rw [show d + Fintype.card K + 1 = d + 1 + Fintype.card K by ring]; exact hup)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem DivCycleMul.full : DivCycleMul.Statement.{u} := DivCycleMul.proof

theorem DivCycleFiniteSupport.full : DivCycleFiniteSupport.Statement.{u} :=
  DivCycleFiniteSupport.proof

theorem SupSpanMultiHomog.full : SupSpanMultiHomog.Statement.{u} := SupSpanMultiHomog.proof

theorem MinimalPrimeMultiHomog.full : MinimalPrimeMultiHomog.Statement.{u} :=
  MinimalPrimeMultiHomog.proof

theorem SpecialQuotDim.full : SpecialQuotDim.Statement.{u} := SpecialQuotDim.proof

theorem MaximalIdealHeightFG.full : MaximalIdealHeightFG.Statement.{u} := MaximalIdealHeightFG.proof

theorem GenericDimBound.full : GenericDimBound.Statement.{u} :=
  GenericDimBound.proof MaximalIdealHeightFG.full

theorem GenericFibProps.full : GenericFibProps.Statement.{u} := GenericFibProps.proof

theorem GenericCycleCorresp.full : GenericCycleCorresp.Statement.{u} := GenericCycleCorresp.proof

theorem ConservationOfNumberLE.full : ConservationOfNumberLE.Statement.{u} :=
  ConservationOfNumberLE.proof IntNumAssoc.full SpecialCycleEval.full SpecialPieceRank.full
    GenericPieceRank.full SpecialIdealMultiHomog.full

theorem UniformiserCase.full : UniformiserCase.Statement.{u} :=
  UniformiserCase.proof ConservationOfNumberLE.full GenericDimBound.full GenericFibProps.full
    GenericCycleCorresp.full MinimalPrimeMultiHomog.full SupSpanMultiHomog.full DimStrictDrop.full
    CutByForm.full

theorem ShiftByUniformiser.full : ShiftByUniformiser.Statement.{u} :=
  ShiftByUniformiser.proof DivCycleMul.full DivCycleFiniteSupport.full

theorem EffectiveShift.full : EffectiveShift.Statement.{u} := EffectiveShift.proof

theorem Representative.full : Representative.Statement.{u} := Representative.proof DivCycleMul.full

theorem IntNumAddFirst.full : IntNumAddFirst.Statement.{u} :=
  IntNumAddFirst.proof FieldNumbers.IntNumAdd.full FieldNumbers.IntNumZeroSlot.full
    FieldNumbers.HilbDegreeBound.full

theorem EffectiveCase.of_steps (h₀ : NoCommonComponentCase.Statement.{u}) (h₁ : CommonFactorInduction.Statement.{u}) :
    EffectiveCase.Statement.{u} :=
  EffectiveCase.proof h₀ h₁

theorem CutByEffectiveDivisor.of_steps (h₀ : NoCommonComponentCase.Statement.{u})
    (h₁ : CommonFactorInduction.Statement.{u}) : CutByEffectiveDivisor.Statement.{u} :=
  CutByEffectiveDivisor.proof (EffectiveCase.of_steps h₀ h₁) UniformiserCase.full
    ShiftByUniformiser.full EffectiveShift.full

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem IntNumIsFieldIntersection.full : IntNumIsFieldIntersection.Statement.{u} :=
  IntNumIsFieldIntersection.of_intNumBase_cutRational FieldNumbers.IntNumBase.full
    FieldNumbers.CutRational.full

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace dividedDifferenceExpansion

theorem prod_split {M : Type*} [CommMonoid M] {r : ℕ} (l : Fin r) (f : Fin r → M) :
    ∏ j, f j = (∏ j ∈ Finset.univ.filter (fun j => j < l), f j) * f l *
      ∏ j ∈ Finset.univ.filter (fun j => l < j), f j := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => j < l),
    ← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter fun j => ¬ j < l) (fun j => j = l),
    Finset.filter_filter, Finset.filter_filter, mul_assoc]
  congr 2
  · rw [Finset.prod_eq_single l]
    · intro b hb hbl
      simp only [Finset.mem_filter] at hb
      exact absurd hb.2.2 hbl
    · intro h
      exact absurd (by simp) h
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
    · intro h
      exact ⟨not_lt.mpr h.le, ne_of_gt h⟩

noncomputable def stair {r : ℕ} (μ : Fin r →₀ ℕ) (k : ℕ) : MvPolynomial (Fin r ⊕ Fin r) ℤ :=
  ∏ j : Fin r, X (if (j : ℕ) < k then Sum.inr j else Sum.inl j) ^ μ j

theorem stair_zero {r : ℕ} (μ : Fin r →₀ ℕ) : stair μ 0 = ∏ j, X (Sum.inl j) ^ μ j := by
  simp [stair]

theorem stair_top {r : ℕ} (μ : Fin r →₀ ℕ) : stair μ r = ∏ j, X (Sum.inr j) ^ μ j := by
  simp [stair]

theorem term_eq {r : ℕ} (μ : Fin r →₀ ℕ) (l : Fin r) :
    (X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
      ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
        (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
        ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) =
      stair μ l - stair μ (l + 1) := by
  have hg : (X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
      (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) =
      X (Sum.inl l) ^ μ l - X (Sum.inr l) ^ μ l := by
    rw [mul_comm]
    exact geom_sum₂_mul _ _ _
  have hlo : ∀ k : ℕ, (l : ℕ) ≤ k →
      ∏ j ∈ Finset.univ.filter (fun j => j < l),
          (X (if (j : ℕ) < k then Sum.inr j else Sum.inl j) : MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j =
        ∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j := by
    intro k hk
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' : (j : ℕ) < l := Fin.lt_def.mp (Finset.mem_filter.mp hj).2
    rw [if_pos (by omega)]
  have hhi : ∀ k : ℕ, k ≤ (l : ℕ) + 1 →
      ∏ j ∈ Finset.univ.filter (fun j => l < j),
          (X (if (j : ℕ) < k then Sum.inr j else Sum.inl j) : MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j =
        ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j := by
    intro k hk
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' : (l : ℕ) < j := Fin.lt_def.mp (Finset.mem_filter.mp hj).2
    rw [if_neg (by omega)]
  unfold stair
  rw [prod_split l, prod_split l (fun j => (X (if (j : ℕ) < (l : ℕ) + 1 then Sum.inr j else Sum.inl j) :
      MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j), hlo l le_rfl, hlo (l + 1) (by omega),
    hhi l (by omega), hhi (l + 1) le_rfl, if_neg (lt_irrefl _), if_pos (Nat.lt_succ_self _)]
  linear_combination
    ((∏ j ∈ Finset.univ.filter (fun j => j < l), (X (Sum.inr j) : MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j) *
      ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) * hg

theorem sum_term_eq {r : ℕ} (μ : Fin r →₀ ℕ) :
    ∑ l : Fin r, (X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
      ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
        (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
        ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) =
      ∏ j, X (Sum.inl j) ^ μ j - ∏ j, X (Sum.inr j) ^ μ j := by
  simp_rw [term_eq]
  rw [Fin.sum_univ_eq_sum_range (fun i => stair μ i - stair μ (i + 1)) r,
    Finset.sum_range_sub', stair_zero, stair_top]

theorem rename_eq_sum {r : ℕ} (f : Fin r → Fin r ⊕ Fin r) (G : MvPolynomial (Fin r) ℤ) :
    rename f G = ∑ μ ∈ G.support, C (G.coeff μ) * ∏ j, X (f j) ^ μ j := by
  conv_lhs => rw [G.as_sum]

  rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), map_mul, rename_C, map_prod]
  simp [map_pow, rename_X]

theorem rename_divDiff {r : ℕ} (l : Fin r) (G : MvPolynomial (Fin r) ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G) =
      ∑ μ ∈ G.support, C (G.coeff μ) *
        ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
          (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
          ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff

  simp only [map_sum, map_mul, map_prod, map_pow, rename_X, rename_C,
  finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

theorem proof : dividedDifferenceExpansion.Statement := by
  intro r m G hG
  refine ⟨?_, ?_⟩
  · rw [rename_eq_sum, rename_eq_sum, ← Finset.sum_sub_distrib]
    calc ∑ μ ∈ G.support, (C (G.coeff μ) * ∏ j, X (Sum.inl j) ^ μ j -
            C (G.coeff μ) * ∏ j, X (Sum.inr j) ^ μ j)
        = ∑ μ ∈ G.support, ∑ l : Fin r, C (G.coeff μ) *
            ((X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
              ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
                (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
                ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j)) :=
          Finset.sum_congr rfl fun μ _ => by rw [← Finset.mul_sum, sum_term_eq, mul_sub]
      _ = ∑ l : Fin r, ∑ μ ∈ G.support, C (G.coeff μ) *
            ((X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
              ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
                (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
                ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j)) :=
          Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun l _ => by
          rw [rename_divDiff, Finset.mul_sum]
          exact Finset.sum_congr rfl fun μ _ => by ring
  · intro l
    rcases m with _ | d
    · have h0 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G = 0 := by
        unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff
        refine Finset.sum_eq_zero fun μ hμ => ?_
        have h := hG (mem_support_iff.mp hμ)
        rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
        have hl : μ l = 0 := by
          have h' : ∑ j, μ j = 0 := by simpa using h
          exact (Finset.sum_eq_zero_iff.mp h') l (Finset.mem_univ l)
        simp [hl]
      rw [h0, map_zero]
      exact isHomogeneous_zero _ _ _
    · simpa using (BundleExamples.isHomogeneous_divDiff l hG).rename_isHomogeneous
        (f := finSumFinEquiv.symm)

end dividedDifferenceExpansion

end GroundTheory.Heights₂.Heights.NumbersDVR
end
