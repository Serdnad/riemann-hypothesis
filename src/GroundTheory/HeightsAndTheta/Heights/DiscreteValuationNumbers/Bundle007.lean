module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Order.Filter.AtTopBot.Group
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

def divisorIdeal (P : Ideal (MRing ι R)) (f g : MRing ι R) : Ideal (MRing ι R) :=
  (P ⊔ Ideal.span {f}).colon {g}

end Defs

section Lemmas

def VNumCut.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (G : Ideal (MRing ι O)) (n : ℕ), G.IsPrime → IsMultiHomogIdeal G → (C ϖ : MRing ι O) ∈ G →
    ringKrullDim (MRing ι O ⧸ G) < ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (s : MRing ι O) (c : K → ℕ), IsMultiHomog s c → s ∉ G →
    ∀ bs : Fin n → K → ℤ,
      vNum G (Matrix.vecCons (fun k => (c k : ℤ)) bs) = cycEval (fun U => vNum U bs) (divCycle G s)

def DivisorIdealCycle.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] [DecidableEq K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι R)) (f g u v : MRing ι R),
    P.IsPrime → W.IsPrime → P ≤ W → g ∉ P →
    (∀ U : Ideal (MRing ι R), U.IsPrime → W ≤ U → IsRelevant U →
      ∃ u' v' : MRing ι R, u' ∉ U ∧ u' * f - v' * g ∈ P) →
    u ∉ W → v ∉ W → u * f - v * g ∈ P →
    ratDiv W v u = idealCycle (W ⊔ divisorIdeal P f g)

def VertCutEff.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P (n + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (W : Ideal (MRing ι O)) (x : MRing ι O), x ∉ P → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W → IsMultiHomogIdeal W → (C ϖ : MRing ι O) ∈ W → ratDiv P f g W = 0 →
    ∀ L : Fin n → K → ℤ,
      vNum W (Matrix.vecCons b L) =
        cycEval (fun U => vNum U L) (idealCycle (W ⊔ divisorIdeal P f g))

def LeftExpansion.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ G, (C ϖ : MRing ι O) ∈ G → divCycle P s G ≠ 0 → ratDiv P f g G = 0) →
    ∀ L : Fin d → K → ℤ,
      cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
        cycEval (fun U => vNum U L) (fun U => cycEval (fun G => divCycle G s U) (ratDiv P f g))


open Classical in
def RightExpansion.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∀ G, (C ϖ : MRing ι O) ∈ G → divCycle P s G ≠ 0 → ratDiv P f g G = 0) →
    ∀ L : Fin d → K → ℤ,
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
          else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s) =
        cycEval (fun U => vNum U L)
          (fun U => cycEval (fun W => idealCycle (W ⊔ divisorIdeal P f g) U) (divCycle P s))

def LocalCoefficient.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∀ G, (C ϖ : MRing ι O) ∈ G → divCycle P s G ≠ 0 → ratDiv P f g G = 0) →
    ∀ U : Ideal (MRing ι O),
      (U.IsPrime → IsMultiHomogIdeal U → IsRelevant U → (C ϖ : MRing ι O) ∈ U →
        ((d + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ U)) →
      cycEval (fun G => divCycle G s U) (ratDiv P f g) =
        cycEval (fun W => idealCycle (W ⊔ divisorIdeal P f g) U) (divCycle P s)

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem mem_minimalPrimes_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*}
    [CommRing R] {P : Ideal (MRing ι R)} {f : MRing ι R} {W : Ideal (MRing ι R)}
    (h : divCycle P f W ≠ 0) : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW
  · exact absurd rfl h

theorem ratDiv_one {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R] (P : Ideal (MRing ι R))
    (f : MRing ι R) : ratDiv P f 1 = divCycle P f := by
  funext W
  rw [ratDiv, divCycle_one, sub_zero]

theorem mixedDiff_cons_zero {K : Type*} {n : ℕ} (L : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) :
    mixedDiff (Matrix.vecCons 0 L) h = 0 := by
  unfold mixedDiff
  rw [List.ofFn_succ, List.foldr_cons, Matrix.cons_val_zero]
  funext m
  simp [diffStep]

theorem eventualValue_zero {K : Type*} : eventualValue (0 : (K → ℤ) → ℤ) = 0 := by
  unfold eventualValue
  split_ifs with hc
  · obtain ⟨m, hm⟩ := hc.choose_spec.exists
    exact hm.symm
  · rfl

theorem vNum_cons_zero {K : Type*} [DecidableEq K] {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (W : Ideal (MRing ι O)) {n : ℕ}
    (L : Fin n → K → ℤ) : vNum W (Matrix.vecCons 0 L) = 0 := by
  rw [vNum, intNum, mixedDiff_cons_zero, eventualValue_zero]

theorem comap_C_eq_bot_of_not_mem {K : Type*} {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    (H : Ideal (MRing ι O)) [hH : H.IsPrime] (hϖH : (C ϖ : MRing ι O) ∉ H) :
    H.comap (C : O →+* MRing ι O) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun a ha => ?_
  by_contra ha0
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  rw [Ideal.mem_comap, map_mul, map_pow] at ha
  rcases hH.mem_or_mem ha with hv | hp
  · exact hH.ne_top (Ideal.eq_top_of_isUnit_mem _ hv ((Units.isUnit v).map C))
  · exact hϖH (hH.mem_of_pow_mem n hp)

theorem withBot_le_of_add_one_le (x : WithBot ℕ∞) (N : ℕ)
    (hx : x + 1 ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) : x ≤ ((N : ℕ) : WithBot ℕ∞) :=
  by apply _root_.UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ <;> assumption

theorem withBot_lt_of_add_one_le (x : WithBot ℕ∞) (N : ℕ)
    (hx : x + 1 ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) : x < ((N + 1 : ℕ) : WithBot ℕ∞) := by
  refine lt_of_le_of_lt (withBot_le_of_add_one_le x N hx) ?_
  exact_mod_cast Nat.lt_succ_self N

theorem UniformiserCase.proof (h1 : ConservationOfNumberLE.Statement.{u})
    (h2 : GenericDimBound.Statement.{u}) (h3 : GenericFibProps.Statement.{u})
    (h4 : GenericCycleCorresp.Statement.{u}) (h5 : MinimalPrimeMultiHomog.Statement.{u})
    (h6 : SupSpanMultiHomog.Statement.{u}) (h7 : DimStrictDrop.Statement.{u})
    (h8 : CutByForm.Statement.{u}) : UniformiserCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP c s hs hsP L
  have hdim : ringKrullDim (MRing ι O ⧸ P) = ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    hP.dim
  have := hP.multiProj.isPrime

  have hL : cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P (C ϖ) 1) =
      gNum P (Matrix.vecCons (fun k => (c k : ℤ)) L) := by
    rw [ratDiv_one]
    exact h1 O ϖ hϖ K ι P (d + 1) hP.multiProj hP.noTorsion hdim.le _

  obtain ⟨hGprime, hGhom, hGs⟩ := h3 O K ι P hP.multiProj hP.noTorsion
  obtain ⟨hsG, hsG'⟩ := hGs s c hs hsP
  have hGdim : ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) <
      ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    have e : d + 2 + Fintype.card K = (d + 1 + Fintype.card K) + 1 := by omega
    rw [e]
    refine withBot_lt_of_add_one_le _ _ ?_
    have := h2 O K ι P hP.multiProj hP.noTorsion
    rw [hdim] at this
    rwa [show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by omega] at this
  have hcut := h8 (FractionRing O) K ι d (genFib P) hGprime hGhom hGdim _ c hsG hsG' L
  have hcorr := h4 O ϖ hϖ K ι P s hP.multiProj.isPrime hP.noTorsion hsP
    (fun V => intNum (FractionRing O) V L)
  rw [cutIdentity, hL, gNum, hcut, ← hcorr]

  unfold cycEval
  refine finsum_congr fun W => ?_
  by_cases hW : divCycle P s W = 0
  · rw [hW, zero_mul, zero_mul]
  congr 1
  dsimp only
  by_cases hϖW : (C ϖ : MRing ι O) ∈ W
  · rw [if_pos hϖW, if_pos hϖW, vNum_cons_zero]
  rw [if_neg hϖW, if_neg hϖW]
  obtain ⟨hWmin, hWrel⟩ := mem_minimalPrimes_of_divCycle_ne_zero hW
  obtain ⟨hWprime, hPW, -⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  have := hWprime
  have hWhom : IsMultiHomogIdeal W :=
    h5 O K ι (P ⊔ Ideal.span {s}) W (h6 O K ι P s c hP.multiProj.multiHomog hs) hWmin
  have hlt : P < W := lt_of_le_of_ne hPW fun h => hsP (h ▸ hWmin.1.2
    (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  have hWdim : ringKrullDim (MRing ι O ⧸ W) ≤ ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    refine withBot_le_of_add_one_le _ _ ?_
    have := h7 (MRing ι O) P W hlt
    rw [hdim] at this
    rwa [show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by omega] at this
  rw [ratDiv_one]
  exact (h1 O ϖ hϖ K ι W d ⟨hWprime, hWhom, hWrel⟩ (comap_C_eq_bot_of_not_mem hϖ W hϖW) hWdim L).symm

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

private theorem withBot_eq_of_add_one_eq (a : WithBot ℕ∞) (m : ℕ)
    (h : a + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) : a = (m : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot =>
    exfalso
    have e : ((m : WithBot ℕ∞) + 1) = (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by push_cast; rfl
    rw [Nat.cast_add, Nat.cast_one, e] at h
    exact WithBot.bot_ne_coe h
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : (⊤ : ℕ∞) = (m + 1 : ℕ) := by
        apply WithBot.coe_injective
        simpa using h
      exact ENat.top_ne_natCast (m + 1) h'
    | coe a =>
      have h' : ((a + 1 : ℕ) : WithBot ℕ∞) = ((m + 1 : ℕ) : WithBot ℕ∞) := by
        rw [← h]; push_cast; rfl
      have : a + 1 = m + 1 := by exact_mod_cast h'
      have ham : a = m := by omega
      subst ham
      rfl

theorem FibreVarieties.proof
    (hGen : GenericFibProps.Statement.{u}) (hBound : GenericDimBound.Statement.{u})
    (hGe : GenericDimGe.Statement.{u}) (hCorr : SpecialIdealCorresp.Statement.{u})
    (hSpecHomog : SpecialIdealMultiHomog.Statement.{u}) (hSup : SupSpanMultiHomog.Statement.{u})
    (hMin : MinimalPrimeMultiHomog.Statement.{u}) (hQuot : SpecialQuotDim.Statement.{u})
    (hComp : ComponentDim.Statement.{u}) : FibreVarieties.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP
  obtain ⟨hprime, hhomog, hforms⟩ := hGen O K ι P hP.multiProj hP.noTorsion
  have hcast : ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) =
      ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
    congr 1; omega
  refine ⟨⟨⟨hprime, hhomog, ?_⟩, ?_⟩, ?_⟩
  ·
    intro k
    obtain ⟨i, hi⟩ := hP.multiProj.relevant k
    obtain ⟨-, h⟩ := hforms _ _ (isWeightedHomogeneous_X O (blockWeight ι) ⟨k, i⟩) hi
    exact ⟨i, by simpa [MvPolynomial.map_X] using h⟩
  ·
    have h1 := hBound O K ι P hP.multiProj hP.noTorsion
    have h2 := hGe O K ι P hP.multiProj.isPrime hP.noTorsion
    rw [hP.dim, hcast] at h1 h2
    exact withBot_eq_of_add_one_eq _ _ (le_antisymm h1 h2)
  ·
    intro W hW
    have hW0 := hW
    unfold divCycle at hW
    split_ifs at hW with h
    · obtain ⟨hWmin, hWrel⟩ := h
      have hWp : W.IsPrime := hWmin.1.1
      have hϖW : (C ϖ : MRing ι O) ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
      obtain ⟨hsp, -, hrel, -⟩ := hCorr O ϖ hϖ K ι P W hWp hϖW
      have hJ : IsMultiHomogIdeal (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) :=
        hSup O K ι P (C ϖ) 0 hP.multiProj.multiHomog (isWeightedHomogeneous_C _ _)
      have hWh : IsMultiHomogIdeal W := hMin O K ι _ W hJ hWmin
      have hϖP : (C ϖ : MRing ι O) ∉ P := by
        intro hmem
        have : ϖ ∈ P.comap (C : O →+* MRing ι O) := hmem
        rw [hP.noTorsion, Ideal.mem_bot] at this
        exact hϖ.ne_zero this
      refine ⟨⟨hsp, hSpecHomog O K ι W hWh, hrel.mp hWrel⟩, ?_⟩
      rw [hQuot O ϖ hϖ K ι W hϖW]
      exact hComp O ϖ hϖ K ι P d hP 0 (C ϖ) (isWeightedHomogeneous_C _ _) hϖP W hW0 hϖW
    · exact absurd rfl hW

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial GroundTheory.Heights₂.Heights.FieldNumbers

universe u

private lemma mixedDiff_eventually_zero {K : Type*} (h : (K → ℤ) → ℤ)
    (hh : ∀ᶠ m in Filter.atTop, h m = 0) {n : ℕ} (bs : Fin n → K → ℤ) :
    ∀ᶠ m in Filter.atTop, mixedDiff bs h m = 0 := by
  unfold mixedDiff
  induction (List.ofFn bs) with
  | nil => simpa using hh
  | cons b l ih =>
    have hs : Filter.Tendsto (fun m : K → ℤ => m - b) Filter.atTop Filter.atTop := by
      simpa [sub_eq_add_neg] using
        Filter.tendsto_atTop_add_const_right Filter.atTop (-b) Filter.tendsto_id
    filter_upwards [ih, hs.eventually ih] with m h1 h2
    simp [List.foldr, diffStep, h1, h2]

private lemma eventualValue_of_eventually_zero {K : Type*} (f : (K → ℤ) → ℤ)
    (hf : ∀ᶠ m in Filter.atTop, f m = 0) : eventualValue f = 0 := by
  classical
  have hex : ∃ c, ∀ᶠ m in Filter.atTop, f m = c := ⟨0, hf⟩
  rw [eventualValue, dite_eq_left hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and hf).exists
  rw [← h1, h2]

theorem IntNumAddFirst.proof (h1 : FieldNumbers.IntNumAdd.Statement.{u})
    (h2 : FieldNumbers.IntNumZeroSlot.Statement.{u})
    (h3 : FieldNumbers.HilbDegreeBound.Statement.{u}) : IntNumAddFirst.Statement.{u} := by
  intro F _ K _ _ ι _ n G hG hGh hdim b₁ b₂ L
  have hupd : ∀ b : K → ℤ,
      Matrix.vecCons b L = Function.update (Matrix.vecCons (0 : K → ℤ) L) 0 b := fun b => by
    simp [Matrix.vecCons, Fin.update_cons_zero]
  by_cases hrel : IsRelevant G
  ·
    have hle : relDim G = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) ∨
        relDim G < ((n + 1 : ℕ) : WithBot (WithTop ℤ)) := by
      have hc : ((n + 1 : ℕ) : WithBot (WithTop ℤ)) = (((n + 1 : ℕ) : ℤ) : WithTop ℤ) := by
        rfl
      unfold relDim
      generalize ringKrullDim (MRing ι F ⧸ G) = x at hdim ⊢
      induction x using WithBot.recBotCoe with
      | bot => exact Or.inr (WithBot.bot_lt_coe _)
      | coe d =>
        induction d using ENat.recTopCoe with
        | top => exfalso; exact absurd hdim (by simp)
        | coe e =>
          have he : e < n + 2 + Fintype.card K := by
            rw [← WithBot.coe_natCast] at hdim
            exact_mod_cast WithBot.coe_lt_coe.1 hdim
          simp only [WithBot.map_coe]
          rw [hc]
          show ((((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) = _ ∨
            ((((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) < _
          rcases (show (e : ℤ) - Fintype.card K ≤ ((n + 1 : ℕ) : ℤ) by omega).lt_or_eq with h | h
          · exact Or.inr (WithBot.coe_lt_coe.2 (WithTop.coe_lt_coe.2 h))
          · exact Or.inl (by rw [h])
    rcases hle with heq | hlt
    · rw [hupd (b₁ + b₂), hupd b₁, hupd b₂]
      exact h1 F K ι G hGh hrel (n + 1) heq (Matrix.vecCons 0 L) 0 b₁ b₂
    · simp only [(h2 F K ι G).2 hGh (n + 1) _ hlt, add_zero]
  · have hz := (h3 F K ι G hGh).2 hrel
    simp only [intNum, eventualValue_of_eventually_zero _ (mixedDiff_eventually_zero _ hz _),
      add_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ProjIdealFormValue.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [DecidableEq K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (w : Module.Basis (Fin N) Ω E)
    (M : ℕ) (φ : Fin M → Module.Dual Ω E) (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ)
    (d : Option K → ℕ) (x : MRing (bundleIdx ι M) F), IsMultiHomog x d →
      (x ∈ projIdeal F y w φ t ↔
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) x = 0)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def TwistedDualGensExist.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B : ChartBundle O (segreVec y) N E),
    ∃ a₁ : K → ℤ, ∀ a : K → ℤ, a₁ ≤ a →
      ∃ (M : ℕ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
