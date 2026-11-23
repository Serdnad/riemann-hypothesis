module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle046
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle048
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagCutChartSection.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ) (hk : k < N) (c : ∀ k, ι k), segreVec y c ≠ 0 →
      (∃ (dl dm : Option (Option K) → ℕ) (l μ : MRing (bundleIdx (bundleIdx ι M) M') O) (m : K → ℕ),
        μ = ∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O) ^ m j ∧
        IsMultiHomog l dl ∧ IsMultiHomog μ dm ∧
        (fun o => (dl o : ℤ) - dm o) = zetaFirst a₀ + liftPairDeg (x ⟨k, hk⟩) ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) l =
          flagLineCoord w w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) μ ∧
        ∀ q ∈ pointIdeal O (flagProjPt Function.Embedding.some y w e φ φ' t k), ∃ n : ℕ,
          (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ n *
              rename (FieldNumbers.blockIncl Function.Embedding.some (bundleIdx (bundleIdx ι M) M')) q ∈
            pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ⊔ Ideal.span {l}) ∧
      (∃ (dl dm : Option (Option K) → ℕ) (l μ : MRing (bundleIdx (bundleIdx ι M) M') O) (m : K → ℕ),
        μ = ∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O) ^ m j ∧
        IsMultiHomog l dl ∧ IsMultiHomog μ dm ∧
        (fun o => (dl o : ℤ) - dm o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) l =
          flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) μ ∧
        ∀ q ∈ pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t k), ∃ n : ℕ,
          (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ n *
              rename (FieldNumbers.blockIncl secondFactorBlocks (bundleIdx (bundleIdx ι M) M')) q ∈
            pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ⊔ Ideal.span {l})

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PrimeDimLeTrdeg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    P.IsPrime → P.comap (C : O →+* MRing ι O) = ⊥ →
      ringKrullDim (MRing ι O ⧸ P) ≤ (((Algebra.trdeg O (MRing ι O ⧸ P)).toENat + 1 : ℕ∞) : WithBot ℕ∞)

def FlagProjTrdegLe.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ k : ℕ, k < N →
      Algebra.trdeg O (MRing (fun o => bundleIdx (bundleIdx ι M) M' (Function.Embedding.some o)) O ⧸
          pointIdeal O (flagProjPt Function.Embedding.some y w e φ φ' t k)) ≤
        Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + (k : Cardinal) ∧
      Algebra.trdeg O (MRing (fun o => bundleIdx (bundleIdx ι M) M' (secondFactorBlocks o)) O ⧸
          pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t k)) ≤
        Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + (k : Cardinal)

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

theorem homLocRing_form_not_mem {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {R : Type u} [CommRing R] {W : Ideal (MRing ι R)} (hW : W.IsPrime) (hrel : IsRelevant W)
    (c : K → ℕ) : ∃ g : MRing ι R, IsMultiHomog g c ∧ g ∉ W := by
  choose i hi using hrel
  refine ⟨∏ k, X ⟨k, i k⟩ ^ c k, ?_, ?_⟩
  · have hc : c = ∑ k, c k • blockWeight ι ⟨k, i k⟩ := by
      funext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    have h := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ c k)
      (fun k => c k • blockWeight ι ⟨k, i k⟩)
      fun k _ => (isWeightedHomogeneous_X R (blockWeight ι) _).pow _
    rw [← hc] at h
    exact h
  · intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hW)).mp h
    exact hi k (hW.mem_of_pow_mem _ hk)

theorem HomLocRingLocal.proof (hloc : HomLocRingIsLocal.Statement.{u})
    (hnoeth : HomLocRingNoetherian.Statement.{u}) (hdim : HomLocRingDimLe.Statement.{u}) :
    HomLocRingLocal.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP c x hx hxP W hW hWrel
  have := hP.isPrime
  have hWp : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hxW : x ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  obtain ⟨hlocal, hunit⟩ := hloc O K ι P W hWp hPW
  have hnoe := hnoeth O K ι P W hP.multiHomog hWp hWrel hPW
  refine ⟨hlocal, hnoe, le_antisymm ?_ ?_⟩
  · refine (hdim O K ι P W hP.multiHomog hWp hWrel hPW).trans ?_
    have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
    exact_mod_cast h1
  · obtain ⟨g, hg, hgW⟩ := homLocRing_form_not_mem hWp hWrel c
    have hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) ∈
          homLocRing P W :=
      Subring.subset_closure ⟨c, x, g, hx, hg, hgW, rfl⟩
    have hnu : ¬ IsUnit (⟨_, hz⟩ : homLocRing P W) :=
      fun h => (hunit c x g hx hg hgW hz).mp h hxW
    have hne : (⟨_, hz⟩ : homLocRing P W) ≠ 0 := by
      intro h0
      have h1 := congrArg Subtype.val h0
      simp only [ZeroMemClass.coe_zero, div_eq_zero_iff,
        IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h1
      rcases h1 with h1 | h1
      · exact hxP h1
      · exact hgW (hPW h1)
    have hlt : (⊥ : Ideal (homLocRing P W)) < IsLocalRing.maximalIdeal (homLocRing P W) := by
      refine bot_lt_iff_ne_bot.mpr fun h => hne ?_
      have hm := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rwa [h, Ideal.mem_bot] at hm
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    have h3 : (1 : ℕ∞) ≤ (IsLocalRing.maximalIdeal (homLocRing P W)).height :=
      le_trans le_add_self h2
    exact_mod_cast h3

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpLocRingFrac.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ W' : Ideal (MRing (extIdx ι J) O), W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes →
        IsRelevant W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        ∀ z ∈ blowUpLocRing P u W', ∃ b ∈ blowUpOverLoc P W u, ∃ s ∈ blowUpOverLoc P W u,
          (∃ t ∈ blowUpLocRing P u W', s * t = 1) ∧ z * s = b

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

section Lemmas

def BlowUpOverLocCentreDom.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ (𝔫 : Ideal (blowUpOverLoc P W u)), 𝔫.IsMaximal →
        ∃ W' : Ideal (MRing (extIdx ι J) O),
          W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ IsRelevant W' ∧ blowUpOf P u ≤ W' ∧
            W'.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W ∧
          ∃ h : blowUpOverLoc P W u ≤ blowUpLocRing P u W',
            ∀ b ∈ 𝔫, ¬ IsUnit (Subring.inclusion h b)

def BlowUpOverLocLocalization.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ W' : Ideal (MRing (extIdx ι J) O), W'.IsPrime → IsMultiHomogIdeal W' → IsRelevant W' →
        blowUpOf P u ≤ W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W →
        ∃ (h : blowUpOverLoc P W u ≤ blowUpLocRing P u W') (𝔭 : Ideal (blowUpOverLoc P W u))
          (h𝔭 : 𝔭.IsPrime),
          letI := (Subring.inclusion h).toAlgebra
          haveI := h𝔭
          IsLocalization.AtPrime (blowUpLocRing P u W') 𝔭

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
