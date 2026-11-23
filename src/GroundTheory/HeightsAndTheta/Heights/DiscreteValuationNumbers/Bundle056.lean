module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle004
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimGe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Polynomial
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAB

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace DvrConeDimTrdeg

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem proof : Statement := by
  intro O _ _ _ K _ _ ι _ P hP hPC
  classical
  let F := FractionRing O
  have hPp : P.IsPrime := hP.isPrime
  have hG : (genFib P).IsPrime := (GenericFibProps.full.{0} O K ι P hP hPC).1
  have hdim : ringKrullDim (MRing ι O ⧸ P) = ringKrullDim (MRing ι F ⧸ genFib P) + 1 :=
    le_antisymm (GenericDimGe.proof.{0} O K ι P hPp hPC) (GenericDimBound.full.{0} O K ι P hP hPC)

  have hB : ringKrullDim (MRing ι F ⧸ genFib P) =
      (Algebra.trdeg F (MRing ι F ⧸ genFib P)).toENat :=
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F

  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C : O →+* MRing ι O)
  have : IsLocalization M (MRing ι F) := MvPolynomial.isLocalization (nonZeroDivisors O) F
  have hdisj : Disjoint (M : Set (MRing ι O)) (P : Set (MRing ι O)) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ hmem
    have : a ∈ P.comap (C : O →+* MRing ι O) := hmem
    rw [hPC] at this
    exact nonZeroDivisors.ne_zero ha ((Submodule.mem_bot _).1 this)
  have hcomap : (genFib P).comap (algebraMap (MRing ι O) (MRing ι F)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (MRing ι F) hPp hdisj
  let φ : (MRing ι O ⧸ P) →+* (MRing ι F ⧸ genFib P) :=
    Ideal.quotientMap (genFib P) (algebraMap (MRing ι O) (MRing ι F)) hcomap.ge
  have hφ : Function.Injective φ := Ideal.quotientMap_injective' hcomap.le
  let _ : Algebra (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) := φ.toAlgebra
  have : IsScalarTower O (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change _ = φ (Ideal.Quotient.mk P (C a))
      simp [φ, Ideal.quotientMap_mk]
      rfl
  have : FaithfulSMul (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : FaithfulSMul O (MRing ι O ⧸ P) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).2 ((injective_iff_map_eq_zero (algebraMap O (MRing ι O ⧸ P))).2 fun a ha => ?_)
    have h : (C a : MRing ι O) ∈ P :=
      Ideal.Quotient.eq_zero_iff_mem.1 (show Ideal.Quotient.mk P (C a) = 0 from ha)
    have : a ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hPC] at this
    exact (Submodule.mem_bot _).1 this
  have : FaithfulSMul O F :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective O F)
  have : FaithfulSMul F (MRing ι F ⧸ genFib P) :=
    (faithfulSMul_iff_algebraMap_injective F (MRing ι F ⧸ genFib P)).2 (algebraMap F _).injective
  have : Algebra.IsAlgebraic O F := IsLocalization.isAlgebraic F (nonZeroDivisors O)
  have : Algebra.IsAlgebraic (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) := by
    refine ⟨fun b => ?_⟩
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective M g
    have hspec := IsLocalization.mk'_spec (MRing ι F) s m
    let y := algebraMap (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) (Ideal.Quotient.mk P (m : MRing ι O))
    have hy0 : y ≠ 0 := by
      refine (map_ne_zero_iff _ hφ).2 fun h => ?_
      exact Set.disjoint_left.1 hdisj m.2 (Ideal.Quotient.eq_zero_iff_mem.1 h)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hy0) (isAlgebraic_algebraMap _) ?_
    have : y * Ideal.Quotient.mk (genFib P) (IsLocalization.mk' (MRing ι F) s m) =
        algebraMap (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) (Ideal.Quotient.mk P s) := by
      change φ _ * _ = φ _
      simp only [φ, Ideal.quotientMap_mk, ← map_mul]
      rw [mul_comm, hspec]
    rw [this]
    exact isAlgebraic_algebraMap _
  have h1 := trdeg_add_eq O F (A := MRing ι F ⧸ genFib P)
  have h2 := trdeg_add_eq O (MRing ι O ⧸ P) (A := MRing ι F ⧸ genFib P)
  rw [trdeg_eq_zero (R := O) (A := F), zero_add] at h1
  rw [trdeg_eq_zero (R := MRing ι O ⧸ P) (A := MRing ι F ⧸ genFib P), add_zero] at h2
  rw [hdim, hB, h1, ← h2]
  rfl

end DvrConeDimTrdeg

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Helpers

theorem ringKrullDim_le_of_isAlgebraic_adjoin_singleton {A B : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B)) (y : B)
    [Algebra.IsAlgebraic (Algebra.adjoin A ({y} : Set B)) B] (N : ℕ)
    (hA : ringKrullDim A < (N : WithBot ℕ∞)) : ringKrullDim B ≤ (N : WithBot ℕ∞) := by
  rw [ringKrullDim_le_iff_height_le]
  intro 𝔓 h𝔓
  have key := DimensionInequality.full A B hinj 𝔓
  have htd : Algebra.trdeg A B ≤ 1 := by
    simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk A ({y} : Set B)
  have hp : (𝔓.under A).height + 1 ≤ (N : ℕ∞) := by
    have h1 := Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top (inferInstance :
      (𝔓.under A).IsPrime))
    have h2 : ((𝔓.under A).height : WithBot ℕ∞) < (N : WithBot ℕ∞) := h1.trans_lt hA
    have h3 : (𝔓.under A).height < (N : ℕ∞) := by exact_mod_cast h2
    exact Order.add_one_le_of_lt h3
  have hc : Cardinal.ofENat 𝔓.height ≤ Cardinal.ofENat (N : ℕ∞) := by
    calc Cardinal.ofENat 𝔓.height
        ≤ Cardinal.ofENat 𝔓.height + Algebra.trdeg (A ⧸ 𝔓.under A) (B ⧸ 𝔓) := le_self_add
      _ ≤ Cardinal.ofENat (𝔓.under A).height + Algebra.trdeg A B := key
      _ ≤ Cardinal.ofENat (𝔓.under A).height + 1 := by gcongr
      _ = Cardinal.ofENat ((𝔓.under A).height + 1) := by simp
      _ ≤ Cardinal.ofENat (N : ℕ∞) := Cardinal.ofENat_le_ofENat.mpr hp
  exact_mod_cast Cardinal.ofENat_le_ofENat.mp hc

private theorem lt_natCast_of_add_one_le_withBotENat {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h (by norm_cast)
    | coe a =>
      norm_cast at h ⊢

end Helpers

section Proof

theorem ExceptionalContraction.proof (h₁ : BlowUpDecomposition.Statement.{u}) :
    ExceptionalContraction.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH e hce m hm hmP hmH G' hϖG' hY₀ hE
  obtain ⟨hQm, -, -, hY₀Q, hD₁, -, -, -⟩ :=
    h₁ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH e hce m hm hmP hmH
  set Q := blowUpOf P (blowUpGens s g f m e) with hQdef
  set G := G'.comap (liftForm (J := BlowUpIdx ι)) with hGdef
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hQp : Q.IsPrime := hQm.multiProj.isPrime
  obtain ⟨hG'p, hQG', hG'rel⟩ := le_and_isRelevant_of_divCycle_ne_zero hY₀.ne'
  obtain ⟨hGp, hPG, hGrel, -⟩ := comap_liftForm_facts hG'p hQG' hG'rel

  have hlift : ∀ {p : MRing ι O}, p ∉ P → liftForm (J := BlowUpIdx ι) p ∉ Q :=
    fun hp => liftForm_not_mem_blowUpOf hp
  have hfP : f ∉ P := hD.1.num_not_mem
  have hgP : g ∉ P := hD.1.den_not_mem
  have hY₁Q : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ Q := hD₁.1.num_not_mem
  have hmul := DivCycleMul.proof O (Option K) (extIdx ι (BlowUpIdx ι)) Q
  have hnm : ∀ {x y}, x ∉ Q → y ∉ Q → x * y ∉ Q := fun hx hy h => (hQp.mem_or_mem h).elim hx hy
  have e1 := congrFun (divCycle_congr_of_sub_mem (blowUp_relation P s g f m e)) G'
  rw [map_mul, hmul _ _ hQp (hnm (hlift hsP) (hlift hgP)) hY₁Q, hmul _ _ hQp (hlift hsP) (hlift hgP),
    hmul _ _ hQp (hlift (fun h => (hPp.mem_or_mem h).elim hfP hmP)) hY₀Q] at e1
  simp only [Pi.add_apply] at e1
  have hE' := hE
  unfold ratDiv at hE'
  rw [hmul _ _ hQp (hlift hgP) hY₁Q] at hE'
  simp only [Pi.add_apply] at hE'
  have hspos : 0 < divCycle Q (liftForm s) G' := by linarith
  have hsG' : liftForm (J := BlowUpIdx ι) s ∈ G' := form_mem_of_divCycle_ne_zero hspos.ne'
  have hsG : s ∈ G := hsG'

  have hY₀G' : (newVar none : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' :=
    form_mem_of_divCycle_ne_zero hY₀.ne'
  obtain ⟨i, hi⟩ := powMonomial_not_mem hGp hGrel e
  have := hGp
  have := hG'p
  let φ : MRing ι O ⧸ G →+* MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G' :=
    Ideal.quotientMap G' (liftForm (J := BlowUpIdx ι) : MRing ι O →ₐ[O] _).toRingHom le_rfl
  let _ : Algebra (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') := φ.toAlgebra
  have hφ : ∀ p : MRing ι O, algebraMap (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G')
      (Ideal.Quotient.mk G p) = Ideal.Quotient.mk G' (liftForm p) := fun p => Ideal.quotientMap_mk
  have : IsScalarTower O (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') := by
    refine IsScalarTower.of_algebraMap_eq (R := O) (S := MRing ι O ⧸ G)
      (A := MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') fun r => ?_
    change Ideal.Quotient.mk G' (algebraMap O (MRing (extIdx ι (BlowUpIdx ι)) O) r) =
      algebraMap (MRing ι O ⧸ G) _ (Ideal.Quotient.mk G (algebraMap O (MRing ι O) r))
    rw [hφ, MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq, liftForm_C]
  have hinj : Function.Injective (algebraMap (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G')) :=
    Ideal.quotientMap_injective
  have : Algebra.FiniteType O (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O G') (Ideal.Quotient.mkₐ_surjective O G')
  have : Algebra.FiniteType (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') :=
    Algebra.FiniteType.of_restrictScalars_finiteType O _ _
  set y : MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G' := Ideal.Quotient.mk G' (newVar (some (some i))) with hy
  set Cy := Algebra.adjoin (MRing ι O ⧸ G) ({y} : Set (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G'))
  let _ : CommRing Cy := inferInstance
  have hAalg : ∀ a : MRing ι O ⧸ G, IsAlgebraic Cy
      (algebraMap (MRing ι O ⧸ G) (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') a) := fun a =>
    isAlgebraic_algebraMap (⟨_, Subalgebra.algebraMap_mem Cy a⟩ : Cy)
  have hpi : Ideal.Quotient.mk G' (liftForm (J := BlowUpIdx ι) (powMonomial e i)) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hi
  have hX : ∀ v, IsAlgebraic Cy (Ideal.Quotient.mk G' (X v : MRing (extIdx ι (BlowUpIdx ι)) O)) := by
    rintro ⟨_ | k, j⟩
    · rcases j with _ | j'
      · change IsAlgebraic Cy (Ideal.Quotient.mk G' (newVar none))
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hY₀G']
        exact isAlgebraic_zero
      · set c : MRing ι O := Option.elim j' m (fun i' => powMonomial e i') with hc
        have hrel : newVar (some j') * liftForm (powMonomial e i) - newVar (some (some i)) * liftForm c ∈ Q :=
          mem_blowUpOf_of_sub (by
            rcases j' with _ | i' <;> simp only [blowUpGens, hc, Option.elim] <;>
              convert P.zero_mem using 1 <;> ring)
        have hrel' := Ideal.Quotient.eq_zero_iff_mem.mpr (hQG' hrel)
        rw [map_sub, map_mul, map_mul] at hrel'
        let a' : Cy := ⟨_, Subalgebra.algebraMap_mem Cy (Ideal.Quotient.mk G (powMonomial e i))⟩
        let z' : Cy := ⟨y * algebraMap (MRing ι O ⧸ G) _ (Ideal.Quotient.mk G c),
          Cy.mul_mem (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem Cy _)⟩
        refine ⟨Polynomial.C a' * Polynomial.X - Polynomial.C z', fun h0 => hpi ?_, ?_⟩
        · have h1 := congrArg (fun p : Polynomial Cy => p.coeff 1) h0
          simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, ite_true,
            Polynomial.coeff_C_of_ne_zero one_ne_zero, sub_zero, Polynomial.coeff_zero] at h1
          have h2 := congrArg Subtype.val h1
          simpa [a', hφ] using h2
        · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
          change (algebraMap (MRing ι O ⧸ G) _ (Ideal.Quotient.mk G (powMonomial e i))) *
            Ideal.Quotient.mk G' (newVar (some j')) -
            y * algebraMap (MRing ι O ⧸ G) _ (Ideal.Quotient.mk G c) = 0
          rw [hφ, hφ, hy]
          linear_combination hrel'
    · rw [← liftForm_X (J := BlowUpIdx ι) (R := O) ⟨k, j⟩, ← hφ]
      exact hAalg _
  have : Algebra.IsAlgebraic Cy (MRing (extIdx ι (BlowUpIdx ι)) O ⧸ G') := ⟨fun x => by
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction t using MvPolynomial.induction_on with
    | C r =>
      have : Ideal.Quotient.mk G' (C r : MRing (extIdx ι (BlowUpIdx ι)) O) =
          algebraMap (MRing ι O ⧸ G) _ (Ideal.Quotient.mk G (C r)) := by
        rw [hφ, liftForm_C]
      rw [this]
      exact hAalg _
    | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
    | mul_X p v hp => rw [map_mul]; exact hp.mul (hX v)⟩
  have hdimB := ComponentDim.proof O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q (d + 1) hQm
    (Pi.single none 1) (newVar none) (isWeightedHomogeneous_X _ _ _) hY₀Q G' hY₀.ne' hϖG'
  have hdimA : ¬ ringKrullDim (MRing ι O ⧸ G) < ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro hlt
    have h := ringKrullDim_le_of_isAlgebraic_adjoin_singleton hinj y _ hlt
    rw [hdimB, Fintype.card_option] at h
    have h' : d + 1 + (Fintype.card K + 1) ≤ d + 1 + Fintype.card K := by exact_mod_cast h
    omega

  have hsum : ringKrullDim (MRing ι O ⧸ (P ⊔ Ideal.span {s})) <
      ((d + 1 + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
    have := hPp
    have h := ringKrullDim_succ_le_of_surjective
      (Ideal.Quotient.factor (le_sup_left : P ≤ P ⊔ Ideal.span {s})) (Ideal.Quotient.factor_surjective _)
      (r := Ideal.Quotient.mk P s)
      (mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]))
      (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    rw [hP.dim] at h
    exact lt_natCast_of_add_one_le_withBotENat (by convert h using 2; omega)
  exact TopDimMinimal.proof DimStrictDrop.proof (MRing ι O) (P ⊔ Ideal.span {s}) G
    (d + 1 + Fintype.card K) (sup_le hPG ((Ideal.span_singleton_le_iff_mem _).mpr hsG)) hsum hdimA

end Proof

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

universe u

theorem sup_span_C_ne_top_of_multiHomog {O : Type*} [CommRing O] {K : Type} [DecidableEq K]
    (ι : K → Type) {W : Ideal (MRing ι O)} (hW : IsMultiHomogIdeal W)
    (h0 : W.comap (C : O →+* MRing ι O) = ⊥) {ϖ : O} (hϖ : ¬ IsUnit ϖ) :
    W ⊔ Ideal.span {(C ϖ : MRing ι O)} ≠ ⊤ := by
  intro htop
  have h1 : (1 : MRing ι O) ∈ W ⊔ Ideal.span {(C ϖ : MRing ι O)} := htop ▸ Submodule.mem_top
  obtain ⟨w, hw, t, ht, hwt⟩ := Submodule.mem_sup.mp h1
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp ht
  have hw0 : (C (AddMonoidAlgebra.coeff w 0) : MRing ι O) ∈ W := by
    have h := hW w hw 0
    rwa [weightedHomogeneousComponent_zero] at h
    intro v hv
    have := congrFun hv v.1
    simp [blockWeight] at this
  have hc : AddMonoidAlgebra.coeff w 0 = 0 := by
    have h : AddMonoidAlgebra.coeff w 0 ∈ W.comap (C : O →+* MRing ι O) := hw0
    rw [h0] at h
    exact h
  have h2 := congrArg (AddMonoidAlgebra.coeff · 0) hwt
  rw [MvPolynomial.coeff_add, mul_comm s, coeff_C_mul, hc, zero_add, coeff_zero_one] at h2
  exact hϖ (isUnit_iff_exists_inv.mpr ⟨_, h2⟩)

theorem ringKrullDim_quotient_eq_of_minimalPrime_of_sup_ne_top {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι O)} [P.IsPrime] {f : MRing ι O} (hfP : f ∉ P)
    (hWmin : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    (hWϖ : W ⊔ Ideal.span {(C ϖ : MRing ι O)} ≠ ⊤) (N : ℕ)
    (hdim : ringKrullDim (MRing ι O ⧸ P) = ((N + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MRing ι O ⧸ W) = (N : WithBot ℕ∞) := by
  have hWp : W.IsPrime := hWmin.1.1
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

  obtain ⟨m, hm, hWm'⟩ := Ideal.exists_le_maximal _ hWϖ
  have hWm : W ≤ m := le_sup_left.trans hWm'
  have : m.IsPrime := hm.isPrime
  have hmge := le_height_of_isMaximal_of_uniformiser_mem hϖ m hm
    (hWm' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
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
  rw [hdim] at hPdim
  have hPdim' : N + 1 ≤ Nat.card (Σ k, ι k) + 1 - h0 := by exact_mod_cast hPdim

  have hlow := Ideal.height_le_ringKrullDim_of_ne_top
    (DimF.isPrime_map_mk (A := MRing ι O) (q := W) (M := m) hWm).ne_top
  rw [hb0] at hlow
  have hb' : N ≤ b0 := by omega
  have hlow' : ((N : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ W) :=
    le_trans (by exact_mod_cast hb') hlow
  rw [hdim] at hup
  exact withBot_eq_of_le_of_add_one_le hlow' hup

theorem HorizontalComponentModel.proof : HorizontalComponentModel.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP c x hxc hxP W hW hϖW
  have hWd : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h
    · exact absurd rfl hW
  obtain ⟨hWmin, hrel⟩ := hWd
  have hWp : W.IsPrime := hWmin.1.1
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hWh : IsMultiHomogIdeal W :=
    MinimalPrimeMultiHomog.proof O K ι _ W
      (SupSpanMultiHomog.proof O K ι P x c hP.multiProj.multiHomog hxc) hWmin

  have h0 : W.comap (C : O →+* MRing ι O) = ⊥ := by
    by_contra hne
    have hmx : (W.comap (C : O →+* MRing ι O)).IsMaximal :=
      haveI : (W.comap (C : O →+* MRing ι O)).IsPrime := Ideal.IsPrime.comap _
      IsPrime.to_maximal_ideal hne
    have hϖm : ϖ ∈ W.comap (C : O →+* MRing ι O) := by
      rw [IsLocalRing.eq_maximalIdeal hmx]
      exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
    exact hϖW hϖm
  have hdim := ringKrullDim_quotient_eq_of_minimalPrime_of_sup_ne_top hϖ hxP hWmin
    (sup_span_C_ne_top_of_multiHomog ι hWh h0 hϖ.not_isUnit) (d + 1 + Fintype.card K)
    (by rw [hP.dim, show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by ring])
  exact ⟨⟨hWp, hWh, hrel⟩, h0, hdim⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
