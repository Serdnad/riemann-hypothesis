module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ZeroLocusDimHGeo
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem PiQuotCokerFiniteLength.proof : PiQuotCokerFiniteLength.Statement := by
  intro B _ _ _ J hJ hQ
  have : Finite J.minimalPrimes := (J.finite_minimalPrimes_of_isNoetherianRing B).to_subtype
  let : Fintype J.minimalPrimes := Fintype.ofFinite _
  classical
  have hfac : ∀ (P : J.minimalPrimes) (x : B),
      quotToPiMinimalPrimes J (Submodule.Quotient.mk x) P = Ideal.Quotient.mk (P : Ideal B) x :=
    fun _ _ => rfl
  refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hxP : ∀ P : J.minimalPrimes, x ∈ (P : Ideal B) := fun P => by
      have h1 := congrFun hy P
      rwa [hfac, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at h1
    have hx : x ∈ sInf J.minimalPrimes := Submodule.mem_sInf.mpr fun p hp => hxP ⟨p, hp⟩
    rw [Ideal.sInf_minimalPrimes, hJ.radical] at hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx

  have hkey : ∀ Q : Ideal B, Q.IsPrime → ∀ P P' : J.minimalPrimes, P ≠ P' →
      (P : Ideal B) ≤ Q → (P' : Ideal B) ≤ Q → Q = IsLocalRing.maximalIdeal B := by
    intro Q hQp P P' hne hPQ hP'Q
    rcases hQ Q hQp (P.2.1.2.trans hPQ) with hmin | hm
    · exfalso
      apply hne
      have e1 : (P : Ideal B) = Q := le_antisymm hPQ (hmin.2 P.2.1 hPQ)
      have e2 : (P' : Ideal B) = Q := le_antisymm hP'Q (hmin.2 P'.2.1 hP'Q)
      exact Subtype.ext (e1.trans e2.symm)
    · exact hm
  let IP : J.minimalPrimes → Ideal B := fun P =>
    (Finset.univ.filter (· ≠ P)).inf fun P' : J.minimalPrimes => (P' : Ideal B)
  let I : Ideal B := Finset.univ.inf fun P => IP P ⊔ (P : Ideal B)
  have hI : ∀ Q : Ideal B, Q.IsPrime → I ≤ Q → Q = IsLocalRing.maximalIdeal B := by
    intro Q hQp hIQ
    obtain ⟨P, -, hPQ⟩ := hQp.inf_le'.mp hIQ
    obtain ⟨P', hP', hP'Q⟩ := hQp.inf_le'.mp (le_sup_left.trans hPQ)
    exact hkey Q hQp P P' (Finset.mem_filter.mp hP').2.symm (le_sup_right.trans hPQ) hP'Q
  have htors : Module.IsTorsionBySet B
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J))
      (I : Set B) := by
    intro c z
    obtain ⟨y, hy⟩ := z
    show y • c = 0
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hyP : ∀ P, y ∈ IP P ⊔ (P : Ideal B) := fun P =>
      Submodule.mem_finsetInf.mp hy P (Finset.mem_univ _)
    choose a ha b hb hab using fun P => Submodule.mem_sup.mp (hyP P)
    choose x hx using fun P => Ideal.Quotient.mk_surjective (v P)
    refine ⟨Submodule.Quotient.mk (∑ P, a P * x P), ?_⟩
    funext Q

    rw [hfac, Pi.smul_apply, ← hx Q, map_sum, Finset.sum_eq_single Q]
    · rw [← hab Q, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_add (f := _), map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr (hb Q), add_zero]
    · intro P _ hPQ
      have hle : IP P ≤ (Q : Ideal B) :=
        Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ Q, hPQ.symm⟩)
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (hle (ha P)))
    · intro h
      exact absurd (Finset.mem_univ Q) h
  by_cases hItop : I = ⊤
  · haveI : Subsingleton
        (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
      ⟨fun c d => by
        have hc := @htors c ⟨1, by rw [hItop]; trivial⟩
        have hd := @htors d ⟨1, by rw [hItop]; trivial⟩
        rw [one_smul] at hc hd
        rw [hc, hd]⟩
    exact IsFiniteLength.of_subsingleton
  have hmax : IsLocalRing.maximalIdeal B ∈ I.minimalPrimes :=
    ⟨⟨inferInstance, IsLocalRing.le_maximalIdeal hItop⟩, fun q hq _ => (hI q hq.1 hq.2).ge⟩
  have : IsArtinianRing (B ⧸ I) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmax
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  refine ⟨inferInstance, ?_⟩
  let := htors.module
  have : IsScalarTower B (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    htors.isScalarTower
  have : Module.Finite (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    Module.Finite.of_restrictScalars_finite B _ _
  have : IsArtinian (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    isArtinian_of_fg_of_artinian'
  exact isArtinian_of_surjective_algebraMap (R := B ⧸ I) Ideal.Quotient.mk_surjective

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

namespace ChartParAlgebraic

theorem proof : ChartParAlgebraic.Statement := by
  intro F _ n e K L _ _ _ _ _ _ u t η hu hη hrel hchart j₀ hη0
  generalize hz : (fun m => η m * (η j₀)⁻¹) = z
  have hzm : ∀ m, z m = η m * (η j₀)⁻¹ := fun m => by rw [← hz]
  have hz0 : z j₀ = 1 := by rw [hzm, mul_inv_cancel₀ hη0]
  set A₀ := Algebra.adjoin F (Set.range z) with hA₀
  set B := Algebra.adjoin A₀ (Set.range fun p : Fin e × {j : Fin n // j ≠ j₀} =>
    algebraMap K L (u (p.1, p.2.1))) with hB
  have hzB : ∀ m, z m ∈ B := fun m =>
    Subalgebra.algebraMap_mem B (⟨z m, Algebra.subset_adjoin ⟨m, rfl⟩⟩ : A₀)
  have hwB : ∀ p : Fin e × {j : Fin n // j ≠ j₀}, algebraMap K L (u (p.1, p.2.1)) ∈ B :=
    fun p => Algebra.subset_adjoin ⟨p, rfl⟩
  have hFB : ∀ c : F, algebraMap F L c ∈ B := fun c => by
    rw [IsScalarTower.algebraMap_apply F A₀ L]
    exact Subalgebra.algebraMap_mem B _
  have huB : ∀ p : Fin e × Fin n, algebraMap K L (u p) ∈ B := by
    rintro ⟨i, j⟩
    by_cases hj : j = j₀
    · rw [hj]
      have hsum : ∑ j, algebraMap K L (u (i, j)) * z j = 0 := by
        simp only [hzm, ← mul_assoc, ← Finset.sum_mul, hrel i, zero_mul]
      have h1 := Finset.add_sum_erase Finset.univ (fun j => algebraMap K L (u (i, j)) * z j)
        (Finset.mem_univ j₀)
      simp only [hz0, mul_one] at h1
      rw [hsum, ← eq_neg_iff_add_eq_zero] at h1
      rw [h1]
      refine neg_mem (Subalgebra.sum_mem _ fun j' hj' => Subalgebra.mul_mem _ ?_ (hzB j'))
      exact hwB (i, ⟨j', Finset.ne_of_mem_erase hj'⟩)
    · exact hwB (i, ⟨j, hj⟩)
  have hmem : ∀ b ∈ B, IsAlgebraic B b := fun b hb => isAlgebraic_algebraMap (⟨b, hb⟩ : B)
  have hη0alg : IsAlgebraic B (η j₀) := by
    have hs : ∑ m, algebraMap F L (t m) * z m = (η j₀)⁻¹ := by
      simp only [hzm, ← mul_assoc, ← Finset.sum_mul, hchart, one_mul]
    have h2 : IsAlgebraic B (∑ m, algebraMap F L (t m) * z m) :=
      hmem _ (Subalgebra.sum_mem _ fun m _ => Subalgebra.mul_mem _ (hFB (t m)) (hzB m))
    have := h2.inv
    rwa [hs, inv_inv] at this
  have hηalg : ∀ m, IsAlgebraic B (η m) := fun m => by
    have hm : η m = z m * η j₀ := by rw [hzm, inv_mul_cancel_right₀ hη0]
    rw [hm]
    exact (hmem _ (hzB m)).mul hη0alg
  have hK : ∀ c : K, IsAlgebraic B (algebraMap K L c) := fun c => by
    have hc : c ∈ IntermediateField.adjoin F (Set.range u) := by rw [hu]; trivial
    induction hc using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact hmem _ (huB p)
    | algebraMap x =>
      rw [← IsScalarTower.algebraMap_apply F K L]
      exact hmem _ (hFB x)
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact hx.add hy
    | inv x _ hx =>
      rw [map_inv₀]
      exact hx.inv
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact hx.mul hy
  refine ⟨fun y => ?_⟩
  have hy : y ∈ IntermediateField.adjoin K (Set.range η) := by rw [hη]; trivial
  induction hy using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact hηalg m
  | algebraMap x => exact hK x
  | add x y _ _ hx hy => exact hx.add hy
  | inv x _ hx => exact hx.inv
  | mul x y _ _ hx hy => exact hx.mul hy

end ChartParAlgebraic

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Cardinal

theorem TrdegBaseAlgebraic.proof : TrdegBaseAlgebraic.Statement := by
  intro F K Ω _ _ _ _ _ _ _ hKF ι z
  obtain ⟨A, hA⟩ : ∃ A : Subalgebra F Ω, A = Algebra.adjoin F (Set.range z) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Subalgebra K Ω, B = Algebra.adjoin K (Set.range z) := ⟨_, rfl⟩
  rw [← hA, ← hB]
  have hAB : ∀ w ∈ A, w ∈ B := by
    intro w hw
    rw [hA] at hw
    rw [hB]
    induction hw using Algebra.adjoin_induction with
    | mem w hw => exact Algebra.subset_adjoin hw
    | algebraMap c =>
      rw [IsScalarTower.algebraMap_apply F K Ω c]
      exact Subalgebra.algebraMap_mem _ _
    | add u v _ _ hu hv => exact Subalgebra.add_mem _ hu hv
    | mul u v _ _ hu hv => exact Subalgebra.mul_mem _ hu hv

  let i : A →+* B :=
    { toFun := fun a => ⟨a, hAB a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have : FaithfulSMul F A :=
    (faithfulSMul_iff_algebraMap_injective F A).mpr (algebraMap F A).injective
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis F A
  let x : t → B := fun a => i a
  set C : Subalgebra K B := Algebra.adjoin K (Set.range x) with hC

  have hFC : ∀ r ∈ Algebra.adjoin F (Set.range ((↑) : t → A)), i r ∈ C := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem r hr =>
      obtain ⟨a, rfl⟩ := hr
      exact Algebra.subset_adjoin ⟨a, rfl⟩
    | algebraMap c =>
      have : i (algebraMap F A c) = algebraMap K B (algebraMap F K c) := by
        apply Subtype.ext
        exact (IsScalarTower.algebraMap_apply F K Ω c)
      rw [this]
      exact C.algebraMap_mem _
    | add r s _ _ hr hs =>
      rw [map_add (f := _)]
      exact C.add_mem hr hs
    | mul r s _ _ hr hs =>
      rw [map_mul]
      exact C.mul_mem hr hs
  let f : Algebra.adjoin F (Set.range ((↑) : t → A)) →+* C :=
    { toFun := fun r => ⟨i r, hFC r r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : C => ((c : B) : Ω)) hab
  have key : ∀ (w : Ω), w ∈ Algebra.adjoin K (Set.range z) →
      ∀ (hw : w ∈ B), IsAlgebraic C (⟨w, hw⟩ : B) := by
    intro w hw'
    induction hw' using Algebra.adjoin_induction with
    | mem w hw' =>
      intro hw
      obtain ⟨m, rfl⟩ := hw'
      have hzA : z m ∈ A := hA ▸ Algebra.subset_adjoin ⟨m, rfl⟩
      have h1 : IsAlgebraic (Algebra.adjoin F (Set.range ((↑) : t → A))) (⟨z m, hzA⟩ : A) :=
        ht.isAlgebraic.isAlgebraic _
      exact h1.ringHom_of_comp_eq f i hf (RingHom.ext fun _ => rfl)
    | algebraMap k =>
      intro hw
      exact (hKF.isAlgebraic k).ringHom_of_comp_eq ((algebraMap K C).comp (algebraMap F K))
        (algebraMap K B) (RingHom.injective _) (RingHom.ext fun _ => rfl)
    | add u v hu' hv' hu hv =>
      intro hw
      exact (hu (hB ▸ hu')).add (hv (hB ▸ hv'))
    | mul u v hu' hv' hu hv =>
      intro hw
      exact (hu (hB ▸ hu')).mul (hv (hB ▸ hv'))
  have alg : Algebra.IsAlgebraic C B := ⟨fun b => key b.1 (hB ▸ b.2) b.2⟩
  calc Algebra.trdeg K B ≤ #(Set.range x) := Algebra.IsAlgebraic.trdeg_le_cardinalMk K (Set.range x)
    _ ≤ #t := Cardinal.mk_range_le
    _ = Algebra.trdeg F A := ht.cardinalMk_eq_trdeg

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ZeroLocusDimH

theorem eval_eval₂_aeval {n s : ℕ} (π : Fin s → MvPolynomial (Fin n) ℂ)
    (Q : Polynomial (MvPolynomial (Fin s) ℂ)) (x : Fin n → ℂ) (i : Fin n) :
    MvPolynomial.eval x (Q.eval₂ (MvPolynomial.aeval π).toRingHom (X i)) =
      Polynomial.eval (x i) (Q.map (MvPolynomial.eval (paramMap π x))) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval_map, MvPolynomial.eval_X]
  congr 1
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
  · simp
  · simp [paramMap]

theorem mem_zeroSet_iff {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) :
    (∀ q ∈ I, MvPolynomial.eval x q = 0) ↔ I ≤ RingHom.ker (MvPolynomial.eval x) :=
  ⟨fun h q hq => RingHom.mem_ker.2 (h q hq), fun h _ hq => RingHom.mem_ker.1 (h hq)⟩

theorem ringKrullDim_quot_sup_add_one_le {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [p.IsPrime]
    (g : MvPolynomial (Fin n) ℂ) (hg : g ∉ p) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g})) + 1 ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) := by
  have hne : Ideal.Quotient.mk p g ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hne)
  have e : ((MvPolynomial (Fin n) ℂ ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p g}) ≃+*
      MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g}) :=
    (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
      (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {g}))
  rwa [ringKrullDim_eq_of_ringEquiv e] at h

theorem le_of_add_one_le_succ {a : WithBot ℕ∞} {k : ℕ} (h : a + 1 ≤ ((k + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ (k : WithBot ℕ∞) :=
  _root_.UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ h

theorem dimH_le_of_step {n : ℕ} (d : ℕ)
    (hIH : ∀ J' : Ideal (MvPolynomial (Fin n) ℂ), ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') + 1 ≤ d →
      dimH {x : Fin n → ℂ | ∀ q ∈ J', MvPolynomial.eval x q = 0} ≤ 2 * (d : ENNReal))
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ d) :
    dimH {x : Fin n → ℂ | ∀ q ∈ J, MvPolynomial.eval x q = 0} ≤ 2 * (d : ENNReal) := by

  have hcover : {x : Fin n → ℂ | ∀ q ∈ J, MvPolynomial.eval x q = 0} ⊆
      ⋃ p ∈ J.minimalPrimes, {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0} := by
    intro x hx
    rw [Set.mem_ofPred_eq, mem_zeroSet_iff] at hx
    have : (RingHom.ker (MvPolynomial.eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le hx
    exact Set.mem_biUnion hp ((mem_zeroSet_iff p x).2 hpx)
  refine (dimH_mono hcover).trans ?_
  rw [dimH_bUnion (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J).countable]
  refine iSup₂_le fun p hp => ?_
  have : p.IsPrime := hp.1.1
  have hpd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ≤ d :=
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hp.1.2)).trans hJ
  obtain ⟨s, hs, π, P, hP, hP'⟩ := exists_simple_root_data p
  set g := ∏ i, (Polynomial.derivative (P i)).eval₂ (MvPolynomial.aeval π).toRingHom (X i) with hgdef
  have hg : g ∉ p := by
    rw [hgdef, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, -, hi⟩
    exact hP' i hi
  have hsplit : {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0} ⊆
      {x | x ∈ {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0} ∧ ∀ i, Polynomial.eval (x i)
        ((Polynomial.derivative (P i)).map (MvPolynomial.eval (paramMap π x))) ≠ 0} ∪
      {x : Fin n → ℂ | ∀ q ∈ p ⊔ Ideal.span {g}, MvPolynomial.eval x q = 0} := by
    intro x hx
    by_cases h : ∀ i, Polynomial.eval (x i)
        ((Polynomial.derivative (P i)).map (MvPolynomial.eval (paramMap π x))) ≠ 0
    · exact Or.inl ⟨hx, h⟩
    · right
      push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Set.mem_ofPred_eq, mem_zeroSet_iff, sup_le_iff, Ideal.span_singleton_le_iff_mem,
        RingHom.mem_ker]
      refine ⟨(mem_zeroSet_iff p x).1 hx, ?_⟩
      rw [hgdef, map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [eval_eval₂_aeval]; exact hi)
  refine (dimH_mono hsplit).trans ?_
  rw [dimH_union]
  refine max_le ?_ ?_
  · have hV : ∀ x ∈ {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0}, ∀ i,
        Polynomial.eval (x i) ((P i).map (MvPolynomial.eval (paramMap π x))) = 0 := by
      intro x hx i
      rw [← eval_eval₂_aeval]
      exact hx _ (hP i)
    refine (dimH_simple_roots_le π P _ hV).trans ?_
    have hsd : s ≤ d := by exact_mod_cast hs.trans hpd
    have : (s : ENNReal) ≤ d := by exact_mod_cast hsd
    gcongr
  · exact hIH _ ((ringKrullDim_quot_sup_add_one_le p g hg).trans hpd)

theorem dimH_zeroLocus_le (d : ℕ) : ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ d →
      dimH {x : Fin n → ℂ | ∀ q ∈ J, MvPolynomial.eval x q = 0} ≤ 2 * (d : ENNReal) := by
  induction d with
  | zero =>
    intro n J hJ
    refine dimH_le_of_step 0 (fun J' hJ' => ?_) J hJ
    by_cases htop : J' = ⊤
    · have : {x : Fin n → ℂ | ∀ q ∈ J', MvPolynomial.eval x q = 0} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]
        exact ⟨1, htop ▸ Submodule.mem_top, by simp⟩
      rw [this, dimH_empty]
      simp
    · have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J') := Ideal.Quotient.nontrivial_iff.2 htop
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ J')
      have h1 : (0 : WithBot ℕ∞) + 1 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') + 1 := by gcongr
      have h2 := h1.trans hJ'
      rw [zero_add, Nat.cast_zero] at h2
      exact absurd h2 (not_le.2 zero_lt_one)
  | succ k ih =>
    intro n J hJ
    refine dimH_le_of_step (k + 1) (fun J' hJ' => ?_) J hJ
    refine (ih n J' (le_of_add_one_le_succ hJ')).trans ?_
    have : (k : ENNReal) ≤ ((k + 1 : ℕ) : ENNReal) := by exact_mod_cast Nat.le_succ k
    gcongr

theorem proof : Statement := fun n d J hJ => dimH_zeroLocus_le d n J hJ

end ZeroLocusDimH

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ChowDegreeSection.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (u : Fin n → F),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((e + 2 : ℕ) : WithBot ℕ∞) →
      linForm u ∉ I →
        chowDegree I (e + 2) = (divCycle I u).sum fun W m => m * chowDegree W (e + 1)

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
