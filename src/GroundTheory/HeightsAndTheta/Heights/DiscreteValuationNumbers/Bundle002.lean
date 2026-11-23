module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle001
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
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
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Combinatorics.Matroid.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Polynomial

universe u

theorem ReesAlgebraDim.proof (h₁ : DimensionInequality.Statement.{u, u}) :
    ReesAlgebraDim.Statement.{u} := by
  intro A _ _ _ I hI n hn
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hinj : Function.Injective (algebraMap A (reesAlgebra I)) := by
    intro x y h
    have := congrArg (fun r : reesAlgebra I => (r : A[X])) h
    simpa using this
  apply le_antisymm
  · rw [ringKrullDim_le_iff_height_le]
    intro P hP
    have key := h₁ A (reesAlgebra I) hinj P
    have htd : Algebra.trdeg A (reesAlgebra I) ≤ 1 := by
      calc Algebra.trdeg A (reesAlgebra I) ≤ Algebra.trdeg A A[X] :=
            trdeg_le_of_injective (reesAlgebra I).val Subtype.val_injective
        _ = 1 := Polynomial.trdeg_of_isDomain
    have hp : (P.under A).height ≤ n := by
      have := Ideal.height_le_ringKrullDim_of_ne_top (inferInstance : (P.under A).IsPrime).ne_top
      rw [hn] at this
      exact_mod_cast this
    have hc : Cardinal.ofENat P.height ≤ Cardinal.ofENat ((n + 1 : ℕ) : ℕ∞) := by
      calc Cardinal.ofENat P.height
          ≤ Cardinal.ofENat P.height + Algebra.trdeg (A ⧸ P.under A) (reesAlgebra I ⧸ P) :=
            le_self_add
        _ ≤ Cardinal.ofENat (P.under A).height + Algebra.trdeg A (reesAlgebra I) := key
        _ ≤ Cardinal.ofENat (n : ℕ∞) + 1 := by gcongr
        _ = Cardinal.ofENat ((n + 1 : ℕ) : ℕ∞) := by simp
    have : P.height ≤ ((n + 1 : ℕ) : ℕ∞) := Cardinal.ofENat_le_ofENat.mp hc
    exact_mod_cast this
  · let f : reesAlgebra I →+* A := (Polynomial.constantCoeff).comp (reesAlgebra I).val.toRingHom
    have hf : Function.Surjective f := fun x => ⟨algebraMap A (reesAlgebra I) x, by simp [f]⟩
    let r : reesAlgebra I := ⟨monomial 1 a, reesAlgebra.monomial_mem.mpr (by simpa using haI)⟩
    have hr0 : r ≠ 0 := by
      intro h
      have := congrArg (fun s : reesAlgebra I => (s : A[X])) h
      simp [r] at this
      exact ha0 this
    have h := ringKrullDim_succ_le_of_surjective f hf (mem_nonZeroDivisors_of_ne_zero hr0)
      (by simp [f, r])
    rw [hn] at h
    exact_mod_cast h
end NumbersDVR
end Heights
end Heights₂
end GroundTheory
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Polynomial


attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
theorem PolynomialPrimeOverZeroHeight.proof : PolynomialPrimeOverZeroHeight.Statement := by
  intro D _ _ Q _ hQ
  let K := FractionRing D
  have disj : Disjoint ((nonZeroDivisors D).map (C : D →+* D[X]) : Set D[X]) (Q : Set D[X]) := by
    refine Set.disjoint_left.mpr fun a ⟨b, hb⟩ ha ↦ ?_
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb.1
    apply hb0
    have : b ∈ Q.comap (C : D →+* D[X]) := by
      rw [Ideal.mem_comap]
      simpa [hb.2] using ha
    rwa [hQ, Ideal.mem_bot] at this
  have hK : ringKrullDim K[X] = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one K[X] (Polynomial.not_isField K)
  have h := IsLocalization.height_map_of_disjoint ((nonZeroDivisors D).map (C : D →+* D[X]))
    (S := K[X]) Q disj
  have hP : (Q.map (algebraMap D[X] K[X])).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint ((nonZeroDivisors D).map (C : D →+* D[X])) K[X] Q
      ‹_› disj
  have hle : ((Q.map (algebraMap D[X] K[X])).height : WithBot ℕ∞) ≤ 1 :=
    hK ▸ Ideal.height_le_ringKrullDim_of_isPrime
  rw [h] at hle
  exact_mod_cast hle

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

open Polynomial Cardinal

theorem DimensionInequalityOneGenerator.proof (h₁ : PolynomialDimensionInequality.Statement.{u})
    (h₂ : QuotientHeightAddOne.Statement.{u}) : DimensionInequalityOneGenerator.Statement.{u, v} := by
  intro A B _ _ _ _ _ _ x hx hinj P _

  let φ : A[X] →ₐ[A] B := aeval x
  have hφ : Function.Surjective φ := by
    intro b
    have hb : b ∈ (aeval x : A[X] →ₐ[A] B).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, hx]; exact Algebra.mem_top
    exact hb

  let P' : Ideal A[X] := P.comap (φ : A[X] →+* B)
  have hP' : P.under A = P'.under A := by
    ext a; simp [P', φ, Ideal.under, Ideal.mem_comap]
  have : P'.LiesOver (P.under A) := ⟨hP'⟩

  have H₁ : ofENat P'.height + Algebra.trdeg (A ⧸ P.under A) (A[X] ⧸ P') ≤
      ofENat (P.under A).height + 1 := by
    have key : ∀ (q : Ideal A) [q.IsPrime] [P'.LiesOver q],
        ofENat P'.height + Algebra.trdeg (A ⧸ q) (A[X] ⧸ P') ≤ ofENat q.height + 1 := by
      intro q _ _
      obtain rfl : q = P'.under A := Ideal.LiesOver.over
      exact h₁ A P'
    exact key _

  have htr : lift.{v} (Algebra.trdeg (A ⧸ P.under A) (A[X] ⧸ P')) =
      lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) := by
    let f : A[X] ⧸ P' →+* B ⧸ P := Ideal.quotientMap P (φ : A[X] →+* B) le_rfl
    have hf : Function.Bijective f :=
      ⟨Ideal.quotientMap_injective' le_rfl, Ideal.quotientMap_surjective hφ⟩
    refine AlgEquiv.lift_trdeg_eq
      (AlgEquiv.ofRingEquiv (f := (RingEquiv.ofBijective f hf : A[X] ⧸ P' ≃+* B ⧸ P)) ?_)
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    simp [f, φ, Ideal.Quotient.algebraMap_mk_of_liesOver]

  have H₁' : ofENat P'.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) ≤
      ofENat (P.under A).height + 1 := by
    have := Cardinal.lift_le.{v}.mpr H₁
    simpa only [lift_add, lift_ofENat, lift_one, htr] using this
  rw [← Cardinal.lift_le.{u}]
  simp only [lift_add, lift_ofENat]
  by_cases hker : RingHom.ker φ = ⊥
  ·
    have hinjφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot _).mpr hker
    let e : A[X] ≃ₐ[A] B := AlgEquiv.ofBijective φ ⟨hinjφ, hφ⟩
    have hh : P'.height = P.height := RingEquiv.height_comap (e : A[X] ≃+* B) P
    have ht : lift.{u} (Algebra.trdeg A B) = 1 := by
      rw [← e.lift_trdeg_eq, Polynomial.trdeg_of_isDomain, lift_one]
    rw [ht, ← hh]
    exact H₁'
  ·
    let e := Ideal.quotientKerAlgEquivOfSurjective hφ
    let Q : Ideal (A[X] ⧸ RingHom.ker φ) := P.comap (e : A[X] ⧸ RingHom.ker φ ≃+* B)
    have hQ : Q.comap (Ideal.Quotient.mk (RingHom.ker φ)) = P' := by
      ext f; simp [Q, P', e, Ideal.mem_comap]
    have H₂ := h₂ A[X] (RingHom.ker φ) hker Q
    rw [hQ, RingEquiv.height_comap] at H₂
    have H : ofENat P.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) + 1 ≤
        ofENat (P.under A).height + 1 :=
      calc ofENat P.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) + 1
          = ofENat (P.height + 1) + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) := by
            rw [ofENat_add, ofENat_one]; ring
        _ ≤ ofENat P'.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) :=
            add_le_add (ofENat_le_ofENat.mpr H₂) le_rfl
        _ ≤ _ := H₁'
    exact (Cardinal.add_one_le_add_one_iff.mp H).trans le_self_add

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem height_eq_of_isMaximal_mvPolynomial_fin (F : Type u) [Field F] :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) F)), M.IsMaximal → M.height = n := by
  intro n
  induction n with
  | zero =>
    intro M hM
    have h := Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    simp at h
    simpa [h]
  | succ n ih =>
    intro M hM
    let e := (finSuccEquiv F n).toRingEquiv
    rw [← e.height_map M]
    set P : Ideal (Polynomial (MvPolynomial (Fin n) F)) := M.map e with hPdef
    have hP : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hc : (P.comap (Polynomial.C : MvPolynomial (Fin n) F →+* _)).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have hlo : P.LiesOver (P.under (MvPolynomial (Fin n) F)) := ⟨rfl⟩
    rw [Polynomial.height_eq_height_add_one (P.under (MvPolynomial (Fin n) F)) P,
      ih (P.under (MvPolynomial (Fin n) F)) hc]
    norm_cast

theorem MaximalIdealHeightFG.proof : MaximalIdealHeightFG.Statement.{u} := by
  intro F _ A _ _ _ _ m hm
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg F A
  let _ : Algebra (MvPolynomial (Fin s) F) A := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) F) A := ⟨hint⟩
  have : FaithfulSMul (MvPolynomial (Fin s) F) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hinj
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing F A
  have : m.IsPrime := hm.isPrime
  have hR : ringKrullDim (MvPolynomial (Fin s) F) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hdim : ringKrullDim A ≤ s := by
    rw [← hR]
    refine Order.krullDim_le_of_strictMono
      (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin s) F) A)) fun p q hpq => ?_
    exact Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin s) F) hpq
  let n := m.under (MvPolynomial (Fin s) F)
  have : n.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal m
  have h1 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown n m
  rw [height_eq_of_isMaximal_mvPolynomial_fin F s n inferInstance] at h1
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top) (hdim.trans ?_)
  rw [h1]
  exact_mod_cast le_self_add

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Algebra Cardinal Set

noncomputable section

theorem AdjoinTrdegAdd.trdeg_adjoin_eq_of_family {R L κ : Type} [CommRing R] [CommRing L] [IsDomain L]
    [Algebra R L] (u : Set L) (w : κ → L) (hwu : range w ⊆ u) (hw : AlgebraicIndependent R w)
    (halg : ∀ a ∈ u, IsAlgebraic (adjoin R (range w)) a) :
    trdeg R (adjoin R u) = #κ := by
  have := (algebraMap R L).domain_nontrivial
  let v : κ → adjoin R u := fun i => ⟨w i, subset_adjoin (hwu ⟨i, rfl⟩)⟩
  have hv : AlgebraicIndependent R v := AlgebraicIndependent.of_comp (adjoin R u).val hw
  have heq : (adjoin R (range v)).map (adjoin R u).val = adjoin R (range w) := by
    rw [AlgHom.map_adjoin, ← range_comp]
    rfl
  let e := ((adjoin R (range v)).equivMapOfInjective (adjoin R u).val Subtype.val_injective).trans
    (Subalgebra.equivOfEq _ _ heq)
  have hval : Algebra.IsAlgebraic (adjoin R (range v)) (adjoin R u) := by
    refine ⟨fun a => ?_⟩
    have h0 : IsAlgebraic (adjoin R u) (a : L) := isAlgebraic_algebraMap a
    have h1 : IsAlgebraic (adjoin R (range w)) ((adjoin R u).val a) :=
      h0.adjoin_of_forall_isAlgebraic fun y hy => halg y hy.1
    exact (isAlgebraic_ringHom_iff_of_comp_eq e (adjoin R u).val Subtype.val_injective
      (by ext; rfl)).mp h1
  exact ((isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr
    ⟨hv, hval⟩).cardinalMk_eq_trdeg).symm

theorem AdjoinTrdegAdd.proof : AdjoinTrdegAdd.Statement := by
  intro R _ L _ _ _ hinj s t ι _ x hxt hx hxalg
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr hinj
  obtain ⟨b, hb⟩ := (AlgebraicIndependent.matroid R L).exists_isBasis s (by simp)
  obtain ⟨hbi, hbs, hbalg⟩ := AlgebraicIndependent.matroid_isBasis_iff.mp hb
  have hbi' : AlgebraicIndependent R ((↑) : b → L) := hbi

  have h1 : trdeg R (adjoin R s) = #b :=
    AdjoinTrdegAdd.trdeg_adjoin_eq_of_family s ((↑) : b → L) (by rw [Subtype.range_coe]; exact hbs) hbi'
      (by rw [Subtype.range_coe]; exact hbalg)

  let _ : Algebra (adjoin R b) (adjoin R s) := (Subalgebra.inclusion (adjoin_mono hbs)).toAlgebra
  have : IsScalarTower (adjoin R b) (adjoin R s) L := .of_algebraMap_eq fun _ => rfl
  have hxb : AlgebraicIndependent (adjoin R (range ((↑) : b → L))) x := by
    rw [Subtype.range_coe]
    exact hx.restrictScalars (Subalgebra.inclusion_injective _)
  have hsum : AlgebraicIndependent R (Sum.elim x ((↑) : b → L)) :=
    AlgebraicIndependent.sumElim_iff.mpr ⟨hbi', hxb⟩
  have hrange : range (Sum.elim x ((↑) : b → L)) = range x ∪ b := by
    rw [Set.Sum.elim_range, Subtype.range_coe]

  have hs : ∀ a ∈ s, IsAlgebraic (adjoin R (range x ∪ b)) a := fun a ha =>
    (hbalg a ha).adjoin_of_forall_isAlgebraic fun y hy => (hy.2 (Or.inr hy.1)).elim
  have hst : ∀ a ∈ s ∪ t, IsAlgebraic (adjoin R (range (Sum.elim x ((↑) : b → L)))) a := by
    rw [hrange]
    rintro a (ha | ha)
    · exact hs a ha
    · refine (hxalg a ha).adjoin_of_forall_isAlgebraic fun y hy => ?_
      rcases hy.1 with hy1 | hy1
      · exact hs y hy1
      · exact (hy.2 (Or.inl hy1)).elim
  have h2 : trdeg R (adjoin R (s ∪ t)) = #(ι ⊕ b) :=
    AdjoinTrdegAdd.trdeg_adjoin_eq_of_family (s ∪ t) (Sum.elim x ((↑) : b → L))
      (by rw [hrange]; exact union_subset (hxt.trans subset_union_right) (hbs.trans subset_union_left))
      hsum hst
  rw [h2, h1, mk_sum, lift_id, lift_id, mk_fintype, add_comm]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

open Cardinal

theorem DimensionInequality.tower_step {A : Type u} {C B : Type v} [CommRing A] [CommRing C]
    [CommRing B] [IsDomain A] [IsDomain C] [IsDomain B] [Algebra A C] [Algebra C B] [Algebra A B]
    [IsScalarTower A C B] (hAC : Function.Injective (algebraMap A C))
    (hCB : Function.Injective (algebraMap C B)) (P : Ideal B) [P.IsPrime] (Q : Ideal C) [Q.IsPrime]
    (p : Ideal A) [p.IsPrime] [P.LiesOver Q] [Q.LiesOver p] [P.LiesOver p]
    (e₁ : ofENat Q.height + Algebra.trdeg (A ⧸ p) (C ⧸ Q) ≤ ofENat p.height + Algebra.trdeg A C)
    (e₂ : ofENat P.height + Algebra.trdeg (C ⧸ Q) (B ⧸ P) ≤ ofENat Q.height + Algebra.trdeg C B) :
    ofENat P.height + Algebra.trdeg (A ⧸ p) (B ⧸ P) ≤ ofENat p.height + Algebra.trdeg A B := by
  have : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr hAC
  have : FaithfulSMul C B := (faithfulSMul_iff_algebraMap_injective C B).mpr hCB
  have : IsScalarTower (A ⧸ p) (C ⧸ Q) (B ⧸ P) := IsScalarTower.of_algebraMap_eq fun x ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [Ideal.Quotient.algebraMap_mk_of_liesOver, ← IsScalarTower.algebraMap_apply]
  have t₁ := trdeg_add_eq A C (A := B)
  have t₂ := trdeg_add_eq (A ⧸ p) (C ⧸ Q) (A := B ⧸ P)
  calc ofENat P.height + Algebra.trdeg (A ⧸ p) (B ⧸ P)
      = (ofENat P.height + Algebra.trdeg (C ⧸ Q) (B ⧸ P)) + Algebra.trdeg (A ⧸ p) (C ⧸ Q) := by
        rw [← t₂]; ring
    _ ≤ (ofENat Q.height + Algebra.trdeg C B) + Algebra.trdeg (A ⧸ p) (C ⧸ Q) := by gcongr
    _ = (ofENat Q.height + Algebra.trdeg (A ⧸ p) (C ⧸ Q)) + Algebra.trdeg C B := by ring
    _ ≤ (ofENat p.height + Algebra.trdeg A C) + Algebra.trdeg C B := by gcongr
    _ = ofENat p.height + Algebra.trdeg A B := by rw [add_assoc, t₁]

theorem DimensionInequality.proof (h₁ : DimensionInequalityOneGenerator.Statement.{u, v})
    (h₂ : DimensionInequalityOneGenerator.Statement.{v, v}) :
    DimensionInequality.Statement.{u, v} := by
  classical
  intro A B _ _ _ _ _ _ _ hinj P _

  suffices key : ∀ (n : ℕ) (B : Type v) [CommRing B] [IsDomain B] [Algebra A B] (x : Fin n → B),
      Algebra.adjoin A (Set.range x) = ⊤ → Function.Injective (algebraMap A B) →
      ∀ (P : Ideal B) [P.IsPrime] (p : Ideal A) [p.IsPrime] [P.LiesOver p],
        ofENat P.height + Algebra.trdeg (A ⧸ p) (B ⧸ P) ≤ ofENat p.height + Algebra.trdeg A B by
    obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
    refine key s.card B (fun i ↦ (s.equivFin.symm i : B)) ?_ hinj P (P.under A)
    rw [← hs]
    congr 1
    ext b
    refine ⟨?_, fun hb ↦ ⟨s.equivFin ⟨b, hb⟩, by simp⟩⟩
    rintro ⟨i, rfl⟩
    exact (s.equivFin.symm i).2
  intro n
  induction n with
  | zero =>
    intro B _ _ _ x hx hinj P _ p _ _
    obtain rfl : p = P.under A := Ideal.LiesOver.over
    refine h₁ A B 0 ?_ hinj P
    rw [eq_top_iff, ← hx]
    exact Algebra.adjoin_mono (by simp [Set.range_eq_empty])
  | succ n ih =>
    intro B _ _ _ x hx hinj P _ p _ _
    set C : Subalgebra A B := Algebra.adjoin A (Set.range (x ∘ Fin.succ)) with hC
    let y : Fin n → C := fun i ↦ ⟨x i.succ, Algebra.subset_adjoin ⟨i, rfl⟩⟩
    have hy : Algebra.adjoin A (Set.range y) = ⊤ := by
      apply Subalgebra.map_injective (f := C.val) Subtype.val_injective
      rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val, ← Set.range_comp]
      rfl
    have hAC : Function.Injective (algebraMap A C) := fun a b hab ↦
      hinj (congrArg Subtype.val hab :)
    have hCB : Function.Injective (algebraMap C B) := Subtype.val_injective
    have : Algebra.FiniteType A C :=
      ⟨⟨Finset.univ.image y, by simpa [Finset.coe_image] using hy⟩⟩
    have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
    have hB : Algebra.adjoin C {x 0} = ⊤ := by
      apply Subalgebra.restrictScalars_injective A
      rw [Subalgebra.restrictScalars_top, ← Algebra.adjoin_union_eq_adjoin_adjoin, eq_top_iff, ← hx]
      apply Algebra.adjoin_mono
      rintro _ ⟨i, rfl⟩
      cases i using Fin.cases with
      | zero => exact Or.inr rfl
      | succ j => exact Or.inl ⟨j, rfl⟩
    have : (P.under C).LiesOver p := Ideal.LiesOver.tower_bot P (P.under C) p
    exact DimensionInequality.tower_step hAC hCB P (P.under C) p
      (ih C y hy hAC (P.under C) p) (h₂ C B (x 0) hB hCB P)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def ComponentDim.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
      ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P →
      ∀ W : Ideal (MRing ι O), divCycle P f W ≠ 0 → (C ϖ : MRing ι O) ∈ W →
        ringKrullDim (MRing ι O ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
