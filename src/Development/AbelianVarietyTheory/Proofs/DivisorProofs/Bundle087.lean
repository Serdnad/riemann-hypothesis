module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Index
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section

section

namespace GlobalTheory

namespace FracAlgDedekind

open Order

theorem ringKrullDim_le_of_isIntegral {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R] (h : Function.Injective (algebraMap A R)) :
    ringKrullDim A ≤ ringKrullDim R := by
  rcases isEmpty_or_nonempty (PrimeSpectrum A) with hA | hA
  · rw [ringKrullDim, Order.krullDim_eq_bot]
    exact bot_le
  rw [ringKrullDim, Order.krullDim_eq_iSup_length]
  rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
  refine iSup_le fun l => ?_
  obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal R)
    (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 h]; exact bot_le)
  have : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact LTSeries.length_le_krullDim L

theorem exists_finite_inj_polynomial (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (hB : ¬ IsField B) :
    ∃ f : Polynomial k →+* B, Function.Injective f ∧ f.Finite := by
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  letI : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) B :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have : Module.Finite (MvPolynomial (Fin s) k) B := hfin
  have hle := ringKrullDim_le_of_isIntegral (A := MvPolynomial (Fin s) k) (R := B) hg
  have hdim : ringKrullDim (MvPolynomial (Fin s) k) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hB1 : ringKrullDim B ≤ 1 := Ring.krullDimLE_iff.1 inferInstance
  rw [hdim] at hle
  have hs1 : s ≤ 1 := by exact_mod_cast hle.trans hB1
  have hs0 : s ≠ 0 := by
    rintro rfl
    have : Algebra.IsIntegral k (MvPolynomial (Fin 0) k) :=
      Algebra.IsIntegral.of_surjective (Algebra.ofId k (MvPolynomial (Fin 0) k))
        (MvPolynomial.C_surjective (Fin 0))
    have : Algebra.IsIntegral k B := Algebra.IsIntegral.trans (MvPolynomial (Fin 0) k)
    exact hB ((Algebra.IsIntegral.isField_iff_isField (algebraMap k B).injective).1
      (Field.toIsField k))
  obtain rfl : s = 1 := by omega
  let e : MvPolynomial (Fin 1) k ≃ₐ[k] Polynomial k :=
    MvPolynomial.uniqueAlgEquiv k (Fin 1)
  refine ⟨g.toRingHom.comp e.symm.toRingEquiv.toRingHom, hg.comp e.symm.injective, ?_⟩
  exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ e.symm.surjective)

theorem exists_isAlgebraic_ratFunc : ∀ (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B]
    [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B →
    ∃ _ : Algebra (RatFunc k) (FractionRing B), Algebra.IsAlgebraic (RatFunc k) (FractionRing B) := by
  intro k B _ _ _ _ _ hB
  obtain ⟨f, hf, hfin⟩ := exists_finite_inj_polynomial k B hB
  letI : Algebra (Polynomial k) B := f.toAlgebra
  have : Module.Finite (Polynomial k) B := hfin
  have hφ : Function.Injective (algebraMap (Polynomial k) (FractionRing B)) := by
    rw [IsScalarTower.algebraMap_eq (Polynomial k) B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hf
  letI alg : Algebra (RatFunc k) (FractionRing B) := (IsFractionRing.lift hφ (K := RatFunc k)).toAlgebra
  have : IsScalarTower (Polynomial k) (RatFunc k) (FractionRing B) :=
    IsScalarTower.of_algebraMap_eq fun p => (IsFractionRing.lift_algebraMap hφ p).symm
  have : FaithfulSMul (Polynomial k) B := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  have : Algebra.IsAlgebraic B (FractionRing B) :=
    IsLocalization.isAlgebraic (FractionRing B) (nonZeroDivisors B)
  have : Algebra.IsAlgebraic (Polynomial k) (FractionRing B) :=
    Algebra.IsAlgebraic.trans (Polynomial k) B (FractionRing B)
  exact ⟨alg, Algebra.IsAlgebraic.extendScalars (R := Polynomial k) (RatFunc.algebraMap_injective k)⟩

end FracAlgDedekind

end GlobalTheory
end

section

open scoped Pointwise

namespace GlobalTheory

theorem doubleCoset_fibre_card {G : Type} [Group G] (T Γ K' : Subgroup G) (x : G) :
    Nat.card ((fun q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G) =>
        DoubleCoset.mk T K' (Quotient.out q)) ⁻¹' {DoubleCoset.mk T K' x}) =
      Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T)
        (((T ⊓ K'.map (MulAut.conj x).toMonoidHom).subgroupOf T : Subgroup T) : Set T)) := by
  classical
  set U : Subgroup G := T ⊓ K'.map (MulAut.conj x).toMonoidHom with hU
  have memU : ∀ u : G, u ∈ U ↔ u ∈ T ∧ x⁻¹ * u * x ∈ K' := by
    intro u
    simp only [hU, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨hT, k, hk, rfl⟩
      exact ⟨hT, by simpa [mul_assoc] using hk⟩
    · rintro ⟨hT, hk⟩
      exact ⟨hT, _, hk, by group⟩
  let F := fun q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G) =>
        DoubleCoset.mk T K' (Quotient.out q)
  have hland : ∀ t : T, DoubleCoset.mk (Γ ⊓ T) K' ((t : G) * x) ∈ F ⁻¹' {DoubleCoset.mk T K' x} := by
    intro t
    obtain ⟨h, hh, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul (Γ ⊓ T) K' ((t : G) * x)
    simp only [Set.mem_preimage, Set.mem_singleton_iff, F]
    rw [eq_comm, DoubleCoset.eq]
    refine ⟨h * t, T.mul_mem (Subgroup.mem_inf.mp hh).2 t.2, k, hk, ?_⟩
    rw [he]; group
  let φ₀ : T → F ⁻¹' {DoubleCoset.mk T K' x} := fun t => ⟨_, hland t⟩
  have hwd : ∀ a b : T, (DoubleCoset.setoid ((Γ.subgroupOf T : Subgroup T) : Set T)
      ((U.subgroupOf T : Subgroup T) : Set T)) a b → φ₀ a = φ₀ b := by
    intro a b hab
    obtain ⟨g, hg, u, hu, rfl⟩ := DoubleCoset.rel_iff.mp hab
    apply Subtype.ext
    simp only [φ₀]
    rw [DoubleCoset.eq]
    rw [Subgroup.mem_subgroupOf] at hg hu
    refine ⟨g, Subgroup.mem_inf.mpr ⟨hg, g.2⟩, x⁻¹ * u * x, ((memU u).mp hu).2, ?_⟩
    simp only [Subgroup.coe_mul]
    group
  let φ : DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T)
      ((U.subgroupOf T : Subgroup T) : Set T) → F ⁻¹' {DoubleCoset.mk T K' x} :=
    Quotient.lift (s := DoubleCoset.setoid _ _) φ₀ hwd
  have hφ : Function.Bijective φ := by
    constructor
    · intro p q hpq
      induction p using Quotient.inductionOn with | h a => ?_
      induction q using Quotient.inductionOn with | h b => ?_
      have h1 : DoubleCoset.mk (Γ ⊓ T) K' ((a : G) * x) = DoubleCoset.mk (Γ ⊓ T) K' ((b : G) * x) :=
        congrArg Subtype.val hpq
      obtain ⟨h, hh, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).mp h1
      have hhT : h ∈ T := (Subgroup.mem_inf.mp hh).2
      have huT : (a : G)⁻¹ * h⁻¹ * b ∈ T :=
        T.mul_mem (T.mul_mem (T.inv_mem a.2) (T.inv_mem hhT)) b.2
      apply Quotient.sound
      refine DoubleCoset.rel_iff.mpr ⟨⟨h, hhT⟩, ?_, ⟨_, huT⟩, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]; exact (Subgroup.mem_inf.mp hh).1
      · rw [Subgroup.mem_subgroupOf, memU]
        refine ⟨huT, ?_⟩
        have : x⁻¹ * ((a : G)⁻¹ * h⁻¹ * b) * x = k := by
          rw [show (b : G) = h * a * x * k * x⁻¹ by
            rw [show h * (a : G) * x * k * x⁻¹ = h * ((a : G) * x) * k * x⁻¹ by group, ← he]; group]
          group
        rw [this]; exact hk
      · apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group
    · rintro ⟨q, hq⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, F] at hq
      obtain ⟨s, hs, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).mp hq
      refine ⟨Quotient.mk _ ⟨s⁻¹, T.inv_mem hs⟩, ?_⟩
      apply Subtype.ext
      show DoubleCoset.mk (Γ ⊓ T) K' (s⁻¹ * x) = q
      conv_rhs => rw [← DoubleCoset.out_eq' q]
      rw [DoubleCoset.eq]
      refine ⟨1, Subgroup.one_mem _, k⁻¹, K'.inv_mem hk, ?_⟩
      rw [he]; group
  exact (Nat.card_eq_of_bijective φ hφ).symm

end GlobalTheory
end

section

namespace GlobalTheory.MassConj

@[ext]
structure ConjPair (H X : Type) where

  elt : H

  pt : X

variable {H X : Type} [Group H] [MulAction H X]

instance : MulAction H (ConjPair H X) where
  smul δ p := ⟨δ * p.elt * δ⁻¹, δ • p.pt⟩
  one_smul p := by
    show ConjPair.mk _ _ = p
    ext <;> simp
  mul_smul δ ε p := by
    show ConjPair.mk (δ * ε * p.elt * (δ * ε)⁻¹) ((δ * ε) • p.pt) =
      ConjPair.mk (δ * (ε * p.elt * ε⁻¹) * δ⁻¹) (δ • ε • p.pt)
    ext
    · simp only; group
    · exact mul_smul δ ε p.pt

@[simp] theorem smul_elt (δ : H) (p : ConjPair H X) : (δ • p).elt = δ * p.elt * δ⁻¹ := rfl

@[simp] theorem smul_pt (δ : H) (p : ConjPair H X) : (δ • p).pt = δ • p.pt := rfl

theorem mem_stabilizer_iff (δ : H) (p : ConjPair H X) :
    δ ∈ MulAction.stabilizer H p ↔ δ * p.elt = p.elt * δ ∧ δ • p.pt = p.pt := by
  rw [MulAction.mem_stabilizer_iff, ConjPair.ext_iff, smul_elt, smul_pt]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    calc δ * p.elt = δ * p.elt * δ⁻¹ * δ := by group
      _ = p.elt * δ := by rw [h1]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h1]; group

end GlobalTheory.MassConj
end

section

namespace GlobalTheory

theorem card_dvd_sum_of_invariant_of_card_stabilizer_dvd (G X : Type) [AddGroup G] [Finite G]
    [Fintype X] [AddAction G X] (h : X → ℤ) (hinv : ∀ (g : G) (x : X), h (g +ᵥ x) = h x)
    (hdvd : ∀ x, (Nat.card (AddAction.stabilizer G x) : ℤ) ∣ h x) :
    (Nat.card G : ℤ) ∣ ∑ x, h x := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun x : X => (Quotient.mk (AddAction.orbitRel G X) x)) (f := h)]
  refine Finset.dvd_sum fun q _ => ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  have hconst : ∀ y ∈ Finset.univ.filter
      (fun y : X => Quotient.mk (AddAction.orbitRel G X) y = Quotient.mk (AddAction.orbitRel G X) x),
      h y = h x := by
    intro y hy
    have hy' := Quotient.exact (Finset.mem_filter.mp hy).2
    obtain ⟨g, rfl⟩ : y ∈ AddAction.orbit G x := AddAction.orbitRel_apply.mp hy'
    exact hinv g x
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter
      (fun y : X => Quotient.mk (AddAction.orbitRel G X) y
        = Quotient.mk (AddAction.orbitRel G X) x)).card = Nat.card (AddAction.orbit G x) := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Quotient.eq]
    exact AddAction.orbitRel_apply
  have hG : Nat.card G = Nat.card (AddAction.orbit G x) * Nat.card (AddAction.stabilizer G x) := by
    rw [Nat.card_congr (AddAction.orbitEquivQuotientStabilizer G x)]
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  rw [hcard, hG, Nat.cast_mul]
  exact mul_dvd_mul_left _ (hdvd x)

end GlobalTheory
end

section

namespace GlobalTheory

open Subgroup

theorem relIndex_cocycle_of_ne_zero {A : Type} [Group A] (X Y Z : Subgroup A)
    (hXY : X.relIndex Y ≠ 0) (hYX : Y.relIndex X ≠ 0) (hYZ : Y.relIndex Z ≠ 0)
    (hZY : Z.relIndex Y ≠ 0) (hXZ : X.relIndex Z ≠ 0) (hZX : Z.relIndex X ≠ 0) :
    Y.relIndex X * Z.relIndex Y * X.relIndex Z = X.relIndex Y * Y.relIndex Z * Z.relIndex X := by
  have a1 := relIndex_inf_mul_relIndex Y Z X
  have a2 := relIndex_inf_mul_relIndex Z Y X
  have b1 := relIndex_inf_mul_relIndex Z X Y
  have b2 := relIndex_inf_mul_relIndex X Z Y
  have c1 := relIndex_inf_mul_relIndex X Y Z
  have c2 := relIndex_inf_mul_relIndex Y X Z
  rw [inf_comm Z Y] at a2
  rw [inf_comm Y X] at c2
  rw [inf_comm X Z] at b2
  rw [inf_comm Z Y] at b2
  rw [inf_comm Y X] at a2
  rw [inf_comm X Z] at c2
  have ha : (Y ⊓ Z).relIndex X ≠ 0 := relIndex_inf_ne_zero hYX hZX
  have hb : (Z ⊓ X).relIndex Y ≠ 0 := relIndex_inf_ne_zero hZY hXY
  have hc : (X ⊓ Y).relIndex Z ≠ 0 := relIndex_inf_ne_zero hXZ hYZ
  have hpY : Y.relIndex (Z ⊓ X) ≠ 0 := by
    intro h; apply ha; rw [← a1, h, zero_mul]
  have hpZ : Z.relIndex (X ⊓ Y) ≠ 0 := by
    intro h; apply hb; rw [← b1, h, zero_mul]
  have hpX : X.relIndex (Y ⊓ Z) ≠ 0 := by
    intro h; apply hc; rw [← c1, h, zero_mul]
  have hP : 0 < Z.relIndex (X ⊓ Y) * X.relIndex (Y ⊓ Z) * Y.relIndex (Z ⊓ X) := by
    positivity
  apply Nat.eq_of_mul_eq_mul_left hP
  calc Z.relIndex (X ⊓ Y) * X.relIndex (Y ⊓ Z) * Y.relIndex (Z ⊓ X) *
        (Y.relIndex X * Z.relIndex Y * X.relIndex Z)
      = (Z.relIndex (X ⊓ Y) * Y.relIndex X) * (X.relIndex (Y ⊓ Z) * Z.relIndex Y) *
        (Y.relIndex (Z ⊓ X) * X.relIndex Z) := by ring
    _ = (Y.relIndex (Z ⊓ X) * Z.relIndex X) * (Z.relIndex (X ⊓ Y) * X.relIndex Y) *
        (X.relIndex (Y ⊓ Z) * Y.relIndex Z) := by rw [a2, b2, c2, a1, b1, c1]
    _ = _ := by ring

theorem map_conj_mul {A : Type} [Group A] (K : Subgroup A) (x y : A) :
    K.map (MulAut.conj (x * y)).toMonoidHom =
      (K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [mul_assoc]

theorem relIndex_map_conj {A : Type} [Group A] (H L : Subgroup A) (g : A) :
    (H.map (MulAut.conj g).toMonoidHom).relIndex (L.map (MulAut.conj g).toMonoidHom) =
      H.relIndex L :=
  Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

theorem map_conj_one {A : Type} [Group A] (K : Subgroup A) :
    K.map (MulAut.conj (1 : A)).toMonoidHom = K := by
  ext x; simp

theorem relIndex_conj_pow_succ {A : Type} [Group A] (K : Subgroup A) (g : A) (i : ℕ) :
    (K.map (MulAut.conj (g ^ (i + 1))).toMonoidHom).relIndex
        (K.map (MulAut.conj (g ^ i)).toMonoidHom) =
      (K.map (MulAut.conj g).toMonoidHom).relIndex K ∧
    (K.map (MulAut.conj (g ^ i)).toMonoidHom).relIndex
        (K.map (MulAut.conj (g ^ (i + 1))).toMonoidHom) =
      K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  rw [pow_succ, map_conj_mul, relIndex_map_conj, relIndex_map_conj]
  exact ⟨rfl, rfl⟩

theorem relIndex_conj_pow_induction {A : Type} [Group A] (K : Subgroup A) (g : A)
    (ha : (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0)
    (hb : K.relIndex (K.map (MulAut.conj g).toMonoidHom) ≠ 0) (i : ℕ) :
    (K.map (MulAut.conj (g ^ i)).toMonoidHom).relIndex K ≠ 0 ∧
    K.relIndex (K.map (MulAut.conj (g ^ i)).toMonoidHom) ≠ 0 ∧
    (K.map (MulAut.conj (g ^ i)).toMonoidHom).relIndex K *
        (K.relIndex (K.map (MulAut.conj g).toMonoidHom)) ^ i =
      K.relIndex (K.map (MulAut.conj (g ^ i)).toMonoidHom) *
        ((K.map (MulAut.conj g).toMonoidHom).relIndex K) ^ i := by
  induction i with
  | zero =>
    rw [pow_zero, map_conj_one]
    simp
  | succ i ih =>
    obtain ⟨hu, hv, hi⟩ := ih
    obtain ⟨sa, sb⟩ := relIndex_conj_pow_succ K g i
    set B := K.map (MulAut.conj (g ^ i)).toMonoidHom
    set C := K.map (MulAut.conj (g ^ (i + 1))).toMonoidHom
    set a := (K.map (MulAut.conj g).toMonoidHom).relIndex K
    set b := K.relIndex (K.map (MulAut.conj g).toMonoidHom)
    have hCB : C.relIndex B ≠ 0 := by rw [sa]; exact ha
    have hBC : B.relIndex C ≠ 0 := by rw [sb]; exact hb
    have hCK : C.relIndex K ≠ 0 := relIndex_ne_zero_trans hCB hu
    have hKC : K.relIndex C ≠ 0 := relIndex_ne_zero_trans hv hBC
    have coc := relIndex_cocycle_of_ne_zero K B C hv hu hBC hCB hKC hCK
    rw [sa, sb] at coc
    refine ⟨hCK, hKC, ?_⟩
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hv)
    calc C.relIndex K * b ^ (i + 1) * K.relIndex B
        = b * K.relIndex B * C.relIndex K * b ^ i := by ring
      _ = B.relIndex K * a * K.relIndex C * b ^ i := by rw [coc]; ring
      _ = a * K.relIndex C * (B.relIndex K * b ^ i) := by ring
      _ = K.relIndex C * a ^ (i + 1) * K.relIndex B := by rw [hi]; ring

theorem relIndex_conj_eq_of_pow_eq : ∀ (A : Type) [Group A] (K : Subgroup A) (g : A) (n : ℕ), 0 < n →
    (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0 →
    K.relIndex (K.map (MulAut.conj g).toMonoidHom) ≠ 0 →
    (K.map (MulAut.conj (g ^ n)).toMonoidHom).relIndex K =
      K.relIndex (K.map (MulAut.conj (g ^ n)).toMonoidHom) →
    (K.map (MulAut.conj g).toMonoidHom).relIndex K =
      K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  intro A _ K g n hn ha hb heq
  obtain ⟨hu, _, hi⟩ := relIndex_conj_pow_induction K g ha hb n
  rw [heq] at hi hu
  have hpow := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hu) hi
  exact (Nat.pow_left_injective (Nat.pos_iff_ne_zero.mp hn) hpow).symm

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_finset_leftTransversal_of_relIndex_ne_zero : ∀ {G : Type} [Group G] (H K : Subgroup G),
    K ≤ H → K.relIndex H ≠ 0 → ∃ R : Finset G, (∀ r ∈ R, r ∈ H) ∧ ∀ k ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * k ∈ K := by
  intro G _ H K _ hrel
  have hfin : Finite (H ⧸ K.subgroupOf H) := by
    apply Nat.finite_of_card_ne_zero
    simpa [Subgroup.relIndex, Subgroup.index] using hrel
  let f : H ⧸ K.subgroupOf H → G := fun q => ((Quotient.out q : H) : G)
  have hR : (Set.range f).Finite := Set.finite_range f
  refine ⟨hR.toFinset, ?_, ?_⟩
  · intro r hr
    rw [Set.Finite.mem_toFinset] at hr
    obtain ⟨q, rfl⟩ := hr
    exact (Quotient.out q : H).2
  · intro k hk
    refine ⟨f (QuotientGroup.mk (⟨k, hk⟩ : H)), ⟨?_, ?_⟩, ?_⟩
    · rw [Set.Finite.mem_toFinset]; exact ⟨_, rfl⟩
    · have h1 : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : H) : H ⧸ K.subgroupOf H)) :
          H ⧸ K.subgroupOf H) = QuotientGroup.mk ⟨k, hk⟩ := QuotientGroup.out_eq' _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
      simpa [f] using h1
    · rintro r ⟨hr, hrk⟩
      rw [Set.Finite.mem_toFinset] at hr
      obtain ⟨q, rfl⟩ := hr
      have h2 : (QuotientGroup.mk (Quotient.out q) : H ⧸ K.subgroupOf H) = QuotientGroup.mk ⟨k, hk⟩ := by
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [f] using hrk
      rw [QuotientGroup.out_eq'] at h2
      simp [f, h2]

end GlobalTheory
end

section

namespace GlobalTheory

theorem stab_relIndex_ne_zero : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ TM : Subgroup M, (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) → ∀ (q : M) (X : N), (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) ≠ 0 := by
  intro P M N _ _ _ s π u _ _ _ KP KM L _ _ _ TM hU q X
  obtain ⟨U, hUK, hUi, hUk⟩ := hU X
  set S := TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM
  set C := KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)
  have hUC : U ≤ C := by
    intro k hk
    simp only [C, Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hUk k hk
  have hSK : S ≤ KM := inf_le_right
  have hUS : U.relIndex S ≠ 0 := fun h =>
    hUi (Subgroup.relIndex_eq_zero_of_le_right hSK h)
  have hCS : C.relIndex S ≠ 0 := fun h =>
    hUS (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.relIndex_dvd_of_le_left S hUC))
  rw [Subgroup.inf_relIndex_left]
  exact hCS

end GlobalTheory
end
