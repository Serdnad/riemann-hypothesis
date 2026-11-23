module

public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.RingHom.Etale
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

@[expose] public section

section

namespace GlobalTheory.TwoVarValRing

theorem not_X_dvd_iff_weightedOrder {σ R : Type} [DecidableEq σ] [Semiring R] (s : σ)
    (f : MvPowerSeries σ R) :
    ¬ MvPowerSeries.X s ∣ f ↔ f.weightedOrder (Pi.single s 1) = 0 := by
  have h := MvPowerSeries.weightedOrder_eq_nat (f := f) (Pi.single s 1) (n := 0)
  rw [Nat.cast_zero] at h
  rw [h, MvPowerSeries.X_dvd_iff]
  simp only [Finsupp.weight_single_one_apply, not_forall, Nat.not_lt_zero, false_imp_iff,
    implies_true, and_true]
  constructor
  · rintro ⟨m, h1, h2⟩; exact ⟨m, h2, h1⟩
  · rintro ⟨m, h1, h2⟩; exact ⟨m, h2, h1⟩

theorem not_X_dvd_mul {σ R : Type} [DecidableEq σ] [Semiring R] [NoZeroDivisors R] (s : σ)
    {f g : MvPowerSeries σ R} (hf : ¬ MvPowerSeries.X s ∣ f) (hg : ¬ MvPowerSeries.X s ∣ g) :
    ¬ MvPowerSeries.X s ∣ f * g := by
  rw [not_X_dvd_iff_weightedOrder] at *
  rw [MvPowerSeries.weightedOrder_mul, hf, hg, add_zero]

theorem not_X_dvd_one {σ R : Type} [DecidableEq σ] [Semiring R] [Nontrivial R] (s : σ) :
    ¬ MvPowerSeries.X s ∣ (1 : MvPowerSeries σ R) := by
  rw [not_X_dvd_iff_weightedOrder, MvPowerSeries.weightedOrder_one]

theorem not_X_one_dvd_X_zero (k : Type) [Field k] :
    ¬ MvPowerSeries.X 1 ∣ (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) := by
  rw [MvPowerSeries.X_dvd_iff]
  intro h
  have := h (Finsupp.single 0 1) (by simp)
  simp [MvPowerSeries.coeff_index_single_self_X] at this

theorem not_X_one_dvd_subst (k : Type) [Field k] (b : PowerSeries k) (hb : b ≠ 0) :
    ¬ MvPowerSeries.X 1 ∣ b.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) := by
  have hs : PowerSeries.HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) :=
    PowerSeries.HasSubst.X 0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb
    (PowerSeries.X_prime (R := k)).irreducible
  rw [PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs]
  apply not_X_dvd_mul
  · intro h
    have hu : IsUnit ((u : PowerSeries k).subst
        (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k)) := by
      rw [← PowerSeries.coe_substAlgHom hs]
      exact u.isUnit.map _
    exact not_X_dvd_one (R := k) (1 : Fin 2) (h.trans hu.dvd)
  · induction n with
    | zero => simpa using not_X_dvd_one (R := k) (1 : Fin 2)
    | succ n ih =>
      rw [pow_succ]
      exact not_X_dvd_mul _ (ih (by simp)) (not_X_one_dvd_X_zero k)

noncomputable def locSecondVar (k : Type) [Field k] :
    Subalgebra k (FractionRing (MvPowerSeries (Fin 2) k)) where
  carrier := {x | ∃ u v : MvPowerSeries (Fin 2) k, ¬ MvPowerSeries.X 1 ∣ v ∧
    x * algebraMap (MvPowerSeries (Fin 2) k) _ v = algebraMap (MvPowerSeries (Fin 2) k) _ u}
  mul_mem' := by
    rintro x y ⟨u, v, hv, h⟩ ⟨u', v', hv', h'⟩
    refine ⟨u * u', v * v', not_X_dvd_mul _ hv hv', ?_⟩
    rw [map_mul, map_mul, ← h, ← h']; ring
  add_mem' := by
    rintro x y ⟨u, v, hv, h⟩ ⟨u', v', hv', h'⟩
    refine ⟨u * v' + u' * v, v * v', not_X_dvd_mul _ hv hv', ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_mul, ← h, ← h']; ring
  algebraMap_mem' := by
    intro r
    refine ⟨algebraMap k _ r, 1, not_X_dvd_one _, ?_⟩
    rw [map_one, mul_one, ← IsScalarTower.algebraMap_apply]

theorem isUnit_locSecondVar (k : Type) [Field k] (x : locSecondVar k) (u v : MvPowerSeries (Fin 2) k)
    (hu : ¬ MvPowerSeries.X 1 ∣ u)
    (h : (x : FractionRing (MvPowerSeries (Fin 2) k)) * algebraMap (MvPowerSeries (Fin 2) k) _ v
      = algebraMap (MvPowerSeries (Fin 2) k) _ u) : IsUnit x := by
  have hu0 : algebraMap (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k)) u
      ≠ 0 := by
    rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
    rintro rfl
    exact hu (dvd_zero _)
  have hx : (x : FractionRing (MvPowerSeries (Fin 2) k)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact hu0 h.symm
  refine IsUnit.of_mul_eq_one (⟨(x : FractionRing (MvPowerSeries (Fin 2) k))⁻¹, v, u, hu, ?_⟩ : locSecondVar k) ?_
  · rw [← h, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]
  · exact Subtype.ext (mul_inv_cancel₀ hx)

instance isLocalRing_locSecondVar (k : Type) [Field k] : IsLocalRing (locSecondVar k) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨u, v, hv, h⟩ := x.2
  by_cases hu : MvPowerSeries.X 1 ∣ u
  · right
    refine isUnit_locSecondVar k _ (v - u) v (fun h' => hv ?_) ?_
    · simpa using dvd_add h' hu
    · rw [map_sub, ← h]
      push_cast
      ring
  · exact Or.inl (isUnit_locSecondVar k x u v hu h)

theorem exists_local_ring_second_variable : ∀ (k : Type) [Field k] (σ₀ σ₁ : FractionRing (PowerSeries k) →ₐ[k] FractionRing (MvPowerSeries (Fin 2) k)), (∀ x : PowerSeries k, σ₀ (algebraMap _ _ x) = algebraMap (MvPowerSeries (Fin 2) k) _ (x.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k))) → (∀ x : PowerSeries k, σ₁ (algebraMap _ _ x) = algebraMap (MvPowerSeries (Fin 2) k) _ (x.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))) → ∃ L : Subalgebra k (FractionRing (MvPowerSeries (Fin 2) k)), IsLocalRing L ∧ (∀ (x : FractionRing (MvPowerSeries (Fin 2) k)) (u v : MvPowerSeries (Fin 2) k), ¬ MvPowerSeries.X 1 ∣ v → x * algebraMap (MvPowerSeries (Fin 2) k) _ v = algebraMap (MvPowerSeries (Fin 2) k) _ u → x ∈ L) ∧ (∀ x, σ₀ x ∈ L) ∧ ∀ x, σ₁ x ∈ L → x ∈ Set.range (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) := by
  intro k _ σ₀ σ₁ h₀ h₁
  refine ⟨locSecondVar k, inferInstance, fun x u v hv h => ⟨u, v, hv, h⟩, fun x => ?_, fun x hx => ?_⟩
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := PowerSeries k) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    refine ⟨a.subst (MvPowerSeries.X 0), b.subst (MvPowerSeries.X 0),
      not_X_one_dvd_subst k b hb0, ?_⟩
    rw [← h₀, ← h₀, ← map_mul, div_mul_cancel₀]
    rwa [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  · rcases ValuationRing.isInteger_or_isInteger (PowerSeries k) x with h | ⟨c, hc⟩
    · exact h
    · by_cases hx0 : x = 0
      · exact ⟨0, by rw [hx0, map_zero]⟩
      by_cases hcu : IsUnit c
      · obtain ⟨d, hd⟩ := hcu.exists_right_inv
        refine ⟨d, ?_⟩
        have : x⁻¹ * algebraMap (PowerSeries k) _ d = 1 := by
          rw [← hc, ← map_mul, hd, map_one]
        rw [← mul_one x, ← this, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
      · exfalso
        have hs : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) :=
          PowerSeries.HasSubst.X 1
        have hX : PowerSeries.X ∣ c := by
          rw [PowerSeries.X_dvd_iff]
          by_contra h0
          exact hcu (PowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit h0))
        obtain ⟨c', rfl⟩ := hX
        obtain ⟨u, v, hv, h⟩ := hx
        apply hv
        have h2 : v = (PowerSeries.X * c').subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) * u := by
          apply IsFractionRing.injective (MvPowerSeries (Fin 2) k)
            (FractionRing (MvPowerSeries (Fin 2) k))
          rw [map_mul, ← h₁, hc, ← h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hx0, map_one, one_mul]
        rw [h2, PowerSeries.subst_mul hs, PowerSeries.subst_X hs, mul_assoc]
        exact dvd_mul_right _ _

end GlobalTheory.TwoVarValRing
end

section

open KaehlerDifferential TensorProduct

namespace GlobalTheory.EtaleCoordJacobian

section tower
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B]

open KaehlerDifferential TensorProduct in
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B] in
theorem _root_.GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis (i : I) :
    mapBaseChange R (MvPolynomial I R) B (((mvPolynomialBasis R I).baseChange B) i) =
      D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i)) := by
  rw [Module.Basis.baseChange_apply, mvPolynomialBasis_apply, mapBaseChange_tmul, one_smul,
    map_D]

open KaehlerDifferential TensorProduct in
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B] in
theorem _root_.GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale [Finite I] [Algebra.Etale (MvPolynomial I R) B] :
    (∃ b : Module.Basis I B Ω[B⁄R],
      ∀ i, b i = D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i))) ∧
      Algebra.Smooth R B := by
  haveI : Algebra.Smooth R (MvPolynomial I R) := Algebra.Smooth.mk
  refine ⟨⟨((mvPolynomialBasis R I).baseChange B).map
    (tensorKaehlerEquivOfFormallyEtale R (MvPolynomial I R) B), fun i => ?_⟩,
    Algebra.Smooth.comp R (MvPolynomial I R) B⟩
  rw [Module.Basis.map_apply, ← _root_.GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis]
  rfl

open KaehlerDifferential TensorProduct in
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B] in
theorem _root_.GlobalTheory.EtaleCoordJacobian.etale_of_basis [Finite I] [Algebra.Smooth R B]
    (b : Module.Basis I B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i))) :
    Algebra.Etale (MvPolynomial I R) B := by
  set bc := (mvPolynomialBasis R I).baseChange B
  have hmap : mapBaseChange R (MvPolynomial I R) B = (bc.equiv b (Equiv.refl I)).toLinearMap :=
    bc.ext fun i => by
      rw [_root_.GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
        Equiv.refl_apply, hb]
  have hinj : Function.Injective (mapBaseChange R (MvPolynomial I R) B) := by
    rw [hmap]; exact (bc.equiv b (Equiv.refl I)).injective
  have hsurj : Function.Surjective (mapBaseChange R (MvPolynomial I R) B) := by
    rw [hmap]; exact (bc.equiv b (Equiv.refl I)).surjective
  have hΩ : Subsingleton Ω[B⁄MvPolynomial I R] := by
    refine ⟨fun x y => ?_⟩
    have hx : ∀ z : Ω[B⁄MvPolynomial I R], z = 0 := fun z => by
      obtain ⟨w, rfl⟩ := map_surjective R (MvPolynomial I R) B z
      obtain ⟨v, rfl⟩ := hsurj w
      exact (exact_mapBaseChange_map R (MvPolynomial I R) B).apply_apply_eq_zero v
    rw [hx x, hx y]
  have hH : Subsingleton (Algebra.H1Cotangent (MvPolynomial I R) B) := by
    haveI : Subsingleton (Algebra.H1Cotangent R B) :=
      Algebra.FormallySmooth.subsingleton_h1Cotangent
    refine ⟨fun x y => ?_⟩
    have hx : ∀ z : Algebra.H1Cotangent (MvPolynomial I R) B, z = 0 := fun z => by
      have h1 : Algebra.H1Cotangent.δ R (MvPolynomial I R) B z = 0 :=
        hinj (((Algebra.H1Cotangent.exact_δ_mapBaseChange R _ B).apply_apply_eq_zero z).trans
          (map_zero _).symm)
      obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R (MvPolynomial I R) B z).mp h1
      rw [Subsingleton.elim w 0, map_zero]
    rw [hx x, hx y]
  haveI : Algebra.FormallyEtale (MvPolynomial I R) B := Algebra.FormallyEtale.mk hΩ hH
  haveI : Algebra.FinitePresentation (MvPolynomial I R) B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ B
  exact Algebra.Etale.mk

end tower

open KaehlerDifferential TensorProduct in
private theorem exists_basis_D_and_smooth_of_etale_eval2Hom (R B I : Type) [CommRing R] [CommRing B]
    [Finite I] [Algebra R B] (t : I → B)
    (h : (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale) :
    (∃ b : Module.Basis I B Ω[B⁄R], ∀ i, b i = D R B (t i)) ∧ Algebra.Smooth R B := by
  letI : Algebra (MvPolynomial I R) B := (MvPolynomial.eval₂Hom (algebraMap R B) t).toAlgebra
  haveI : IsScalarTower R (MvPolynomial I R) B := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
  haveI : Algebra.Etale (MvPolynomial I R) B := h
  obtain ⟨⟨b, hb⟩, hs⟩ := _root_.GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale R B I
  exact ⟨⟨b, fun i => by rw [hb]; simp [RingHom.algebraMap_toAlgebra]⟩, hs⟩

open KaehlerDifferential TensorProduct in
private theorem det_derivation_eq_mul_det_repr {R B I : Type} [CommRing R] [CommRing B] [Fintype I]
    [DecidableEq I] [Algebra R B] (t t' : I → B) (b : Module.Basis I B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (t i)) (C : Type) [CommRing C] (φ : B →+* C) (d : I → B →+ C)
    (hd : ∀ i x y, d i (x * y) = φ x * d i y + φ y * d i x)
    (hc : ∀ i r, d i (algebraMap R B r) = 0) :
    (Matrix.of fun i j => d i (t' j)).det =
      φ (Matrix.of fun k j => b.repr (D R B (t' j)) k).det *
        (Matrix.of fun i j => d i (t j)).det := by
  letI : Algebra B C := φ.toAlgebra
  letI : Algebra R C := (φ.comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have key : ∀ i j, d i (t' j) = ∑ k, d i (t k) * φ (b.repr (D R B (t' j)) k) := by
    intro i j
    let δ : Derivation R B C := Derivation.mk'
      { toFun := d i
        map_add' := map_add (d i)
        map_smul' := fun r x => by
          rw [RingHom.id_apply, Algebra.smul_def r (d i x), Algebra.smul_def, hd, hc, mul_zero,
            add_zero]
          rfl }
      (fun x y => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, Algebra.smul_def]
        exact hd i x y)
    have h1 : ∀ x, d i x = δ.liftKaehlerDifferential (D R B x) := fun x => by
      rw [Derivation.liftKaehlerDifferential_comp_D]; rfl
    rw [h1]
    conv_lhs => rw [← b.sum_repr (D R B (t' j))]

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hb, ← h1, Algebra.smul_def, mul_comm]
    rfl
  have hmat : (Matrix.of fun i j => d i (t' j)) = (Matrix.of fun i j => d i (t j)) *
      (Matrix.of fun k j => b.repr (D R B (t' j)) k).map φ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, key]
  rw [hmat, Matrix.det_mul, mul_comm]
  congr 1
  exact (RingHom.map_det φ _).symm

open KaehlerDifferential TensorProduct in
private theorem exists_basis_D_of_isUnit_det_repr {R B I : Type} [CommRing R] [CommRing B]
    [Fintype I] [DecidableEq I] [Algebra R B] (t' : I → B) (b : Module.Basis I B Ω[B⁄R])
    (ha : IsUnit (Matrix.of fun k j => b.repr (D R B (t' j)) k).det) :
    ∃ b' : Module.Basis I B Ω[B⁄R], ∀ j, b' j = D R B (t' j) := by
  refine ⟨b.map (Matrix.toLinearEquiv b _ ha), fun j => ?_⟩
  rw [Module.Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  conv_rhs => rw [← b.sum_repr (D R B (t' j))]
  simp only [Matrix.of_apply]

open KaehlerDifferential TensorProduct in
private theorem etale_eval2Hom_of_basis_D (R B I : Type) [CommRing R] [CommRing B]
    [Finite I] [Algebra R B] [Algebra.Smooth R B] (t : I → B) (b : Module.Basis I B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (t i)) : (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale := by
  letI : Algebra (MvPolynomial I R) B := (MvPolynomial.eval₂Hom (algebraMap R B) t).toAlgebra
  haveI : IsScalarTower R (MvPolynomial I R) B := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
  exact _root_.GlobalTheory.EtaleCoordJacobian.etale_of_basis R B I b fun i => by
    rw [hb]; simp [RingHom.algebraMap_toAlgebra]


open KaehlerDifferential TensorProduct in
theorem _root_.GlobalTheory.EtaleCoordJacobian.chain_rule_and_jacobian_criterion : ∀ (R B : Type) [CommRing R] [CommRing B] (c : R →+* B) (I : Type) [Fintype I] [DecidableEq I] (t t' : I → B), (MvPolynomial.eval₂Hom c t).Etale → ∃ a : B, (∀ (C : Type) [CommRing C] (φ : B →+* C) (d : I → B →+ C), (∀ i x y, d i (x * y) = φ x * d i y + φ y * d i x) → (∀ i r, d i (c r) = 0) → (Matrix.of fun i j => d i (t' j)).det = φ a * (Matrix.of fun i j => d i (t j)).det) ∧ (IsUnit a → (MvPolynomial.eval₂Hom c t').Etale) := by
  intro R B _ _ c I _ _ t t' het
  letI : Algebra R B := c.toAlgebra
  obtain ⟨⟨b, hb⟩, hs⟩ := exists_basis_D_and_smooth_of_etale_eval2Hom R B I t het
  refine ⟨(Matrix.of fun k j => b.repr (D R B (t' j)) k).det,
    fun C _ φ d hd hc => det_derivation_eq_mul_det_repr t t' b hb C φ d hd hc, fun ha => ?_⟩
  obtain ⟨b', hb'⟩ := exists_basis_D_of_isUnit_det_repr t' b ha
  exact etale_eval2Hom_of_basis_D R B I t' b' hb'

end GlobalTheory.EtaleCoordJacobian
end
