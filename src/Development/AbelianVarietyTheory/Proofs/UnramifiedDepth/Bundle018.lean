module

public import ReciprocityTheory.DualLattices.Bundle002
public import ReciprocityTheory.DualLattices.Bundle012
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.DualLattices.Bundle014
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.DualLattices.Bundle007
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

@[expose] public section

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section GroupIdentities
variable {M : Type} [CommGroup M]

private lemma mul_rearrange_five {u u' u'' a b c d : M} (h : b * a = d * c) :
    u * u' * a * u'' * b = u * (u' * u'' * c) * d := by
  calc _ = u * u' * u'' * (b * a) := by ac_rfl
    _ = u * u' * u'' * (d * c) := by rw [h]
    _ = _ := by ac_rfl

private lemma fs_zero {u a b : M} (h : b * a = b * b) : a⁻¹ * u * b = u := by
  rw [← mul_left_cancel h, mul_right_comm, inv_mul_cancel, _root_.one_mul]

private lemma fs_inter {u u' w w' a b c d e f : M} (h : a * b * c = d * e * f) :
    u * u' * e * (w * w' * f) * d = u * w * b * (u' * w' * c) * a := by
  calc _ = u * u' * w * w' * (d * e * f) := by ac_rfl
    _ = u * u' * w * w' * (a * b * c) := by rw [h]
    _ = _ := by ac_rfl

private lemma fs_nat {u u' a b c d e : M} (h : a * b = c * d * e) :
    u * u' * a * b = u * c * (u' * d) * e := by
  calc _ = u * u' * (a * b) := by ac_rfl
    _ = u * u' * (c * d * e) := by rw [h]
    _ = _ := by ac_rfl

private lemma fs_zero_nat {a b c : M} (h : a * b = b * b * c) : a⁻¹ * b = c⁻¹ := by
  have h' : a = b * c := by
    apply mul_right_cancel (b := b)
    rw [h]; ac_rfl
  rw [h', mul_inv, mul_right_comm, inv_mul_cancel, _root_.one_mul]

end GroupIdentities

private lemma fs_sigma_eq {A U : Type} {x x' y y' : A} {u u' : U} :
    (⟨x, y, u⟩ : Σ _ : A, Σ _ : A, U) = ⟨x', y', u'⟩ ↔ x = x' ∧ y = y' ∧ u = u' := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private lemma fs_units_fibre {R₀ : Type} [CommRing R₀] {F R₁ R₂ R : LAlg R₀} {p₁ : LHom F R₁}
    {p₂ : LHom F R₂} {f₁ : LHom R₁ R} {f₂ : LHom R₂ R} (h : IsFibreSq p₁ p₂ f₁ f₂)
    (a : (R₁ : Type)ˣ) (b : (R₂ : Type)ˣ)
    (hab : Units.map (f₁.1 : (R₁ : Type) →* (R : Type)) a =
      Units.map (f₂.1 : (R₂ : Type) →* (R : Type)) b) :
    ∃! c : (F : Type)ˣ, Units.map (p₁.1 : (F : Type) →* (R₁ : Type)) c = a ∧
      Units.map (p₂.1 : (F : Type) →* (R₂ : Type)) c = b := by
  obtain ⟨c, ⟨h1, h2⟩, hu⟩ := h.2.2.2 (a : R₁.carrier) (b : R₂.carrier) (congrArg Units.val hab)
  have hc : IsUnit c := p₁.2.map_nonunit c (by
    have : (p₁.1 : F.carrier →+* R₁.carrier) c = a := h1
    rw [this]; exact a.isUnit)
  refine ⟨hc.unit, ⟨Units.ext h1, Units.ext h2⟩, ?_⟩
  rintro c' ⟨e1, e2⟩
  exact Units.ext (hu c' ⟨congrArg Units.val e1, congrArg Units.val e2⟩)

theorem exists_BX_of_factorSystems :
  (∀ {R₀ : Type} [CommRing R₀] (B₀ : BX R₀) (δ : ∀ {R S : LAlg R₀}, LHom R S → B₀.G R → B₀.G R → (S : Type)ˣ)
    (t₁ t₂ : ∀ R : LAlg R₀, B₀.G R → B₀.G R → B₀.G R → (R : Type)ˣ) (w : ∀ R : LAlg R₀, B₀.G R → B₀.G R → (R : Type)ˣ),
    (∀ R x y, δ (LHom.id R) x y = 1) →
    (∀ {Q R S : LAlg R₀} (f : LHom Q R) (h : LHom R S) x y, δ (h.comp f) x y = Units.map (h.1 : (R : Type) →* (S : Type)) (δ f x y) * δ h (B₀.map f x) (B₀.map f y)) →
    (∀ R x x' x'' y, t₁ R (x + x') x'' y * t₁ R x x' y = t₁ R x (x' + x'') y * t₁ R x' x'' y) → (∀ R x x' y, t₁ R x x' y = t₁ R x' x y) →
    (∀ R x y y' y'', t₂ R x (y + y') y'' * t₂ R x y y' = t₂ R x y (y' + y'') * t₂ R x y' y'') → (∀ R x y y', t₂ R x y y' = t₂ R x y' y) →
    (∀ R x x' y y', t₁ R x x' (y + y') * t₂ R x y y' * t₂ R x' y y' = t₂ R (x + x') y y' * t₁ R x x' y * t₁ R x x' y') →
    (∀ {R S : LAlg R₀} (f : LHom R S) x x' y, Units.map (f.1 : (R : Type) →* (S : Type)) (t₁ R x x' y) * δ f (x + x') y =
      δ f x y * δ f x' y * t₁ S (B₀.map f x) (B₀.map f x') (B₀.map f y)) →
    (∀ {R S : LAlg R₀} (f : LHom R S) x y y', Units.map (f.1 : (R : Type) →* (S : Type)) (t₂ R x y y') * δ f x (y + y') =
      δ f x y * δ f x y' * t₂ S (B₀.map f x) (B₀.map f y) (B₀.map f y')) →
    (∀ R x y, w R x y * w R y x = 1) → (∀ R x x' y, t₁ R x x' y * w R (x + x') y = w R x y * w R x' y * t₂ R y x x') →
    (∀ {R S : LAlg R₀} (f : LHom R S) x y, Units.map (f.1 : (R : Type) →* (S : Type)) (w R x y) * δ f y x = δ f x y * w S (B₀.map f x) (B₀.map f y)) →
    ∃ (B : BX R₀) (κ : ∀ R, B.G R ≃+ B₀.G R) (b : ∀ R x y, B.P R x y),
      (∀ {R S : LAlg R₀} (f : LHom R S) x, κ S (B.map f x) = B₀.map f (κ R x)) ∧
      (∀ R x x' y, B.add1 (b R x y) (b R x' y) = B.smul (t₁ R (κ R x) (κ R x') (κ R y)) (b R (x + x') y)) ∧
      (∀ R x y y', B.add2 (b R x y) (b R x y') = B.smul (t₂ R (κ R x) (κ R y) (κ R y')) (b R x (y + y'))) ∧
      (∀ {R S : LAlg R₀} (f : LHom R S) x y, B.pmap f (b R x y) = B.smul (δ f (κ R x) (κ R y)) (b S (B.map f x) (B.map f y)))) := by
  intro R₀ _ B₀ δ t₁ t₂ w hid hcomp h1a h1c h2a h2c hint h1n h2n hww hw1 hwn
  let B : BX R₀ :=
    { B₀ with
      P := fun R _ _ => (R : Type)ˣ
      smul := fun l u => l * u
      one_smul := fun u => _root_.one_mul u
      mul_smul := fun l l' u => _root_.mul_assoc l l' u
      nonempty := fun _ _ _ => ⟨1⟩
      trans := fun u v => ⟨v * u⁻¹, by simp, fun l hl => by rw [← hl]; simp⟩
      pmap := fun {R S} f {x y} u => Units.map (f.1 : (R : Type) →* (S : Type)) u * δ f x y
      pmap_smul := fun f _ _ l u => by rw [map_mul, _root_.mul_assoc]
      pmap_id := fun {R x y} u => heq_of_eq (by rw [hid, _root_.mul_one]; rfl)
      pmap_comp := fun f g _ _ u => heq_of_eq (by rw [hcomp, map_mul, ← _root_.mul_assoc]; rfl)
      add1 := fun {R x x' y} u u' => u * u' * t₁ R x x' y
      add2 := fun {R x y y'} u u' => u * u' * t₂ R x y y'
      zero1 := fun {R} y => (t₁ R 0 0 y)⁻¹
      zero2 := fun {R} x => (t₂ R x 0 0)⁻¹
      addFst_assoc := fun u u' u'' => heq_of_eq (mul_rearrange_five (h1a _ _ _ _ _))
      addSnd_assoc := fun u u' u'' => heq_of_eq (mul_rearrange_five (h2a _ _ _ _ _))
      addFst_comm := fun u u' => heq_of_eq (by rw [h1c, _root_.mul_comm u])
      addSnd_comm := fun u u' => heq_of_eq (by rw [h2c, _root_.mul_comm u])
      zeroFst_add := fun {R x y} u => heq_of_eq (fs_zero (by
        simpa only [add_zero, zero_add] using h1a R 0 0 x y))
      zeroSnd_add := fun {R x y} u => heq_of_eq (fs_zero (by
        simpa only [add_zero, zero_add] using h2a R x 0 0 y))
      addFst_smul := fun l l' u u' => by ac_rfl
      addSnd_smul := fun l l' u u' => by ac_rfl
      interchange := fun u u' v v' => fs_inter (hint _ _ _ _ _)
      addFst_nat := fun f _ _ _ u u' => heq_of_eq (by
        rw [map_mul, map_mul]; exact fs_nat (h1n _ _ _ _))
      addSnd_nat := fun f _ _ _ u u' => heq_of_eq (by
        rw [map_mul, map_mul]; exact fs_nat (h2n _ _ _ _))
      zeroFst_nat := fun f y => heq_of_eq (by
        rw [map_inv]
        exact fs_zero_nat (by simpa only [add_zero, map_zero] using h1n f 0 0 y))
      zeroSnd_nat := fun f x => heq_of_eq (by
        rw [map_inv]
        exact fs_zero_nat (by simpa only [add_zero, map_zero] using h2n f x 0 0))
      sw := fun {R x y} u => u * w R x y
      sw_smul := fun l u => _root_.mul_assoc _ _ _
      sw_nat := fun f _ _ u => by rw [map_mul, _root_.mul_assoc, _root_.mul_assoc, hwn]
      swap_addFst := fun u u' => fs_nat (hw1 _ _ _ _)
      sw_sw := fun u => by rw [_root_.mul_assoc, hww, _root_.mul_one]
      fibre_P := by
        intro F R₁ R₂ R p₁ p₂ f₁ f₂ h
        rintro ⟨x₁, y₁, u₁⟩ ⟨x₂, y₂, u₂⟩ e
        obtain ⟨ex, ey, eu⟩ := fs_sigma_eq.1 e
        obtain ⟨x, ⟨rfl, rfl⟩, hx⟩ := B₀.fibre_G p₁ p₂ f₁ f₂ h x₁ x₂ ex
        obtain ⟨y, ⟨rfl, rfl⟩, hy⟩ := B₀.fibre_G p₁ p₂ f₁ f₂ h y₁ y₂ ey
        have hsq : f₁.comp p₁ = f₂.comp p₂ := Subtype.ext h.1
        have hδ := (hcomp p₁ f₁ x y).symm.trans (hsq ▸ hcomp p₂ f₂ x y)
        obtain ⟨u, ⟨hu1, hu2⟩, hu⟩ := fs_units_fibre h (u₁ / δ p₁ x y) (u₂ / δ p₂ x y) (by
          rw [map_div, map_div, div_eq_div_iff_mul_eq_mul]
          apply mul_right_cancel (b := δ f₁ (B₀.map p₁ x) (B₀.map p₁ y) *
            δ f₂ (B₀.map p₂ x) (B₀.map p₂ y))
          dsimp only at eu
          calc _ = (Units.map (f₁.1 : (R₁ : Type) →* (R : Type)) u₁ *
                δ f₁ (B₀.map p₁ x) (B₀.map p₁ y)) *
                (Units.map (f₂.1 : (R₂ : Type) →* (R : Type)) (δ p₂ x y) *
                δ f₂ (B₀.map p₂ x) (B₀.map p₂ y)) := by ac_rfl
            _ = _ := by rw [eu, ← hδ]; ac_rfl)
        refine ⟨⟨x, y, u⟩, ⟨fs_sigma_eq.2 ⟨rfl, rfl, ?_⟩, fs_sigma_eq.2 ⟨rfl, rfl, ?_⟩⟩, ?_⟩
        · dsimp only
          rw [hu1, div_mul_cancel]
        · dsimp only
          rw [hu2, div_mul_cancel]
        · rintro ⟨x', y', u'⟩ ⟨e1, e2⟩
          obtain ⟨a1, b1, c1⟩ := fs_sigma_eq.1 e1
          obtain ⟨a2, b2, c2⟩ := fs_sigma_eq.1 e2
          obtain rfl := hx x' ⟨a1, a2⟩
          obtain rfl := hy y' ⟨b1, b2⟩
          exact fs_sigma_eq.2 ⟨rfl, rfl, hu u' ⟨eq_div_iff_mul_eq'.2 c1, eq_div_iff_mul_eq'.2 c2⟩⟩ }
  refine ⟨B, fun R => AddEquiv.refl _, fun R _ _ => (1 : (R : Type)ˣ), fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro R x x' y
    exact show (1 : (R : Type)ˣ) * 1 * t₁ R x x' y = t₁ R x x' y * 1 by simp
  · intro R x y y'
    exact show (1 : (R : Type)ˣ) * 1 * t₂ R x y y' = t₂ R x y y' * 1 by simp
  · intro R S f x y
    exact show Units.map (f.1 : (R : Type) →* (S : Type)) 1 * δ f x y = δ f x y * 1 by simp

end GlobalTheory
end

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

variable {R₀ : Type} [CommRing R₀]

private lemma endDiff_exists_lift {O R : LAlg R₀} (s : LHom O R) (i : (R : Type)) (hi : i * i = 0) :
    ∃ φ : LHom (DualNum.dualPair O).D R, φ.comp (DualNum.dualPair O).σ = s ∧
      φ.1 (DualNum.dualPair O).η = i := by
  let ψ : DualNum.DN O →ₐ[R₀] (R : Type) :=
    Ideal.Quotient.liftₐ _ (Polynomial.aevalTower s.1 i) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp [pow_two, hi])
  have hσ : ∀ r, ψ ((DualNum.dualPair O).σ.1 r) = s.1 r := fun r => by
    change ψ (algebraMap (O : Type) (DualNum.DN O) r) = _
    rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply]
    exact Polynomial.aevalTower_C s.1 i r
  have hη : ψ (DualNum.dualPair O).η = i := by
    change ψ (Ideal.Quotient.mk _ Polynomial.X) = _
    exact Polynomial.aevalTower_X s.1 i
  refine ⟨⟨ψ, ⟨fun d hd => ?_⟩⟩, ?_, hη⟩
  · have hk : d - (DualNum.dualPair O).σ.1 ((DualNum.dualPair O).π.1 d) ∈
        RingHom.ker (DualNum.dualPair O).π.1 := by
      rw [RingHom.mem_ker, map_sub, (DualNum.dualPair O).sect, sub_self]
    rw [(DualNum.dualPair O).ker_eq] at hk
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hk
    have h1 : ψ y * i = ψ d - s.1 ((DualNum.dualPair O).π.1 d) := by
      rw [← hσ, ← hη]
      exact (map_mul ψ _ _).symm.trans ((congrArg ψ hy).trans (map_sub ψ _ _))
    have hn : IsNilpotent (-(ψ y * i)) := ⟨2, by
      rw [show (-(ψ y * i)) ^ 2 = ψ y * ψ y * (i * i) by ring, hi, mul_zero]⟩
    have hu : IsUnit (s.1 ((DualNum.dualPair O).π.1 d)) := by
      have h2 := hn.isUnit_add_left_of_commute (u := ψ d) hd (Commute.all _ _)
      rw [h1] at h2
      simpa using h2
    exact (DualNum.dualPair O).π.2.map_nonunit d (s.2.map_nonunit _ hu)
  · exact Subtype.ext (AlgHom.ext hσ)

private lemma endDiff_ηmap_surj {O : LAlg R₀} (Dp : DualPair O) :
    Function.Surjective Dp.ηmap := by
  rintro ⟨x, hx⟩
  have hx' := hx
  rw [Submodule.restrictScalars_mem, Dp.ker_eq] at hx'
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
  have hk : y - Dp.σ.1 (Dp.π.1 y) ∈ RingHom.ker Dp.π.1 := by
    rw [RingHom.mem_ker, map_sub, Dp.sect, sub_self]
  rw [Dp.ker_eq] at hk
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hk
  refine ⟨Dp.π.1 y, Subtype.ext ?_⟩
  change Dp.σ.1 (Dp.π.1 y) * Dp.η = y * Dp.η
  have := Dp.η_sq
  linear_combination (-Dp.η) * (-hz) - z * this

private lemma endDiff_ηmap_inj {O : LAlg R₀} (Dp : DualPair O) :
    Function.Injective Dp.ηmap := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  exact Dp.free r (congrArg Subtype.val hr)

private lemma endDiff_coord {g : ℕ} {V M : Type} [AddCommGroup V] [Module R₀ V] [AddCommGroup M]
    [Module R₀ M] (gb : Module.Basis (Fin g) R₀ V) :
    Function.Bijective (fun m : Fin g → M => ∑ k, gb k ⊗ₜ[R₀] m k) := by
  have : (fun m : Fin g → M => ∑ k, gb k ⊗ₜ[R₀] m k) =
      (TensorProduct.equivFinsuppOfBasisLeft gb).symm ∘ Finsupp.equivFunOnFinite.symm := by
    funext m
    simp [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype]
  rw [this]
  exact (TensorProduct.equivFinsuppOfBasisLeft gb).symm.bijective.comp
    Finsupp.equivFunOnFinite.symm.bijective

private def endDiff_IsMat {g : ℕ} {B : BX R₀} {O : LAlg R₀} (gb : Module.Basis (Fin g) R₀ B.gg)
    (e : OEnd B O) (d : Matrix (Fin g) (Fin g) (O : Type)) : Prop :=
  ∀ {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker)
    (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (d k l) * i) →
      e.f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)

private lemma endDiff_exists {g : ℕ} {B : BX R₀} {O : LAlg R₀} (gb : Module.Basis (Fin g) R₀ B.gg)
    (e : OEnd B O) : ∃ d, endDiff_IsMat gb e d := by
  let Dp := DualNum.dualPair O
  have h1 : ∀ l, ∃ c : Fin g → (O : Type), e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηk)) =
      B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (c k)) := fun l => by
    have h0 : B.map Dp.π (e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηk))) = 0 := by
      rw [← e.nat, (B.tg_ker Dp.π Dp.sqZero _).2 ⟨_, rfl⟩, map_zero]
    obtain ⟨v, hv⟩ := (B.tg_ker Dp.π Dp.sqZero _).1 h0
    obtain ⟨m, rfl⟩ := (endDiff_coord (M := Dp.π.ker) gb).2 v
    choose c hc using fun k => endDiff_ηmap_surj Dp (m k)
    exact ⟨c, by rw [← hv]; simp only [hc]⟩
  choose c hc using h1
  refine ⟨fun k l => c l k, ?_⟩
  intro R S s π hπ l i m hm
  have hi : (i : (R : Type)) * i = 0 := by
    have : (i : (R : Type)) * i ∈ RingHom.ker π.1 ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul i.2 i.2
    rw [hπ.2] at this
    simpa using this
  obtain ⟨φ, hφ, hη⟩ := endDiff_exists_lift s (i : (R : Type)) hi
  have hs : ∀ r, φ.1 (Dp.σ.1 r) = s.1 r := fun r => by rw [← hφ]; rfl
  have hf : ∀ a ∈ Dp.π.ker, φ.1.toLinearMap a ∈ π.ker := fun a ha => by
    obtain ⟨r, hr⟩ := endDiff_ηmap_surj Dp ⟨a, ha⟩
    have : a = Dp.σ.1 r * Dp.η := (congrArg Subtype.val hr).symm
    rw [this]
    change φ.1 (Dp.σ.1 r * Dp.η) ∈ RingHom.ker π.1
    rw [map_mul, hη]
    exact Ideal.mul_mem_left _ _ i.2
  have hA : gb l ⊗ₜ[R₀] i = LinearMap.lTensor B.gg (φ.1.toLinearMap.restrict hf)
      (gb l ⊗ₜ[R₀] Dp.ηk) := by
    rw [LinearMap.lTensor_tmul]
    congr 1
    exact Subtype.ext hη.symm
  have hB : ∑ k, gb k ⊗ₜ[R₀] m k = LinearMap.lTensor B.gg (φ.1.toLinearMap.restrict hf)
      (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (c l k)) := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.lTensor_tmul]
    congr 1
    refine Subtype.ext ?_
    change _ = φ.1 (Dp.σ.1 (c l k) * Dp.η)
    rw [hm k, map_mul, hη, hs]
  rw [hA, hB, B.tg_nat Dp.π π Dp.sqZero hπ φ hf, B.tg_nat Dp.π π Dp.sqZero hπ φ hf, ← hc l,
    ← e.nat, hφ]

private lemma endDiff_spec {g : ℕ} {B : BX R₀} {O : LAlg R₀} {gb : Module.Basis (Fin g) R₀ B.gg}
    {e : OEnd B O} {d : Matrix (Fin g) (Fin g) (O : Type)} (h : endDiff_IsMat gb e d)
    (Dp : DualPair O) (l : Fin g) (r : (O : Type)) :
    e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηmap r)) =
      B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (d k l * r)) :=
  h Dp.σ Dp.π Dp.sqZero l _ _ fun k => by
    change Dp.σ.1 (d k l * r) * Dp.η = Dp.σ.1 (d k l) * (Dp.σ.1 r * Dp.η)
    rw [map_mul, _root_.mul_assoc]

private lemma endDiff_unique {g : ℕ} {B : BX R₀} {O : LAlg R₀} {gb : Module.Basis (Fin g) R₀ B.gg}
    {e : OEnd B O} {d : Matrix (Fin g) (Fin g) (O : Type)} (h : endDiff_IsMat gb e d)
    (Dp : DualPair O) (d' : Matrix (Fin g) (Fin g) (O : Type))
    (h' : ∀ l, e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηmap 1)) =
      B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (d' k l))) : d = d' := by
  ext k l
  have h1 := B.tg_inj _ _ ((endDiff_spec h Dp l 1).symm.trans (h' l))
  have h2 := (endDiff_coord (M := Dp.π.ker) gb).1 h1
  simpa using endDiff_ηmap_inj Dp (congrFun h2 k)

theorem exists_endDifferential_ringHom :
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} (B : BX R₀) (O : LAlg R₀) (gb : Module.Basis (Fin g) R₀ B.gg) (O₀ : Type) [CommRing O₀] (f : O₀ → OEnd B O),
    (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R), (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) →
    ∃ dL : O₀ →+* Matrix (Fin g) (Fin g) (O : Type), (∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (dL a k l) * i) →
      (f a).f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k))) := by
  intro R₀ _ g B O gb O₀ _ f hf
  choose d hd using fun a => endDiff_exists gb (f a)
  let Dp := DualNum.dualPair O
  have hadd : ∀ a b, d (a + b) = d a + d b := fun a b =>
    endDiff_unique (hd _) Dp _ fun l => by
      rw [((hf _ _).2 a b).1, endDiff_spec (hd a), endDiff_spec (hd b), ← map_add (f := _),
        ← Finset.sum_add_distrib]
      simp [TensorProduct.tmul_add]
  have hone : d 1 = 1 :=
    endDiff_unique (hd _) Dp _ fun l => by
      rw [(hf _ _).1, Finset.sum_eq_single l]
      · simp
      · intro k _ hk
        simp [Matrix.one_apply_ne hk]
      · simp
  have hmul : ∀ a b, d (a * b) = d a * d b := fun a b =>
    endDiff_unique (hd _) Dp _ fun l => by

      rw [((hf _ _).2 a b).2, endDiff_spec (hd b), map_sum, map_sum]
      simp only [endDiff_spec (hd a)]

      rw [← map_sum, Finset.sum_comm]
      simp [Matrix.mul_apply, TensorProduct.tmul_sum]
  have hzero : d 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  exact ⟨⟨⟨⟨d, hone⟩, hmul⟩, hzero, hadd⟩, fun a => hd a⟩

end GlobalTheory
end
end
