module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderUnipotentAutDivisiblePrimaryEqId
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.RingTheory.Artinian.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle016
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Finite.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle013
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle017
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section


theorem _root_.GlobalTheory.T.exists_dualNumber_deformation_extend_away : ∀ {S S' : Type} [CommRing S] [CommRing S'] [Algebra S S'] (g : S) [IsLocalization.Away g S'] (d : S →+* DualNumber S), (∀ s, (d s).fst = s) → ∃ d' : S' →+* DualNumber S', (∀ s, (d' s).fst = s) ∧ ∀ s, (d' (algebraMap S S' s)).snd = algebraMap S S' (d s).snd := by
  first | exact @GlobalTheory.dualNumber_deformation_extends_away | exact GlobalTheory.dualNumber_deformation_extends_away | (intros; apply GlobalTheory.dualNumber_deformation_extends_away <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SchRing

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {a b : R →+* S} (h : spMap a = spMap b) : a = b := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem subsingleton_primeSpectrum_trivSqZeroExt (k : Type) [Field k] (M : Type) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M] :
    Subsingleton (PrimeSpectrum (TrivSqZeroExt k M)) := by
  have key : ∀ (P : PrimeSpectrum (TrivSqZeroExt k M)) (a : TrivSqZeroExt k M), a ∈ P.asIdeal ↔ a.fst = 0 := by
    intro P a
    constructor
    · intro ha
      by_contra h
      have hu : IsUnit a := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr h)
      exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
    · intro h
      have ha : a = TrivSqZeroExt.inr a.snd := TrivSqZeroExt.ext (by simp [h]) (by simp)
      apply P.isPrime.mem_of_pow_mem 2
      rw [ha, pow_two, TrivSqZeroExt.inr_mul_inr]
      exact P.asIdeal.zero_mem
  exact ⟨fun P Q => PrimeSpectrum.ext (Ideal.ext fun a => (key P a).trans (key Q a).symm)⟩

theorem range_subset_of_fst {X : Scheme.{0}} (k : Type) [Field k] (M : Type) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M]
    (x : Sp k ⟶ X) (u : Sp (TrivSqZeroExt k M) ⟶ X)
    (h : spMap (TrivSqZeroExt.fstHom k k M).toRingHom ≫ u = x) : Set.range u.base ⊆ Set.range x.base := by
  rintro _ ⟨y, rfl⟩
  haveI := subsingleton_primeSpectrum_trivSqZeroExt k M
  let z : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
  refine ⟨z, ?_⟩
  have hy : (spMap (TrivSqZeroExt.fstHom k k M).toRingHom).base z = y := Subsingleton.elim (α := PrimeSpectrum (TrivSqZeroExt k M)) _ _
  rw [← h, ← hy]
  rfl

theorem exists_ringHom_of_range {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (D : Type) [CommRing D]
    (g : Sp D ⟶ X) (hg : Set.range g.base ⊆ (V : Set X)) : ∃ r : Γ(X, V) →+* D, g = spMap r ≫ hV.fromSpec := by
  have h' : Set.range g ⊆ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hg
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec g h')).hom, ?_⟩
  have e1 : spMap (Spec.preimage (IsOpenImmersion.lift hV.fromSpec g h')).hom = IsOpenImmersion.lift hV.fromSpec g h' := by
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
  rw [e1, IsOpenImmersion.lift_fac]

theorem spMap_cancel {R D : Type} [CommRing R] [CommRing D] {Y : Scheme.{0}} (G : Sp R ⟶ Y) [Mono G]
    {a b : R →+* D} (h : spMap a ≫ G = spMap b ≫ G) : a = b :=
  spMap_inj (cancel_mono G |>.mp h)

end GlobalTheory.SchRing

namespace GlobalTheory.SchRing

theorem deformation_on_sections : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (U : (Sp B).Opens) (V : X.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U) (d : ℕ) (k : Type) [Field k] (x : Sp k ⟶ X),
    Set.range x.base ⊆ (V : Set X) → (∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) →
    ∃ (φ : Γ(X, V) →+* k) (ψ : Γ(X, V) →+* TrivSqZeroExt k (Fin d → k)),
      (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ ∧
      ψ.comp (s.appLE U V e).hom = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (s.appLE U V e).hom) ∧
      ∀ v : Γ(X, V) →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
        v.comp (s.appLE U V e).hom = (algebraMap k (DualNumber k)).comp (φ.comp (s.appLE U V e).hom) →
        ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ := by
  intro B _ X s U V hU hV e d k _ x hx hyp
  obtain ⟨u, hux, hus, huniq⟩ := hyp
  obtain ⟨φ, hφ⟩ := exists_ringHom_of_range hV k x hx
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_range hV _ u ((range_subset_of_fst k _ x u hux).trans hx)
  have key := IsAffineOpen.SpecMap_appLE_fromSpec s hU hV e
  have hs : ∀ (D : Type) [CommRing D] (r : Γ(X, V) →+* D),
      spMap r ≫ hV.fromSpec ≫ s = spMap (r.comp (s.appLE U V e).hom) ≫ hU.fromSpec := by
    intro D _ r
    rw [← key, spMap_comp']
    rfl
  have hbase : ∀ (D : Type) [CommRing D] (alg : k →+* D) (r : Γ(X, V) →+* D),
      (spMap r ≫ hV.fromSpec) ≫ s = spMap alg ≫ x ≫ s ↔
        r.comp (s.appLE U V e).hom = alg.comp (φ.comp (s.appLE U V e).hom) := by
    intro D _ alg r
    rw [hφ]
    simp only [Category.assoc]
    rw [hs, ← Category.assoc (spMap alg) (spMap φ), ← spMap_comp', hs]
    constructor
    · intro h; exact spMap_inj ((cancel_mono hU.fromSpec).mp h)
    · intro h; rw [h]
  have hfst : ∀ (D : Type) [CommRing D] (f : D →+* k) (r : Γ(X, V) →+* D),
      spMap f ≫ spMap r ≫ hV.fromSpec = x ↔ f.comp r = φ := by
    intro D _ f r
    rw [hφ, ← Category.assoc, ← spMap_comp']
    constructor
    · intro h; exact spMap_cancel hV.fromSpec h
    · intro h; rw [h]
  refine ⟨φ, ψ, ?_, ?_, ?_⟩
  · rw [hψ] at hux; exact (hfst _ _ _).mp hux
  · rw [hψ] at hus; exact (hbase _ _ _).mp hus
  · intro v hv1 hv2
    have h1 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (spMap v ≫ hV.fromSpec) = x := (hfst _ _ _).mpr hv1
    have h2 := (hbase _ _ _).mpr hv2
    obtain ⟨c, hc, hcu⟩ := huniq _ h1 h2
    refine ⟨c, ?_, ?_⟩
    · rw [hψ, ← Category.assoc, ← spMap_comp'] at hc
      exact spMap_cancel hV.fromSpec hc
    · intro c' hc'
      apply hcu
      rw [hψ, ← Category.assoc, ← spMap_comp', ← hc']

end GlobalTheory.SchRing
end
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.mem_polyring_of_integral_closure_range' : ∀ {K : Type} [Field K] {D : ℕ} (y : Fin D → K), AlgebraicIndependent ℤ y → ∀ (t : K), t ∈ Subfield.closure (Set.range y) → ∀ {ι : Type} (z : ι → K), (∀ i, ∃ p : MvPolynomial (Fin D) ℤ, aeval y p = z i) → ∀ (f : Polynomial (MvPolynomial ι ℤ)), f.Monic → f.eval₂ (aeval z).toRingHom t = 0 → ∃ T₀ : MvPolynomial (Fin D) ℤ, t = aeval y T₀ := by
  first | exact @GlobalTheory.mem_polyring_of_integral_closure_range | exact GlobalTheory.mem_polyring_of_integral_closure_range | (intros; apply GlobalTheory.mem_polyring_of_integral_closure_range <;> assumption)
end

section


theorem _root_.GlobalTheory.T.perm_invariant_of_cons_swap_and_tail : ∀ (α : Type 1) (n : ℕ) (F : (Fin (n + 2) → α) → ℝ), (∀ (a : α) (L : Fin (n + 1) → α) (e : Equiv.Perm (Fin (n + 1))), F (Fin.cons a fun i => L (e i)) = F (Fin.cons a L)) → (∀ (a b : α) (L : Fin n → α), F (Fin.cons a (Fin.cons b L : Fin (n + 1) → α)) = F (Fin.cons b (Fin.cons a L : Fin (n + 1) → α))) → ∀ (L : Fin (n + 2) → α) (e : Equiv.Perm (Fin (n + 2))), F (fun i => L (e i)) = F L := by
  first | exact @GlobalTheory.perm_invariant_of_cons_swap | exact GlobalTheory.perm_invariant_of_cons_swap | (intros; apply GlobalTheory.perm_invariant_of_cons_swap <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finiteOrder_unipotent_aut_divisible_primary_eq_id : ∀ (A : Type) [AddCommGroup A] (β : A →+ A) (n g r m : ℕ), 0 < n → (∀ x : A, β^[n] x = x) → g.Prime → r + 2 ≤ g → (∀ x : A, ∃ y : A, g • y = x) → (∀ x : A, ∃ j : ℕ, g ^ j • x = 0) → (∃ T : Finset A, T.card ≤ g ^ r ∧ ∀ x : A, g • x = 0 → x ∈ T) → (∀ x : A, g • x = 0 → (fun z => β z - z)^[m] x = 0) → ∀ x : A, β x = x := by
  first | exact @GlobalTheory.finite_order_unipotent_eq_id | exact GlobalTheory.finite_order_unipotent_eq_id | (intros; apply GlobalTheory.finite_order_unipotent_eq_id <;> assumption)
end

section

open Matrix Polynomial

theorem _root_.GlobalTheory.T.reduced_artinian_involution_idempotent_split : ∀ (R : Type) [CommRing R] [IsReduced R] [IsArtinianRing R] (σ : R →+* R), (∀ x, σ (σ x) = x) → ∃ e f : R, IsIdempotentElem e ∧ IsIdempotentElem f ∧ e * σ e = 0 ∧ e + σ e + f = 1 ∧ ∀ w, w * σ w = 0 → w * f = 0 := by
  first | exact @GlobalTheory.reducedArtinian_involution_split | exact GlobalTheory.reducedArtinian_involution_split | (intros; apply GlobalTheory.reducedArtinian_involution_split <;> assumption)
end

section

open Polynomial

namespace GlobalTheory

theorem binQuad_represents_unit_of_finite_reduced (S : Type) [CommRing S] [Finite S]
    [IsReduced S] (t m f : S) (hd : IsUnit (t ^ 2 - 4 * m)) (hf : IsUnit f) :
    ∃ a b : S, a ^ 2 + t * a * b + m * b ^ 2 = f := by
  first
  | exact @_root_.GlobalTheory.FieldCaseReduction.main
  | exact _root_.GlobalTheory.FieldCaseReduction.main
  | (apply _root_.GlobalTheory.FieldCaseReduction.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FieldCaseReduction.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FieldCaseReduction.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FieldCaseReduction.main ..)

theorem norm_surj_of_finite_reduced_involution : ∀ (R : Type) [CommRing R] [Finite R]
    [IsReduced R] (τ : R →+* R), (∀ x, τ (τ x) = x) → ∀ θ : R, IsUnit (θ - τ θ) →
    ∀ f : R, IsUnit f → τ f = f → ∃ c : R, τ c * c = f := by
  intro R _ _ _ τ hτ θ hθ f hf hτf
  classical
  let A : Subring R := τ.eqLocus (RingHom.id R)
  have memA : ∀ x, τ x = x → x ∈ A := fun x hx => show τ x = RingHom.id R x from hx
  have fixA : ∀ x : A, τ (x : R) = x := fun x => x.2
  obtain ⟨u, hu⟩ := hθ
  have h4 : ((4 : A) : R) = 4 := map_ofNat A.subtype 4
  have hτd : τ (θ - τ θ) = -(θ - τ θ) := by rw [map_sub, hτ]; ring
  have hτdi : τ (↑u⁻¹ : R) = -↑u⁻¹ := by
    have h1 : τ (↑u⁻¹ : R) * (θ - τ θ) = -1 := by
      have := congrArg τ u.inv_mul
      rw [map_mul, map_one, hu, hτd] at this
      linear_combination -this
    calc τ (↑u⁻¹ : R) = τ ↑u⁻¹ * ((θ - τ θ) * ↑u⁻¹) := by rw [← hu, u.mul_inv, mul_one]
      _ = -↑u⁻¹ := by rw [← mul_assoc, h1]; ring
  obtain ⟨v, hv⟩ := hf
  have hτfi : τ (↑v⁻¹ : R) = ↑v⁻¹ := by
    have h1 : τ (↑v⁻¹ : R) * f = 1 := by
      rw [← hτf, ← map_mul, ← hv, v.inv_mul, map_one]
    calc τ (↑v⁻¹ : R) = τ ↑v⁻¹ * (f * ↑v⁻¹) := by rw [← hv, v.mul_inv, mul_one]
      _ = ↑v⁻¹ := by rw [← mul_assoc, h1, one_mul]
  let tA : A := ⟨θ + τ θ, memA _ (by rw [map_add (f := _), hτ, add_comm])⟩
  let mA : A := ⟨θ * τ θ, memA _ (by rw [map_mul, hτ, mul_comm])⟩
  let fA : A := ⟨f, memA _ hτf⟩
  let wA : A := ⟨↑u⁻¹ * ↑u⁻¹, memA _ (by rw [map_mul, hτdi]; ring)⟩
  let vA : A := ⟨↑v⁻¹, memA _ hτfi⟩
  have hdisc : IsUnit (tA ^ 2 - 4 * mA) := by
    suffices h : (tA ^ 2 - 4 * mA) * wA = 1 from ⟨⟨_, wA, h, by rw [mul_comm]; exact h⟩, rfl⟩
    refine Subtype.ext ?_
    have e1 : (θ + τ θ) ^ 2 - 4 * (θ * τ θ) = ↑u * ↑u := by rw [hu]; ring
    push_cast [tA, mA, wA]
    rw [h4, e1, show (↑u : R) * ↑u * (↑u⁻¹ * ↑u⁻¹) = (↑u * ↑u⁻¹) * (↑u * ↑u⁻¹) by ring, u.mul_inv,
      one_mul]
  have hfA : IsUnit fA := by
    suffices h : fA * vA = 1 from ⟨⟨_, vA, h, by rw [mul_comm]; exact h⟩, rfl⟩
    refine Subtype.ext ?_
    push_cast [fA, vA]
    rw [← hv, v.mul_inv]
  haveI : IsReduced A := ⟨fun x hx => Subtype.ext (IsNilpotent.eq_zero (hx.map A.subtype))⟩
  obtain ⟨a, b, hab⟩ := binQuad_represents_unit_of_finite_reduced A tA mA fA hdisc hfA
  have hab' := congrArg Subtype.val hab
  push_cast [tA, mA, fA] at hab'
  refine ⟨(a : R) + θ * b, ?_⟩
  rw [map_add (f := _), map_mul, fixA a, fixA b]
  linear_combination hab'

end GlobalTheory
end

section

open NumberField IsDedekindDomain
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_localBasis_at_prime_of_isLattice : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsFullLattice E → ∃ X : Matrix (Fin n) (Fin n) E, IsUnit X.det ∧ (∀ j, (fun i => X i j) ∈ L) ∧ ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1 := by
  exact @GlobalTheory.exists_local_basis_of_isLattice
end

section

universe u

theorem _root_.GlobalTheory.T.exists_coords_range_idempotent_of_retract : ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C), I ≠ ⊤ →
  ∀ {W : Type u} [AddCommGroup W] [Module C W] (m : ℕ) (s : W →ₗ[C] (Fin m → C ⧸ I))
  (r : (Fin m → C ⧸ I) →ₗ[C] W), r ∘ₗ s = LinearMap.id →
  ∀ (p : Module.End C W), p * p = p →
  ∃ (n : ℕ) (b : Fin n → W) (f : Fin n → W →ₗ[C] C ⧸ I),
    (∀ k, b k ∈ LinearMap.range p) ∧ (∀ k w, f k (p w) = f k w) ∧
    (∀ j k, f j (b k) = if j = k then 1 else 0) ∧
    (∀ w ∈ LinearMap.range p, (∀ k, f k w = 0) → w = 0) := by
  first | exact @GlobalTheory.idem_retract_coords | exact GlobalTheory.idem_retract_coords | (intros; apply GlobalTheory.idem_retract_coords <;> assumption)
end

section

open scoped TensorProduct
universe u

theorem _root_.GlobalTheory.T.finrank_quot_one_sub_idempotent_eq_mul : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (φ : A →ₐ[k] k) (e : A), IsIdempotentElem e → φ e = 1 → (∀ a, φ a = 0 → IsNilpotent (e * a)) → ∀ (H : Type u) [AddCommGroup H] [Module A H] [Module k H] [IsScalarTower k A H] [FiniteDimensional k H] [Module.Projective A H], Module.finrank k (H ⧸ (Ideal.span {1 - e} • ⊤ : Submodule A H)) = Module.finrank k (H ⧸ (RingHom.ker φ • ⊤ : Submodule A H)) * Module.finrank k (A ⧸ Ideal.span {1 - e}) := by
  first | (exact @GlobalTheory.finrank_quot_one_sub_idem_eq_mul) | (exact GlobalTheory.finrank_quot_one_sub_idem_eq_mul) | (intros; apply GlobalTheory.finrank_quot_one_sub_idem_eq_mul  <;> assumption)
end

section

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.exists_presentation_matrix_of_projective_baseChange : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M), Function.Surjective π →
    ∀ (r : Fin m → Fin n → R), Submodule.span R (Set.range r) = LinearMap.ker π →
    Module.Projective B (B ⊗[R] M) →
    ∃ (v : Fin n → Fin n → B) (w : Fin n → Fin m → B),
    (∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0) ∧
    (∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) := by
  first | (exact @GlobalTheory.projective_baseChange_presentation_matrix) | (exact GlobalTheory.projective_baseChange_presentation_matrix) | (intros; apply GlobalTheory.projective_baseChange_presentation_matrix <;> assumption)
end

section

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.projective_baseChange_of_presentation_matrix_split : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M), Function.Surjective π →
    ∀ (r : Fin m → Fin n → R), Submodule.span R (Set.range r) = LinearMap.ker π →
    ∀ (v : Fin n → Fin n → B) (w : Fin n → Fin m → B),
    (∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0) →
    (∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) →
    Module.Projective B (B ⊗[R] M) := by
  first | (exact @GlobalTheory.projective_baseChange_of_presentation_split) | (exact GlobalTheory.projective_baseChange_of_presentation_split) | (intros; apply GlobalTheory.projective_baseChange_of_presentation_split <;> assumption)
end
