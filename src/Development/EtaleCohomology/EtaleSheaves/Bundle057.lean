module

public import Development.EtaleCohomology.EtaleSheaves.Bundle046
public import Development.EtaleCohomology.EtaleSheaves.Bundle047
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafNormalModelPf

def intCl (Ω : Type) {L : Type} [Field Ω] [Field L] [Algebra Ω L] (u : L) : Subalgebra Ω L :=
  (integralClosure (Algebra.adjoin Ω {u}) L).restrictScalars Ω

theorem intCl_subset {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L} (V : ValuationSubring L)
    (hΩ : ∀ a : Ω, algebraMap Ω L a ∈ V) (hu : u ∈ V) : (intCl Ω u : Set L) ⊆ V := by
  intro x hx
  let V' : Subalgebra Ω L := { V.toSubring with algebraMap_mem' := hΩ }
  have hle : Algebra.adjoin Ω {u} ≤ V' := Algebra.adjoin_le (Set.singleton_subset_iff.2 hu)
  obtain ⟨p, hp, hpx⟩ := (hx : IsIntegral (Algebra.adjoin Ω {u}) x)
  let f : Algebra.adjoin Ω {u} →+* V :=
    { toFun := fun y => ⟨y.1, hle y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hint : IsIntegral V x := ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map]; exact hpx⟩
  obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := L)).1 hint
  exact y.2

theorem valuation_covers {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (u : L) (V : ValuationSubring L)
    (hΩ : ∀ a : Ω, algebraMap Ω L a ∈ V) : (intCl Ω u : Set L) ⊆ V ∨ (intCl Ω u⁻¹ : Set L) ⊆ V := by
  rcases V.mem_or_inv_mem u with h | h
  · exact Or.inl (intCl_subset V hΩ h)
  · exact Or.inr (intCl_subset V hΩ h)

theorem transcendental_inv {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L}
    (hu : Transcendental Ω u) : Transcendental Ω u⁻¹ := by
  intro h
  apply hu
  simpa using h.inv

theorem adjoin_inv_eq {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (u : L) :
    IntermediateField.adjoin Ω {u⁻¹} = IntermediateField.adjoin Ω {u} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self Ω u)
  · rw [IntermediateField.adjoin_simple_le_iff]
    simpa using inv_mem (IntermediateField.mem_adjoin_simple_self Ω u⁻¹)

theorem ne_zero_of_transcendental {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L}
    (hu : Transcendental Ω u) : u ≠ 0 := by
  rintro rfl
  exact hu isAlgebraic_zero

theorem self_mem_intCl {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (u : L) : u ∈ intCl Ω u :=
  isIntegral_algebraMap (x := (⟨u, Algebra.subset_adjoin (Set.mem_singleton u)⟩ : Algebra.adjoin Ω {u}))

def LeafIntClosureAlg : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    Algebra.FiniteType Ω (intCl Ω u) ∧ IsIntegrallyClosed (intCl Ω u) ∧ ringKrullDim (intCl Ω u) = 1 ∧
      IsFractionRing (intCl Ω u) L

def LeafIntClosureLoc : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    Algebra.adjoin Ω ((intCl Ω u : Set L) ∪ {u⁻¹}) = Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u})

def LeafGlueProper : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L),
  u ≠ 0 → u ∈ A → u⁻¹ ∈ B → Algebra.FiniteType Ω A → Algebra.FiniteType Ω B →
  IsIntegrallyClosed A → IsIntegrallyClosed B → ringKrullDim A = 1 → ringKrullDim B = 1 →
  IsFractionRing A L → IsFractionRing B L →
  Algebra.adjoin Ω ((A : Set L) ∪ {u⁻¹}) = Algebra.adjoin Ω ((B : Set L) ∪ {u}) →
  (∀ V : ValuationSubring L, (∀ a : Ω, algebraMap Ω L a ∈ V) → (A : Set L) ⊆ V ∨ (B : Set L) ⊆ V) →
    ∃ (C0 : Scheme.{0}) (c0 : C0 ⟶ Sp Ω) (x : C0) (ψ : Spec (C0.presheaf.stalk x) ⟶ Sp L),
      IsIntegral C0 ∧ IsProper c0 ∧ (∀ y : C0, IsIntegrallyClosed (C0.presheaf.stalk y)) ∧
      topologicalKrullDim C0 = 1 ∧ IsGenericPoint x (⊤ : Set C0) ∧
      ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = C0.fromSpecStalk x ≫ c0

theorem adjoin_le_of_shift {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L} (hu : u ≠ 0)
    (h : ∀ x ∈ intCl Ω u, ∃ n : ℕ, x * u⁻¹ ^ n ∈ intCl Ω u⁻¹) :
    Algebra.adjoin Ω ((intCl Ω u : Set L) ∪ {u⁻¹}) ≤ Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u}) := by
  rw [Algebra.adjoin_le_iff]
  rintro x (hx | hx)
  · obtain ⟨n, hn⟩ := h x hx
    have : x = x * u⁻¹ ^ n * u ^ n := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hu, one_pow, mul_one]
    rw [this]
    have h1 : x * u⁻¹ ^ n ∈ Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u}) :=
      Algebra.subset_adjoin (Set.mem_union_left _ hn)
    have h2 : u ∈ Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u}) :=
      Algebra.subset_adjoin (Set.mem_union_right _ rfl)
    exact mul_mem h1 (pow_mem h2 n)
  · rw [Set.mem_singleton_iff.1 hx]
    exact Algebra.subset_adjoin (Set.mem_union_left _ (self_mem_intCl u⁻¹))

def LeafIntShift : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L), u ≠ 0 →
  ∀ x ∈ intCl Ω u, ∃ n : ℕ, x * u⁻¹ ^ n ∈ intCl Ω u⁻¹

theorem LeafIntClosureLoc_of (h : LeafIntShift) : LeafIntClosureLoc := by
  intro Ω L _ _ _ u hu _
  have hu0 := ne_zero_of_transcendental hu
  apply le_antisymm (adjoin_le_of_shift hu0 (h Ω L u hu0))
  have h' := adjoin_le_of_shift (inv_ne_zero hu0) (by simpa using h Ω L u⁻¹ (inv_ne_zero hu0))
  simpa using h'

theorem shift_mem {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L} (hu : u ≠ 0) (c : L)
    (hc : c ∈ Algebra.adjoin Ω {u}) : ∃ N : ℕ, ∀ m, N ≤ m → c * u⁻¹ ^ m ∈ Algebra.adjoin Ω {u⁻¹} := by
  have hinv : u⁻¹ ∈ Algebra.adjoin Ω {u⁻¹} := Algebra.subset_adjoin (Set.mem_singleton _)
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, pow_one, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
    exact pow_mem hinv k
  | algebraMap a =>
    exact ⟨0, fun m _ => mul_mem (Subalgebra.algebraMap_mem _ a) (pow_mem hinv m)⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨N1, h1⟩ := ihx
    obtain ⟨N2, h2⟩ := ihy
    refine ⟨max N1 N2, fun m hm => ?_⟩
    rw [add_mul]
    exact add_mem (h1 m (le_trans (le_max_left _ _) hm)) (h2 m (le_trans (le_max_right _ _) hm))
  | mul x y _ _ ihx ihy =>
    obtain ⟨N1, h1⟩ := ihx
    obtain ⟨N2, h2⟩ := ihy
    refine ⟨N1 + N2, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have : x * y * u⁻¹ ^ (N1 + N2 + k) = (x * u⁻¹ ^ N1) * (y * u⁻¹ ^ (N2 + k)) := by ring
    rw [this]
    exact mul_mem (h1 N1 le_rfl) (h2 _ (Nat.le_add_right _ _))

theorem integral_closure_polynomial_elem_mul_inv_pow_mem_inv_closure : LeafIntShift := by
  intro Ω L _ _ _ u hu x hx
  classical
  obtain ⟨p, hpm, hpx⟩ := (hx : IsIntegral (Algebra.adjoin Ω {u}) x)
  have hN : ∀ c : Algebra.adjoin Ω {u}, ∃ N : ℕ, ∀ m, N ≤ m → (c : L) * u⁻¹ ^ m ∈ Algebra.adjoin Ω {u⁻¹} :=
    fun c => shift_mem hu c c.2
  choose Nf hNf using hN
  set p' := p.map (algebraMap (Algebra.adjoin Ω {u}) L) with hp'
  have hpm' : p'.Monic := hpm.map _
  have hdeg : p'.natDegree = p.natDegree := hpm.natDegree_map _
  set N := (Finset.range (p.natDegree + 1)).sup (fun i => Nf (p.coeff i)) with hNdef
  set r : L := u⁻¹ ^ N
  refine ⟨N, ?_⟩
  show IsIntegral (Algebra.adjoin Ω {u⁻¹}) (x * u⁻¹ ^ N)
  have hroot : (p'.scaleRoots r).eval (r * x) = 0 := by
    have h0 : p'.eval₂ (RingHom.id L) x = 0 := by
      rw [hp', Polynomial.eval₂_map]; exact hpx
    have h := Polynomial.scaleRoots_eval₂_mul (p := p') (RingHom.id L) x r
    rw [h0, mul_zero] at h
    exact h
  have hmon : (p'.scaleRoots r).Monic := (Polynomial.monic_scaleRoots_iff r).2 hpm'
  have hlift : p'.scaleRoots r ∈ Polynomial.lifts (algebraMap (Algebra.adjoin Ω {u⁻¹}) L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots, hp', Polynomial.coeff_map]
    rcases lt_or_ge i p.natDegree with hi | hi
    · have hle : Nf (p.coeff i) ≤ N * (p'.natDegree - i) := by
        have h1 : Nf (p.coeff i) ≤ N :=
          Finset.le_sup (f := fun i => Nf (p.coeff i)) (Finset.mem_range.2 (by omega))
        have h2 : 1 ≤ p'.natDegree - i := by omega
        nlinarith
      have := hNf (p.coeff i) _ hle
      rw [← pow_mul] at *
      exact ⟨⟨_, this⟩, rfl⟩
    · have he : p'.natDegree - i = 0 := by omega
      rw [he, pow_zero, mul_one]
      rcases eq_or_lt_of_le hi with h | h
      · rw [← h, hpm.coeff_natDegree, map_one]; exact ⟨1, map_one _⟩
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h, map_zero]; exact ⟨0, map_zero _⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hmon
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, mul_comm]
  exact hroot

theorem LeafNormalModel_of (hA : LeafIntClosureAlg) (hC : LeafGlueProper) :
    LateralTheory.E.LeafModelCurveCut.ExistsNormalProperCurveModel := by
  intro Ω L _ _ _ u hu hfin
  have hu' := transcendental_inv hu
  have hfin' : FiniteDimensional (IntermediateField.adjoin Ω {u⁻¹}) L := by
    rw [adjoin_inv_eq (Ω := Ω) u]; exact hfin
  obtain ⟨a1, a2, a3, a4⟩ := hA Ω L u hu hfin
  obtain ⟨b1, b2, b3, b4⟩ := hA Ω L u⁻¹ hu' hfin'
  exact hC Ω L (intCl Ω u) (intCl Ω u⁻¹) u (ne_zero_of_transcendental hu) (self_mem_intCl u)
    (self_mem_intCl u⁻¹) a1 b1 a2 b2 a3 b3 a4 b4
    (LeafIntClosureLoc_of integral_closure_polynomial_elem_mul_inv_pow_mem_inv_closure Ω L u hu hfin) (fun V hΩ => valuation_covers u V hΩ)

end LateralTheory.E.LeafNormalModelPf
end
end

section

noncomputable section

namespace LateralTheory.E.LIdemLiftPf

open Polynomial

def IdemLiftFin (A : Type) [CommRing A] (I : Ideal A) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] [Module.Finite A B]
    (ε : B ⧸ I.map (algebraMap A B)), IsIdempotentElem ε →
    ∃ e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = ε

def FactLift (A : Type) [CommRing A] (I : Ideal A) : Prop :=
  ∀ (g : A[X]), g.Monic → ∀ n m : ℕ, g.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) ^ m →
    ∃ P Q : A[X], P.Monic ∧ Q.Monic ∧ g = P * Q ∧
      P.map (Ideal.Quotient.mk I) = X ^ n ∧ Q.map (Ideal.Quotient.mk I) = (X - 1) ^ m

def LFact : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I], FactLift A I

def LFinOfFact : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A), I ≤ Ideal.jacobson ⊥ →
  FactLift A I → IdemLiftFin A I

def LRed : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A), IdemLiftFin A I →
  LateralTheory.E.LChartPf.IdemLiftInt A I

theorem idem_of_mul_eq_zero {B : Type} [CommRing B] (x y : B) (hxy : x * y = 0) (hu : IsUnit (x + y)) :
    IsIdempotentElem (x * hu.unit⁻¹) := by
  have hx : x * x = x * (x + y) := by rw [mul_add, hxy, add_zero]
  have h1 : (x + y) * (hu.unit⁻¹ : Bˣ) = 1 := hu.mul_val_inv
  unfold IsIdempotentElem
  calc x * ↑hu.unit⁻¹ * (x * ↑hu.unit⁻¹) = x * x * (↑hu.unit⁻¹ * ↑hu.unit⁻¹) := by ring
    _ = x * ((x + y) * ↑hu.unit⁻¹) * ↑hu.unit⁻¹ := by rw [hx]; ring
    _ = x * ↑hu.unit⁻¹ := by rw [h1, mul_one]

theorem lRed : LRed := by
  intro A _ I hfin B _ _ _ ε hε
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective ε
  have hb : b * b - b ∈ I.map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hε.eq, sub_self]
  rw [Ideal.map, Submodule.mem_span_set'] at hb
  obtain ⟨n, f, g, hfg⟩ := hb
  choose a ha hag using fun i => (g i).2
  let C : Subalgebra A B := Algebra.adjoin A (insert b (Set.range f))
  have hC : Module.Finite A C := by
    have := Algebra.finite_adjoin_of_finite_of_isIntegral (R := A) (s := insert b (Set.range f))
      ((Set.finite_range f).insert b) (fun x _ => Algebra.IsIntegral.isIntegral x)
    exact this
  have hbC : b ∈ C := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hfC : ∀ i, f i ∈ C := fun i => Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  let bC : C := ⟨b, hbC⟩
  have hmem : bC * bC - bC ∈ I.map (algebraMap A C) := by
    have : bC * bC - bC = ∑ i, (⟨f i, hfC i⟩ : C) * algebraMap A C (a i) := by
      apply Subtype.ext
      simp only [bC, Subalgebra.coe_sub, Subalgebra.coe_mul, ← hfg, smul_eq_mul]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hag i]
    rw [this]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i))
  have hidC : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A C)) bC) := by
    unfold IsIdempotentElem
    rw [← map_mul, Ideal.Quotient.eq]; exact hmem
  obtain ⟨e, he, hee⟩ := hfin C _ hidC
  refine ⟨(e : B), ?_, ?_⟩
  · unfold IsIdempotentElem; exact congrArg Subtype.val he.eq
  · rw [Ideal.Quotient.eq] at hee ⊢
    have := Ideal.mem_map_of_mem (C.val : C →ₐ[A] B).toRingHom hee
    rw [Ideal.map_map] at this
    simpa [bC] using this

theorem exists_monic_of_idem_mod {A : Type} [CommRing A] (I : Ideal A) (B : Type) [CommRing B] [Algebra A B]
    [Module.Finite A B] (b : B) (hb : b * b - b ∈ I.map (algebraMap A B)) :
    ∃ (g : A[X]) (d : ℕ), g.Monic ∧ aeval b g = 0 ∧
      g.map (Ideal.Quotient.mk I) = X ^ (d + 1) * (X - 1) ^ (d + 1) := by
  let φ : Module.End A B := LinearMap.mulLeft A (b * b - b)
  have hφ : LinearMap.range φ ≤ I • (⊤ : Submodule A B) := by
    rintro _ ⟨y, rfl⟩
    rw [Ideal.smul_top_eq_map]
    exact Ideal.mul_mem_right _ _ hb
  obtain ⟨p, hpm, -, hpc, hpφ⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero A φ I hφ
  have hp0 : aeval (b * b - b) p = 0 := by
    have hφ' : φ = Algebra.lmul A B (b * b - b) := rfl
    rw [hφ', Polynomial.aeval_algHom_apply] at hpφ
    simpa using congrArg (fun ψ : Module.End A B => ψ 1) hpφ
  have hpmap : p.map (Ideal.Quotient.mk I) = X ^ p.natDegree := by
    ext k
    rw [coeff_map, coeff_X_pow]
    split_ifs with hk
    · subst hk; rw [hpm.coeff_natDegree, map_one]
    · rcases lt_or_gt_of_ne hk with h | h
      · rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_le_self (by omega) (hpc k)
      · rw [coeff_eq_zero_of_natDegree_lt h, map_zero]
  rcases subsingleton_or_nontrivial A with hA | hA
  · have h10 : (1 : B) = 0 := by rw [← map_one (algebraMap A B), Subsingleton.elim (1 : A) 0, map_zero]
    have : Subsingleton B := subsingleton_of_zero_eq_one h10.symm
    have h10' : (1 : A ⧸ I) = 0 := by rw [← map_one (Ideal.Quotient.mk I), Subsingleton.elim (1 : A) 0, map_zero]
    have : Subsingleton (A ⧸ I) := subsingleton_of_zero_eq_one h10'.symm
    exact ⟨p, 0, hpm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hqm : (X * X - X : A[X]).Monic := by
    rw [show (X * X - X : A[X]) = X ^ 2 - X by ring]
    exact monic_X_pow_sub (by rw [degree_X]; exact_mod_cast (by norm_num : 1 < 2))
  have hq : (X * X - X : A[X]).natDegree = 2 := by
    rw [show (X * X - X : A[X]) = X ^ 2 - X by ring]
    compute_degree!
  refine ⟨p.comp (X * X - X) * (X * X - X), p.natDegree, (hpm.comp hqm (by omega)).mul hqm, ?_, ?_⟩
  · rw [map_mul, aeval_comp]; simp [hp0]
  · simp only [Polynomial.map_mul, map_comp, hpmap, X_pow_comp, Polynomial.map_sub, map_X]
    rw [show (X * X - X : (A ⧸ I)[X]) = X * (X - 1) by ring, mul_pow]
    ring

theorem aeval_sub_mem_of_map_eq {A : Type} [CommRing A] (I : Ideal A) {B : Type} [CommRing B] [Algebra A B]
    (f f' : A[X]) (h : f.map (Ideal.Quotient.mk I) = f'.map (Ideal.Quotient.mk I)) (b : B) :
    aeval b f - aeval b f' ∈ I.map (algebraMap A B) := by
  have h1 : f - f' ∈ Ideal.map (C : A →+* A[X]) I := by
    rw [← Ideal.mk_ker (I := I), ← Polynomial.ker_mapRingHom, RingHom.mem_ker, map_sub]
    simp only [coe_mapRingHom, h, sub_self]
  have h2 := Ideal.mem_map_of_mem (aeval b).toRingHom h1
  rw [Ideal.map_map] at h2
  have h3 : (aeval b).toRingHom.comp (C : A →+* A[X]) = algebraMap A B := by ext; simp
  rw [h3] at h2
  simpa using h2

theorem isUnit_one_add_of_finite {A : Type} [CommRing A] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    {B : Type} [CommRing B] [Algebra A B] [Module.Finite A B] (s : B)
    (hs : s - 1 ∈ I.map (algebraMap A B)) : IsUnit s := by
  have key : (⊤ : Submodule A B) ≤ (Ideal.span {s}).restrictScalars A := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI ?_
    intro y _
    have hy : y = s * y - (s - 1) * y := by ring
    rw [hy]
    refine Submodule.sub_mem_sup (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) ?_
    rw [Ideal.smul_top_eq_map]
    exact Ideal.mul_mem_right _ _ hs
  have h1 : (1 : B) ∈ Ideal.span {s} := key Submodule.mem_top
  rw [Ideal.mem_span_singleton] at h1
  exact isUnit_of_dvd_one h1

theorem lFinOfFact : LFinOfFact := by
  intro A _ I hI hF B _ _ _ ε hε
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective ε
  set π := Ideal.Quotient.mk (I.map (algebraMap A B))
  have hb : b * b - b ∈ I.map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hε.eq, sub_self]
  obtain ⟨g, d, hgm, hgb, hgmap⟩ := exists_monic_of_idem_mod I B b hb
  obtain ⟨P, Q, -, -, hPQ, hP, hQ⟩ := hF g hgm _ _ hgmap
  have hcop : IsCoprime (X ^ (d + 1) : (A ⧸ I)[X]) ((X - 1) ^ (d + 1)) :=
    (show IsCoprime (X : (A ⧸ I)[X]) (X - 1) from ⟨1, -1, by ring⟩).pow
  obtain ⟨u0, v0, huv0⟩ := hcop
  obtain ⟨u, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective u0
  obtain ⟨v, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective v0
  have hπ : ∀ f f' : A[X], f.map (Ideal.Quotient.mk I) = f'.map (Ideal.Quotient.mk I) →
      π (aeval b f) = π (aeval b f') := fun f f' h =>
    Ideal.Quotient.eq.2 (aeval_sub_mem_of_map_eq I f f' h b)
  have hPb : π (aeval b P) = π b ^ (d + 1) := by
    rw [hπ P (X ^ (d + 1)) (by rw [hP]; simp)]; simp
  have hQb : π (aeval b Q) = (π b - 1) ^ (d + 1) := by
    rw [hπ Q ((X - 1) ^ (d + 1)) (by rw [hQ]; simp)]; simp
  have hUb : π (aeval b (u * P)) + π (aeval b (v * Q)) = 1 := by
    rw [← map_add (f := _), ← map_add (f := _), hπ (u * P + v * Q) 1 (by simp [Polynomial.map_add (f := _), Polynomial.map_mul, hP, hQ, huv0])]
    simp
  set x := aeval b (u * P)
  set y := aeval b (v * Q)
  have hxy : x * y = 0 := by
    simp only [x, y, ← map_mul]
    rw [show u * P * (v * Q) = u * v * g by rw [hPQ]; ring, map_mul, hgb, mul_zero]
  have hs : (x + y) - 1 ∈ I.map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add (f := _), hUb, map_one, sub_self]
  have hu := isUnit_one_add_of_finite I hI (x + y) hs
  refine ⟨x * hu.unit⁻¹, idem_of_mul_eq_zero x y hxy hu, ?_⟩
  have hinv : π (hu.unit⁻¹ : Bˣ) = 1 := by
    have h1 : π (x + y) * π (hu.unit⁻¹ : Bˣ) = 1 := by rw [← map_mul, hu.mul_val_inv, map_one]
    rwa [map_add, hUb, one_mul] at h1
  have he : π b * π b = π b := hε.eq
  have hx : π x = π b := by
    have e1 : π x * (1 - π b) = 0 := by
      simp only [x, map_mul, hPb]
      rw [pow_succ, mul_assoc, mul_assoc, mul_sub, mul_one, he, sub_self, mul_zero, mul_zero]
    have e2 : π y * π b = 0 := by
      simp only [y, map_mul, hQb]
      rw [pow_succ, mul_assoc, mul_assoc, sub_mul, he, one_mul, sub_self, mul_zero, mul_zero]
    have e3 : π x = π x * π b := by linear_combination e1
    rw [e3]; linear_combination (π b) * hUb - e2
  rw [map_mul, hinv, mul_one, hx]

theorem LIdemLift_of (h1 : LFact) : LateralTheory.E.LChartPf.LIdemLift := by
  intro A _ I _
  exact lRed A I (lFinOfFact A I (by simpa only [Ideal.jacobson_bot] using (HenselianRing.jac (R := A) (I := I))) (h1 A I))

end LateralTheory.E.LIdemLiftPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Topology

namespace LateralTheory.E.LeafGlueExtendPf

lemma dominant_of_generic {C W : Scheme.{0}} (e : W ⟶ C) [IsOpenImmersion e] (x : C)
    (hx : IsGenericPoint x (⊤ : Set C)) (g : Spec (C.presheaf.stalk x) ⟶ W)
    (hg : g ≫ e = C.fromSpecStalk x) : IsDominant g := by
  constructor
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  intro w
  obtain ⟨pt, hpt⟩ : ∃ pt : Spec (C.presheaf.stalk x), C.fromSpecStalk x pt = x :=
    ⟨_, Scheme.fromSpecStalk_closedPoint⟩
  rw [← hg] at hpt
  have he : e (g pt) = x := hpt
  have hmem : g pt ∈ Set.range g := ⟨_, rfl⟩
  have h1 : closure ({g pt} : Set W) ⊆ closure (Set.range g) :=
    closure_mono (Set.singleton_subset_iff.mpr hmem)
  apply h1
  rw [e.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton, he]
  show e w ∈ closure {x}
  rw [show closure ({x} : Set C) = (⊤ : Set C) from hx]
  trivial

theorem LeafGlueExtend_of : LateralTheory.E.LeafExtendCut.LeafGlueExtend := by
  intro C X S _ sC p _ x hx ψ H
  choose U hyU hxU f hf1 hf2 using H
  let 𝒰 : C.OpenCover := Scheme.Cover.mkOfCovers C (fun y => (U y).toScheme) (fun y => (U y).ι)
    (fun y => ⟨y, ⟨y, hyU y⟩, rfl⟩)
  have hcompat0 : ∀ i j : C,
      pullback.fst (U i).ι (U j).ι ≫ f i = pullback.snd (U i).ι (U j).ι ≫ f j := by
    intro i j
    have : IsReduced (pullback (U i).ι (U j).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst (U i).ι (U j).ι ≫ (U i).ι)
    let g := pullback.lift ((U i).fromSpecStalkOfMem x (hxU i))
      ((U j).fromSpecStalkOfMem x (hxU j))
      (by rw [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι])
    have : IsDominant g :=
      dominant_of_generic (pullback.fst (U i).ι (U j).ι ≫ (U i).ι) x hx g
        (by simp only [g, pullback.lift_fst_assoc, Scheme.Opens.fromSpecStalkOfMem_ι])
    refine ext_of_isDominant_of_isSeparated p ?_ g ?_
    · simp only [Category.assoc, hf2]; rw [pullback.condition_assoc]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hf1, hf1]
  have hcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd _ _ ≫ f j :=
    fun i j => hcompat0 i j
  refine ⟨𝒰.glueMorphisms f hcompat, ?_, ?_⟩
  · have := 𝒰.ι_glueMorphisms f hcompat x
    rw [← (U x).fromSpecStalkOfMem_ι x (hxU x), Category.assoc]
    change _ ≫ 𝒰.f x ≫ _ = _
    rw [this]
    exact hf1 x
  · refine Scheme.Cover.hom_ext 𝒰 _ _ (fun y => ?_)
    rw [𝒰.ι_glueMorphisms_assoc f hcompat y]
    exact hf2 y

end LateralTheory.E.LeafGlueExtendPf
end
end
