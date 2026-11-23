module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

section

open Polynomial

private lemma coords {E : Type} [Field E] [CharZero E] (d : ℕ) (s : E) (hs : s ^ 2 = -(d : E))
    (z : E) (hz : z ∈ IntermediateField.adjoin ℚ ({s} : Set E)) :
    ∃ a b : ℚ, z = (a : E) + (b : E) * s := by
  have hint : IsIntegral ℚ s := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hs]
    exact (isIntegral_natCast d).neg
  have hz' : z ∈ Algebra.adjoin ℚ ({s} : Set E) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hz
  clear hz
  induction hz' using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    refine ⟨a * c - d * b * e, a * e + b * c, ?_⟩
    push_cast
    linear_combination (b : E) * e * hs

private lemma aeval_pair {E : Type} [Field E] [CharZero E] (d : ℕ) (s : E) (hs : s ^ 2 = -(d : E))
    (a b : ℚ) (p : ℤ[X]) :
    ∃ u v : ℚ, aeval ((a : E) + (b : E) * s) p = (u : E) + (v : E) * s ∧
      aeval ((a : E) - (b : E) * s) p = (u : E) - (v : E) * s := by
  induction p using Polynomial.induction_on with
  | C c => exact ⟨c, 0, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨u, v, h1, h2⟩ := hp
    obtain ⟨u', v', h1', h2'⟩ := hq
    refine ⟨u + u', v + v', ?_, ?_⟩
    · rw [map_add (f := _), h1, h1']; push_cast; ring
    · rw [map_add (f := _), h2, h2']; push_cast; ring
  | monomial n c h =>
    obtain ⟨u, v, h1, h2⟩ := h
    refine ⟨u * a - d * v * b, u * b + v * a, ?_, ?_⟩
    · rw [pow_succ, ← mul_assoc, map_mul, h1, aeval_X]
      push_cast
      linear_combination (v : E) * b * hs
    · rw [pow_succ, ← mul_assoc, map_mul, h2, aeval_X]
      push_cast
      linear_combination (v : E) * b * hs

private lemma conj_integral {E : Type} [Field E] [CharZero E] (d : ℕ) (s : E) (hd : 0 < d)
    (hs : s ^ 2 = -(d : E)) (a b : ℚ) (h : IsIntegral ℤ ((a : E) + (b : E) * s)) :
    IsIntegral ℤ ((a : E) - (b : E) * s) := by
  obtain ⟨p, hp, h0⟩ := h
  obtain ⟨u, v, h1, h2⟩ := aeval_pair d s hs a b p
  rw [← aeval_def, h1] at h0
  have hn : u ^ 2 + d * v ^ 2 = 0 := by
    have : (u : E) ^ 2 + d * (v : E) ^ 2 = 0 := by
      linear_combination ((u : E) - v * s) * h0 + (v : E) ^ 2 * hs
    exact_mod_cast this
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hv2 : 0 ≤ (d : ℚ) * v ^ 2 := by positivity
  have hu : u = 0 := by nlinarith [sq_nonneg u]
  have hv : v = 0 := by
    rw [hu] at hn
    have : (d : ℚ) * v ^ 2 = 0 := by simpa using hn
    simpa [hd'.ne'] using this
  refine ⟨p, hp, ?_⟩
  rw [← aeval_def, h2, hu, hv]
  simp

private lemma rat_int {E : Type} [Field E] [CharZero E] (q : ℚ) (h : IsIntegral ℤ (q : E)) :
    ∃ n : ℤ, (n : ℚ) = q := by
  have h' : IsIntegral ℤ q := by
    have := (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := E) (x := q)
      ).1 (by simpa using h)
    exact this
  simpa using (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 h'

private lemma int_of_sqfree_mul_sq (d : ℕ) (hd : Squarefree d) (q : ℚ) (m : ℤ)
    (h : (m : ℚ) = d * q ^ 2) : ∃ n : ℤ, (n : ℚ) = q := by
  have h1 : q * q.den = q.num := Rat.mul_den_eq_num q
  have h2 : (d : ℤ) * q.num ^ 2 = (q.den : ℤ) ^ 2 * m := by
    have : (d : ℚ) * (q.num : ℚ) ^ 2 = (q.den : ℚ) ^ 2 * m := by
      rw [← h1, h]; ring
    exact_mod_cast this
  have hc : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) :=
    (Rat.isCoprime_num_den q).symm.pow
  have h3 : (q.den : ℤ) ^ 2 ∣ d := hc.dvd_of_dvd_mul_right ⟨m, h2⟩
  have h4 : q.den * q.den ∣ d := by
    rw [← sq]; exact_mod_cast h3
  have h5 : q.den = 1 := Nat.isUnit_iff.1 (hd _ h4)
  exact ⟨q.num, by rw [← h1, h5]; simp⟩

theorem UpperTheory.integral_imag_quadratic_half_int :
    ∀ (E : Type) [Field E] [CharZero E] (d : ℕ) (s : E), Squarefree d → s ^ 2 = -(d : E) → ∀ z : E, z ∈ IntermediateField.adjoin ℚ ({s} : Set E) → IsIntegral ℤ z → ∃ x y : ℤ, Even (x - y) ∧ z = ((x : E) + (y : E) * s) / 2 := by
  intro E _ _ d s hd hs z hz hi
  obtain ⟨a, b, rfl⟩ := coords d s hs z hz
  have hc := conj_integral d s (Nat.pos_of_ne_zero hd.ne_zero) hs a b hi
  obtain ⟨x, hx⟩ := rat_int (E := E) (2 * a) (by
    have e : ((2 * a : ℚ) : E) = (a : E) + (b : E) * s + ((a : E) - (b : E) * s) := by
      push_cast; ring
    rw [e]
    exact hi.add hc)
  obtain ⟨n, hn⟩ := rat_int (E := E) (a ^ 2 + d * b ^ 2) (by
    have e : ((a ^ 2 + d * b ^ 2 : ℚ) : E)
        = ((a : E) + (b : E) * s) * ((a : E) - (b : E) * s) := by
      push_cast
      linear_combination (b : E) ^ 2 * hs
    rw [e]
    exact hi.mul hc)
  obtain ⟨y, hy⟩ := int_of_sqfree_mul_sq d hd (2 * b) (4 * n - x ^ 2) (by
    push_cast
    rw [hx, hn]; ring)
  have key : x ^ 2 + d * y ^ 2 = 4 * n := by
    have : (x : ℚ) ^ 2 + d * (y : ℚ) ^ 2 = 4 * n := by
      rw [hx, hy, hn]; ring
    exact_mod_cast this
  refine ⟨x, y, ?_, ?_⟩
  · rcases Int.even_or_odd' x with ⟨k, rfl | rfl⟩ <;>
      rcases Int.even_or_odd' y with ⟨l, rfl | rfl⟩
    · exact ⟨k - l, by ring⟩
    · exfalso
      have h4 : (4 : ℤ) ∣ d := ⟨n - k ^ 2 - d * (l ^ 2 + l), by linear_combination key⟩
      have h5 : 2 * 2 ∣ d := by exact_mod_cast h4
      simpa using hd 2 h5
    · exfalso
      have h4 : 4 * (n - k ^ 2 - k - d * l ^ 2) = 1 := by linear_combination -key
      omega
    · exact ⟨k - l, by ring⟩
  · have hx' : (x : E) = 2 * (a : E) := by exact_mod_cast congrArg (fun t : ℚ => (t : E)) hx
    have hy' : (y : E) = 2 * (b : E) := by exact_mod_cast congrArg (fun t : ℚ => (t : E)) hy
    rw [hx', hy']; ring
end

section

open AlgebraicGeometry

private lemma exists_kill {A : Type*} [CommRing A] [IsNoetherianRing A] (M : Submonoid A)
    (I : Ideal A) (h : ∀ a ∈ I, ∃ m ∈ M, m * a = 0) :
    ∃ s ∈ M, ∀ a ∈ I, s * a = 0 := by
  classical
  obtain ⟨t, rfl⟩ := (IsNoetherian.noetherian I : I.FG)
  induction t using Finset.induction_on with
  | empty => exact ⟨1, M.one_mem, by simp⟩
  | insert x t _ ih =>
    obtain ⟨s, hs, hs'⟩ := ih fun a ha => h a (Ideal.span_mono (by simp) ha)
    obtain ⟨m, hm, hm'⟩ := h x (Ideal.subset_span (by simp))
    refine ⟨m * s, M.mul_mem hm hs, fun a ha => ?_⟩
    rw [Finset.coe_insert, Submodule.mem_span_insert] at ha
    obtain ⟨c, z, hz, rfl⟩ := ha
    have h2 := hs' z hz
    rw [smul_eq_mul]
    linear_combination (s * c) * hm' + m * h2

private lemma isDomain_away {A L B : Type*} [CommRing A] [CommRing L] [IsDomain L]
    [CommRing B] [Algebra A L] [Algebra A B] (M : Submonoid A) [IsLocalization M L]
    (s : A) (hs : s ∈ M) (hk : ∀ a, algebraMap A L a = 0 → s * a = 0)
    [IsLocalization.Away s B] : IsDomain B := by
  have hu : IsUnit (algebraMap A L s) := IsLocalization.map_units L (⟨s, hs⟩ : M)
  let φ : B →+* L := IsLocalization.Away.lift s hu
  have hφ : ∀ a, φ (algebraMap A B a) = algebraMap A L a := fun a =>
    IsLocalization.Away.lift_eq s hu a
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) b
    have h0 : algebraMap A L a = 0 := by
      rw [← hφ, ← hm, map_mul, hb, zero_mul]
    have h1 : algebraMap A B s * algebraMap A B a = 0 := by
      rw [← map_mul, hk a h0, map_zero]
    have hsu : IsUnit (algebraMap A B s) := IsLocalization.Away.algebraMap_isUnit s
    have h2 : algebraMap A B a = 0 := (hsu.mul_right_eq_zero).mp h1
    have hmu : IsUnit (algebraMap A B (m : A)) :=
      IsLocalization.map_units B m
    simp only at hm
    rw [h2] at hm
    exact (hmu.mul_left_eq_zero).mp hm
  exact hinj.isDomain φ

theorem UpperTheory.Reformulated.B.DYde8.main :
    ∀ {X : AlgebraicGeometry.Scheme} {V : X.Opens},
      AlgebraicGeometry.IsAffineOpen V →
        ∀ [IsNoetherianRing (↑(X.presheaf.obj (Opposite.op V)) : Type)],
          ∀ ξ ∈ V,
            ∀ [IsDomain (↑(X.presheaf.stalk ξ) : Type)],
              ∃ (f : (↑(X.presheaf.obj (Opposite.op V)) : Type)),
                ξ ∈ X.basicOpen f ∧ IsDomain (↑(X.presheaf.obj (Opposite.op (X.basicOpen f))) : Type) := by
  intro X V hV _ ξ hξ _
  letI alg : Algebra Γ(X, V) (X.presheaf.stalk ξ) :=
    X.presheaf.algebra_section_stalk (⟨ξ, hξ⟩ : V)
  let P := (hV.primeIdealOf ⟨ξ, hξ⟩).asIdeal
  have hloc : IsLocalization P.primeCompl (X.presheaf.stalk ξ) :=
    hV.isLocalization_stalk ⟨ξ, hξ⟩
  obtain ⟨s, hs, hk⟩ := exists_kill P.primeCompl
    (RingHom.ker (algebraMap Γ(X, V) (X.presheaf.stalk ξ)))
    (fun a ha => by
      obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl (X.presheaf.stalk ξ) a).mp ha
      exact ⟨m, m.2, hm⟩)
  refine ⟨s, ?_, ?_⟩
  · have hu : IsUnit (algebraMap Γ(X, V) (X.presheaf.stalk ξ) s) :=
      IsLocalization.map_units (X.presheaf.stalk ξ) (⟨s, hs⟩ : P.primeCompl)
    exact (X.mem_basicOpen s ξ hξ).mpr hu
  · have := hV.isLocalization_basicOpen s
    exact isDomain_away (L := X.presheaf.stalk ξ) P.primeCompl s hs (fun a ha => hk a ha)
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp :
    (R : Type) → [CommRing R] → AlgebraicGeometry.Scheme :=
    fun (R : Type) [CommRing R] ↦ AlgebraicGeometry.Spec (CommRingCat.of R)

@[reducible] noncomputable def UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.spMap :
    {R R' : Type} →
      [inst : CommRing R] → [inst_1 : CommRing R'] → (R →+* R') → (UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp R' ⟶ UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp R) :=
    fun {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') ↦ AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)

private lemma UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.exists_finite_subfield {A C : Type} [CommRing A] [Field C] [CharZero C]
    [Algebra.IsAlgebraic ℚ C] [Algebra.FiniteType ℤ A] (φ : A →+* C) :
    ∃ K : IntermediateField ℚ C, FiniteDimensional ℚ K ∧ ∀ a, φ a ∈ K := by
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℤ A).FG)
  refine ⟨IntermediateField.adjoin ℚ (φ '' (s : Set A)), ?_, ?_⟩
  · have : Finite (φ '' (s : Set A)) := (s.finite_toSet.image φ).to_subtype
    exact IntermediateField.finiteDimensional_adjoin
      (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral)
  · intro a
    have ha : a ∈ Algebra.adjoin ℤ (s : Set A) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | algebraMap r =>
      have : φ (algebraMap ℤ A r) = (r : C) := by simp
      rw [this]
      exact intCast_mem _ r
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

open AlgebraicGeometry CategoryTheory in
theorem UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.main :
    ∀ (C : Type) [inst : Field C] [inst_1 : CharZero C] [Algebra.IsAlgebraic ℚ C] (X : AlgebraicGeometry.Scheme)
      (π : X ⟶ UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp ℤ) [AlgebraicGeometry.LocallyOfFiniteType π] (x : UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp C ⟶ X),
      ∃ (K : Type) (x_1 : Field K) (_ : NumberField K) (e : K →+* C) (x' : UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp K ⟶ X),
        CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.spMap e) x' = x := by
  intro C _ _ _ X π _ x
  let pt : Spec (CommRingCat.of C) := IsLocalRing.closedPoint C
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x pt) (U := ⊤) trivial
  have hrange : Set.range x ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have : y = pt := Subsingleton.elim _ _
    rw [this]
    exact hxU
  let y := IsOpenImmersion.lift hU.fromSpec x hrange
  have hy : y ≫ hU.fromSpec = x := IsOpenImmersion.lift_fac _ _ _
  let φ : Γ(X, U) →+* C := (Spec.preimage y).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = y := Spec.map_preimage y
  have hft : (π.appLE ⊤ U (by simp)).hom.FiniteType :=
    π.finiteType_appLE (isAffineOpen_top _) hU _
  have hft' : ((π.appLE ⊤ U (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom).FiniteType :=
    RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _
      ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv).2))
  have hA : Algebra.FiniteType ℤ Γ(X, U) := by
    have h : algebraMap ℤ Γ(X, U) = ((π.appLE ⊤ U (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom) := Subsingleton.elim _ _
    rw [← h] at hft'
    exact RingHom.finiteType_algebraMap.mp hft'
  obtain ⟨K, hK, hmem⟩ := UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.exists_finite_subfield φ
  let ψ : Γ(X, U) →+* K := φ.codRestrict K hmem
  refine ⟨K, inferInstance, { to_finiteDimensional := hK }, K.val.toRingHom,
    Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_⟩
  rw [← hy, ← hφ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp :
    (R : Type) → [CommRing R] → AlgebraicGeometry.Scheme :=
    fun (R : Type) [CommRing R] ↦ AlgebraicGeometry.Spec (CommRingCat.of R)

@[reducible] noncomputable def UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap :
    {R R' : Type} →
      [inst : CommRing R] → [inst_1 : CommRing R'] → (R →+* R') → (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp R' ⟶ UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp R) :=
    fun {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') ↦ AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)

theorem UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.main :
    ∀ {A : Type} [inst : CommRing A] {Y Z : AlgebraicGeometry.Scheme} {f g : UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp A ⟶ Y} (s : Y ⟶ Z)
      [AlgebraicGeometry.IsSeparated s],
      CategoryTheory.CategoryStruct.comp f s = CategoryTheory.CategoryStruct.comp g s →
        ∀ {N : Type} (I : N → Ideal A),
          (∀ (x : A), (∀ (n : N), x ∈ I n) → x = (0 : A)) →
            (∀ (n : N),
                CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))) f =
                  CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))) g) →
              f = g := by
  open AlgebraicGeometry CategoryTheory CategoryTheory.Limits in
  intro A _ Y Z f g s _ h N I hI hn
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  have : IsSeparated Y'.hom := ‹_›
  have : IsAffine X'.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  have hcl : IsClosedImmersion (equalizer.ι f' g').left := inferInstance
  obtain ⟨haff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (equalizer.ι f' g').left
  have hfac : ∀ n, ∃ l : UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp (A ⧸ I n) ⟶ (equalizer f' g').left,
      l ≫ (equalizer.ι f' g').left = UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)) := by
    intro n
    let T' : Over Z := Over.mk (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)) ≫ f ≫ s)
    let ι' : T' ⟶ X' := Over.homMk (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)))
    have hc : ι' ≫ f' = ι' ≫ g' := by
      ext1
      exact hn n
    refine ⟨(equalizer.lift ι' hc).left, ?_⟩
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have hinj : Function.Injective (equalizer.ι f' g').left.appTop := by
    refine (injective_iff_map_eq_zero (equalizer.ι f' g').left.appTop.hom).mpr fun y hy ↦ ?_
    obtain ⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso (CommRingCat.of A)).inv a = y :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom y, by simp⟩
    have ha : a = 0 := by
      refine hI a fun n ↦ ?_
      obtain ⟨l, hl⟩ := hfac n
      have h1 : (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = 0 := by
        rw [← hl, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        erw [hy]
        exact map_zero _
      have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I n)))
      have h3 : (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I n))).inv (Ideal.Quotient.mk (I n) a) = 0 := by
        have h4 := congr($h2 a)
        simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h4
        exact h4.trans h1
      have h5 := congr((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I n))).hom $h3)
      simp only [map_zero] at h5
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa using h5
    simp [ha]
  have hiso : IsIso (equalizer.ι f' g').left.appTop := by
    exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  have hE : IsIso (equalizer.ι f' g').left :=
    (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
      (arrowIsoSpecΓOfIsAffine (equalizer.ι f' g').left)).mpr
      (inferInstanceAs (IsIso (Spec.map (equalizer.ι f' g').left.appTop)))
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)
end

section

private lemma UpperTheory.isLocalHom_of_square_zero {A B : Type*} [CommRing A] [CommRing B] (π : A →+* B)
    (hs : Function.Surjective π) (hk : ∀ x, π x = 0 → x * x = 0) : IsLocalHom π := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := ha.exists_right_inv
  obtain ⟨b, rfl⟩ := hs c
  have h0 : π (a * b - 1) = 0 := by rw [map_sub, map_mul, hc, map_one, sub_self]
  have hn : IsNilpotent (a * b - 1) := ⟨2, by rw [pow_two]; exact hk _ h0⟩
  have hu : IsUnit (a * b) := by simpa using hn.isUnit_add_one
  exact isUnit_of_mul_isUnit_left hu

theorem UpperTheory.formally_smooth_section_stalk :
    open AlgebraicGeometry CategoryTheory in
        ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [Smooth f] (s : X ⟶ Y), s ≫ f = 𝟙 X → ∀ p : X,
          ∃ (B : CommRingCat.{0}) (α : X.presheaf.stalk p ⟶ B) (σ : B ⟶ X.presheaf.stalk p) (ι : Spec B ⟶ Y),
            α.hom.FormallySmooth ∧ α.hom.EssFiniteType ∧ Mono ι ∧
              ι ≫ f = Spec.map α ≫ X.fromSpecStalk p ∧ Spec.map σ ≫ ι = X.fromSpecStalk p ≫ s ∧
              ∀ (R R' : CommRingCat.{0}) [IsLocalRing R] (π : R' ⟶ R) (φ : X.presheaf.stalk p ⟶ R) (v : Spec R' ⟶ Y),
                Function.Surjective π.hom → (∀ x, π.hom x = 0 → x * x = 0) →
                  Spec.map π ≫ v = Spec.map φ ≫ X.fromSpecStalk p ≫ s → ∃ g : B ⟶ R', v = Spec.map g ≫ ι := by
  open AlgebraicGeometry CategoryTheory in
  intro X Y f _ s hs p
  have hp : f (s p) = p := by
    rw [← Scheme.Hom.comp_apply, hs]; rfl
  have hi : Inseparable p (f (s p)) := Inseparable.of_eq hp.symm
  have hfs : (f.stalkMap (s p)).hom.FormallySmooth := by
    rw [← Scheme.Hom.mem_smoothLocus, f.smoothLocus_eq_top]; trivial
  have hft : (f.stalkMap (s p)).hom.EssFiniteType := LocallyOfFiniteType.stalkMap f (s p)
  refine ⟨Y.presheaf.stalk (s p), (X.presheaf.stalkCongr hi).hom ≫ f.stalkMap (s p),
    s.stalkMap p, Y.fromSpecStalk (s p), ?_, ?_, inferInstance, ?_, ?_, ?_⟩
  · exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).mpr hfs
  · exact (RingHom.EssFiniteType.respectsIso.cancel_left_isIso _ _).mpr hft
  · have h : Spec.map (X.presheaf.stalkCongr hi).hom ≫ X.fromSpecStalk p =
        X.fromSpecStalk (f (s p)) :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hi.specializes'
    rw [Spec.map_comp, Category.assoc, h, Scheme.SpecMap_stalkMap_fromSpecStalk]
  · exact Scheme.SpecMap_stalkMap_fromSpecStalk s
  · intro R R' _ π φ v hπ hk hv
    haveI : IsLocalHom π.hom := UpperTheory.isLocalHom_of_square_zero π.hom hπ hk
    haveI : IsLocalRing R' := π.hom.domain_isLocalRing
    have hsp : v (IsLocalRing.closedPoint R') ⤳ s p := by
      have h1 : v (IsLocalRing.closedPoint R') =
          s (X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R))) := by
        have h3 : v (Spec.map π (IsLocalRing.closedPoint R)) =
            s (X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R))) :=
          congrArg (fun k : Spec R ⟶ Y => k (IsLocalRing.closedPoint R)) hv
        exact (congrArg v (Spec_closedPoint (f := π)).symm).trans h3
      have h2 : X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R)) ⤳ p := by
        have : X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R)) ∈
            Set.range (X.fromSpecStalk p) := ⟨_, rfl⟩
        rwa [Scheme.range_fromSpecStalk] at this
      rw [h1]
      exact h2.map s.continuous
    refine ⟨Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo v, ?_⟩
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
end
