module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.RingTheory.Localization.Away.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

section

namespace GlobalTheory

theorem away_range_le_of_dvd (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R)
    (hcc : c ∣ c') (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P)
    (hκ : κ.comp (algebraMap R (Localization.Away c)) = g)
    (hκ' : κ'.comp (algebraMap R (Localization.Away c')) = g) : κ.range ≤ κ'.range := by
  have hu : IsUnit (algebraMap R (Localization.Away c') c) :=
    isUnit_of_dvd_unit (map_dvd _ hcc) (IsLocalization.Away.algebraMap_isUnit c')
  let φ : Localization.Away c →+* Localization.Away c' := IsLocalization.Away.lift c hu
  have hφ : (κ'.comp φ) = κ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers c)
    rw [hκ, RingHom.comp_assoc]
    have : φ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.Away c') :=
      IsLocalization.Away.lift_comp c hu
    rw [this, hκ']
  rintro y ⟨x, rfl⟩
  exact ⟨φ x, by rw [← hφ]; rfl⟩

theorem away_range_le_of_dvd' : ∀ (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R), c ∣ c' → ∀ (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P), κ.comp (algebraMap R (Localization.Away c)) = g → κ'.comp (algebraMap R (Localization.Away c')) = g → κ.range ≤ κ'.range :=
  fun R _ P _ g c c' h κ κ' hκ hκ' => away_range_le_of_dvd R P g c c' h κ κ' hκ hκ'

end GlobalTheory
end

section

open Filter Topology

namespace GlobalTheory
namespace SquareZeroSum

open TrivSqZeroExt

theorem isNilpotent_comap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal B)
    (hI : IsNilpotent I) (hf : ∀ x y, f x = 0 → f y = 0 → x * y = 0) :
    IsNilpotent (I.comap f) := by
  obtain ⟨m, hm⟩ := hI
  have h1 : (I.comap f) ^ m ≤ RingHom.ker f := by
    have := Ideal.le_comap_pow f (K := I) m
    rw [hm] at this
    exact this
  refine ⟨m + m, ?_⟩
  rw [pow_add, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  exact (Submodule.mem_bot _).2 (hf r s (h1 hr) (h1 hs))

theorem isNilpotent_of_comap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (I : Ideal B) (hI : IsNilpotent (I.comap f)) :
    IsNilpotent I := by
  obtain ⟨m, hm⟩ := hI
  refine ⟨m, ?_⟩
  rw [← Ideal.map_comap_of_surjective f hf I, ← Ideal.map_pow, hm]
  simp

section
variable {K : Type} [Fintype K] [DecidableEq K] {D : Type} [CommRing D] (δ : K → D)

theorem prod_fst_snd {ι : Type} [DecidableEq ι] (s : ι → K) (t : Finset ι) :
    (∏ a ∈ t, ((inl (δ (s a)) : TrivSqZeroExt D (K → D)) - inr (Pi.single (s a) 1))).fst
        = ∏ a ∈ t, δ (s a) ∧
      ∑ k, (∏ a ∈ t, ((inl (δ (s a)) : TrivSqZeroExt D (K → D))
          - inr (Pi.single (s a) 1))).snd k * δ k = -(t.card : D) * ∏ a ∈ t, δ (s a) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    generalize (∏ a ∈ t, ((inl (δ (s a)) : TrivSqZeroExt D (K → D))
      - inr (Pi.single (s a) 1))) = P at h1 h2 ⊢
    refine ⟨by simp [h1], ?_⟩
    have h3 : ∀ k, ((((inl (δ (s a)) : TrivSqZeroExt D (K → D))
        - inr (Pi.single (s a) 1))) * P).snd k * δ k
        = δ (s a) * (P.snd k * δ k) - P.fst * ((Pi.single (s a) 1 : K → D) k * δ k) := by
      intro k
      simp [snd_mul]
      ring
    simp only [h3, Finset.sum_sub_distrib, ← Finset.mul_sum, h2, h1]
    simp [Pi.single_apply]
    ring

end

theorem step (N : ℕ) {K : Type} [Fintype K] (D : Type) [CommRing D] [Algebra ℂ D]
    (π : D →ₐ[ℂ] ℂ) (δ : K → D) (hπ : IsNilpotent (RingHom.ker π)) (hδ : ∀ a, π (δ a) = 0)
    (hs : ∀ s : Fin (N + 1 + 1) → K, ∏ a, δ (s a) = 0) :
    ∃ (D' : Type) (_ : CommRing D') (_ : Algebra ℂ D') (ι : D →ₐ[ℂ] D') (π' : D' →ₐ[ℂ] ℂ)
      (ν : K → D'), Function.Injective ι ∧ (∀ d, π' (ι d) = π d) ∧
      IsNilpotent (RingHom.ker π') ∧ (∀ a, π' (ν a) = 0) ∧ (∀ a b, ν a * ν b = 0) ∧
      ∀ s : Fin (N + 1) → K, ∏ a, (ι (δ (s a)) - ν (s a)) = 0 := by
  classical
  let g : (Fin (N + 1) → K) → TrivSqZeroExt D (K → D) := fun s =>
    ∏ a, ((inl (δ (s a)) : TrivSqZeroExt D (K → D)) - inr (Pi.single (s a) 1))
  let Q : Ideal (TrivSqZeroExt D (K → D)) := Ideal.span (Set.range g)
  let E : TrivSqZeroExt D (K → D) → D := fun x => ((N + 1 : ℕ) : D) * x.fst + ∑ k, x.snd k * δ k
  have hEadd : ∀ x y, E (x + y) = E x + E y := by
    intro x y
    simp only [E, fst_add, snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  have hg : ∀ s c, E (c * g s) = 0 := by
    intro s c
    obtain ⟨h1, h2⟩ := prod_fst_snd δ s Finset.univ
    change (g s).fst = _ at h1
    change ∑ k, (g s).snd k * δ k = _ at h2
    have h3 : ∀ k, (c * g s).snd k * δ k
        = c.fst * ((g s).snd k * δ k) + c.snd k * (δ k * ∏ a, δ (s a)) := by
      intro k
      simp [snd_mul, h1]
      ring
    have h4 : ∀ k, δ k * ∏ a, δ (s a) = 0 := by
      intro k
      have := hs (Fin.cons k s)
      rw [Fin.prod_univ_succ] at this
      simpa using this
    simp only [E, h3, h4, mul_zero, add_zero, ← Finset.mul_sum, h2, fst_mul, h1,
      Finset.card_univ, Fintype.card_fin]
    ring
  have hQ : ∀ x ∈ Q, ∀ c, E (c * x) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨s, rfl⟩ := hx; exact hg s
    | zero => intro c; simp [E]
    | add x y _ _ hx hy => intro c; rw [mul_add, hEadd, hx, hy, add_zero]
    | smul a x _ hx => intro c; rw [smul_eq_mul, ← mul_assoc]; exact hx _
  let p : TrivSqZeroExt D (K → D) →ₐ[ℂ] ℂ := π.comp (fstHom ℂ D (K → D))
  have hp : ∀ x ∈ Q, p x = 0 := by
    have : Q ≤ RingHom.ker p := by
      rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      have h1 : (g s).fst = _ := (prod_fst_snd δ s Finset.univ).1
      simp [p, h1, hδ, map_prod]
    exact this
  refine ⟨TrivSqZeroExt D (K → D) ⧸ Q, inferInstance, inferInstance,
    (Ideal.Quotient.mkₐ ℂ Q).comp (inlAlgHom ℂ D (K → D)), Ideal.Quotient.liftₐ Q p hp,
    fun a => Ideal.Quotient.mk Q (inr (Pi.single a 1)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro d hd
    have hd' : (inl d : TrivSqZeroExt D (K → D)) ∈ Q := Ideal.Quotient.eq_zero_iff_mem.1 hd
    have h := hQ _ hd' 1
    simp only [E, one_mul, fst_inl, snd_inl, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      add_zero] at h
    have hu : IsUnit ((N + 1 : ℕ) : D) := by
      rw [← map_natCast (algebraMap ℂ D)]
      exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero N))).map _
    exact hu.mul_right_eq_zero.1 h
  · intro d
    rfl
  · refine isNilpotent_of_comap (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective _ ?_
    have := isNilpotent_comap (fstHom ℂ D (K → D)).toRingHom _ hπ (by
      intro x y hx hy
      have hx' : x.fst = 0 := hx
      have hy' : y.fst = 0 := hy
      ext1 <;> simp [snd_mul, hx', hy'])
    exact this
  · intro a
    change p (inr _) = 0
    simp [p]
  · intro a b
    rw [← map_mul, inr_mul_inr, map_zero]
  · intro s
    have : Ideal.Quotient.mk Q (g s) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨s, rfl⟩)
    rw [← this]
    simp only [g, map_prod, map_sub]
    rfl

theorem exists_sum_sq_zero : ∀ (N : ℕ) {K : Type} [Fintype K] (D : Type) [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) (δ : K → D), IsNilpotent (RingHom.ker π) → (∀ a, π (δ a) = 0) → (∀ s : Fin (N + 1) → K, ∏ a, δ (s a) = 0) → ∃ (D' : Type) (_ : CommRing D') (_ : Algebra ℂ D') (ι : D →ₐ[ℂ] D') (π' : D' →ₐ[ℂ] ℂ) (n : Fin N → K → D'), Function.Injective ι ∧ (∀ d, π' (ι d) = π d) ∧ IsNilpotent (RingHom.ker π') ∧ (∀ j a, π' (n j a) = 0) ∧ (∀ j a b, n j a * n j b = 0) ∧ ∀ a, ι (δ a) = ∑ j, n j a := by
  intro N
  induction N with
  | zero =>
    intro K _ D _ _ π δ hπ hδ hs
    refine ⟨D, inferInstance, inferInstance, AlgHom.id ℂ D, π, fun j => j.elim0,
      Function.injective_id, fun _ => rfl, hπ, fun j => j.elim0, fun j => j.elim0, ?_⟩
    intro a
    simpa using hs (fun _ => a)
  | succ N ih =>
    intro K _ D _ _ π δ hπ hδ hs
    obtain ⟨D₁, _, _, ι₁, π₁, ν, hi₁, hc₁, hn₁, hν, hνν, hs₁⟩ := step N D π δ hπ hδ hs
    obtain ⟨D₂, _, _, ι₂, π₂, n, hi₂, hc₂, hn₂, hn, hnn, hsum⟩ :=
      ih D₁ π₁ (fun a => ι₁ (δ a) - ν a) hn₁ (fun a => by simp [hc₁, hδ, hν]) hs₁
    refine ⟨D₂, inferInstance, inferInstance, ι₂.comp ι₁, π₂,
      Fin.cons (fun a => ι₂ (ν a)) n, hi₂.comp hi₁, fun d => by simp [hc₂, hc₁], hn₂, ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases (fun a => ?_) (fun j a => ?_) j
      · simp [hc₂, hν]
      · simp [hn]
    · intro j
      refine Fin.cases (fun a b => ?_) (fun j a b => ?_) j
      · simp [← map_mul, hνν]
      · simp [hnn]
    · intro a
      rw [Fin.sum_univ_succ]
      simp [← hsum]

end SquareZeroSum
end GlobalTheory
end

section

open AlgebraicGeometry

namespace GlobalTheory

theorem affineOpen_exists_field_point_basicOpen_commonDenom :
    ∀ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (p : X), p ∈ U →
      ∃ (K : Type) (_ : Field K) (ψ : Γ(X, U) →+* K), (∀ g, ψ g ≠ 0 → p ∈ X.basicOpen g) ∧
        ∀ (ι : Type) [Fintype ι] (m : ι → K), ∃ (a : ι → Γ(X, U)) (t : Γ(X, U)),
          ψ t ≠ 0 ∧ ∀ i, m i * ψ t = ψ (a i) := by
  intro X U hU p hp
  classical
  let P := hU.primeIdealOf ⟨p, hp⟩
  haveI : P.asIdeal.IsPrime := P.isPrime
  let K := FractionRing (Γ(X, U) ⧸ P.asIdeal)
  let ψ : Γ(X, U) →+* K := (algebraMap (Γ(X, U) ⧸ P.asIdeal) K).comp (Ideal.Quotient.mk P.asIdeal)
  have hψ : ∀ g, ψ g ≠ 0 ↔ g ∉ P.asIdeal := by
    intro g
    simp only [ψ, RingHom.comp_apply, ne_eq]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨K, inferInstance, ψ, ?_, ?_⟩
  · intro g hg
    have h1 : P ∈ PrimeSpectrum.basicOpen g := (hψ g).1 hg
    rw [← hU.fromSpec_preimage_basicOpen] at h1
    have h2 : hU.fromSpec P = p := hU.fromSpec_primeIdealOf ⟨p, hp⟩
    have h3 : hU.fromSpec P ∈ X.basicOpen g := h1
    rwa [h2] at h3
  · intro ι _ m
    have hrep : ∀ i, ∃ b s : Γ(X, U), ψ s ≠ 0 ∧ m i * ψ s = ψ b := by
      intro i
      obtain ⟨⟨b', ⟨s', hs'⟩⟩, he⟩ := IsLocalization.mk'_surjective
        (nonZeroDivisors (Γ(X, U) ⧸ P.asIdeal)) (m i)
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
      refine ⟨b, s, ?_, ?_⟩
      · simp only [ψ, RingHom.comp_apply, ne_eq]
        exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs'
      · rw [← he]
        simp only [ψ, RingHom.comp_apply]
        exact IsLocalization.mk'_spec _ _ _
    choose b s hs hbs using hrep
    refine ⟨fun i => b i * ∏ j ∈ Finset.univ.erase i, s j, ∏ j, s j, ?_, ?_⟩
    · rw [map_prod]
      exact Finset.prod_ne_zero_iff.2 (fun j _ => hs j)
    · intro i
      rw [map_prod, ← Finset.mul_prod_erase Finset.univ (fun j => ψ (s j)) (Finset.mem_univ i),
        ← mul_assoc, hbs i, map_mul, map_prod]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem exists_separating_basicOpen_functions : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (F : Finset X), (∀ a ∈ F, a ∈ U) → (∀ a ∈ F, ∀ b ∈ F, a ⤳ b → a = b) → ∀ W : X → X.Opens, (∀ a ∈ F, a ∈ W a) → ∃ f : X → Γ(X, U), ∀ a ∈ F, a ∈ X.basicOpen (f a) ∧ X.basicOpen (f a) ≤ W a ∧ ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen (f a) := by
  intro X U hU F hFU hsp W hW
  classical
  have key : ∀ a ∈ F, ∃ g : Γ(X, U), a ∈ X.basicOpen g ∧ X.basicOpen g ≤ W a ∧
      ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen g := by
    intro a ha
    let C : Set X := ⋃ b ∈ F.erase a, closure {b}
    have hC : IsClosed C := isClosed_biUnion_finset (fun b _ => isClosed_closure)
    let V : X.Opens := W a ⊓ ⟨Cᶜ, hC.isOpen_compl⟩
    have haC : a ∉ C := by
      simp only [C, Set.mem_iUnion, not_exists]
      intro b hb hab
      have hb' := Finset.mem_erase.mp hb
      exact hb'.1 (hsp b hb'.2 a ha (specializes_iff_mem_closure.mpr hab))
    have haV : a ∈ V := ⟨hW a ha, haC⟩
    obtain ⟨g, hgV, hag⟩ := hU.exists_basicOpen_le ⟨a, haV⟩ (hFU a ha)
    refine ⟨g, hag, le_trans hgV inf_le_left, ?_⟩
    intro b hb hba hbg
    have hbV : b ∈ V := hgV hbg
    apply hbV.2
    simp only [C, Set.mem_iUnion]
    exact ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩, subset_closure rfl⟩
  choose! f hf using key
  exact ⟨f, hf⟩

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.SectionsPinch

theorem app_eq_of_factor {X Y : Scheme.{0}} {A : CommRingCat.{0}} (κ : Spec A ⟶ Y) [IsOpenImmersion κ]
    (j : X ⟶ Y) (O : X.Opens) (q : A ⟶ Γ(X, O)) (hO : j ⁻¹ᵁ κ.opensRange = O)
    (hfac : O.ι ≫ j = (O.toSpecΓ ≫ Spec.map q) ≫ κ) :
    j.app κ.opensRange ≫ X.presheaf.map (homOfLE hO.ge).op =
      κ.appLE κ.opensRange ⊤ (fun x _ ↦ ⟨x, rfl⟩) ≫ (Scheme.ΓSpecIso A).hom ≫ q := by
  have key : ∀ (f g : O.toScheme ⟶ Y), f = g → ∀ e e',
      f.appLE κ.opensRange ⊤ e = g.appLE κ.opensRange ⊤ e' := by
    rintro f g rfl e e'; rfl
  have hle' : ⊤ ≤ (O.ι ≫ j) ⁻¹ᵁ κ.opensRange := fun x _ ↦
    (hO.ge x.2 : _)
  rw [← cancel_mono O.topIso.inv]
  have lhs : (j.app κ.opensRange ≫ X.presheaf.map (homOfLE hO.ge).op) ≫ O.topIso.inv =
      (O.ι ≫ j).appLE κ.opensRange ⊤ hle' := by
    show j.appLE κ.opensRange O hO.ge ≫ O.topIso.inv = _
    rw [← Scheme.Hom.appLE_comp_appLE O.ι j κ.opensRange O ⊤ hO.ge (fun x _ ↦ x.2)]
    congr 1
    rw [Scheme.Opens.topIso_inv]
    exact (Scheme.Opens.ι_appLE O O ⊤ _).symm
  rw [lhs, key _ _ hfac hle' (hfac ▸ hle')]
  simp only [Category.assoc]
  rw [← Scheme.ΓSpecIso_naturality_assoc, ← Scheme.Opens.toSpecΓ_appTop]
  rw [← Scheme.Hom.appLE_comp_appLE O.toSpecΓ (Spec.map q ≫ κ) κ.opensRange ⊤ ⊤
      (fun x _ ↦ ⟨_, rfl⟩) le_top,
    ← Scheme.Hom.appLE_comp_appLE (Spec.map q) κ κ.opensRange ⊤ ⊤ (fun x _ ↦ ⟨x, rfl⟩) le_top,
    Category.assoc]
  have top : ∀ {P Q : Scheme.{0}} (f : P ⟶ Q) (e : ⊤ ≤ f ⁻¹ᵁ ⊤), f.appLE ⊤ ⊤ e = f.appTop :=
    fun f _ ↦ Scheme.Hom.appLE_eq_app (f := f) (U := ⊤)
  rw [← top (Spec.map q) le_top, ← top O.toSpecΓ le_top]

end GlobalTheory.SectionsPinch
end

section

open AlgebraicGeometry CategoryTheory Limits Topology

namespace GlobalTheory

theorem fibre_dense_affine_chart_primes : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens) (U : X.Opens) (V : T.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : U ≤ p ⁻¹ᵁ V),
    (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) →
    ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) →
    ∀ q : PrimeSpectrum Γ(X, U), q ∈ closure ({P : PrimeSpectrum Γ(X, U) | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (p.appLE V U e).hom ⁻¹' {PrimeSpectrum.comap (p.appLE V U e).hom q}) := by
  intro X T p W U V hU hV e hW b hb q
  set f := hU.fromSpec with hf
  have hemb : IsOpenEmbedding f := f.isOpenEmbedding

  have hmemU : ∀ P : PrimeSpectrum Γ(X, U), f P ∈ U := fun P => hU.range_fromSpec.le ⟨P, rfl⟩
  have hprime : ∀ P : PrimeSpectrum Γ(X, U), hU.primeIdealOf ⟨f P, hmemU P⟩ = P := fun P =>
    hemb.injective (hU.fromSpec_primeIdealOf _)
  have hcomap : ∀ P : PrimeSpectrum Γ(X, U),
      PrimeSpectrum.comap (p.appLE V U e).hom P = hV.primeIdealOf ⟨p (f P), e (hmemU P)⟩ := by
    intro P
    have := IsAffineOpen.comap_primeIdealOf_appLE (f := p) V hV U hU e (hmemU P)
    rw [hprime P] at this
    exact this
  set A : Set X := (W : Set X) ∩ p ⁻¹' {p (f q)} with hA
  have hq : q ∈ closure (f ⁻¹' A) := by
    rw [← hemb.isOpenMap.preimage_closure_eq_closure_preimage hemb.continuous]
    exact hW (f q)
  refine closure_mono ?_ hq
  intro P hP
  obtain ⟨hPW, hPp⟩ := hP
  refine ⟨?_, ?_⟩
  · let _ : Algebra Γ(X, U) (X.presheaf.stalk (f P)) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨f P, hmemU P⟩
    haveI hloc : IsLocalization P.asIdeal.primeCompl (X.presheaf.stalk (f P)) := hU.isLocalization_stalk' P (hmemU P)
    have h0 : algebraMap Γ(X, U) (X.presheaf.stalk (f P)) b = 0 := hb (f P) (hmemU P) hPW
    obtain ⟨⟨s, hs⟩, hsb⟩ := (IsLocalization.map_eq_zero_iff P.asIdeal.primeCompl _ b).mp h0
    exact ⟨s, hs, hsb⟩
  · show PrimeSpectrum.comap (p.appLE V U e).hom P = PrimeSpectrum.comap (p.appLE V U e).hom q
    rw [hcomap P, hcomap q]
    have : p (f P) = p (f q) := hPp
    congr 2

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem spec_local_hom_factors_affineOpen : ∀ (X : Scheme.{0}) (V : X.Opens) (hV : IsAffineOpen V)
    (A : Type) [CommRing A] [IsLocalRing A]
    (f : Spec (CommRingCat.of A) ⟶ X), f (IsLocalRing.closedPoint A) ∈ V →
    ∃ g : Γ(X, V) →+* A, f = Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec := by
  intro X V hV A _ _ f hf
  have H : Set.range f ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have hs : x ⤳ IsLocalRing.closedPoint A := IsLocalRing.specializes_closedPoint x
    exact (hs.map f.continuous).mem_open V.isOpen hf
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec f H)).hom, ?_⟩
  simp [IsOpenImmersion.lift_fac]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace GlobalTheory.HilbAff

theorem idealSheafData_ext_of_openCover {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0})
    (f : ∀ i, V i ⟶ X) (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : X, ∃ i y, f i y = x)
    (I I' : X.IdealSheafData) (h : ∀ i, I.comap (f i) = I'.comap (f i)) : I = I' := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := Σ i, (V i).affineOpens)
    (fun p => ⟨(f p.1) ''ᵁ p.2.1, p.2.2.image_of_isOpenImmersion (f p.1)⟩) ?_ ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, y, rfl⟩ := hcov x
    have hy : y ∈ (⊤ : (V i).Opens) := trivial
    rw [← iSup_affineOpens_eq_top (V i)] at hy
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, W⟩, ⟨y, hW, rfl⟩⟩
  · rintro ⟨i, W⟩
    have e := congrArg (fun J => J.ideal W) (h i)
    simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at e
    exact Ideal.comap_injective_of_surjective _
      ((ConcreteCategory.bijective_of_isIso ((f i).appIso W).inv).2) e

end GlobalTheory.HilbAff
end
