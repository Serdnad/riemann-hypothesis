module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.Away.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartHom

theorem exists_hom_adjoin_inv {σ Ω R : Type*} [Field Ω] [CharZero Ω] [CommRing R]
    (u : σ → Ω) (θ : MvPolynomial σ ℚ →+* R)
    (hker : ∀ G : MvPolynomial σ ℚ, aeval u G = (0 : Ω) → θ G = 0)
    (F : MvPolynomial σ ℚ) (hF : IsUnit (θ F))
    (S : Subalgebra ℚ Ω) (hS : S = Algebra.adjoin ℚ (insert (aeval u F : Ω)⁻¹ (Set.range u))) :
    ∃ ψ : S →+* R, ∀ (G : MvPolynomial σ ℚ) (s : S), (s : Ω) = aeval u G → ψ s = θ G := by
  classical
  by_cases hf : (aeval u F : Ω) = 0
  · have h0 : θ F = 0 := hker F hf
    have hR : Subsingleton R := by
      have : IsUnit (0 : R) := h0 ▸ hF
      exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp this)
    refine ⟨{ toFun := fun _ => 0, map_one' := Subsingleton.elim _ _, map_mul' := fun _ _ => Subsingleton.elim _ _,
              map_zero' := rfl, map_add' := fun _ _ => Subsingleton.elim _ _ }, fun _ _ _ => Subsingleton.elim _ _⟩
  · let B := Localization.Away F
    have hunit : ∀ y : Submonoid.powers F, IsUnit (aeval u (y : MvPolynomial σ ℚ) : Ω) := by
      rintro ⟨_, n, rfl⟩
      simpa using (IsUnit.mk0 _ hf).pow n
    let Φ : B →ₐ[ℚ] Ω := IsLocalization.liftAlgHom (M := Submonoid.powers F) (f := aeval u) hunit
    have hΦ : ∀ a : MvPolynomial σ ℚ, Φ (algebraMap _ B a) = aeval u a := fun a =>
      by simp [Φ, IsLocalization.liftAlgHom_apply]
    let Θ : B →+* R := IsLocalization.Away.lift F hF
    have hΘ : ∀ a : MvPolynomial σ ℚ, Θ (algebraMap _ B a) = θ a := fun a =>
      IsLocalization.Away.lift_eq F hF a
    have hnum : ∀ z : B, ∃ (n : ℕ) (a : MvPolynomial σ ℚ), z * algebraMap _ B (F ^ n) = algebraMap _ B a := by
      intro z
      obtain ⟨n, a, h⟩ := IsLocalization.Away.surj F z
      exact ⟨n, a, by simpa using h⟩
    have hmem : ∀ a : MvPolynomial σ ℚ, (aeval u a : Ω) ∈ S := by
      intro a
      have : (aeval u a : Ω) ∈ Algebra.adjoin ℚ (Set.range u) := by
        rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨a, rfl⟩
      rw [hS]
      exact Algebra.adjoin_mono (Set.subset_insert _ _) this
    have hinv : (aeval u F : Ω)⁻¹ ∈ S := by
      rw [hS]; exact Algebra.subset_adjoin (Set.mem_insert _ _)
    have hΦS : ∀ z : B, Φ z ∈ S := by
      intro z
      obtain ⟨n, a, h⟩ := hnum z
      have h2 := congrArg Φ h
      rw [map_mul, hΦ, hΦ, map_pow] at h2
      have : Φ z = aeval u a * ((aeval u F : Ω)⁻¹) ^ n := by
        rw [← h2, inv_pow, _root_.mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hf), _root_.mul_one]
      rw [this]
      exact S.mul_mem (hmem a) (S.pow_mem hinv n)
    let Φ' : B →+* S := (Φ : B →+* Ω).codRestrict S.toSubsemiring hΦS
    have hΦ' : ∀ z, ((Φ' z : S) : Ω) = Φ z := fun _ => rfl
    have hsurj : Function.Surjective Φ' := by
      have hle : S ≤ Φ.range := by
        rw [hS]
        refine Algebra.adjoin_le ?_
        rintro _ (rfl | ⟨p, rfl⟩)
        · have hu : IsUnit (algebraMap _ B F) := IsLocalization.Away.algebraMap_isUnit F
          obtain ⟨v, hv⟩ := hu
          refine ⟨(↑v⁻¹ : B), ?_⟩
          have h1 : Φ (↑v⁻¹ : B) * aeval u F = 1 := by
            rw [← hΦ, ← hv, ← map_mul]; simp
          exact eq_inv_of_mul_eq_one_left h1
        · exact ⟨algebraMap (MvPolynomial σ ℚ) B (X p), (hΦ (X p)).trans (aeval_X u p)⟩
      intro s
      obtain ⟨z, hz⟩ := hle s.2
      exact ⟨z, Subtype.ext hz⟩
    have hkerΘ : RingHom.ker Φ' ≤ RingHom.ker Θ := by
      intro z hz
      rw [RingHom.mem_ker] at hz ⊢
      have hz0 : Φ z = 0 := by
        have := congrArg (Subtype.val) hz
        simpa [hΦ'] using this
      obtain ⟨n, a, h⟩ := hnum z
      have h2 := congrArg Φ h
      rw [map_mul, hz0, zero_mul, hΦ] at h2
      have ha : θ a = 0 := hker a h2.symm
      have h3 := congrArg Θ h
      rw [map_mul, hΘ, hΘ, ha, map_pow] at h3
      exact (hF.pow n).mul_left_eq_zero.mp h3
    refine ⟨RingHom.liftOfSurjective Φ' hsurj ⟨Θ, hkerΘ⟩, fun G s hs => ?_⟩
    have hsG : s = Φ' (algebraMap _ B G) := Subtype.ext (by rw [hΦ', hΦ, hs])
    rw [hsG, RingHom.liftOfRightInverse_comp_apply]
    exact hΘ G

end GlobalTheory.CompanionTheory.Ar.ChartHom
end

section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HopfPrim

variable {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A]

theorem comul_pow_of_primitive (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) (i : ℕ) :
    Coalgebra.comul (R := k) (f ^ i) =
      ∑ l ∈ Finset.range (i + 1), (i.choose l : k) • ((f ^ l) ⊗ₜ[k] (f ^ (i - l))) := by
  have h1 : Coalgebra.comul (R := k) (f ^ i) = (f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) ^ i := by
    rw [← hf, ← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply]
  rw [h1, add_pow]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_pow, mul_one, one_mul,
    Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_comm]

noncomputable def convPow (y : A →ₗ[k] k) : ℕ → (A →ₗ[k] k)
  | 0 => Coalgebra.counit
  | m + 1 => LinearMap.mul' k k ∘ₗ TensorProduct.map y (convPow y m) ∘ₗ Coalgebra.comul

theorem convPow_succ_pow (y : A →ₗ[k] k) (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) (m i : ℕ) :
    convPow y (m + 1) (f ^ i) =
      ∑ l ∈ Finset.range (i + 1), (i.choose l : k) * (y (f ^ l) * convPow y m (f ^ (i - l))) := by
  simp only [convPow, LinearMap.comp_apply]

  rw [comul_pow_of_primitive f hf i, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [map_smul, map_smul, TensorProduct.map_tmul, LinearMap.mul'_apply, smul_eq_mul]

theorem convPow_pow (y : A →ₗ[k] k) (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f)
    (hy1 : y 1 = 0) (hyf : y f = 1) (m : ℕ) :
    (∀ i < m, convPow y m (f ^ i) = 0) ∧ convPow y m (f ^ m) = (m.factorial : k) := by
  induction m with
  | zero =>
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    simp [convPow]
  | succ m ih =>
    have hterm : ∀ i ≤ m + 1, ∀ l ∈ Finset.range (i + 1), l ≠ 1 →
        (i.choose l : k) * (y (f ^ l) * convPow y m (f ^ (i - l))) = 0 := by
      intro i hi l hl hl1
      rcases Nat.lt_or_ge l 2 with h | h
      · have : l = 0 := by omega
        subst this
        simp [hy1]
      · have hlt : i - l < m := by
          have := Finset.mem_range.mp hl
          omega
        rw [ih.1 _ hlt, mul_zero, mul_zero]
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [convPow_succ_pow y f hf m i]
      refine Finset.sum_eq_zero (fun l hl => ?_)
      by_cases hl1 : l = 1
      · subst hl1
        have hlt : i - 1 < m := by
          have := Finset.mem_range.mp hl
          omega
        rw [ih.1 _ hlt, mul_zero, mul_zero]
      · exact hterm i hi.le l hl hl1
    · rw [convPow_succ_pow y f hf m (m + 1),
        Finset.sum_eq_single 1 (fun l hl hl1 => hterm (m + 1) le_rfl l hl hl1)
          (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
      rw [pow_one, hyf, Nat.add_sub_cancel, ih.2, Nat.choose_one_right, Nat.factorial_succ]
      push_cast
      ring

theorem counit_eq_zero_of_primitive [Nontrivial A] (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) :
    Coalgebra.counit (R := k) f = 0 := by
  have key := congrArg (fun t => TensorProduct.lid k A (LinearMap.rTensor A Coalgebra.counit t)) hf
  simp only [Coalgebra.rTensor_counit_comul, map_add (f := _), LinearMap.rTensor_tmul,
    TensorProduct.lid_tmul, Bialgebra.counit_one, one_smul] at key
  have h2 : Coalgebra.counit (R := k) f • (1 : A) = 0 := by
    have := congrArg (· - f) key
    simpa using this.symm
  rw [Algebra.smul_def, mul_one] at h2
  exact (algebraMap k A).injective (h2.trans (map_zero _).symm)

theorem exists_form_of_primitive (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) (hf0 : f ≠ 0) :
    ∃ y : A →ₗ[k] k, y 1 = 0 ∧ y f = 1 := by
  have : Nontrivial A := nontrivial_of_ne f 0 hf0
  have hε := counit_eq_zero_of_primitive f hf
  let p : Submodule k A := k ∙ (1 : A)
  have hfp : Submodule.Quotient.mk (p := p) f ≠ 0 := by
    rw [ne_eq, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
    rintro ⟨a, rfl⟩
    apply hf0
    rw [map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one] at hε
    rw [hε, zero_smul]
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k (A ⧸ p), φ (Submodule.Quotient.mk f) ≠ 0 := by
    by_contra h
    push Not at h
    exact hfp ((Module.forall_dual_apply_eq_zero_iff k _).mp h)
  refine ⟨(φ (Submodule.Quotient.mk f))⁻¹ • (φ ∘ₗ p.mkQ), ?_, ?_⟩
  · have h1 : Submodule.Quotient.mk (p := p) (1 : A) = 0 :=
      (Submodule.Quotient.mk_eq_zero p).mpr (Submodule.mem_span_singleton_self 1)
    simp [h1]
  · simp [inv_mul_cancel₀ hφ]

theorem powers_indep_of_primitive :
    ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A] (f : A),
    Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f → f ≠ 0 →
    ∀ c : ℕ → k, ∑ i ∈ Finset.range p, c i • f ^ i = 0 → ∀ i < p, c i = 0 := by
  intro k _ p _ _ A _ _ _ _ f hf hf0 c hsum
  obtain ⟨y, hy1, hyf⟩ := exists_form_of_primitive f hf hf0
  have key : ∀ m < p, (∀ i, m < i → i < p → c i = 0) → c m = 0 := by
    intro m hm hgt
    have h := congrArg (convPow y m) hsum

    rw [map_sum, map_zero] at h
    simp only [map_smul, smul_eq_mul] at h
    rw [Finset.sum_eq_single m] at h
    · rw [(convPow_pow y f hf hy1 hyf m).2] at h
      have hfact : (m.factorial : k) ≠ 0 := by
        rw [ne_eq, CharP.cast_eq_zero_iff k p, Nat.Prime.dvd_factorial (Fact.out)]
        omega
      exact (mul_eq_zero.mp h).resolve_right hfact
    · intro i hi hne
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · rw [(convPow_pow y f hf hy1 hyf m).1 i h', mul_zero]
      · rw [hgt i h' (Finset.mem_range.mp hi), zero_mul]
    · intro h'
      exact absurd (Finset.mem_range.mpr hm) h'
  have hall : ∀ n, ∀ i < p, p - 1 - i < n → c i = 0 := by
    intro n
    induction n with
    | zero => intro i _ h; omega
    | succ n ih =>
      intro i hi hn
      exact key i hi (fun j hij hj => ih j hj (by omega))
  intro i hi
  exact hall p i hi (by omega)

end GlobalTheory.CompanionTheory.HopfPrim
end

section

namespace GlobalTheory.CompanionTheory.BasicCover

theorem exists_uniform_bound {J : Type} [Finite J] (P : J → ℕ → Prop)
    (mono : ∀ j n m, n ≤ m → P j n → P j m) (h : ∀ j, ∃ n, P j n) : ∃ N, ∀ j, P j N := by
  classical
  cases nonempty_fintype J
  choose n hn using h
  exact ⟨∑ j, n j, fun j => mono j _ _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)) (hn j)⟩

theorem pow_smul_eq_zero_mono {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (t : R) (y : M) {n m : ℕ} (hnm : n ≤ m) (h : t ^ n • y = 0) : t ^ m • y = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [pow_add, mul_comm, mul_smul, h, smul_zero]

theorem exists_pow_smul_eq_zero {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (t : R) (φ : M →ₗ[R] M')
    [IsLocalizedModule (Submonoid.powers t) φ] (y : M) (h : φ y = 0) :
    ∃ n : ℕ, t ^ n • y = 0 := by
  obtain ⟨⟨c, hc⟩, hc'⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers t) (f := φ)
    (x₁ := y) (x₂ := 0) (by rw [h, map_zero])
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hc
  exact ⟨n, by simpa [Submonoid.smul_def] using hc'⟩

theorem exists_pow_smul_eq_map {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (t : R) (φ : M →ₗ[R] M')
    [IsLocalizedModule (Submonoid.powers t) φ] (z : M') :
    ∃ (n : ℕ) (y : M), t ^ n • z = φ y := by
  obtain ⟨⟨y, ⟨c, hc⟩⟩, hy⟩ := IsLocalizedModule.surj (Submonoid.powers t) φ z
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hc
  exact ⟨n, y, by simpa [Submonoid.smul_def] using hy⟩

theorem isLocalizedModule_of_basic_cover : ∀ (R E : Type) [CommRing R] [AddCommGroup E] [Module R E] (J : Type) [Finite J] (f : J → R), Ideal.span (Set.range f) = ⊤ →
  ∀ (F : {g : R // ∃ i, f i ∣ g} → Type) [∀ g, AddCommGroup (F g)] [∀ g, Module R (F g)]
    (res : ∀ g g' : {g : R // ∃ i, f i ∣ g}, g.1 ∣ g'.1 → (F g →ₗ[R] F g'))
    (ρ : ∀ g, E →ₗ[R] F g),
    (∀ g (h : g.1 ∣ g.1) y, res g g h y = y) →
    (∀ g g' g'' (h : g.1 ∣ g'.1) (h' : g'.1 ∣ g''.1) (h'' : g.1 ∣ g''.1) y, res g' g'' h' (res g g' h y) = res g g'' h'' y) →
    (∀ g g' (h : g.1 ∣ g'.1) e, res g g' h (ρ g e) = ρ g' e) →
    (∀ g (a : R), a ∣ g.1 → IsUnit (algebraMap R (Module.End R (F g)) a)) →
    (∀ g g' (h : g.1 ∣ g'.1) (t : R), g'.1 = g.1 * t → IsLocalizedModule (Submonoid.powers t) (res g g' h)) →
    (∀ e, (∀ i, ρ ⟨f i, i, dvd_rfl⟩ e = 0) → e = 0) →
    (∀ w : ∀ i, F ⟨f i, i, dvd_rfl⟩,
      (∀ i j, res ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (w i) =
        res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (w j)) →
      ∃ e, ∀ i, ρ ⟨f i, i, dvd_rfl⟩ e = w i) →
    ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (ρ ⟨f i, i, dvd_rfl⟩) := by
  intro R E _ _ _ J _ f _ F _ _ res ρ _ hcomp hrρ hunit hloc hsep hglue i
  have inj : ∀ (g g' : {g : R // ∃ i, f i ∣ g}) (h : g.1 ∣ g'.1) (t : R), g'.1 = g.1 * t → t ∣ g.1 →
      ∀ x, res g g' h x = 0 → x = 0 := by
    intro g g' h t ht htd x hx
    have := hloc g g' h t ht
    obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.BasicCover.exists_pow_smul_eq_zero t (res g g' h) x hx
    have hu : IsUnit (algebraMap R (Module.End R (F g)) (t ^ n)) := by
      rw [map_pow]
      exact (hunit g t htd).pow n
    apply ((Module.End.isUnit_iff _).1 hu).1
    rw [Module.algebraMap_end_apply, hn, map_zero]
  refine ⟨fun x => ?_, fun z => ?_, fun {x₁ x₂} hx => ?_⟩
  · obtain ⟨c, hc⟩ := x
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hc
    show IsUnit (algebraMap R (Module.End R (F ⟨f i, i, dvd_rfl⟩)) (f i ^ n))
    rw [map_pow]
    exact (hunit _ (f i) dvd_rfl).pow n
  · have Pex : ∀ j, ∃ n, (fun j n => ∃ y : F ⟨f j, j, dvd_rfl⟩, f i ^ n • res ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) z = res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) y) j n := by
      intro j
      have := hloc ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (f i) (mul_comm _ _)
      exact GlobalTheory.CompanionTheory.BasicCover.exists_pow_smul_eq_map (f i) _ _
    obtain ⟨N, hN⟩ := GlobalTheory.CompanionTheory.BasicCover.exists_uniform_bound (fun j n => ∃ y : F ⟨f j, j, dvd_rfl⟩, f i ^ n • res ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) z = res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) y)
      (fun j n m hnm hex => by
        obtain ⟨y, hy⟩ := hex
        exact ⟨f i ^ (m - n) • y, by
          rw [map_smul, ← hy, smul_smul, ← pow_add, Nat.sub_add_cancel hnm]⟩) Pex
    choose y hy using hN
    have lift : ∀ j (g'' : {g : R // ∃ i, f i ∣ g}) (h1 : f j ∣ g''.1) (h2 : f i * f j ∣ g''.1)
        (h3 : f i ∣ g''.1), res ⟨f j, j, dvd_rfl⟩ g'' h1 (y j) = f i ^ N • res ⟨f i, i, dvd_rfl⟩ g'' h3 z := by
      intro j g'' h1 h2 h3
      rw [← hcomp ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ g'' (dvd_mul_left _ _) h2 h1 (y j), ← hy j, map_smul,
        hcomp ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ g'' (dvd_mul_right _ _) h2 h3 z]
    have Qex : ∀ p : J × J, ∃ m, f i ^ m • (res ⟨f p.1, p.1, dvd_rfl⟩ ⟨f p.1 * f p.2, p.1, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (y p.1) - res ⟨f p.2, p.2, dvd_rfl⟩ ⟨f p.1 * f p.2, p.1, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (y p.2)) = 0 := by
      rintro ⟨j, k⟩
      dsimp only
      have := hloc ⟨f j * f k, j, dvd_mul_right _ _⟩ ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_right _ _) (f i) rfl
      apply GlobalTheory.CompanionTheory.BasicCover.exists_pow_smul_eq_zero (f i) (res ⟨f j * f k, j, dvd_mul_right _ _⟩ ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_right _ _))
      rw [map_sub, hcomp ⟨f j, j, dvd_rfl⟩ ⟨f j * f k, j, dvd_mul_right _ _⟩ ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_right _ _) (dvd_mul_right _ _)
          (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) (y j),
        hcomp ⟨f k, k, dvd_rfl⟩ ⟨f j * f k, j, dvd_mul_right _ _⟩ ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_left _ _) (dvd_mul_right _ _)
          (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) (y k),
        lift j ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
          (Dvd.intro (f k) (show f i * f j * f k = f j * f k * f i by ring))
          (Dvd.intro (f j * f k) (show f i * (f j * f k) = f j * f k * f i by ring)),
        lift k ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
          (Dvd.intro (f j) (show f i * f k * f j = f j * f k * f i by ring))
          (Dvd.intro (f j * f k) (show f i * (f j * f k) = f j * f k * f i by ring)), sub_self]
    obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.BasicCover.exists_uniform_bound
      (fun (p : J × J) m => f i ^ m • (res ⟨f p.1, p.1, dvd_rfl⟩ ⟨f p.1 * f p.2, p.1, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (y p.1) - res ⟨f p.2, p.2, dvd_rfl⟩ ⟨f p.1 * f p.2, p.1, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (y p.2)) = 0)
      (fun p n m hnm hn => GlobalTheory.CompanionTheory.BasicCover.pow_smul_eq_zero_mono _ _ hnm hn) Qex
    have hii : f i ^ N • z = y i := by
      apply sub_eq_zero.1
      apply inj ⟨f i, i, dvd_rfl⟩ ⟨f i * f i, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (f i) rfl dvd_rfl
      rw [map_sub, map_smul, hy i, sub_self]
    obtain ⟨e, he⟩ := hglue (fun j => f i ^ M • y j) fun j k => by
      have h4 := hM (j, k)
      dsimp only at h4 ⊢
      rw [smul_sub, sub_eq_zero] at h4
      rw [map_smul, map_smul]
      exact h4
    refine ⟨(e, ⟨f i ^ (M + N), pow_mem (Submonoid.mem_powers _) _⟩), ?_⟩
    show f i ^ (M + N) • z = ρ ⟨f i, i, dvd_rfl⟩ e
    rw [he i]
    rw [← hii, smul_smul, ← pow_add]
  · have hd : ρ ⟨f i, i, dvd_rfl⟩ (x₁ - x₂) = 0 := by rw [map_sub, hx, sub_self]
    have Rj : ∀ j, ∃ n, f i ^ n • ρ ⟨f j, j, dvd_rfl⟩ (x₁ - x₂) = 0 := by
      intro j
      have := hloc ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (f i) (mul_comm _ _)
      apply GlobalTheory.CompanionTheory.BasicCover.exists_pow_smul_eq_zero (f i)
        (res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _))
      rw [hrρ, ← hrρ ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _), hd, map_zero]
    obtain ⟨N, hN⟩ := GlobalTheory.CompanionTheory.BasicCover.exists_uniform_bound
      (fun j n => f i ^ n • ρ ⟨f j, j, dvd_rfl⟩ (x₁ - x₂) = 0)
      (fun j n m hnm hn => GlobalTheory.CompanionTheory.BasicCover.pow_smul_eq_zero_mono _ _ hnm hn) Rj
    have h0 : f i ^ N • (x₁ - x₂) = 0 := hsep _ fun j => by rw [map_smul]; exact hN j
    refine ⟨⟨f i ^ N, pow_mem (Submonoid.mem_powers _) N⟩, ?_⟩
    show f i ^ N • x₁ = f i ^ N • x₂
    rw [← sub_eq_zero, ← smul_sub]
    exact h0

end GlobalTheory.CompanionTheory.BasicCover
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem existsUnique_valuationRing_lift : ∀ (O V C : Type) [CommRing O] [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C] [IsFractionRing V C] (b : O →+* V) (Z : Scheme.{0}) (s : Z ⟶ Spec (CommRingCat.of O)) [IsProper s] (y : Spec (CommRingCat.of C) ⟶ Z), y ≫ s = Spec.map (CommRingCat.ofHom ((algebraMap V C).comp b)) → ∃! y' : Spec (CommRingCat.of V) ⟶ Z, Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ y' = y ∧ y' ≫ s = Spec.map (CommRingCat.ofHom b) := by
  intro O V C _ _ _ _ _ _ _ b Z s hs y hy
  have hv : ValuativeCriterion s := by
    have h : (@IsProper : MorphismProperty Scheme.{0}) s := hs
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hc : CommSq y (Spec.map (CommRingCat.ofHom (algebraMap V C))) s
      (Spec.map (CommRingCat.ofHom b)) := ⟨by
    rw [hy, ← Spec.map_comp]; rfl⟩
  let S : ValuativeCommSq s :=
    { R := V, K := C, i₁ := y, i₂ := Spec.map (CommRingCat.ofHom b), commSq := hc }
  obtain ⟨u⟩ := hv S
  refine ⟨u.default.l, ⟨u.default.fac_left, u.default.fac_right⟩, ?_⟩
  rintro y' ⟨h1, h2⟩
  have := u.uniq ⟨y', h1, h2⟩
  exact congrArg CommSq.LiftStruct.l this

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hB_bound : ∀ (N j B : ℕ) (S : Finset ℕ) (d v : ℕ → ℝ) (lrd Lv hrec hB : ℝ), j ≤ N → 3 ≤ B → 0 ≤ lrd → |hrec| ≤ N * (3 / 2 * lrd + |Lv| / 2) → hB = hrec + ∑ p ∈ S, d p → (∀ p ∈ S, p.Prime) → (∀ p ∈ S, 0 ≤ v p) → (∀ p ∈ S, |d p| ≤ (N / ((p : ℝ) - 1) + j * v p + ((N : ℝ) - j) * v p) * Real.log p) → ∑ p ∈ S, v p * Real.log p ≤ lrd → ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 3 * Real.log B + 1 → |hB| ≤ 4 * N * (Real.log B + lrd + |Lv|) := by
  intro N j B S d v lrd Lv hrec hB hj hB3 hl hrecb hBeq hprime hv hd hsv hsl
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hlogB : 1 ≤ Real.log B := by
    have h3 : (3 : ℝ) ≤ B := by exact_mod_cast hB3
    have hexp : Real.exp 1 ≤ B := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hsum : |∑ p ∈ S, d p| ≤ N * (3 * Real.log B + 1) + N * lrd := by
    calc |∑ p ∈ S, d p| ≤ ∑ p ∈ S, |d p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ S, ((N : ℝ) * (Real.log p / ((p : ℝ) - 1)) + N * (v p * Real.log p)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hdp := hd p hp
        have e : ((N : ℝ) / ((p : ℝ) - 1) + j * v p + ((N : ℝ) - j) * v p) * Real.log p =
            (N : ℝ) * (Real.log p / ((p : ℝ) - 1)) + N * (v p * Real.log p) := by ring
        linarith
      _ = (N : ℝ) * ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) + N * ∑ p ∈ S, v p * Real.log p := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ N * (3 * Real.log B + 1) + N * lrd := by gcongr
  have htot : |hB| ≤ |hrec| + |∑ p ∈ S, d p| := by
    rw [hBeq]; exact abs_add_le _ _
  nlinarith [mul_nonneg hN (sub_nonneg.mpr hlogB), mul_nonneg hN hl, mul_nonneg hN (abs_nonneg Lv)]

end GlobalTheory.CompanionTheory.Ar.Flat
end
