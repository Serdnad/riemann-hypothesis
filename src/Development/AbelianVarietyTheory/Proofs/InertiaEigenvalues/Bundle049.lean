module

public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Data.List.GetD
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Order.Int.LeastGreatest
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem card_quotient_eq_of_pow_sub_self_mem : ∀ {R : Type} [CommRing R] (P : Ideal R) [P.IsMaximal] (q : ℕ) (ζ : R), 2 ≤ q → ζ ^ (q - 1) = 1 →
    (∀ j : ℕ, 0 < j → j < q - 1 → ζ ^ j - 1 ∉ P) → (∀ y : R, y ^ q - y ∈ P) → Nat.card (R ⧸ P) = q := by
  intro R _ P _ q ζ hq hζ hprim hall
  classical
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  have hfix : ∀ x : R ⧸ P, x ^ q = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hall y
  set f : Polynomial (R ⧸ P) := X ^ q - X with hf
  have hdeg : f.natDegree = q := by
    rw [hf, natDegree_sub_eq_left_of_natDegree_lt] <;> simp <;> omega
  have hf0 : f ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg; omega
  have hmem : ∀ x : R ⧸ P, x ∈ f.roots.toFinset := by
    intro x
    rw [Multiset.mem_toFinset, mem_roots hf0]
    simp [hf, hfix x]
  haveI : Finite (R ⧸ P) := by
    apply Finite.of_injective (fun x : R ⧸ P => (⟨x, hmem x⟩ : f.roots.toFinset))
    intro a b h; simpa using congrArg Subtype.val h
  letI : Fintype (R ⧸ P) := Fintype.ofFinite _
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]
    calc Fintype.card (R ⧸ P) = (Finset.univ : Finset (R ⧸ P)).card := rfl
      _ ≤ f.roots.toFinset.card := Finset.card_le_card (fun x _ => hmem x)
      _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := card_roots' f
      _ = q := hdeg
  · set z : R ⧸ P := Ideal.Quotient.mk P ζ with hz
    have hz1 : z ^ (q - 1) = 1 := by rw [hz, ← map_pow, hζ, map_one]
    have hz0 : z ≠ 0 := by
      intro h; rw [h, zero_pow (by omega)] at hz1; exact zero_ne_one hz1
    have hord : orderOf z = q - 1 := by
      rw [orderOf_eq_iff (by omega)]
      refine ⟨hz1, fun m hm hm0 h => hprim m hm0 hm ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, ← hz, h, sub_self]
    have hinj := pow_injOn_Iio_orderOf (x := z)
    rw [hord] at hinj
    let g : Fin q → R ⧸ P := fun i => if (i : ℕ) = 0 then 0 else z ^ ((i : ℕ) - 1)
    have hg : Function.Injective g := by
      intro a b hab
      simp only [g] at hab
      apply Fin.ext
      by_cases ha : (a : ℕ) = 0 <;> by_cases hb : (b : ℕ) = 0 <;> simp only [ha, hb, if_true, if_false] at hab
      · omega
      · exact absurd hab.symm (pow_ne_zero _ hz0)
      · exact absurd hab (pow_ne_zero _ hz0)
      · have := hinj (show (a : ℕ) - 1 ∈ Set.Iio (q - 1) by simp; omega)
          (show (b : ℕ) - 1 ∈ Set.Iio (q - 1) by simp; omega) hab
        omega
    have := Nat.card_le_card_of_injective g hg
    simpa using this

end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory

theorem exists_span_eq_top_of_card_hom_residueField_le
    (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
    (A : Type) [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] (a : ℕ)
    (h : Nat.card (A →ₗ[Λ] IsLocalRing.ResidueField Λ) ≤
      Nat.card (IsLocalRing.ResidueField Λ) ^ a) :
    ∃ v : Fin a → A, Submodule.span Λ (Set.range v) = ⊤ := by
  classical
  set k := IsLocalRing.ResidueField Λ
  let V := k ⊗[Λ] A
  let d := Module.finrank k V
  let b : Module.Basis (Fin d) k V := Module.finBasis k V

  have hsurj : Function.Surjective (TensorProduct.mk Λ k A 1) :=
    TensorProduct.mk_surjective Λ A k Ideal.Quotient.mk_surjective
  choose f hf using fun i => hsurj (b i)

  have hspan : Submodule.span Λ (Set.range f) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis f b (fun i => hf i)

  let Φ : (V →ₗ[k] k) → (A →ₗ[Λ] k) := fun g =>
    (g.restrictScalars Λ).comp (TensorProduct.mk Λ k A 1)
  have hΦ : Function.Injective Φ := by
    intro g₁ g₂ h
    apply TensorProduct.AlgebraTensorModule.ext
    intro x y
    have h' := LinearMap.congr_fun h y
    simp only [Φ, LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply] at h'
    have e : x ⊗ₜ[Λ] y = x • ((1 : k) ⊗ₜ[Λ] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul, map_smul]
    exact congrArg (x • ·) h'

  have : Finite (A →ₗ[Λ] k) := by
    refine Finite.of_injective (fun g : A →ₗ[Λ] k => fun i => g (f i)) ?_
    intro g₁ g₂ h
    exact LinearMap.ext_on_range hspan (fun i => congr_fun h i)
  have hcard : Nat.card (V →ₗ[k] k) = Nat.card k ^ d := by
    rw [← Nat.card_congr (b.constr k).toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin d),
      Fintype.card_fin]
  have hle : Nat.card k ^ d ≤ Nat.card k ^ a := by
    rw [← hcard]; exact (Nat.card_le_card_of_injective Φ hΦ).trans h
  have hk : 1 < Nat.card k := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hda : d ≤ a := (Nat.pow_le_pow_iff_right hk).mp hle

  refine ⟨fun i => if hi : (i : ℕ) < d then f ⟨i, hi⟩ else 0, ?_⟩
  rw [eq_top_iff, ← hspan]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, i.2.trans_le hda⟩, by simp⟩

end GlobalTheory
end

section

open PowerSeries

namespace GlobalTheory

theorem filtLaurent_prod_preserves {L : Type} [Field L] (D : Module.End L L⟦X⟧) (e : ℕ → L)
    (hD : ∀ (i : ℕ) (f : L⟦X⟧), X ^ i ∣ f → X ^ (i + 1) ∣ D f - e i • f)
    (c : ℤ → L) (xs : List ℤ) (i : ℕ) (f : L⟦X⟧) (hf : X ^ i ∣ f) :
    X ^ i ∣ Polynomial.aeval D
      (xs.map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod f := by
  induction xs with
  | nil => simpa using hf
  | cons x xs ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply]
    set g := Polynomial.aeval D
      (xs.map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod f
    have h1 : X ^ i ∣ D g - e i • g := (pow_dvd_pow X (Nat.le_succ i)).trans (hD i g ih)
    have h2 : Polynomial.aeval D (Polynomial.X - Polynomial.C (c x) : Polynomial L) g
        = (D g - e i • g) + (e i - c x) • g := by
      simp [sub_smul, Module.algebraMap_end_apply]
    rw [h2]
    exact dvd_add h1 (Dvd.dvd.trans ih ⟨PowerSeries.C (e i - c x), by
      rw [PowerSeries.smul_eq_C_mul, mul_comm]⟩)

theorem filtLaurent_prod_raises {L : Type} [Field L] (D : Module.End L L⟦X⟧) (c : ℤ → L) (K : ℤ)
    (hD : ∀ (i : ℕ) (f : L⟦X⟧), X ^ i ∣ f → X ^ (i + 1) ∣ D f - c (-(K + i)) • f)
    (n : ℕ) : ∀ (xs : List ℤ) (i : ℕ) (f : L⟦X⟧), X ^ i ∣ f →
      (∀ l : ℕ, i ≤ l → l < i + n → -(K + l) ∈ xs) →
      X ^ (i + n) ∣ Polynomial.aeval D
        (xs.map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod f := by
  induction n with
  | zero => exact fun xs i f hf _ => filtLaurent_prod_preserves D _ hD c xs i f hf
  | succ n ih =>
    intro xs i f hf hxs
    have hx : -(K + i) ∈ xs := hxs i le_rfl (by omega)
    have hperm := ((List.perm_cons_erase hx).map
      fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod_eq
    rw [hperm, List.map_cons, List.prod_cons, mul_comm, map_mul, Module.End.mul_apply]
    have h2 : Polynomial.aeval D (Polynomial.X - Polynomial.C (c (-(K + i))) : Polynomial L) f
        = D f - c (-(K + i)) • f := by
      simp [Module.algebraMap_end_apply]
    rw [h2, show i + (n + 1) = (i + 1) + n by omega]
    refine ih _ (i + 1) _ (hD i f hf) fun l hl hl' => ?_
    exact (List.mem_erase_of_ne (by omega)).2 (hxs l (by omega) (by omega))

noncomputable def filtLaurentDiag {L : Type} [Field L] (w : ℕ → L) : Module.End L L⟦X⟧ where
  toFun f := PowerSeries.mk fun i => w i * coeff i f
  map_add' f g := by ext i; simp [mul_add]
  map_smul' a f := by ext i; simp [mul_left_comm]

theorem filtLaurent_triangular {L : Type} [Field L] (w : ℕ → L) (p : L⟦X⟧)
    (hp : constantCoeff p ≠ 0) (i : ℕ) (a : L) (ha : constantCoeff p * a = w i)
    (f : L⟦X⟧) (hf : X ^ i ∣ f) :
    X ^ (i + 1) ∣ (LinearMap.mulLeft L p⁻¹ ∘ₗ filtLaurentDiag w) f - a • f := by
  have h1 : (LinearMap.mulLeft L p⁻¹ ∘ₗ filtLaurentDiag w) f - a • f
      = p⁻¹ * (filtLaurentDiag w f - a • (p * f)) := by
    rw [mul_sub, mul_smul_comm, ← mul_assoc, PowerSeries.inv_mul_cancel _ hp, one_mul]
    rfl
  rw [h1]
  refine Dvd.dvd.mul_left ?_ _
  rw [X_pow_dvd_iff]
  intro l hl
  have hpf : X ^ i ∣ p * f := hf.mul_left p
  rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | rfl
  · simp [filtLaurentDiag, X_pow_dvd_iff.1 hf l h, X_pow_dvd_iff.1 hpf l h]
  · obtain ⟨g, rfl⟩ := hf
    have e1 : coeff l (X ^ l * g) = constantCoeff g := by
      simpa using coeff_X_pow_mul g l 0
    have e2 : coeff l (p * (X ^ l * g)) = constantCoeff p * constantCoeff g := by
      rw [mul_left_comm]
      simpa using coeff_X_pow_mul (p * g) l 0
    simp only [map_sub, filtLaurentDiag, LinearMap.coe_mk, AddHom.coe_mk, coeff_mk, map_smul,
      e1, e2, smul_eq_mul, ← ha]
    ring

theorem filtLaurent_shift_line : ∀ (L : Type) [Field L] (M : Type) [AddCommGroup M] [Module L M] (Fl : ℤ → Submodule L M), Antitone Fl → ∀ (u : Lˣ) (p : PowerSeries L) (c : ℤ → L), PowerSeries.constantCoeff p ≠ 0 → (∀ x : ℤ, PowerSeries.constantCoeff p * c x = ((u ^ (-x) : Lˣ) : L) - 1) → ∀ (y' Y : ℕ) (xs : List ℤ), (∀ (a : ℤ) (j : ℕ), Fl (a + 1) ≠ Fl a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) → ∀ seq : ℕ → ℤ → M, (∀ m, ∃ k₀ : ℤ, ∀ k < k₀, seq m k = 0) → (∀ m < xs.length, ∀ k : ℤ, ∑ᶠ j : ℕ, PowerSeries.coeff j p • (seq (m + 1) (k - j) + c (xs.getD m 0) • seq m (k - j)) = (((u ^ k : Lˣ) : L) - 1) • seq m k) → (∀ k : ℤ, seq 0 k ∈ Fl (-k - Y)) → ∀ k : ℤ, seq xs.length k ∈ Fl (-k - y') := by
  intro L _ M _ _ Fl hFl u p c hp hc y' Y xs hxs seq hbd hrec h0 k
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  choose k₀ hk₀ using hbd

  have core : ∀ (K : ℤ), (∀ m ≤ xs.length, K ≤ k₀ m) → ∀ i n : ℕ,
      (∀ l < i, φ (seq 0 (K + l)) = 0) → (∀ l : ℕ, i ≤ l → l < i + n → -(K + l) ∈ xs) →
      ∀ l < i + n, φ (seq xs.length (K + l)) = 0 := by
    intro K hK i n hi hn
    set w : ℕ → L := fun l => ((u ^ (K + l) : Lˣ) : L) - 1 with hw
    set D : Module.End L L⟦X⟧ := LinearMap.mulLeft L p⁻¹ ∘ₗ filtLaurentDiag w with hDdef
    set G : ℕ → L⟦X⟧ := fun m => PowerSeries.mk fun l => φ (seq m (K + l)) with hG
    have hstep : ∀ m < xs.length, G (m + 1) = D (G m) - c (xs.getD m 0) • G m := by
      intro m hm
      have key : p * (G (m + 1) + c (xs.getD m 0) • G m) = filtLaurentDiag w (G m) := by
        ext l
        have h1 := hrec m hm (K + l)
        rw [finsum_eq_sum_of_support_subset (s := Finset.range (l + 1))] at h1
        · have h2 := congrArg φ h1
          rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => coeff a p * coeff b (G (m + 1) + c (xs.getD m 0) • G m))]

          rw [map_sum, map_smul] at h2
          simp only [filtLaurentDiag, LinearMap.coe_mk, AddHom.coe_mk, coeff_mk, hG, hw]
          rw [← smul_eq_mul, ← h2]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hj' : j ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
          have : K + ((l - j : ℕ) : ℤ) = K + l - j := by omega
          simp only [map_add (f := _), map_smul, coeff_mk, this, smul_eq_mul]
        · intro j hj
          by_contra hj'
          have hj'' : l + 1 ≤ j := by simpa using hj'
          have a1 := hK m hm.le
          have a2 := hK (m + 1) hm
          apply hj
          simp only
          rw [hk₀ (m + 1) _ (by omega), hk₀ m _ (by omega)]
          simp
      rw [eq_sub_iff_add_eq, hDdef, LinearMap.comp_apply, ← key, LinearMap.mulLeft_apply,
        ← mul_assoc, PowerSeries.inv_mul_cancel _ hp, one_mul]
    have hall : ∀ m ≤ xs.length, G m = Polynomial.aeval D
        ((xs.take m).map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod
          (G 0) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        intro hm
        have hm' : m < xs.length := hm
        rw [hstep m hm', List.take_succ_eq_append_getElem hm', List.map_append, List.prod_append,
          mul_comm, map_mul, Module.End.mul_apply, ← ih hm'.le, List.getD_eq_getElem _ _ hm']
        simp [Module.algebraMap_end_apply]
    have hfin := filtLaurent_prod_raises D c K (fun l f hf =>
      filtLaurent_triangular w p hp l _ (by rw [hc, neg_neg]) f hf) n xs i (G 0)
      (X_pow_dvd_iff.2 fun l hl => by simpa [hG] using hi l hl) hn
    have h3 := hall xs.length le_rfl
    rw [List.take_length] at h3
    rw [← h3] at hfin
    intro l hl
    simpa [hG] using X_pow_dvd_iff.1 hfin l hl
  obtain ⟨K₀, hK₀⟩ := ((Set.finite_le_nat xs.length).image k₀).bddBelow
  have hK₁ : ∀ m ≤ xs.length, K₀ ≤ k₀ m := fun m hm => hK₀ ⟨m, hm, rfl⟩
  by_cases hex : ∃ a : ℤ, ¬ ∀ v ∈ Fl a, φ v = 0
  · have hbdd : ∀ a : ℤ, (¬ ∀ v ∈ Fl a, φ v = 0) → a < -k - y' := by
      intro a ha
      by_contra h
      exact ha fun v hv => hφ v (hFl (not_lt.1 h) hv)
    obtain ⟨a, ha, hmax⟩ := Int.exists_greatest_of_bdd
      ⟨-k - y', fun a ha => (hbdd a ha).le⟩ hex
    have ha1 : ∀ v ∈ Fl (a + 1), φ v = 0 := by
      by_contra h
      have := hmax _ h
      omega
    have hjump : Fl (a + 1) ≠ Fl a := fun h => ha (h ▸ ha1)
    have hlt := hbdd a ha
    set K := min K₀ (min k (-a - Y)) with hK
    have := core K (fun m hm => (min_le_left _ _).trans (hK₁ m hm)) (-a - Y - K).toNat (Y - y')
      (fun l hl => ha1 _ (hFl (by omega) (h0 _)))
      (fun l hl hl' => by
        have := hxs a (-(K + l) - a).toNat hjump (by omega) (by omega)
        convert this using 1
        omega) (k - K).toNat (by omega)
    convert this using 3
    omega
  · push Not at hex
    set K := min K₀ k with hK
    have := core K (fun m hm => (min_le_left _ _).trans (hK₁ m hm)) ((k - K).toNat + 1) 0
      (fun l _ => hex _ _ (h0 _)) (fun l hl hl' => by omega) (k - K).toNat (by omega)
    convert this using 3
    omega

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

theorem det_traceGram_blockMatrix {E E' : Type} [Field E] [Field E'] [Algebra E E'] [FiniteDimensional E E'] {d n : ℕ}
    (w : Module.Basis (Fin d) E E') (H : Matrix (Fin n) (Fin n) E') (v : Fin d → E') :
    (Matrix.of fun (p q : Fin d × Fin n) => Algebra.trace E E' (w p.1 * H p.2 q.2 * v q.1)).det
      = (Matrix.of fun k l => Algebra.trace E E' (w k * v l)).det ^ n * Algebra.norm E H.det := by
  classical
  set D : Matrix (Fin d) (Fin d) E := Matrix.of fun k m => Algebra.trace E E' (w k * w m) with hD
  set C : Matrix (Fin d) (Fin d) E := w.toMatrix v with hC
  set Λ : Matrix (Fin d × Fin n) (Fin d × Fin n) E :=
    Matrix.of fun p q => Algebra.leftMulMatrix w (H p.2 q.2) p.1 q.1 with hΛ

  have htr : ∀ k (y : E'), Algebra.trace E E' (w k * y) = ∑ m, D k m * w.repr y m := by
    intro k y
    calc Algebra.trace E E' (w k * y) = Algebra.trace E E' (w k * ∑ m, w.repr y m • w m) := by
          rw [w.sum_repr y]
      _ = ∑ m, D k m * w.repr y m := by

          simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul, hD, of_apply]
          exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have hrep : ∀ (x y : E') m, w.repr (x * y) m = ∑ s, Algebra.leftMulMatrix w x m s * w.repr y s := by
    intro x y m
    have := congrFun (Algebra.leftMulMatrix_mulVec_repr w x y) m
    rw [← this]; simp [Matrix.mulVec, dotProduct]
  have hDC : D * C = Matrix.of fun k l => Algebra.trace E E' (w k * v l) := by
    ext k l
    simp [Matrix.mul_apply, htr, hC, Module.Basis.toMatrix_apply]
  have hM : (Matrix.of fun (p q : Fin d × Fin n) => Algebra.trace E E' (w p.1 * H p.2 q.2 * v q.1))
      = blockDiagonal (fun _ : Fin n => D) * Λ * blockDiagonal (fun _ : Fin n => C) := by
    ext ⟨k, i⟩ ⟨l, j⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, blockDiagonal_apply, ite_mul, mul_ite, zero_mul,
      mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, of_apply, hΛ]
    rw [mul_assoc, htr]
    simp only [hrep, hC, Module.Basis.toMatrix_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hΛdet : Λ.det = Algebra.norm E H.det := by
    let bt := w.smulTower (Pi.basisFun E' (Fin n))
    have hmat : LinearMap.toMatrix bt bt ((Matrix.toLin' H).restrictScalars E) = Λ := by
      ext ⟨k, i⟩ ⟨l, j⟩
      simp [LinearMap.toMatrix_apply, bt, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr, hΛ,
        Algebra.leftMulMatrix_eq_repr_mul, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [mul_comm]
    rw [← hmat, LinearMap.det_toMatrix, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  rw [hM, det_mul, det_mul, det_blockDiagonal, det_blockDiagonal, hΛdet, ← hDC, det_mul]
  simp [Finset.prod_const, mul_pow]
  ring

end GlobalTheory
end

section

open PowerSeries

namespace GlobalTheory

noncomputable def eigenSeriesCoeff {F : Type} [Field F] (a c : ℕ → F) : ℕ → F
  | 0 => 1
  | k + 1 => (a (k + 1))⁻¹ * ∑ i : Fin (k + 1), c (i + 1) * eigenSeriesCoeff a c (k - i)
decreasing_by omega

theorem eigenSeriesCoeff_succ {F : Type} [Field F] (a c : ℕ → F) (k : ℕ) (ha : a (k + 1) ≠ 0) :
    a (k + 1) * eigenSeriesCoeff a c (k + 1)
      = ∑ i ∈ Finset.range (k + 1), c (i + 1) * eigenSeriesCoeff a c (k - i) := by
  rw [eigenSeriesCoeff, mul_inv_cancel_left₀ ha]
  exact Fin.sum_univ_eq_sum_range (fun i => c (i + 1) * eigenSeriesCoeff a c (k - i)) (k + 1)

theorem exists_rescale_eigen_series_zero {F : Type} [Field F] (p : F⟦X⟧) (χ u : F)
    (hp : constantCoeff p ≠ 0) (hu : u ≠ 0) (hχ : ∀ k : ℕ, 0 < k → χ ^ k ≠ 1) :
    ∃ h : F⟦X⟧, constantCoeff h = 1 ∧
      C u * rescale χ h - h = C ((u - 1) / constantCoeff p) * (p * h) := by
  set L : F := (u - 1) / constantCoeff p with hL
  have hLp : L * coeff 0 p = u - 1 := by
    rw [coeff_zero_eq_constantCoeff_apply, hL]
    field_simp
  refine ⟨PowerSeries.mk (eigenSeriesCoeff (fun k => u * (χ ^ k - 1)) (fun j => L * coeff j p)),
    ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, eigenSeriesCoeff]
  · ext k
    simp only [map_sub, coeff_C_mul, coeff_rescale, coeff_mk]
    rw [coeff_mul]
    simp only [coeff_mk]
    cases k with
    | zero =>
      simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, pow_zero]
      rw [eigenSeriesCoeff]
      linear_combination -hLp
    | succ k =>
      have ha : u * (χ ^ (k + 1) - 1) ≠ 0 :=
        mul_ne_zero hu (sub_ne_zero.mpr (hχ (k + 1) (Nat.succ_pos k)))
      have key := eigenSeriesCoeff_succ (fun k => u * (χ ^ k - 1)) (fun j => L * coeff j p) k ha
      simp only [mul_assoc] at key
      rw [← Finset.mul_sum] at key
      rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [Nat.succ_eq_add_one]
      linear_combination key - eigenSeriesCoeff (fun k => u * (χ ^ k - 1))
        (fun j => L * coeff j p) (k + 1) * hLp

theorem exists_rescale_eigen_series : ∀ {F : Type} [Field F] (p : F⟦X⟧) (χ κ : F) (n : ℕ), constantCoeff p ≠ 0 → κ ≠ 0 → χ ≠ 0 → (∀ k : ℕ, 0 < k → χ ^ k ≠ 1) → ∃ h : F⟦X⟧, constantCoeff h = 1 ∧ C κ * rescale χ (X ^ n * h) - X ^ n * h = C ((κ * χ ^ n - 1) / constantCoeff p) * (p * (X ^ n * h)) := by
  intro F _ p χ κ n hp hκ hχ0 hχ
  obtain ⟨h, h0, hh⟩ :=
    exists_rescale_eigen_series_zero p χ (κ * χ ^ n) hp (mul_ne_zero hκ (pow_ne_zero n hχ0)) hχ
  refine ⟨h, h0, ?_⟩
  have hX : rescale χ (X ^ n * h) = C (χ ^ n) * X ^ n * rescale χ h := by
    rw [map_mul, map_pow, rescale_X, mul_pow, map_pow]
  rw [hX]
  calc C κ * (C (χ ^ n) * X ^ n * rescale χ h) - X ^ n * h
      = X ^ n * (C (κ * χ ^ n) * rescale χ h - h) := by rw [map_mul]; ring
    _ = X ^ n * (C ((κ * χ ^ n - 1) / constantCoeff p) * (p * h)) := by rw [hh]
    _ = C ((κ * χ ^ n - 1) / constantCoeff p) * (p * (X ^ n * h)) := by ring

end GlobalTheory
end
