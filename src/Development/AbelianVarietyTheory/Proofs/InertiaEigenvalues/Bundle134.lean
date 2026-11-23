module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Formalism.GaloisCohomology.StatementLoc
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Operator.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerOperatorInjectiveEigenvector
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle114
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle115
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle116
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
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

namespace GlobalTheory.UnitLemma.TorusPts

section Ring

variable {A : Type} [CommRing A] {I : Type} [Fintype I]

def tt (f h c d : I → A) : A := 1 + ∑ i, ((c i - 1) * f i + (d i - 1) * h i)

theorem f_mul_tt (f h c d : I → A) (hf : ∀ i, f i * f i = f i) (hff : ∀ i j, i ≠ j → f i * f j = 0)
    (hfh : ∀ i j, f i * h j = 0) (j : I) : f j * tt f h c d = c j * f j := by
  classical
  unfold tt
  rw [mul_add, Finset.mul_sum, Finset.sum_eq_single j]
  · linear_combination (c j - 1) * hf j + (d j - 1) * hfh j j
  · intro i _ hi
    linear_combination (c i - 1) * hff j i hi.symm + (d i - 1) * hfh j i
  · simp

theorem tt_swap (f h c d : I → A) : tt f h c d = tt h f d c := by
  unfold tt
  congr 1
  exact Finset.sum_congr rfl fun i _ => add_comm _ _

theorem tt_mul (f h c d c' d' : I → A) (hf : ∀ i, f i * f i = f i) (hff : ∀ i j, i ≠ j → f i * f j = 0)
    (hh : ∀ i, h i * h i = h i) (hhh : ∀ i j, i ≠ j → h i * h j = 0)
    (hfh : ∀ i j, f i * h j = 0) : tt f h c d * tt f h c' d' = tt f h (c * c') (d * d') := by
  have h1 := f_mul_tt f h c' d' hf hff hfh
  have h2 := f_mul_tt h f d' c' hh hhh (fun i j => by rw [mul_comm]; exact hfh j i)
  rw [← tt_swap] at h2
  have h3 : tt f h c d * tt f h c' d' =
      tt f h c' d' + ∑ i, ((c i - 1) * (f i * tt f h c' d') + (d i - 1) * (h i * tt f h c' d')) := by
    conv_lhs => arg 1; unfold tt
    rw [add_mul, one_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h3]
  simp only [h1, h2]
  unfold tt
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.mul_apply]; ring

theorem tt_one (f h : I → A) : tt f h 1 1 = 1 := by simp [tt]

end Ring

theorem isIntegral_idem {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {f : A} (hf : f * f = f) :
    IsIntegral O f := by
  nontriviality O
  refine ⟨X ^ 2 - X, ?_, ?_⟩
  · monicity!
  · simp [pow_two, hf]

theorem isIntegral_of_mul_idem {K : UQ} (B : InvAlg K) {f : B.A} (hf : f * f = f) (h0 : f ≠ 0) (x : K.E)
    (hx : IsIntegral K.O (algebraMap K.E B.A x * f)) : IsIntegral K.O x := by
  let J : Ideal B.A := Ideal.span {1 - f}
  have hJ : J ≠ ⊤ := by
    intro h
    have : (1 : B.A) ∈ J := h ▸ Submodule.mem_top
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 this
    apply h0
    linear_combination (-f) * hr - r * hf
  haveI : Nontrivial (B.A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
  let φ : K.E →ₐ[K.O] B.A ⧸ J := (Ideal.Quotient.mkₐ K.O J).comp (IsScalarTower.toAlgHom K.O K.E B.A)
  have hinj : Function.Injective φ := φ.toRingHom.injective
  rw [← isIntegral_algHom_iff φ hinj]
  have h1 := hx.map (Ideal.Quotient.mkₐ K.O J)
  have h2 : Ideal.Quotient.mkₐ K.O J (algebraMap K.E B.A x * f) = φ x := by
    show Ideal.Quotient.mk J _ = Ideal.Quotient.mk J (algebraMap K.E B.A x)
    rw [Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.2 ⟨-algebraMap K.E B.A x, by ring⟩
  rwa [h2] at h1

theorem le_of_isIntegral {K : UQ} {a : K.O} (ha : K.Small a) (n m : ℕ)
    (h : IsIntegral K.O (((algebraMap K.O K.E a) ^ n)⁻¹ * (algebraMap K.O K.E a) ^ m)) : n ≤ m := by
  by_contra hlt
  push Not at hlt
  obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff).1 h
  have ha0 : algebraMap K.O K.E a ≠ 0 := by
    simpa using ha.1
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  have h1 : algebraMap K.O K.E (a * (a ^ d * r)) = algebraMap K.O K.E 1 := by
    simp only [map_mul, map_pow, map_one, hr]
    field_simp
    ring
  have h2 := IsFractionRing.injective K.O K.E h1
  exact ha.2.1 (IsUnit.of_mul_eq_one _ h2)

theorem torus_points : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e : ι → B.A) (S : Finset ι) (a : K.O), K.Small a → IsPre B e S → ∀ k : ℕ, ∃ f : ({i // i ∉ S} → Fin (k + 1)) → B.T ⧸ (intUnits K.O B.A).subgroupOf B.T, Function.Injective f ∧ ∀ n, IsIntegral K.O ((((Quotient.out (f n) : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A) := by
  intro K B ι _ e S a ha hP k
  classical
  obtain ⟨hC, hP⟩ := hP
  choose F hFi hF0 _ _ hFS using hP
  let f : {i // i ∉ S} → B.A := fun i => F i
  let h : {i // i ∉ S} → B.A := fun i => B.σ (F i)
  have hf : ∀ i, f i * f i = f i := fun i => hFi i
  have hh : ∀ i, h i * h i = h i := fun i => by
    show B.σ _ * B.σ _ = B.σ _
    rw [← map_mul, hFi i]
  have hfe : ∀ i, f i = f i * e i := fun i => by
    rw [(hFS i i.2).2]
    linear_combination -(hf i) - (hFS i i.2).1
  have hhe : ∀ i, h i = h i * e i := fun i => by
    rw [(hFS i i.2).2]
    linear_combination -(hh i) - (hFS i i.2).1
  have hee : ∀ i j : {i // i ∉ S}, i ≠ j → e i * e j = 0 := fun i j hij =>
    hC.ortho (fun h => hij (Subtype.ext h))
  have hff : ∀ i j, i ≠ j → f i * f j = 0 := fun i j hij => by
    rw [hfe i, hfe j]; linear_combination f i * f j * hee i j hij
  have hhh : ∀ i j, i ≠ j → h i * h j = 0 := fun i j hij => by
    rw [hhe i, hhe j]; linear_combination h i * h j * hee i j hij
  have hfh : ∀ i j, f i * h j = 0 := fun i j => by
    by_cases hij : i = j
    · subst hij; exact (hFS i i.2).1
    · rw [hfe i, hhe j]; linear_combination f i * h j * hee i j hij
  set α : K.E := algebraMap K.O K.E a with hα
  have hα0 : α ≠ 0 := by simpa [hα] using ha.1
  let c : ({i // i ∉ S} → Fin (k + 1)) → {i // i ∉ S} → B.A := fun n i => algebraMap K.E B.A (α ^ (n i : ℕ))
  let d : ({i // i ∉ S} → Fin (k + 1)) → {i // i ∉ S} → B.A := fun n i => algebraMap K.E B.A (α ^ (n i : ℕ))⁻¹
  have hcd : ∀ n, c n * d n = 1 := fun n => by
    funext i
    show algebraMap K.E B.A _ * algebraMap K.E B.A _ = 1
    rw [← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hα0), map_one]
  have hinv : ∀ n, tt f h (c n) (d n) * tt f h (d n) (c n) = 1 := fun n => by
    rw [tt_mul f h _ _ _ _ hf hff hh hhh hfh, hcd, mul_comm (d n), hcd, tt_one]
  have hσ : ∀ n, B.σ (tt f h (c n) (d n)) = tt f h (d n) (c n) := fun n => by
    rw [tt_swap f h (d n)]
    unfold tt
    have hcα : K.c α = α := ha.2.2

    simp only [map_add (f := _), map_one, map_sum, map_mul, map_sub, c, d, f, h, B.σ_σ, B.σ_alg, map_inv₀, map_pow, hcα]
  let u : ({i // i ∉ S} → Fin (k + 1)) → B.Aˣ := fun n =>
    ⟨tt f h (c n) (d n), tt f h (d n) (c n), hinv n, by rw [mul_comm]; exact hinv n⟩
  let t : ({i // i ∉ S} → Fin (k + 1)) → B.T := fun n => ⟨u n, by
    show tt f h (c n) (d n) * B.σ (tt f h (c n) (d n)) = 1
    rw [hσ, hinv]⟩
  have hαA : algebraMap K.O B.A a = algebraMap K.E B.A α := IsScalarTower.algebraMap_apply _ _ _ _
  have hia : IsIntegral K.O (algebraMap K.E B.A α) := hαA ▸ isIntegral_algebraMap
  have key : ∀ n m, ((t n)⁻¹ * t m) ∈ (intUnits K.O B.A).subgroupOf B.T → ∀ i, (n i : ℕ) ≤ m i := by
    intro n m hnm i
    have h1 : IsIntegral K.O (tt f h (d n) (c n) * tt f h (c m) (d m)) := hnm.1
    rw [tt_mul f h _ _ _ _ hf hff hh hhh hfh] at h1
    have h2 := (isIntegral_idem (O := K.O) (hf i)).mul h1
    rw [f_mul_tt f h _ _ hf hff hfh] at h2
    apply le_of_isIntegral ha
    apply isIntegral_of_mul_idem B (hf i) (hF0 i)
    rw [map_mul]
    exact h2
  refine ⟨fun n => QuotientGroup.mk (t n), ?_, ?_⟩
  · intro n m hnm
    funext i
    exact Fin.ext (le_antisymm (key n m (QuotientGroup.eq.1 hnm) i) (key m n (QuotientGroup.eq.1 hnm.symm) i))
  · intro n
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul ((intUnits K.O B.A).subgroupOf B.T) (t n)
    show IsIntegral K.O (((((QuotientGroup.mk (t n) : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T).out : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)
    rw [hw, Subgroup.coe_mul, mul_inv_rev, Units.val_mul, mul_assoc]
    refine IsIntegral.mul w.2.2 ?_
    show IsIntegral K.O (tt f h (d n) (c n) * _)
    rw [hαA]
    unfold tt
    rw [add_mul, Finset.sum_mul]
    refine IsIntegral.add (by rw [one_mul]; exact hia.pow k) (IsIntegral.sum _ fun i _ => ?_)
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (n i).2)
    have h1 : d n i * algebraMap K.E B.A α ^ k = algebraMap K.E B.A α ^ r := by
      have := congrFun (hcd n) i
      simp only [Pi.mul_apply, Pi.one_apply, c, map_pow] at this
      generalize (n i : ℕ) = j at hr this
      rw [hr, pow_add]
      linear_combination algebraMap K.E B.A α ^ r * this
    have h2 : ((d n i - 1) * f i + (c n i - 1) * h i) * algebraMap K.E B.A α ^ k =
        (algebraMap K.E B.A α ^ r - algebraMap K.E B.A α ^ k) * f i +
          (algebraMap K.E B.A α ^ (n i : ℕ) - 1) * h i * algebraMap K.E B.A α ^ k := by
      rw [← h1]; simp only [c, map_pow]; ring
    rw [h2]
    exact (((hia.pow r).sub (hia.pow k)).mul (isIntegral_idem (hf i))).add
      ((((hia.pow _).sub isIntegral_one).mul (isIntegral_idem (hh i))).mul (hia.pow k))

end GlobalTheory.UnitLemma.TorusPts
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

section Prod

variable {R A₁ A₂ : Type} [CommRing R] [CommRing A₁] [CommRing A₂] [Algebra R A₁] [Algebra R A₂]

theorem aeval_prod_fst (x : A₁ × A₂) (f : R[X]) : (aeval x f).1 = aeval x.1 f :=
  (aeval_algHom_apply (AlgHom.fst R A₁ A₂) x f).symm

theorem aeval_prod_snd (x : A₁ × A₂) (f : R[X]) : (aeval x f).2 = aeval x.2 f :=
  (aeval_algHom_apply (AlgHom.snd R A₁ A₂) x f).symm

theorem isIntegral_pair_one {r : A₁} (hr : IsIntegral R r) : IsIntegral R ((r, 1) : A₁ × A₂) := by
  obtain ⟨f, hf, hfr⟩ := hr
  refine ⟨f * (X - C 1), hf.mul (monic_X_sub_C 1), ?_⟩
  rw [← aeval_def, map_mul]
  rw [← aeval_def] at hfr
  ext
  · rw [Prod.fst_mul, aeval_prod_fst, hfr, zero_mul]; rfl
  · rw [Prod.snd_mul, aeval_prod_snd (f := X - C 1)]; simp

theorem isIntegral_one_pair {r : A₂} (hr : IsIntegral R r) : IsIntegral R ((1, r) : A₁ × A₂) := by
  obtain ⟨f, hf, hfr⟩ := hr
  refine ⟨f * (X - C 1), hf.mul (monic_X_sub_C 1), ?_⟩
  rw [← aeval_def, map_mul]
  rw [← aeval_def] at hfr
  ext
  · rw [Prod.fst_mul, aeval_prod_fst (f := X - C 1)]; simp
  · rw [Prod.snd_mul, aeval_prod_snd, hfr, zero_mul]; rfl

theorem isIntegral_fst {x : A₁ × A₂} (hx : IsIntegral R x) : IsIntegral R x.1 := hx.map (AlgHom.fst R A₁ A₂)

theorem isIntegral_snd {x : A₁ × A₂} (hx : IsIntegral R x) : IsIntegral R x.2 := hx.map (AlgHom.snd R A₁ A₂)

end Prod

theorem dlt_map {ι κ A : Type} [CommMonoid A] (π : κ → A) (e : ι ↪ κ) (I : Finset ι) (f : A → ℚ) (y : A) :
    dlt π (I.map e) f y = dlt (π ∘ e) I f y := by
  unfold dlt
  symm
  refine Finset.sum_bij (fun J _ => J.map e) (fun J hJ => ?_) (fun J₁ _ J₂ _ h => Finset.map_injective e h)
    (fun J hJ => ?_) (fun J _ => ?_)
  · exact Finset.mem_powerset.2 (Finset.map_subset_map.2 (Finset.mem_powerset.1 hJ))
  · obtain ⟨u, hu, rfl⟩ := Finset.subset_map_iff.1 (Finset.mem_powerset.1 hJ)
    exact ⟨u, Finset.mem_powerset.2 hu, rfl⟩
  · simp [Finset.prod_map, Finset.card_map]

theorem dlt_empty {ι A : Type} [CommMonoid A] (π : ι → A) (f : A → ℚ) (y : A) : dlt π ∅ f y = f y := by
  simp [dlt]

theorem pos_term_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂) (a : K.O) (N : ℕ) (M : Submodule K.O (B₁.A × B₂.A)) (p : ι₁ ⊕ ι₂ → ℤ) (u₁ : B₁.A) (u₂ : B₂.A), (Pos (B₁.prod B₂) a (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) N M p → Pos B₁ a e₁ N (M.comap (LinearMap.inl K.O B₁.A B₂.A)) (p ∘ Sum.inl) ∧ Pos B₂ a e₂ N (M.map (LinearMap.snd K.O B₁.A B₂.A)) (p ∘ Sum.inr)) ∧ term (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) * (show (B₁.prod B₂).A from (u₁, u₂))) (eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₂.map Function.Embedding.inr) * 1) M = term B₁ π₁ S₁ ∅ (eS B₁ e₁ S₁ * u₁) (eS B₁ e₁ ∅ * 1) (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * term B₂ π₂ ∅ S₂ (eS B₂ e₂ ∅ * u₂) (eS B₂ e₂ S₂ * 1) (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
  intro K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ a N M p u₁ u₂
  refine ⟨fun h => ⟨fun i => ⟨fun r hr => ?_, fun m hm => ?_⟩, fun j => ⟨fun r hr => ?_, fun m hm => ?_⟩⟩, ?_⟩
  · have := (h (Sum.inl i)).1 (r, 1) (isIntegral_pair_one hr)
    have key : (LinearMap.inl K.O B₁.A B₂.A) (al K a ^ ((p ∘ Sum.inl) i + N) • (e₁ i * r)) =
        al K a ^ (p (Sum.inl i) + N) • (((e₁ i, 0) : B₁.A × B₂.A) * (r, 1)) :=
      Prod.ext rfl (by show (0 : B₂.A) = al K a ^ (p (Sum.inl i) + N) • ((0 : B₂.A) * 1); simp)
    rw [Submodule.mem_comap, key]
    exact this
  · exact isIntegral_fst ((h (Sum.inl i)).2 (m, 0) hm)
  · have := (h (Sum.inr j)).1 (1, r) (isIntegral_one_pair hr)
    exact ⟨_, this, rfl⟩
  · obtain ⟨m', hm', rfl⟩ := hm
    exact isIntegral_snd ((h (Sum.inr j)).2 m' hm')
  · have hT : ∀ (z : B₁.A × B₂.A), z ∈ M → ∀ t : B₂.A,
        Algebra.trace K.E (B₁.A × B₂.A) (((0 : B₁.A), t) * z) = Algebra.trace K.E B₂.A (t * z.2) := by
      intro z _ t
      rw [Algebra.trace_prod_apply]
      simp
    have hD : ∀ t : B₂.A, InDual (B₁.prod B₂) ((0 : B₁.A), t) M ↔ InDual B₂ t (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
      intro t
      constructor
      · rintro h z ⟨z', hz', rfl⟩
        show Algebra.trace K.E B₂.A (t * z'.2) ∈ _
        rw [← hT z' hz' t]
        exact h z' hz'
      · intro h z hz
        convert h z.2 ⟨z, hz, rfl⟩ using 1
        exact hT z hz t
    have hE1 : eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A)))
        (S₁.map Function.Embedding.inl) = ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) := by
      unfold eS
      rw [Finset.sum_map]
      show (∑ x ∈ S₁, ((e₁ x, 0) : B₁.A × B₂.A)) = (∑ i ∈ S₁, e₁ i, 0)
      ext <;> simp [Prod.fst_sum, Prod.snd_sum]
    have hE2 : eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A)))
        (S₂.map Function.Embedding.inr) = ((0, eS B₂ e₂ S₂) : B₁.A × B₂.A) := by
      unfold eS
      rw [Finset.sum_map]
      show (∑ x ∈ S₂, ((0, e₂ x) : B₁.A × B₂.A)) = (0, ∑ i ∈ S₂, e₂ i)
      ext <;> simp [Prod.fst_sum, Prod.snd_sum]
    have keyM : ∀ y : B₁.A, indM (B₁.prod B₂) M (LinearMap.inl K.O B₁.A B₂.A y) =
        indM B₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) y := fun y => by
      unfold indM
      classical
      exact if_congr Iff.rfl rfl rfl
    have keyD : ∀ t : B₂.A, indD (B₁.prod B₂) M (((0 : B₁.A), t) : B₁.A × B₂.A) =
        indD B₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) t := fun t => by
      unfold indD
      classical
      exact if_congr (hD t) rfl rfl
    unfold term
    rw [dlt_map, dlt_map, dlt_empty, dlt_empty, hE1, hE2]
    have h0 : ∀ (B : InvAlg K) (e : ι₁ → B.A), eS B e ∅ = 0 := fun _ _ => by simp [eS]
    have h0' : ∀ (B : InvAlg K) (e : ι₂ → B.A), eS B e ∅ = 0 := fun _ _ => by simp [eS]
    rw [h0, h0', zero_mul, zero_mul]
    have hm0 : indM B₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) 0 = 1 := by simp [indM]
    have hd0 : indD B₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) 0 = 1 := by
      simp [indD, InDual]
    rw [hm0, hd0, mul_one, one_mul]
    congr 1
    · unfold dlt
      refine Finset.sum_congr rfl fun J _ => ?_
      congr 1
      unfold indM
      have : (∏ j ∈ J, (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)) ∘ Sum.inl) j) *
          (((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) * (u₁, u₂)) =
          LinearMap.inl K.O B₁.A B₂.A ((∏ j ∈ J, π₁ j) * (eS B₁ e₁ S₁ * u₁)) := by
        ext <;> simp [Prod.fst_prod, Prod.snd_prod]
      exact (congrArg (indM (B₁.prod B₂) M) this).trans (keyM _)
    · unfold dlt
      refine Finset.sum_congr rfl fun J _ => ?_
      congr 1
      have : (∏ j ∈ J, (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)) ∘ Sum.inr) j) *
          (((0, eS B₂ e₂ S₂) : B₁.A × B₂.A) * 1) = ((0 : B₁.A), (∏ j ∈ J, π₂ j) * (eS B₂ e₂ S₂ * 1)) := by
        ext <;> simp [Prod.fst_prod, Prod.snd_prod]
      exact (congrArg (indD (B₁.prod B₂) M) this).trans (keyD _)

end GlobalTheory.UnitLemma.Desc
end
end

section

open ReciprocityTheory.Gal
namespace GlobalTheory.ShapeNeg

theorem int_dvd_of_mem_span_pow {O : Type} [CommRing O] [IsDomain O] {p : ℕ} (hp : p.Prime)
    [IsLocalRing O] (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hp0 : (p : O) ≠ 0) (n : ℕ) (z : ℤ)
    (hz : (z : O) ∈ Ideal.span {(p : O) ^ n}) : (p : ℤ) ^ n ∣ z := by
  have hd : z.gcd ((p : ℤ) ^ n) ∣ p ^ n := by
    have := Int.gcd_dvd_right (a := z) (b := (p : ℤ) ^ n)
    have h2 : ((z.gcd ((p : ℤ) ^ n) : ℕ) : ℤ) ∣ ((p ^ n : ℕ) : ℤ) := by push_cast; exact this
    exact_mod_cast h2
  obtain ⟨m, hm, hgm⟩ := (Nat.dvd_prime_pow hp).1 hd
  rcases lt_or_eq_of_le hm with hlt | heq
  · exfalso
    have hb := Int.gcd_eq_gcd_ab z ((p : ℤ) ^ n)
    rw [hgm] at hb
    have hmem : ((p : O) ^ m) ∈ Ideal.span {(p : O) ^ n} := by
      have : (((p ^ m : ℕ) : ℤ) : O) = (z : O) * (z.gcdA ((p : ℤ) ^ n) : O)
          + ((p : O) ^ n) * (z.gcdB ((p : ℤ) ^ n) : O) := by
        rw [hb]; push_cast; ring
      have e : (((p ^ m : ℕ) : ℤ) : O) = (p : O) ^ m := by push_cast; ring
      rw [← e, this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hz)
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hmem
    have hsplit : (p : O) ^ n = (p : O) ^ m * (p : O) ^ (n - m) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, mul_assoc] at hc
    have h1 : (p : O) ^ (n - m) * c = 1 := by
      have hne : (p : O) ^ m ≠ 0 := pow_ne_zero _ hp0
      have := mul_left_cancel₀ hne (hc.symm.trans (mul_one _).symm)
      exact this
    have hu : IsUnit ((p : O) ^ (n - m)) := isUnit_iff_exists_inv.2 ⟨c, h1⟩
    rw [isUnit_pow_iff (Nat.sub_ne_zero_of_lt hlt)] at hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hpm hu
  · have := Int.gcd_dvd_left (a := z) (b := (p : ℤ) ^ n)
    rw [hgm, heq] at this
    exact_mod_cast this

theorem cyc_char_pow_ne_one : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], (p : O) ∈ IsLocalRing.maximalIdeal O → (p : O) ≠ 0 →
    ∀ ε : Formalism.GaloisCohomology.GK p K →* Oˣ, (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ k : ℕ,
    (∃ (σ : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 ∧ (σ ^ k) ζ ≠ ζ) →
    ∃ σ : Formalism.GaloisCohomology.GK p K, ε σ ^ k ≠ 1 := by
  intro p hpF K O _ _ _ hpm hp0 ε hcyc k ⟨σ, n, ζ, hζ, hne⟩
  refine ⟨σ, fun hk => hne ?_⟩
  obtain ⟨a, ha, hmem⟩ := hcyc (σ ^ k) n ζ hζ
  rw [map_pow, hk, Units.val_one] at hmem
  have hz : (((a : ℤ) - 1 : ℤ) : O) ∈ Ideal.span {(p : O) ^ n} := by
    have := (Ideal.neg_mem_iff _).2 hmem
    push_cast
    convert this using 1; ring
  obtain ⟨t, ht⟩ := int_dvd_of_mem_span_pow hpF.out hpm hp0 n _ hz
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ hpF.out.ne_zero)] at hζ
    exact zero_ne_one hζ
  rw [ha, ← zpow_natCast, show (a : ℤ) = 1 + (p : ℤ) ^ n * t by omega, zpow_add₀ hζ0, zpow_mul,
    zpow_one]
  have : ζ ^ ((p : ℤ) ^ n) = 1 := by
    rw [show ((p : ℤ) ^ n) = ((p ^ n : ℕ) : ℤ) by push_cast; rfl, zpow_natCast, hζ]
  rw [this, one_zpow, mul_one]

end GlobalTheory.ShapeNeg
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.eulerOperator_injective_eigenvector : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : ∀ v, X v → ℂ) (s : ι → ℝ) (B : (∀ v, X v) → (H →L[ℂ] H)) (Z : ι → (H →L[ℂ] H)), (∀ v, a v (x0 v) = 1) → Summable s → (∀ v, s v < 1) → (∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, ‖a v x‖ ≤ s v) → (∀ f, ‖B f‖ ≤ 1) → B x0 = 1 → (∀ v (f : ∀ v, X v), {w | f w ≠ x0 w}.Finite → f v = x0 v → HasSum (fun x => a v x • B (Function.update f v x)) (B f * Z v)) → ∃ W : H →L[ℂ] H, HasSum (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => (∏ᶠ v, a v (f.1 v)) • B f.1) W ∧ Function.Injective W ∧ ∀ (y : H) (z : ι → ℂ), (∀ v, Z v y = z v • y) → W y = (∏' v, z v) • y := by
  first | exact @GlobalTheory.eulerOp_injective_eigen | exact GlobalTheory.eulerOp_injective_eigen | (intros; apply GlobalTheory.eulerOp_injective_eigen <;> assumption)
end

section


theorem _root_.GlobalTheory.T.norm_apply_neg_mul_sub_sub_le_mul : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (σ : E →+* E) (r M Mi Z : Matrix n n E) (a s t : ℝ), 0 ≤ a → 0 ≤ s → 0 ≤ t → (∀ x, ‖σ x‖ = ‖x‖) → M * Mi = 1 → r * M.map σ = M → Z.map σ = Z → (∀ i j, ‖M i j‖ ≤ a) → (∀ i j, ‖(Mi - Z) i j‖ ≤ s) → (∀ i j, ‖(r - 1) i j‖ ≤ t) → ∀ i j, ‖σ (-(M * Z) i j) - (-(M * Z) i j) - (r - 1) i j‖ ≤ t * (a * s) := by
  first | exact @GlobalTheory.normalisedPeriod_algebraic_estimate | exact GlobalTheory.normalisedPeriod_algebraic_estimate | (intros; apply GlobalTheory.normalisedPeriod_algebraic_estimate <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.exists_hyperplane_residue_outside_translates : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) O, (¬ ∃ (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)) → ∃ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 ∧ ∀ g : GL (Fin r) (IsLocalRing.ResidueField O), (∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).mulVec v = v) → ∀ L : Matrix (Fin r) (Fin r) O, L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) → ∃ h : GL (Fin r ⊕ Fin t) O, (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j ∈ Ideal.span {ϖ}) ∧ (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}) ∧ (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) * (Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O) * x) = x := by
  first | exact @GlobalTheory.gen_type_core | exact GlobalTheory.gen_type_core | (intros; apply GlobalTheory.gen_type_core <;> assumption)
end

section


theorem _root_.GlobalTheory.T.norm_sub_one_le_of_norm_pow_prime_sub_one_le : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (X : Matrix n n ℚ_[l]) (k : ℕ), (∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-2 : ℤ)) → (∀ i j, ‖(X ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2))) → ∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
  first | exact @GlobalTheory.matrix_near_one_pow_prime_deep | exact GlobalTheory.matrix_near_one_pow_prime_deep | (intros; apply GlobalTheory.matrix_near_one_pow_prime_deep <;> assumption)
end

section


theorem _root_.GlobalTheory.T.norm_pow_prime_sub_one_le_of_norm_sub_one_le : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (X : Matrix n n ℚ_[l]) (k : ℕ), (∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) → ∀ i j, ‖(X ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) := by
  first | exact @GlobalTheory.pow_prime_sub_one_norm_le | exact GlobalTheory.pow_prime_sub_one_norm_le | (intros; apply GlobalTheory.pow_prime_sub_one_norm_le <;> assumption)
end
