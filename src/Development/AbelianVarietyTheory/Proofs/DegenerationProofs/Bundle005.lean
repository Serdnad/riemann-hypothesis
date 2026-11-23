module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.PowerSeries.Expand
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

section

namespace GlobalTheory

open IsLocalRing


open IsLocalRing in
theorem _root_.GlobalTheory.exists_arithFrobenius_absGalois (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (hfin : Finite (IsLocalRing.ResidueField V)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω] [IsLocalRing (integralClosure V Ω)] : ∃ φ : Ω ≃ₐ[K] Ω, ∀ x : integralClosure V Ω, ∃ y : integralClosure V Ω, (y : Ω) = φ x ∧ y - x ^ Nat.card (IsLocalRing.ResidueField V) ∈ IsLocalRing.maximalIdeal (integralClosure V Ω) := by
  classical
  haveI : Algebra.IsIntegral K Ω := inferInstance
  letI : TopologicalSpace (integralClosure V Ω) := ⊥
  haveI : DiscreteTopology (integralClosure V Ω) := ⟨rfl⟩
  haveI : ContinuousSMul (Ω ≃ₐ[K] Ω) (integralClosure V Ω) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    convert stabilizer_isOpen_of_isIntegral (K := K) (L := Ω) (x : Ω) using 2
    ext g
    simp [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
  haveI : Algebra.IsInvariant V (integralClosure V Ω) (Ω ≃ₐ[K] Ω) := by
    refine ⟨fun x hx => ?_⟩
    have hmem : (x : Ω) ∈ IntermediateField.fixedField (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) := by
      rintro ⟨g, -⟩
      exact congrArg Subtype.val (hx g)
    rw [InfiniteGalois.fixedField_bot, IntermediateField.mem_bot] at hmem
    obtain ⟨k, hk⟩ := hmem
    have hx2 : IsIntegral V (x : Ω) := x.2
    rw [← hk] at hx2
    have hint : IsIntegral V k :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom V K Ω) (algebraMap K Ω).injective).mp hx2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨v, Subtype.ext ?_⟩
    simp [IsScalarTower.algebraMap_apply V K Ω, hv, hk]
  haveI : (maximalIdeal (integralClosure V Ω)).LiesOver (maximalIdeal V) := by
    refine ⟨(IsLocalRing.eq_maximalIdeal ?_).symm⟩
    exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := V)
      (maximalIdeal (integralClosure V Ω))
  letI : Fintype (V ⧸ maximalIdeal V) := @Fintype.ofFinite _ hfin
  letI : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  letI : Field (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) :=
    Ideal.Quotient.field _
  haveI : Algebra.IsIntegral (V ⧸ maximalIdeal V)
      (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) := inferInstance
  haveI : Algebra.IsAlgebraic (V ⧸ maximalIdeal V)
      (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) := Algebra.IsIntegral.isAlgebraic
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[K] Ω)
    (maximalIdeal V) (maximalIdeal (integralClosure V Ω))
    (FiniteField.frobeniusAlgEquivOfAlgebraic (V ⧸ maximalIdeal V) _)
  refine ⟨g.1, fun x => ⟨g.1 • x, rfl, ?_⟩⟩
  rw [← Ideal.Quotient.eq]
  have h := congrArg (fun e => e (Ideal.Quotient.mk (maximalIdeal (integralClosure V Ω)) x)) hg
  simp only [Ideal.Quotient.stabilizerHom_apply, FiniteField.frobeniusAlgEquivOfAlgebraic_apply] at h
  rw [Fintype.card_eq_nat_card] at h
  rw [map_pow]
  exact h

end GlobalTheory
end

section

open Module

namespace GlobalTheory

private theorem int_eq_zero_of_forall_pow_dvd (n : ℕ) (hn : 2 ≤ n) (c : ℤ)
    (h : ∀ j : ℕ, (n : ℤ) ^ j ∣ c) : c = 0 := by
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h c.natAbs) ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)

private theorem eq_zero_of_forall_pow_nsmul_dvd (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (n : ℕ) (hn : 2 ≤ n) (z : X) (h : ∀ j : ℕ, ∃ μ : X, z = n ^ j • μ) :
    z = 0 := by
  set b := Module.Free.chooseBasis ℤ X
  apply b.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  refine int_eq_zero_of_forall_pow_dvd n hn _ fun j => ?_
  obtain ⟨μ, hμ⟩ := h j
  refine ⟨b.repr μ i, ?_⟩
  rw [hμ, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  push_cast
  ring


open Module in
theorem _root_.GlobalTheory.existsUnique_addEquiv_of_compatible_congr :
    ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (n : ℕ), 2 ≤ n → ∀ r : ℕ → X → X' → Prop, (∀ j x, ∃ x', r j x x') → (∀ j x', ∃ x, r j x x') → (∀ j x y x' y', r j x x' → r j y y' → r j (x + y) (x' + y')) → (∀ j x y x' y', r j x x' → r j y y' → ((∃ μ, y = x + n ^ j • μ) ↔ ∃ μ', y' = x' + n ^ j • μ')) → (∀ j x x' μ μ', r j x x' → r j (x + n ^ j • μ) (x' + n ^ j • μ')) → (∀ x, ∃ x', ∀ j, r j x x') → (∀ x', ∃ x, ∀ j, r j x x') → ∃! e : X ≃+ X', ∀ j x, r j x (e x) := by
  intro X X' _ _ _ _ _ _ n hn r _ _ hadd hcong _ hfwd hbwd
  have sepR : ∀ x x' y', (∀ j, r j x x') → (∀ j, r j x y') → x' = y' := by
    intro x x' y' hx hy
    refine (sub_eq_zero.1 (eq_zero_of_forall_pow_nsmul_dvd X' n hn (y' - x') fun j => ?_)).symm
    obtain ⟨μ', hμ'⟩ := (hcong j x x x' y' (hx j) (hy j)).1 ⟨0, by simp⟩
    exact ⟨μ', by rw [hμ', add_sub_cancel_left]⟩
  have sepL : ∀ x y x', (∀ j, r j x x') → (∀ j, r j y x') → x = y := by
    intro x y x' hx hy
    refine (sub_eq_zero.1 (eq_zero_of_forall_pow_nsmul_dvd X n hn (y - x) fun j => ?_)).symm
    obtain ⟨μ, hμ⟩ := (hcong j x y x' x' (hx j) (hy j)).2 ⟨0, by simp⟩
    exact ⟨μ, by rw [hμ, add_sub_cancel_left]⟩
  choose f hf using hfwd
  have fadd : ∀ x y, f (x + y) = f x + f y := fun x y =>
    sepR _ _ _ (hf (x + y)) fun j => hadd j x y _ _ (hf x j) (hf y j)
  have bij : Function.Bijective f := by
    refine ⟨fun x y hxy => sepL x y (f x) (hf x) fun j => ?_, fun x' => ?_⟩
    · rw [hxy]
      exact hf y j
    · obtain ⟨x, hx⟩ := hbwd x'
      exact ⟨x, sepR _ _ _ (hf x) hx⟩
  refine ⟨AddEquiv.ofBijective (AddMonoidHom.mk' f fadd) bij, fun j x => hf x j, fun e he => ?_⟩
  ext x
  exact sepR x (e x) (f x) (fun j => he j x) (hf x)

end GlobalTheory
end

section

namespace GlobalTheory.CharacterSumInverse

open scoped BigOperators

theorem charSum_inv {o : Type} [CommRing o] [IsDomain o] {T : Type} [CommGroup T] [Fintype T]
    [HasEnoughRootsOfUnity o (Monoid.exponent T)] [Fintype (T →* oˣ)] [DecidableEq T] (t : T) :
    (∑ c : T →* oˣ, ((c t)⁻¹ : oˣ).val) = if t = 1 then (Fintype.card T : o) else 0 := by
  classical
  have hinv : ∀ c : T →* oˣ, ((c t)⁻¹ : oˣ).val = (c t⁻¹).val := fun c => by rw [map_inv]
  simp_rw [hinv]
  split_ifs with ht
  · subst ht
    simp only [inv_one, map_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
    have h := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity T o
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    rw [h]
  · have hs : t⁻¹ ≠ 1 := by simpa using ht
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity T o hs
    set S := ∑ c : T →* oˣ, (c t⁻¹).val with hS
    have hshift : (∑ c : T →* oˣ, ((φ * c) t⁻¹).val) = S :=
      Fintype.sum_equiv (Equiv.mulLeft φ) _ _ (fun _ => rfl)
    have hmul : (∑ c : T →* oˣ, ((φ * c) t⁻¹).val) = (φ t⁻¹).val * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      simp [MonoidHom.mul_apply, Units.val_mul]
    have h0 : ((φ t⁻¹).val - 1) * S = 0 := by
      rw [sub_mul, ← hmul, hshift, one_mul, sub_self]
    have hne : (φ t⁻¹).val - 1 ≠ 0 := by
      intro h
      apply hφ
      exact Units.val_eq_one.mp (sub_eq_zero.mp h)
    exact (mul_eq_zero.mp h0).resolve_left hne

theorem main : (let d1 : {o : Type} → [inst : CommRing o] → {T : Type} → [inst_1 : CommGroup T] → {M : Type} → [inst_2 : AddCommGroup M] → [inst_3 : Module o M] → [Fintype T] → Representation o T M → o → (T →* oˣ) → M →ₗ[o] M := @(fun {o : Type} [CommRing o] {T : Type} [CommGroup T] {M : Type} [AddCommGroup M] [Module o M] [Fintype T] (ρ : Representation o T M) (u : o) (c : T →* oˣ) ↦ u • ∑ t : T, (↑((c : T → oˣ) t)⁻¹ : o) • (ρ : T → M →ₗ[o] M) t); ∀ {o : Type} [inst : CommRing o] {T : Type} [inst_1 : CommGroup T] {M : Type} [inst_2 : AddCommGroup M] [inst_3 : Module o M] [inst_4 : Fintype T] (ρ : Representation o T M) (u : o) [IsDomain o] [HasEnoughRootsOfUnity o (Monoid.exponent T)] [inst_7 : Fintype (T →* oˣ)], u * (↑(Fintype.card T) : o) = (1 : o) → ∀ (x : M), ∑ c : T →* oˣ, (d1 ρ u c : M → M) x = x) := by
  intro d1 o _ T _ M _ _ _ ρ u _ _ _ hu x
  classical
  simp only [d1, LinearMap.smul_apply, LinearMap.sum_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_smul, charSum_inv]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_one,
    Module.End.one_apply]
  rw [smul_smul, hu, one_smul]

end GlobalTheory.CharacterSumInverse
end

section

namespace GlobalTheory.Degen

open MvPolynomial

theorem exists_form_limit_ideal (R : Type) [CommRing R] (I : Ideal R) (hI : IsAdicComplete I R)
    (σ : Type) [Finite σ] (K : ℕ → Ideal (MvPolynomial σ R)) (t : ℕ)
    (hK : ∀ e F, F.IsHomogeneous t → F ∈ K (e + 1) → F ∈ K e)
    (ha : ∀ e, ∀ a ∈ I ^ (e + 1), MvPolynomial.C a ∈ K e)
    (hs : ∀ e F, F.IsHomogeneous t → F ∈ K e → ∃ G : MvPolynomial σ R, G.IsHomogeneous t ∧
      (∀ d, AddMonoidAlgebra.coeff G d ∈ I ^ (e + 1)) ∧ F - G ∈ K (e + 1))
    (e : ℕ) (F : MvPolynomial σ R) (hF : F.IsHomogeneous t) (hFe : F ∈ K e) :
    ∃ F₁ : MvPolynomial σ R, F₁.IsHomogeneous t ∧ (∀ e', F₁ ∈ K e') ∧
      ∀ d, AddMonoidAlgebra.coeff (F - F₁) d ∈ I ^ (e + 1) := by
  classical
  have hdesc : ∀ (P : MvPolynomial σ R), P.IsHomogeneous t → ∀ m k, P ∈ K (m + k) → P ∈ K m := by
    intro P hP m k
    induction k with
    | zero => exact id
    | succ k ih => exact fun h => ih (hK _ _ hP h)
  have hcoef : ∀ (j : ℕ) (P : MvPolynomial σ R), (∀ d, AddMonoidAlgebra.coeff P d ∈ I ^ (j + 1)) → P ∈ K j := by
    intro j P hP
    rw [P.as_sum]
    refine Ideal.sum_mem _ fun d _ => ?_
    have : (monomial d (AddMonoidAlgebra.coeff P d) : MvPolynomial σ R) = C (AddMonoidAlgebra.coeff P d) * monomial d 1 := by
      rw [C_mul_monomial, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (ha _ _ (hP d))
  choose G hG1 hG2 hG3 using hs
  let s : (n : ℕ) → {P : MvPolynomial σ R // P.IsHomogeneous t ∧ P ∈ K (e + n)} := fun n =>
    Nat.rec (motive := fun n => {P : MvPolynomial σ R // P.IsHomogeneous t ∧ P ∈ K (e + n)})
      ⟨F, hF, hFe⟩
      (fun n z => ⟨z.1 - G (e + n) z.1 z.2.1 z.2.2, z.2.1.sub (hG1 _ _ _ _), hG3 _ _ _ _⟩) n
  have hs0 : (s 0).1 = F := rfl
  have hsn : ∀ n, (s (n + 1)).1 = (s n).1 - G (e + n) (s n).1 (s n).2.1 (s n).2.2 :=
    fun n => rfl
  have hd : ∀ d m n, m ≤ n → AddMonoidAlgebra.coeff (s m).1 d - AddMonoidAlgebra.coeff (s n).1 d ∈ I ^ (e + m + 1) := by
    intro d m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hsn, MvPolynomial.coeff_sub, ← sub_add]
      exact Ideal.add_mem _ ih
        (Ideal.pow_le_pow_right (by omega) (hG2 (e + n) (s n).1 (s n).2.1 (s n).2.2 d))
  have hmem : ∀ (n : ℕ) (z : R), z ∈ (I ^ n • ⊤ : Submodule R R) ↔ z ∈ I ^ n := by
    intro n z
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have hlim : ∀ d, ∃ L : R, ∀ m, AddMonoidAlgebra.coeff (s m).1 d - L ∈ I ^ (e + m + 1) := by
    intro d
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := R) hI.toIsPrecomplete
      (f := fun n => AddMonoidAlgebra.coeff (s n).1 d) (by
        intro m n hmn
        rw [SModEq.sub_mem, hmem]
        exact Ideal.pow_le_pow_right (by omega) (hd d m n hmn))
    refine ⟨L, fun m => ?_⟩
    have h := hL (e + m + 1)
    rw [SModEq.sub_mem, hmem] at h
    have h2 := Ideal.add_mem _ (hd d m (e + m + 1) (by omega)) h
    simpa using h2
  choose L hL using hlim
  have hfin : {d : σ →₀ ℕ | d.degree = t}.Finite :=
    (Finsupp.finite_of_degree_le t).subset fun d hd => le_of_eq hd
  let F₁ : MvPolynomial σ R := ∑ d ∈ hfin.toFinset, monomial d (L d)
  have hF₁ : F₁.IsHomogeneous t :=
    IsHomogeneous.sum _ _ _ fun d hd => isHomogeneous_monomial _ (by simpa using hd)
  have hc : ∀ m d, AddMonoidAlgebra.coeff ((s m).1 - F₁) d ∈ I ^ (e + m + 1) := by
    intro m d
    by_cases hdt : d.degree = t
    · have : AddMonoidAlgebra.coeff F₁ d = L d := by
        simp only [F₁, coeff_sum, coeff_monomial]
        rw [Finset.sum_ite_eq']
        simp [hdt]
      rw [MvPolynomial.coeff_sub, this]
      exact hL d m
    · rw [((s m).2.1.sub hF₁).coeff_eq_zero hdt]
      exact Ideal.zero_mem _
  refine ⟨F₁, hF₁, fun m => hdesc _ hF₁ m e ?_, hc 0⟩
  rw [add_comm m e]
  have h := Ideal.sub_mem _ (s m).2.2 (hcoef _ _ (hc m))
  simpa using h

end GlobalTheory.Degen
end

section

open PowerSeries

namespace GlobalTheory

namespace SeriesRoot

variable {O : Type*} [CommRing O]

noncomputable def residuePart (k l : ℕ) : PowerSeries O →+ PowerSeries O where
  toFun f := PowerSeries.mk fun n => coeff (k * n + l) f
  map_zero' := by ext n; simp
  map_add' f g := by ext n; simp

theorem coeff_residuePart (k l n : ℕ) (f : PowerSeries O) :
    coeff n (residuePart k l f) = coeff (k * n + l) f := by
  simp [residuePart]

theorem coeff_X_pow_mul_expand {k : ℕ} (hk : k ≠ 0) {j : ℕ} (hj : j < k) (g : PowerSeries O)
    (m : ℕ) :
    coeff m (X ^ j * expand k hk g) = if m % k = j then coeff (m / k) g else 0 := by
  rw [coeff_X_pow_mul', coeff_expand]
  by_cases h : m % k = j
  · have hm : m = k * (m / k) + j := by rw [← h]; exact (Nat.div_add_mod m k).symm
    have h1 : j ≤ m := by omega
    have h2 : m - j = k * (m / k) := by omega
    rw [if_pos h1, if_pos h, h2, if_pos (dvd_mul_right _ _),
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hk)]
  · rw [if_neg h]
    split_ifs with h1 h2
    · exfalso
      obtain ⟨c, hc⟩ := h2
      apply h
      have : m = j + k * c := by omega
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    · rfl
    · rfl

theorem sum_residuePart {k : ℕ} (hk : k ≠ 0) (f : PowerSeries O) :
    ∑ l ∈ Finset.range k, X ^ l * expand k hk (residuePart k l f) = f := by
  ext m

  rw [map_sum, Finset.sum_congr rfl
  (fun l hl => coeff_X_pow_mul_expand hk (Finset.mem_range.1 hl) _ m), Finset.sum_ite_eq,
  if_pos (Finset.mem_range.2 (Nat.mod_lt _ (Nat.pos_of_ne_zero hk))), coeff_residuePart,
  Nat.div_add_mod]

theorem residuePart_X_pow_mul_expand {k : ℕ} (hk : k ≠ 0) {j l : ℕ} (hj : j < k) (hl : l < k)
    (g : PowerSeries O) :
    residuePart k l (X ^ j * expand k hk g) = if l = j then g else 0 := by
  ext n
  rw [coeff_residuePart, coeff_X_pow_mul_expand hk hj, Nat.mul_add_mod, Nat.mod_eq_of_lt hl,
    Nat.mul_add_div (Nat.pos_of_ne_zero hk), Nat.div_eq_of_lt hl, add_zero]
  split_ifs <;> simp

variable {K : Type*} [CommRing K]

noncomputable def extendAdd (φ : PowerSeries O →+* K) (k : ℕ) (t : K) : PowerSeries O →+ K where
  toFun f := ∑ l ∈ Finset.range k, t ^ l * φ (residuePart k l f)
  map_zero' := by simp
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]

theorem extendAdd_apply (φ : PowerSeries O →+* K) (k : ℕ) (t : K) (f : PowerSeries O) :
    extendAdd φ k t f = ∑ l ∈ Finset.range k, t ^ l * φ (residuePart k l f) := rfl

theorem extendAdd_X_pow_mul_expand_of_lt (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) (t : K)
    {j : ℕ} (hj : j < k) (g : PowerSeries O) :
    extendAdd φ k t (X ^ j * expand k hk g) = t ^ j * φ g := by
  rw [extendAdd_apply, Finset.sum_eq_single j]
  · rw [residuePart_X_pow_mul_expand hk hj hj, if_pos rfl]
  · intro l hl hlj
    rw [residuePart_X_pow_mul_expand hk hj (Finset.mem_range.1 hl), if_neg hlj, map_zero,
      mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 hj) h

theorem extendAdd_X_pow_mul_expand (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) (j : ℕ) (g : PowerSeries O) :
    extendAdd φ k t (X ^ j * expand k hk g) = t ^ j * φ g := by
  have h : (X : PowerSeries O) ^ j * expand k hk g =
      X ^ (j % k) * expand k hk (X ^ (j / k) * g) := by
    rw [map_mul, map_pow, expand_X, ← pow_mul, ← mul_assoc, ← pow_add, Nat.mod_add_div]
  rw [h, extendAdd_X_pow_mul_expand_of_lt φ hk t (Nat.mod_lt _ (Nat.pos_of_ne_zero hk)),
    map_mul, map_pow, ← ht, ← pow_mul, ← mul_assoc, ← pow_add, Nat.mod_add_div]

theorem extendAdd_mul (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) (f g : PowerSeries O) :
    extendAdd φ k t (f * g) = extendAdd φ k t f * extendAdd φ k t g := by
  conv_lhs => rw [← sum_residuePart hk f, ← sum_residuePart hk g]

  rw [extendAdd_apply φ k t f, extendAdd_apply φ k t g, Finset.sum_mul_sum, Finset.sum_mul_sum,
  map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_mul_mul_comm, ← pow_add, ← map_mul, extendAdd_X_pow_mul_expand φ hk ht, map_mul,
    pow_add]
  ring

noncomputable def extendHom (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) : PowerSeries O →+* K where
  toFun := extendAdd φ k t
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by simpa using extendAdd_X_pow_mul_expand φ hk ht 0 1
  map_mul' := extendAdd_mul φ hk ht

theorem extendHom_expand (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) (g : PowerSeries O) : extendHom φ hk ht (expand k hk g) = φ g := by
  have := extendAdd_X_pow_mul_expand φ hk ht 0 g
  rw [pow_zero, pow_zero, one_mul, one_mul] at this
  exact this

theorem extendHom_X (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) : extendHom φ hk ht X = t := by
  have := extendAdd_X_pow_mul_expand φ hk ht 1 1
  rw [pow_one, pow_one, map_one, map_one, mul_one, mul_one] at this
  exact this

end SeriesRoot

theorem exists_ringHom_powerSeries_root :
    ∀ (O K : Type) [CommRing O] [CommRing K] (φ : PowerSeries O →+* K) (k : ℕ) (t : K), 0 < k →
      t ^ k = φ PowerSeries.X → ∃ Φ : PowerSeries O →+* K,
        (∀ a, Φ (PowerSeries.C a) = φ (PowerSeries.C a)) ∧ Φ PowerSeries.X = t ∧
          ∀ f, Φ f ∈ Subring.closure (Set.range φ ∪ {t}) := by
  intro O K _ _ φ k t hk ht
  refine ⟨SeriesRoot.extendHom φ hk.ne' ht, fun a => ?_, SeriesRoot.extendHom_X φ hk.ne' ht,
    fun f => ?_⟩
  · rw [← SeriesRoot.extendHom_expand φ hk.ne' ht (PowerSeries.C a), expand_C]
  · change ∑ l ∈ Finset.range k, t ^ l * φ (SeriesRoot.residuePart k l f) ∈ _
    refine Subring.sum_mem _ fun l _ => Subring.mul_mem _ (Subring.pow_mem _ ?_ l) ?_
    · exact Subring.subset_closure (Or.inr rfl)
    · exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)

end GlobalTheory
end
