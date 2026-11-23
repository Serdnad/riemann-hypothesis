module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle001
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.RingTheory.Filtration

@[expose] public section

section

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

section Lau

variable {C K : Type} [CommRing C] [CommRing K] [Algebra C K] (P : ℤ → Submodule C K) [SetLike.GradedMonoid P]

theorem coeff_mul_mem {p q : AddMonoidAlgebra K ℤ} (j : ℤ) (M : Submodule C K)
    (h : ∀ a b, a + b = j → p.coeff a * q.coeff b ∈ M) : (p * q).coeff j ∈ M := by
  classical
  rw [AddMonoidAlgebra.coeff_mul]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  dsimp only
  split_ifs with e
  · exact h a b e
  · exact zero_mem _

def lauSub : Subalgebra C (AddMonoidAlgebra K ℤ) where
  carrier := {p | ∀ j, p.coeff j ∈ P j}
  mul_mem' {p q} hp hq j := coeff_mul_mem j _ fun a b e => e ▸ SetLike.mul_mem_graded (hp a) (hq b)
  add_mem' {p q} hp hq j := add_mem (hp j) (hq j)
  algebraMap_mem' c j := by
    classical
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with e
    · subst e
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (SetLike.one_mem_graded P)
    · exact zero_mem _

theorem single_mem_lauSub {j : ℤ} {x : K} (hx : x ∈ P j) : AddMonoidAlgebra.single j x ∈ lauSub P := by
  classical
  intro i
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with e
  · subst e
    exact hx
  · exact zero_mem _

variable [IsLocalRing C]

structure HasVertex : Prop where
  zero : ∀ x ∈ P 0, ∃ c : C, algebraMap C K c = x
  cross : ∀ j, j ≠ 0 → ∀ x ∈ P j, ∀ y ∈ P (-j), ∃ c ∈ maximalIdeal C, algebraMap C K c = x * y


variable {P} in
def vertex (h : HasVertex P) : Ideal (lauSub P) where
  carrier := {p | ∃ c ∈ maximalIdeal C, algebraMap C K c = p.1.coeff 0}
  add_mem' := by
    rintro p q ⟨c, h1, h2⟩ ⟨d, h3, h4⟩
    exact ⟨c + d, add_mem h1 h3, by rw [map_add (f := _), h2, h4]; rfl⟩
  zero_mem' := ⟨0, zero_mem _, map_zero _⟩
  smul_mem' := by
    rintro q p ⟨c, h1, h2⟩
    refine Submodule.mem_map.1 (coeff_mul_mem (p := q.1) (q := p.1) 0
      (Submodule.map (Algebra.linearMap C K) (maximalIdeal C)) fun a b e => Submodule.mem_map.2 ?_)
    by_cases h0 : a = 0
    · subst h0
      rw [zero_add] at e
      subst e
      obtain ⟨d, hd⟩ := h.zero _ (q.2 0)
      exact ⟨d * c, Ideal.mul_mem_left _ _ h1, by rw [← hd, ← h2, ← map_mul]; rfl⟩
    · obtain rfl : b = -a := by omega
      exact h.cross a h0 _ (q.2 a) _ (p.2 _)

variable {P} in
theorem mem_vertex (h : HasVertex P) {p : lauSub P} :
    p ∈ UpperTheory.V.Fr.vertex (P := P) h ↔
      ∃ c ∈ maximalIdeal C, algebraMap C K c = p.1.coeff 0 := Iff.rfl

end Lau

section Part

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} (C : Type) [CommRing C] {K : Type}
  [CommRing K] [Algebra C K] (ρ : NRep F n K)

def NRep.part (j : ℤ) : Submodule C K := Submodule.span C (ρ.mon j)

instance : SetLike.GradedMonoid (ρ.part C) where
  one_mem := Submodule.subset_span ⟨[], by simp, by simp⟩
  mul_mem i j x y hx hy := by
    have := Submodule.mul_mem_mul hx hy
    rw [NRep.part, NRep.part, Submodule.span_mul_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨L, h1, rfl⟩, _, ⟨M, h2, rfl⟩, rfl⟩
    exact ⟨L ++ M, by simp only [List.map_append, List.sum_append, h1, h2], by simp⟩

theorem NRep.r_mem_part (g : F.G0) (i j : Fin n) : ρ.r g i j ∈ ρ.part C (w n i - w n j) :=
  Submodule.subset_span ⟨[(g, i, j)], by simp, by simp⟩

end Part

variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ}

structure IsVertexRing (C : Type) [CommRing C] [IsLocalRing C] {D : Type} [CommRing D] [Algebra C D] (𝔪 : Ideal D) :
    Prop where
  noeth : IsNoetherianRing D
  inj : Function.Injective (algebraMap C D)
  sep : ⨅ N : ℕ, 𝔪 ^ N = ⊥
  comap : 𝔪.comap (algebraMap C D) = maximalIdeal C
  surj : ∀ d : D, ∃ c : C, d - algebraMap C D c ∈ 𝔪

structure IsModel (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {D : Type} [CommRing D] [Algebra C D]
    (𝔪 : Ideal D) (ρ : NRep F n D) : Prop where
  cont : ρ.Cont 𝔪
  off : ∀ g i j, i ≠ j → ρ.r g i j ∈ 𝔪
  dg : ∀ g i, ∃ c : C, algebraMap C D c = ρ.r g i i ∧
    res O C c = ((F.Ψ g ^ w n i : (ResidueField O)ˣ) : ResidueField O)
  psi : ∀ v i g, ∃ c : C, algebraMap C D c = ρ.ψ v i g ∧
    res O C c = ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O)
  mon : ∀ x ∈ ρ.mon 0, ∃ c : C, algebraMap C D c = x

end UpperTheory.V.Fr
end
end

section

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [CommRing K]

def cor : Fin 2 → Fin 3 := ![0, 2]

theorem w_cor (i : Fin 2) : w 3 (cor i) = w 2 i := by
  fin_cases i <;> rfl

structure IsCorner (ρ : NRep F 3 K) (σ : NRep F 2 K) : Prop where
  odd : ∀ g i j, Odd (w 3 i - w 3 j) → ρ.r g i j = 0
  r : ∀ g i j, σ.r g i j = ρ.r g (cor i) (cor j)
  ψ : ∀ v i g, σ.ψ v i g = ρ.ψ v (cor i) g
  mid : ∀ v g, ρ.r (F.loc0 v g) 1 1 = ρ.ψ v 1 g

def CornerUnits (ρ : NRep F 3 K) : Prop :=
  ∀ v, ∃ g, IsUnit (ρ.r (F.loc0 v g) 1 1 - ρ.ψ v 0 g) ∧ IsUnit (ρ.r (F.loc0 v g) 1 1 - ρ.ψ v 2 g) ∧
    IsUnit ((ρ.r (F.loc0 v g) 0 0 - ρ.ψ v 1 g) * (ρ.r (F.loc0 v g) 2 2 - ρ.ψ v 1 g) -
      ρ.r (F.loc0 v g) 0 2 * ρ.r (F.loc0 v g) 2 0)

theorem mid_mul (ρ : NRep F 3 K) (h : ∀ g i j, Odd (w 3 i - w 3 j) → ρ.r g i j = 0) (g g' : F.G0) :
    ρ.r (g * g') 1 1 = ρ.r g 1 1 * ρ.r g' 1 1 := by
  rw [map_mul, Matrix.mul_apply, Fin.sum_univ_three, h g 1 0 (by decide), h g 1 2 (by decide)]
  simp

end UpperTheory.V.Fr
end
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.det_mem :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
      [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ n : ℕ},
      F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (S : Space O F n) (m : ℕ) (g : Fin m → F.G0)
        (α : Fin m →₀ ℕ),
        (∑ a, (MvPolynomial.X a : MvPolynomial (Fin m) S.R) •
          (S.ρ.r (g a)).map MvPolynomial.C).det.coeff α ∈ S.B := by
  intro l _ O _ _ _ _ F C₀ n _ _ S m g α
  classical
  rw [Matrix.det_apply, MvPolynomial.coeff_sum]
  refine sum_mem (fun σ _ => ?_)
  rw [Units.smul_def, MvPolynomial.coeff_smul]
  refine zsmul_mem ?_ _
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [Finset.prod_univ_sum, MvPolynomial.coeff_sum]
  refine sum_mem (fun f _ => ?_)
  rw [Finset.prod_mul_distrib, ← map_prod, mul_comm, MvPolynomial.coeff_C_mul]
  refine mul_mem (S.mon_mem ?_) ?_
  · refine ⟨List.ofFn (fun i => (g (f i), σ i, i)), ?_, ?_⟩
    · rw [List.map_ofFn, List.sum_ofFn]
      simp only [Function.comp_def]
      rw [Finset.sum_sub_distrib, Equiv.sum_comp, sub_self]
    · rw [List.map_ofFn, List.prod_ofFn]
      rfl
  · obtain ⟨d, hd⟩ : ∃ d, ∏ i, (MvPolynomial.X (f i) : MvPolynomial (Fin m) S.R) =
        MvPolynomial.monomial d 1 := by
      refine Finset.prod_induction _ (fun p => ∃ d, p = MvPolynomial.monomial d 1) ?_ ?_ ?_
      · rintro a b ⟨d₁, rfl⟩ ⟨d₂, rfl⟩
        exact ⟨d₁ + d₂, by rw [MvPolynomial.monomial_mul, mul_one]⟩
      · exact ⟨0, by rw [MvPolynomial.monomial_zero', MvPolynomial.C_1]⟩
      · intro i _
        exact ⟨Finsupp.single (f i) 1, rfl⟩
    rw [hd, MvPolynomial.coeff_monomial]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem exists_prime_power_pow_eq_one {l : ℕ} [Fact l.Prime] {D : Type} [CommRing D] [IsDomain D] [IsLocalRing D]
    [CharP D l] {x : D} (hx : x - 1 ∈ maximalIdeal D) {h : ℕ} (hh : h ≠ 0) (hp : x ^ h = 1) : x = 1 := by
  have hl : l.Prime := Fact.out
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hh l hl.ne_one
  have h1 : (x ^ m - 1) ^ l ^ a = 0 := by
    rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm, hp, sub_self]
  have h2 : x ^ m - 1 = 0 := (pow_eq_zero_iff (pow_ne_zero _ hl.ne_zero)).1 h1
  rw [← mul_geom_sum, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact sub_eq_zero.1 h2
  · exfalso
    have h3 : residue D x = 1 := by
      have := (residue_eq_zero_iff _).2 hx
      rwa [map_sub, map_one, sub_eq_zero] at this
    have h4 := congrArg (residue D) h2

    simp only [map_sum, map_pow, h3, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    map_zero] at h4
    have h5 : (l : ResidueField D) = 0 := by
      rw [← map_natCast (residue D), CharP.cast_eq_zero, map_zero]
    haveI : CharP (ResidueField D) l := (CharP.charP_iff_prime_eq_zero hl).2 h5
    exact hm ((CharP.cast_eq_zero_iff _ l m).1 h4)

theorem UpperTheory.V.Fr.frobenius_corner_middle_trivial :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra O D] [IsCO O D], (∀ c ∈ maximalIdeal O, algebraMap O D c = 0) → ∀ χ : F.G0 →* D, AdicCont (maximalIdeal D) χ → (∀ g, χ g - 1 ∈ maximalIdeal D) → (∀ g, χ (F.star g) = χ g) → (∀ v g, g ∈ F.Iv v → F.Ψ (F.loc v g) = 1 → χ (F.loc0 v g) = 1) → ∀ g, χ g = 1 := by
  intro l _ O _ _ _ _ F C₀ hF D _ _ _ _ hO χ hc h1 hs hI g
  have hl : l.Prime := Fact.out
  have hlO : (l : O) ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  haveI : CharP D l := (CharP.charP_iff_prime_eq_zero hl).2 (by
    rw [← map_natCast (algebraMap O D), hO _ hlO])
  haveI : CompactSpace F.G0 :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ hF.del_open).isCompact
  obtain ⟨s, s', h, hh, -, hs', H⟩ := UpperTheory.V.Fr.ab_gen hF
  refine exists_prime_power_pow_eq_one (h1 g) hh ?_
  have key : ∀ N : ℕ, χ g ^ h - 1 ∈ maximalIdeal D ^ N := by
    intro N
    let q := Ideal.Quotient.mk (maximalIdeal D ^ N)
    let φ : F.G0 →* (D ⧸ maximalIdeal D ^ N)ˣ := ((q : D →* _).comp χ).toHomUnits
    have hφ : ∀ x, (φ x : D ⧸ maximalIdeal D ^ N) = q (χ x) := fun _ => rfl
    have hone : ∀ x n, φ.rangeRestrict x ^ n = 1 ↔ χ x ^ n - 1 ∈ maximalIdeal D ^ N := by
      intro x n
      rw [← Ideal.Quotient.eq, Subtype.ext_iff, Units.ext_iff, map_pow, map_one]
      rfl
    haveI : Finite φ.range := by
      haveI hf : Finite (Set.range fun g => q (χ g)) := (hc N).range_finite
      refine Finite.of_injective (β := Set.range fun g => q (χ g))
        (fun y => ⟨(y.1 : D ⧸ maximalIdeal D ^ N), ?_⟩) ?_
      · obtain ⟨_, x, rfl⟩ := y
        exact ⟨x, rfl⟩
      · intro y z hyz
        exact Subtype.ext (Units.ext (congrArg Subtype.val hyz))
    have hP : IsPGroup l φ.range := by
      intro y
      obtain ⟨x, rfl⟩ := φ.rangeRestrict_surjective y
      refine ⟨N, (hone x _).2 ?_⟩
      have e : χ x ^ l ^ N - 1 = (χ x - 1) ^ l ^ N := by rw [sub_pow_char_pow, one_pow]
      rw [e]
      exact Ideal.pow_le_pow_right (Nat.lt_pow_self hl.one_lt).le (Ideal.pow_mem_pow (h1 x) _)
    have hop : IsOpen (φ.rangeRestrict.ker : Set F.G0) := by
      convert (hc N).isOpen_fiber 1 using 1
      ext x
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq]
      rw [Subtype.ext_iff, Units.ext_iff]
      rfl
    refine (hone g h).1 ((H φ.range hP φ.rangeRestrict hop).2 (fun x => ?_) (fun a => ?_) g)
    · refine Subtype.ext (Units.ext ?_)
      show q (χ _) = q (χ _)
      rw [hs]
    · obtain ⟨v, x, hx, hΨ, e⟩ := hs' a
      refine Subtype.ext (Units.ext ?_)
      show q (χ _) = 1
      rw [e, hI v x hx hΨ, map_one]
  rw [← sub_eq_zero]
  have hb := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal D) (maximalIdeal.isMaximal D).ne_top
  rw [← Ideal.mem_bot, ← hb]
  exact Ideal.mem_iInf.2 key
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem prod_tri {C : Type} [CommRing C] {n : ℕ} (M : Fin n → Matrix (Fin n) (Fin n) C)
    (h1 : ∀ k i j, j < i → M k i j = 0) (h2 : ∀ k, M k k k = 0) : (List.ofFn M).prod = 0 := by
  have main : ∀ k, k ≤ n → ∀ i j : Fin n, (j : ℕ) < k → ((List.ofFn M).take k).prod i j = 0 := by
    intro k
    induction k with
    | zero => intro _ i j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ k ih =>
      intro hk i j hj
      have htake : (List.ofFn M).take (k + 1) = (List.ofFn M).take k ++ [M ⟨k, hk⟩] := by
        rw [List.take_succ]
        simp [show k < n by omega]
      rw [htake, List.prod_append, List.prod_singleton, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro m _
      by_cases hm : (m : ℕ) < k
      · rw [ih (Nat.le_of_succ_le hk) i m hm, zero_mul]
      · by_cases hmj : j < m
        · rw [h1 ⟨k, hk⟩ m j hmj, mul_zero]
        · have e1 : m = ⟨k, hk⟩ := Fin.ext (by simp only [not_lt, Fin.le_def] at hm hmj ⊢; omega)
          have e2 : j = ⟨k, hk⟩ := Fin.ext (by simp only [not_lt, Fin.le_def] at hm hmj ⊢; omega)
          rw [e1, e2, h2, mul_zero]
  have hall : (List.ofFn M).take n = List.ofFn M := List.take_of_length_le (by simp)
  ext i j
  rw [← hall]
  exact main n le_rfl i j j.2

private theorem prod_conj {R : Type} [Monoid R] (g : Rˣ) (L : List R) :
    (L.map fun x => (g : R) * x * ((g⁻¹ : Rˣ) : R)).prod = g * L.prod * ((g⁻¹ : Rˣ) : R) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.prod_cons]
    simp [mul_assoc]

theorem UpperTheory.V.Fr.ord_of_flag :
    ∀ {H C : Type} [Group H] [CommRing C] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) C) (ψ : Fin n → H →* Cˣ), UpperTheory.V.W.HasFlag r.toHomUnits ψ → (∀ g, ordProd r (fun i s => (ψ i s : C)) g = 0) ∧ ∀ g, (r g).charpoly = ∏ i, (Polynomial.X - Polynomial.C (ψ i g : C)) := by
  intro H C _ _ n r ψ hf
  obtain ⟨g, hg⟩ := hf
  have hconj : ∀ s, ((g * r.toHomUnits s * g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
      (g : Matrix (Fin n) (Fin n) C) * r s * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) := by
    intro s
    simp [Units.val_mul]
  constructor
  · intro gs
    show (List.ofFn fun i => r (gs i) - (ψ i (gs i) : C) • (1 : Matrix (Fin n) (Fin n) C)).prod = 0
    let M : Fin n → Matrix (Fin n) (Fin n) C := fun i =>
      (g : Matrix (Fin n) (Fin n) C) * (r (gs i) - (ψ i (gs i) : C) • 1) * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)
    have hM : ∀ i, M i = ((g * r.toHomUnits (gs i) * g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) -
        (ψ i (gs i) : C) • 1 := by
      intro i
      rw [hconj]
      simp only [M]
      rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.mul_inv]
    have h0 : (List.ofFn M).prod = 0 := by
      refine prod_tri M (fun k i j hij => ?_) (fun k => ?_)
      · rw [hM, Matrix.sub_apply, Matrix.smul_apply, one_apply_ne (ne_of_lt hij).symm, smul_zero, sub_zero]
        exact (hg (gs k)).1 i j hij
      · rw [hM, Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, (hg (gs k)).2 k, sub_self]
    have hmap : List.ofFn M = (List.ofFn fun i => r (gs i) - (ψ i (gs i) : C) • (1 : Matrix (Fin n) (Fin n) C)).map
        (fun x => (g : Matrix (Fin n) (Fin n) C) * x * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) := by
      rw [List.map_ofFn]
      rfl
    rw [hmap, prod_conj g] at h0
    calc (List.ofFn fun i => r (gs i) - (ψ i (gs i) : C) • (1 : Matrix (Fin n) (Fin n) C)).prod
        = ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) *
          ((g : Matrix (Fin n) (Fin n) C) *
            (List.ofFn fun i => r (gs i) - (ψ i (gs i) : C) • (1 : Matrix (Fin n) (Fin n) C)).prod *
            ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) * (g : Matrix (Fin n) (Fin n) C) := by
          simp [mul_assoc]
      _ = 0 := by rw [h0, mul_zero, zero_mul]
  · intro s
    rw [← Matrix.charpoly_units_conj g (r s), ← Matrix.coe_units_inv, ← hconj,
      Matrix.charpoly_of_upperTriangular _ (fun i j hij => (hg s).1 i j hij)]
    exact Finset.prod_congr rfl fun i _ => by rw [(hg s).2 i]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem entry_of_conj {C : Type} [CommRing C] {n : ℕ} (g : GL (Fin n) C) (f : Fin n → Matrix (Fin n) (Fin n) C)
    (hg : ∀ i, (g : Matrix (Fin n) (Fin n) C) * f i * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = single i i 1)
    (M : Matrix (Fin n) (Fin n) C) (a b : Fin n) :
    ((g : Matrix (Fin n) (Fin n) C) * M * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) a b =
      ((g : Matrix (Fin n) (Fin n) C) * (f a * M * f b) * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) a b := by
  have h : (g : Matrix (Fin n) (Fin n) C) * (f a * M * f b) * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
      single a a 1 * ((g : Matrix (Fin n) (Fin n) C) * M * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) *
        single b b 1 := by
    rw [← hg a, ← hg b]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  rw [h, Matrix.mul_single_apply_same, Matrix.single_mul_apply_same, one_mul, mul_one]

theorem UpperTheory.V.Fr.flag_loc :
    ∀ {H C : Type} [Group H] [CommRing C] [IsLocalRing C] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) C) (ψ : Fin n → H →* Cˣ) (g₀ : H), (∀ i j, i ≠ j → IsUnit ((ψ i g₀ : C) - ψ j g₀)) → ((r g₀).map (residue C)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (residue C (ψ i g₀))) → (∀ g, ordProd r (fun i s => (ψ i s : C)) g = 0) → UpperTheory.V.W.HasFlag r.toHomUnits ψ := by
  intro H C _ _ _ n r ψ g₀ hu hc ho
  have h0 := UpperTheory.V.AlgebraTools.ord_ext (R := C) r (fun i => (Units.coeHom C).comp (ψ i)) (fun g => by
    have := ho g
    unfold ordProd at this
    simpa only [Algebra.algebraMap_eq_smul_one, MonoidHom.comp_apply, Units.coeHom_apply] using this)
  obtain ⟨h1, h2, h3⟩ := UpperTheory.V.AlgebraTools.lag_triangular (MonoidAlgebra.lift C (Matrix (Fin n) (Fin n) C) H r)
    (fun i => MonoidAlgebra.lift C C H ((Units.coeHom C).comp (ψ i))) (MonoidAlgebra.of C H g₀) h0
    (fun i j hij => by simpa using hu i j hij)
  simp only [MonoidAlgebra.lift_of, MonoidHom.comp_apply, Units.coeHom_apply] at h1 h2 h3
  have h4 := UpperTheory.V.AlgebraTools.lag_ne_zero (fun i => (ψ i g₀ : C)) (r g₀) hu (by rw [← Matrix.charpoly_map, hc])
  obtain ⟨g, hg⟩ := UpperTheory.V.AlgebraTools.coi_conj_single _ h1 h4
  refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · have h5 := h2 (MonoidAlgebra.of C H s) i j hij
    rw [MonoidAlgebra.lift_of] at h5
    have h6 := entry_of_conj g _ hg (r s) i j
    rw [h5, mul_zero, zero_mul] at h6
    exact h6
  · have h5 := h3 (MonoidAlgebra.of C H s) i
    rw [MonoidAlgebra.lift_of, MonoidAlgebra.lift_of] at h5
    have h6 := entry_of_conj g _ hg (r s) i i
    rw [h5, mul_smul_comm, smul_mul_assoc, hg] at h6
    refine h6.trans ?_
    simp
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.residually_diagonal_representation :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] (f : k →+* Q) (ρ : NRep F n Q), (ρ.map (residue Q)).IsBar ((residue Q).comp f) → ρ.triM = ⊥ → (∀ v g, (ρ.r (F.loc0 v g)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (ρ.ψ v i g : Q))) → (∀ (g : F.G0) (i : Fin n), ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k)) → ρ.IsBar f := by
  intro l _ k _ F n Q _ _ _ f ρ hbar htri hchar hdiag
  refine ⟨hdiag, ?_⟩
  intro v i g
  have hz : ∀ (s : F.G0) (a b : Fin n), a < b → ρ.r s a b = 0 := fun s a b hab => by
    have : ρ.r s a b ∈ ρ.triM := Ideal.subset_span ⟨s, a, b, hab, rfl⟩
    rw [htri] at this
    exact (Submodule.mem_bot Q).1 this
  have hT : (ρ.r (F.loc0 v g))ᵀ.BlockTriangular id := fun a b hab => hz _ b a hab
  have h1 := Matrix.charpoly_of_upperTriangular _ hT
  rw [Matrix.charpoly_transpose, hchar] at h1
  have h2 := congrArg (Polynomial.eval (ρ.ψ v i g : Q)) h1
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h2
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)] at h2
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 h2.symm
  rw [sub_eq_zero, Matrix.transpose_apply, hdiag] at hj
  have h3 := hbar.2 v i g
  rw [NRep.map_ψ, hj] at h3
  have h4 := ((residue Q).comp f).injective h3
  rw [hj, h4]
end
