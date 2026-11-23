module

public import Development.EtaleCohomology.EtaleSheaves.Bundle012
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open Polynomial IsLocalRing GlobalTheory.EtC

namespace LateralTheory.E.LocSHPf

theorem aic_localization (S : Type) [CommRing S] (hS : AIC S) (M : Submonoid S) (R : Type) [CommRing R]
    [Algebra S R] [IsLocalization M R] : AIC R := by
  intro P hP hd
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset M ((Finset.range (P.natDegree + 1)).image P.coeff)
  set s : R := algebraMap S R (b : S) with hs
  have hlift : P.scaleRoots s ∈ lifts (algebraMap S R) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i P.natDegree with hi | hi | hi
    · obtain ⟨y, hy⟩ := hb (P.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
      obtain ⟨k, hk⟩ : ∃ k, P.natDegree - i = k + 1 := ⟨P.natDegree - i - 1, by omega⟩
      refine ⟨y * (b : S) ^ k, ?_⟩
      rw [map_mul, map_pow, hy, hk, pow_succ, Algebra.smul_def, ← hs]
      ring
    · subst hi
      rw [Nat.sub_self, pow_zero, mul_one]
      exact ⟨1, by rw [map_one]; exact hP.symm⟩
    · rw [coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact ⟨0, map_zero _⟩
  have hmon : (P.scaleRoots s).Monic := by
    rw [Monic, leadingCoeff, natDegree_scaleRoots, coeff_scaleRoots_natDegree]; exact hP
  obtain ⟨Q, hQ, hQd, hQm⟩ := lifts_and_natDegree_eq_and_monic hlift hmon
  obtain ⟨a, ha⟩ := hS Q hQm (by rw [hQd, natDegree_scaleRoots]; exact hd)
  have hu : IsUnit s := IsLocalization.map_units R b
  refine ⟨hu.unit⁻¹ * algebraMap S R a, ?_⟩
  have h1 := scaleRoots_eval₂_mul (p := P) (RingHom.id R) (hu.unit⁻¹ * algebraMap S R a) s
  have h2 : s * (hu.unit⁻¹ * algebraMap S R a) = algebraMap S R a := by
    rw [← mul_assoc, hu.mul_val_inv, one_mul]
  rw [RingHom.id_apply, h2, ← eval, ← eval, ← hQ, eval_map, eval₂_hom, ha, map_zero] at h1
  have := (hu.pow P.natDegree).mul_right_eq_zero.1 h1.symm
  exact this

theorem root_near (R : Type) [CommRing R] [IsLocalRing R] (hR : AIC R) (a₀ : R) :
    ∀ n : ℕ, ∀ f : R[X], f.natDegree = n → f.Monic → f.eval a₀ ∈ maximalIdeal R →
      ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R := by
  intro n
  induction n with
  | zero =>
    intro f hn hf he
    rw [eq_one_of_monic_natDegree_zero hf hn, eval_one] at he
    exact absurd he (Ideal.IsMaximal.ne_top inferInstance |> fun h => fun h1 => h ((Ideal.eq_top_iff_one _).2 h1))
  | succ n ih =>
    intro f hn hf he
    obtain ⟨a, ha⟩ := hR f hf (by omega)
    have hfac := (mul_divByMonic_eq_iff_isRoot (p := f) (a := a)).2 ha
    have hgm : (f /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [hfac]; exact hf)
    have hgd : (f /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at he
    rcases Ideal.IsPrime.mem_or_mem (inferInstance : (maximalIdeal R).IsPrime) he with h | h
    · refine ⟨a, ha, ?_⟩
      rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 h
    · obtain ⟨b, hb, hb'⟩ := ih _ hgd hgm h
      refine ⟨b, ?_, hb'⟩
      rw [← hfac, IsRoot, eval_mul, hb.eq_zero, mul_zero]

theorem henselian_of_aic (R : Type) [CommRing R] [IsLocalRing R] (hR : AIC R) : HenselianLocalRing R where
  is_henselian f hf a₀ he _ := root_near R hR a₀ _ f rfl hf he

theorem residue_algClosed (R : Type) [CommRing R] [IsLocalRing R] (hR : AIC R) : IsAlgClosed (ResidueField R) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hl : p ∈ lifts (residue R) := by
    rw [lifts_iff_coeff_lifts]; intro n; exact residue_surjective _
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hp
  have hpos : 0 < p.natDegree := natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hirr)
  obtain ⟨a, ha⟩ := hR q hqm (by omega)
  exact ⟨residue R a, by rw [← hq, eval_map, eval₂_hom, ha, map_zero]⟩

theorem LocSH_of : LateralTheory.E.ZarLocalPf.LocSH := by
  intro S _ hS p
  have hA := aic_localization S hS p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
  have := residue_algClosed _ hA
  exact ⟨henselian_of_aic _ hA, inferInstance⟩

end LateralTheory.E.LocSHPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SHTensorPf

def LocTensor : Prop := ∀ {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z), IsPushout x b u v →
  SH A → SH X → IsLocalHom x.hom → b.hom.IsIntegral → IsLocalRing B → IsLocalRing Z

def SepTensor : Prop := ∀ {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z), IsPushout x b u v →
  SH A → SH X → IsLocalHom x.hom → b.hom.IsIntegral → IsLocalRing B → ∀ (_ : IsLocalRing Z),
  IsSepClosed (IsLocalRing.ResidueField Z)

theorem intPush {A X B Z : CommRingCat.{0}} {x : A ⟶ X} {b : A ⟶ B} {u : X ⟶ Z} {v : B ⟶ Z}
    (hp : IsPushout x b u v) (hb : b.hom.IsIntegral) : u.hom.IsIntegral := by
  have h : (RingHom.toMorphismProperty fun f => f.IsIntegral).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.isIntegral_isStableUnderBaseChange
  exact h.of_isPushout hp hb

theorem idem_local (R : Type) [CommRing R] [IsLocalRing R] (e : R) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · right; exact (sub_eq_zero.mp ((h.mul_right_eq_zero).mp h0)).symm
  · left; exact (h.mul_left_eq_zero).mp h0

theorem SHTensor_of (hH : LateralTheory.E.t_E3Cut.HensInt) (hL : LocTensor) (hS : SepTensor) : LateralTheory.E.t_E3Cut.SHTensor := by
  intro A X B Z x b u v hp hA hX hx hb hB
  have hZ : IsLocalRing Z := hL x b u v hp hA hX hx hb hB
  have hsep := hS x b u v hp hA hX hx hb hB hZ
  obtain ⟨hXh, _⟩ := hX
  obtain ⟨hZh⟩ := hH X Z u.hom (intPush hp hb) (idem_local Z)
  exact ⟨hZh, hsep⟩

end LateralTheory.E.SHTensorPf
end
end

section

noncomputable section
open PowerSeries

namespace LateralTheory.E.LeafNewtonPf

def nser {A : Type 1} [CommRing A] (c : ℕ → A) : PowerSeries A :=
  -(X * PowerSeries.derivative (mk c)) * (mk c).invOfUnit 1

lemma uniq {A : Type 1} [CommRing A] {f g s : PowerSeries A} (hf : constantCoeff f = 1) (h : s * f = g) :
    g * f.invOfUnit 1 = s := by
  rw [← h, mul_assoc, mul_invOfUnit f 1 (by simp [hf]), mul_one]

lemma nser_eq {A : Type 1} [CommRing A] (c : ℕ → A) {s : PowerSeries A} (h0 : constantCoeff (mk c) = 1)
    (h : s * mk c = -(X * PowerSeries.derivative (mk c))) : nser c = s := uniq h0 h

lemma nser_spec {A : Type 1} [CommRing A] (c : ℕ → A) (h0 : c 0 = 1) :
    nser c * mk c = -(X * PowerSeries.derivative (mk c)) := by
  unfold nser
  rw [mul_assoc, invOfUnit_mul (mk c) 1 (by simp [h0]), mul_one]

lemma map_deriv {A B : Type 1} [CommRing A] [CommRing B] (φ : A →+* B) (f : PowerSeries A) :
    map φ (PowerSeries.derivative f) = PowerSeries.derivative (map φ f) := by
  ext n
  simp [coeff_derivative, coeff_map, map_mul, map_natCast]

lemma part1 {A B : Type 1} [CommRing A] [CommRing B] (φ : A →+* B) (c : ℕ → A) (h0 : c 0 = 1) (k : ℕ) :
    φ (LateralTheory.E.D2.newton c k) = LateralTheory.E.D2.newton (fun j => φ (c j)) k := by
  have hm : map φ (mk c) = mk (fun j => φ (c j)) := by ext n; simp [coeff_map]
  have key : nser (fun j => φ (c j)) = map φ (nser c) := by
    apply nser_eq _ (by simp [h0])
    have := congrArg (map φ) (nser_spec c h0)
    rw [map_mul, hm, map_neg, map_mul, map_X, map_deriv, hm] at this
    exact this
  show φ (coeff k (nser c)) = coeff k (nser (fun j => φ (c j)))
  rw [key, coeff_map]

lemma part2 {A : Type 1} [CommRing A] (c d e : ℕ → A) (hc : c 0 = 1) (hd : d 0 = 1)
    (he : ∀ k, e k = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, c p.1 * d p.2) (k : ℕ) :
    LateralTheory.E.D2.newton e k = LateralTheory.E.D2.newton c k + LateralTheory.E.D2.newton d k := by
  have hm : mk e = mk c * mk d := by ext n; rw [coeff_mk, he, coeff_mul]; simp [coeff_mk]
  have he0 : e 0 = 1 := by rw [he]; simp [hc, hd]
  have key : nser e = nser c + nser d := by
    apply nser_eq _ (by simp [he0])
    rw [hm, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have h1 := nser_spec c hc
    have h2 := nser_spec d hd
    linear_combination (mk d) * h1 + (mk c) * h2
  show coeff k (nser e) = coeff k (nser c) + coeff k (nser d)
  rw [key, map_add (f := _)]

lemma geom {A : Type 1} [CommRing A] (x : A) : mk (fun k => x ^ k) * (1 - C x * X) = 1 := by
  ext n
  rcases n with _ | n
  · simp [mul_sub]
  · rw [mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm _ (C x), coeff_succ_mul_X, coeff_C_mul]
    simp [pow_succ, mul_comm]

lemma part3 {A : Type 1} [CommRing A] (c : ℕ → A) (x : A) (h0 : c 0 = 1) (h1 : c 1 = -x)
    (h2 : ∀ j, 1 < j → c j = 0) (k : ℕ) (hk : 0 < k) : LateralTheory.E.D2.newton c k = x ^ k := by
  have hm : mk c = 1 - C x * X := by
    ext n
    rcases n with _ | _ | n
    · simp [h0]
    · simp [h1]
    · rw [coeff_mk, h2 _ (by omega)]
      simp [coeff_one]
  have key : nser c = C x * X * mk (fun k => x ^ k) := by
    apply nser_eq _ (by simp [h0])
    rw [mul_assoc, hm, geom, mul_one]
    simp [map_sub, mul_comm]
  show coeff k (nser c) = x ^ k
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [key, mul_comm (C x) X, mul_assoc, coeff_succ_X_mul, coeff_C_mul, coeff_mk, pow_succ, mul_comm]

theorem LeafNewton_of : LateralTheory.E.D2.LeafNewton :=
  ⟨fun _ _ _ _ φ c h0 k => part1 φ c h0 k,
   fun _ _ c d e hc hd he k => part2 c d e hc hd he k,
   fun _ _ c x h0 h1 h2 k hk => part3 c x h0 h1 h2 k hk⟩

end LateralTheory.E.LeafNewtonPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2.ChernPf

theorem cast_rfl {q : ℕ} {E : Spc} {n i : ℤ} (x : Ht q E n i) (h1 : n = n) (h2 : i = i) : x.cast h1 h2 = x := rfl

theorem cast_cast {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (x : Ht q E n i) (h1 : n = n') (h2 : i = i')
    (h3 : n' = n'') (h4 : i' = i'') : (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4; rfl

theorem term {q : ℕ} (P : Collected q) {E F : Spc} (f : F ⟶ E) (h : Inv q E) (h' : Inv q F) (y : Ht q F 2 1)
    {n' i' : ℤ} (u : Ht q E n' i') (k m N : ℕ) (hN : k + m = N) (hn : n' = 2 * (k : ℤ)) (hi : i' = k)
    (h1 : n' + 2 * (m : ℤ) = 2 * (N : ℤ)) (h2 : i' + (m : ℤ) = N) :
    P.ι h' N ((cup q (pull _ f _ _ u) (cpow q y m)).cast h1 h2) =
      P.map f h' h (P.ι h k (u.cast hn hi)) * P.ι h' m (cpow q y m) := by
  subst hN hn hi
  rw [cast_rfl, P.map_ι]
  exact P.ι_mul h' k m _ _

variable {q : ℕ} {E : Spc} {N : ℕ}

def Phi (V : E ⟶ ofCat (glCat N)) (a : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ))) :
    Ht q (PB V) (2 * (N : ℤ)) N :=
  ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j))
      (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ (2 * (N : ℤ)) N)

def ac (c : ∀ j : ℕ, Ht q E (2 * j) j) : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ)) :=
  fun j => (c (N - j)).cast (by have := j.isLt; omega) (by have := j.isLt; omega)

theorem phi_ι (P : Collected q) (h : Inv q E) (V : E ⟶ ofCat (glCat N))
    (a : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ))) :
    P.ι (inv_of (PB.pr V) h) N (Phi V a) = ∑ j : Fin N, P.map (PB.pr V) (inv_of (PB.pr V) h) h
      (P.ι h (N - j) ((a j).cast (by have := j.isLt; omega) (by have := j.isLt; omega))) *
      P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ (j : ℕ) := by
  unfold Phi

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [term P (PB.pr V) h (inv_of (PB.pr V) h) _ (a j) (N - j) j N (by have := j.isLt; omega)
    (by have := j.isLt; omega) (by have := j.isLt; omega), P.ι_cpow]

end LateralTheory.E.D2.ChernPf

namespace LateralTheory.E.D2.ChernPf
variable {q : ℕ} {E : Spc} {N : ℕ}

theorem cast_inj {n i n' i' : ℤ} {x y : Ht q E n i} (h1 : n = n') (h2 : i = i') (e : x.cast h1 h2 = y.cast h1 h2) : x = y := by
  subst h1 h2; exact e

theorem cast_idx {n i : Fin N → ℤ} (a : ∀ j, Ht q E (n j) (i j)) (j j' : Fin N) (e : j = j')
    (h1 : n j = n j') (h2 : i j = i j') : (a j).cast h1 h2 = a j' := by
  subst e; rfl

theorem sum_eq (P : Collected q) (h : Inv q E) (V : E ⟶ ofCat (glCat N)) (c : ∀ j : ℕ, Ht q E (2 * j) j)
    (h0 : P.ι h 0 (c 0) = 1) :
    ∑ j ∈ Finset.range (N + 1), P.map (PB.pr V) (inv_of (PB.pr V) h) h (P.ι h j (c j)) *
      P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ (N - j) =
      P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ N + P.ι (inv_of (PB.pr V) h) N (Phi V (ac c)) := by
  have key : ∀ g : ℕ → P.R (PB V) (inv_of (PB.pr V) h),
      ∑ j ∈ Finset.range (N + 1), g j = ∑ j ∈ Finset.range N, g (N - j) + g 0 := by
    intro g
    rw [← Finset.sum_range_reflect, Finset.sum_range_succ]
    simp
  rw [key, phi_ι P h V, h0, map_one, one_mul, Nat.sub_zero, add_comm, Finset.sum_range]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.sub_sub_self j.isLt.le]
  dsimp only [ac]
  rw [ChernPf.cast_cast, cast_rfl]

def mkc (a : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ))) : ∀ j : ℕ, Ht q E (2 * j) j :=
  fun j => if h0 : j = 0 then (one q E).cast (by simp [h0]) (by simp [h0])
    else if hj : j ≤ N then (a ⟨N - j, by omega⟩).cast (by simp; omega) (by simp; omega) else 0

end LateralTheory.E.D2.ChernPf

namespace LateralTheory.E.D2
open ChernPf

theorem LeafChern_of : LeafChern := by
  intro hD1 q _ P E h N V
  have hB : Function.Bijective (Phi (q := q) V) := hD1 q V h (2 * (N : ℤ)) N
  have hι : ∀ {F : Spc} (h : Inv q F) k, Function.Injective (P.ι h k) := fun h k a b e => by
    simpa [P.π_ι] using congrArg (P.π h k) e
  have char : ∀ c, P.ι h 0 (c 0) = 1 → (IsChern P h V c ↔
      (∀ j, N < j → c j = 0) ∧ Phi V (ac c) = -cpow q (c1 q (PB.line V)) N) := by
    intro c h0
    unfold IsChern
    rw [sum_eq P h V c h0, ← P.ι_cpow, ← map_add (f := _), map_eq_zero_iff _ (hι _ _), add_eq_zero_iff_neg_eq, eq_comm]
    simp only [h0, true_and]
    exact and_congr_right fun _ => eq_comm
  have uniq : ∀ c c', IsChern P h V c → IsChern P h V c' → c = c' := by
    intro c c' hc hc'
    have hA : ac c = ac c' := hB.1 (((char c hc.1).1 hc).2.trans ((char c' hc'.1).1 hc').2.symm)
    funext j
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hι h 0 (hc.1.trans hc'.1.symm)
    by_cases hjN : N < j
    · rw [hc.2.1 j hjN, hc'.2.1 j hjN]
    have := cast_inj _ _ (congrFun hA ⟨N - j, by omega⟩)
    have e : N - ((⟨N - j, by omega⟩ : Fin N) : ℕ) = j := by simp; omega
    rw [e] at this
    exact this
  obtain ⟨a, ha⟩ := hB.2 (-cpow q (c1 q (PB.line V)) N)
  have hc0 : P.ι h 0 (mkc a 0) = 1 := by
    dsimp only [mkc]
    rw [dite_eq_left rfl]
    exact P.ι_one h
  have hac : ac (mkc a) = a := by
    funext j
    dsimp only [ac, mkc]
    rw [dite_eq_right (by omega), dite_eq_left (by omega), ChernPf.cast_cast]
    exact cast_idx a _ _ (Fin.ext (by simp; omega)) _ _
  have hC : IsChern P h V (mkc a) := (char _ hc0).2 ⟨fun j hj => by
    dsimp only [mkc]
    rw [dite_eq_right (by omega), dite_eq_right (by omega)], by rw [hac]; exact ha⟩
  exact ⟨mkc a, hC, fun c' hc' => uniq _ _ hc' hC⟩

end LateralTheory.E.D2
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2

namespace LateralTheory.E.LeafGeomPf

def vec0 {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X : Scheme.{0}}
    (x : Sx (PB (bsumOf V W)) n X) : Fin (a + b) → Scheme.Γ.obj (op X) :=
  ((show Fin (n + 1) ⥤ Um (a + b) (Scheme.Γ.obj (op X)) from
    ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) x).obj 0).1

def First {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X : Scheme.{0}}
    (x : Sx (PB (bsumOf V W)) n X) : Prop :=
  Ideal.span (Set.range fun i : Fin a => vec0 V W x (Fin.castAdd b i)) = ⊤

def Second {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X : Scheme.{0}}
    (x : Sx (PB (bsumOf V W)) n X) : Prop :=
  Ideal.span (Set.range fun i : Fin b => vec0 V W x (Fin.natAdd a i)) = ⊤

def LeafHalf1 : Prop := ∀ {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)),
  ∃ (U₁ : Spc) (f₁ : U₁ ⟶ PB (bsumOf V W)) (p₁ : U₁ ⟶ PB V), Mono f₁ ∧
    p₁ ≫ PB.pr V = f₁ ≫ PB.pr _ ∧ p₁ ≫ PB.line V = f₁ ≫ PB.line _ ∧
    ∀ (n : ℕ) (X : Scheme.{0}) (x : Sx (PB (bsumOf V W)) n X), First V W x → ∃ y : Sx U₁ n X, (f₁.app _).app _ y = x

def LeafHalf2 : Prop := ∀ {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)),
  ∃ (U₂ : Spc) (f₂ : U₂ ⟶ PB (bsumOf V W)) (p₂ : U₂ ⟶ PB W), Mono f₂ ∧
    p₂ ≫ PB.pr W = f₂ ≫ PB.pr _ ∧ p₂ ≫ PB.line W = f₂ ≫ PB.line _ ∧
    ∀ (n : ℕ) (X : Scheme.{0}) (x : Sx (PB (bsumOf V W)) n X), Second V W x → ∃ y : Sx U₂ n X, (f₂.app _).app _ y = x

def LeafLocal : Prop := ∀ {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) (n : ℕ) (X : Scheme.{0})
  (x : Sx (PB (bsumOf V W)) n X), ∃ S : Sieve X, S ∈ Scheme.etaleTopology X ∧ ∀ (Y : Scheme.{0}) (k : Y ⟶ X), S.arrows k →
    First V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x) ∨
    Second V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x)

theorem LeafGeom_of (h1 : LeafHalf1) (h2 : LeafHalf2) (hL : LeafLocal) : LateralTheory.E.D2.LeafGeom := by
  intro E a b V W
  obtain ⟨U₁, f₁, p₁, m₁, e₁, l₁, s₁⟩ := h1 V W
  obtain ⟨U₂, f₂, p₂, m₂, e₂, l₂, s₂⟩ := h2 V W
  refine ⟨U₁, U₂, f₁, f₂, p₁, p₂, m₁, m₂, ?_, e₁, l₁, e₂, l₂⟩
  intro n X x
  obtain ⟨S, hS, hk⟩ := hL V W n X x
  refine ⟨S, hS, fun Y k hk' => ?_⟩
  rcases hk Y k hk' with h | h
  · exact Or.inl (s₁ n Y _ h)
  · exact Or.inr (s₂ n Y _ h)

end LateralTheory.E.LeafGeomPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2

theorem pull_cast_nat {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn hi; rfl

abbrev PB.over {E E' : Spc} (f : E ⟶ E') {N : ℕ} (V : E' ⟶ ofCat (glCat N)) : PB (f ≫ V) ⟶ PB V :=
  pullback.map (f ≫ V) (PGL.pr N) V (PGL.pr N) f (𝟙 _) (𝟙 _) (by simp) (by simp)

theorem PB.over_pr {E E' : Spc} (f : E ⟶ E') {N : ℕ} (V : E' ⟶ ofCat (glCat N)) :
    PB.over f V ≫ PB.pr V = PB.pr (f ≫ V) ≫ f := by
  simp only [PB.over, PB.pr, pullback.map, pullback.lift_fst]

theorem PB.over_line {E E' : Spc} (f : E ⟶ E') {N : ℕ} (V : E' ⟶ ofCat (glCat N)) :
    PB.over f V ≫ PB.line V = PB.line (f ≫ V) := by
  simp only [PB.over, PB.line, pullback.map, pullback.lift_snd_assoc, Category.comp_id]

theorem LeafNat_of (hA : LeafA6nat) : LeafNat := by
  intro q _ P E E' f h h' N V c hc
  obtain ⟨h0, hz, hs⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · rw [← P.map_ι f h h', h0, map_one]
  · intro j hj; simp [hz j hj]
  · have hg := congrArg (P.map (PB.over f V) (inv_of (PB.pr (f ≫ V)) h) (inv_of (PB.pr V) h')) hs

    rw [map_zero, map_sum] at hg
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, map_pow, P.map_ι, Collected.deg1, pull_cast_nat, ← pull_comp, PB.over_pr]
    rw [(hA q).2.2.1 _ _ (inv_of (PB.pr V) h'), PB.over_line]

end LateralTheory.E.D2
end
end
