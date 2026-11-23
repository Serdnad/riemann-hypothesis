module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle352
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

noncomputable section

open Matrix

namespace GlobalTheory.PlaneSU

open Formalism.UG

theorem cT_cT_invol {R : Type} [CommRing R] (c : R →+* R) (hc : ∀ x, c (c x) = x) {m p : Type}
    (P : Matrix m p R) : cT c (cT c P) = P := by
  ext i j; simp [cT, hc]

theorem eq_emb_of_fix {R : Type} [CommRing R] (c : R →+* R) (hc : ∀ x, c (c x) = x) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) R) (hJ : IsUnit J.det) (A : Matrix (Fin M) (Fin 2) R)
    (B : Matrix (Fin 2) (Fin M) R) (H : Matrix (Fin 2) (Fin 2) R) (hBA : B * A = 1)
    (h1 : cT c A * J = H * B) (h2 : J * A = cT c B * H) (G : Matrix (Fin M) (Fin M) R)
    (hG : cT c G * J * G = J) (hN : G * (1 - A * B) = 1 - A * B) :
    G = emb A B (B * G * A) ∧ cT c (B * G * A) * H * (B * G * A) = H := by
  set N := 1 - A * B with hNdef
  have hBN : B * N = 0 := by
    rw [hNdef, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hBA, Matrix.one_mul, sub_self]
  have hcN : cT c N = 1 - cT c B * cT c A := by
    rw [hNdef, cT_sub, cT_one, cT_mul]
  have hNJ : cT c N * J = J - cT c B * H * B := by
    rw [hcN, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have hNJA : cT c N * J * A = 0 := by
    rw [hNJ, Matrix.sub_mul, h2, Matrix.mul_assoc, hBA, Matrix.mul_one, sub_self]
  have hNJN : cT c N * J * N = J * N := by
    rw [hNJ, Matrix.sub_mul, Matrix.mul_assoc (cT c B * H), hBN, Matrix.mul_zero, sub_zero]
  have hAJA : cT c A * J * A = H := by
    rw [h1, Matrix.mul_assoc, hBA, Matrix.mul_one]
  have hAJN : cT c A * J * N = 0 := by
    rw [h1, Matrix.mul_assoc, hBN, Matrix.mul_zero]
  set W := N * G * A with hWdef
  have hcW : cT c W = cT c A * cT c G * cT c N := by
    rw [hWdef, cT_mul, cT_mul, Matrix.mul_assoc]
  have hWJA : cT c W * J * A = 0 := by
    rw [hcW, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT c N), hNJA, Matrix.mul_zero]
  have hWJN : cT c W * J * N = 0 := by
    have e1 : cT c W * J * N = cT c A * cT c G * (cT c N * J * N) := by
      rw [hcW]; simp only [Matrix.mul_assoc]
    have e2 : cT c G * (J * N) = J * N := by
      calc cT c G * (J * N) = cT c G * (J * (G * N)) := by rw [hN]
        _ = (cT c G * J * G) * N := by simp only [Matrix.mul_assoc]
        _ = J * N := by rw [hG]
    rw [e1, hNJN, Matrix.mul_assoc, e2, ← Matrix.mul_assoc, hAJN]
  have hsplit : A * B + N = 1 := by rw [hNdef]; abel
  have hWJ : cT c W * J = 0 := by
    calc cT c W * J = cT c W * J * (A * B + N) := by rw [hsplit, Matrix.mul_one]
      _ = cT c W * J * A * B + cT c W * J * N := by
          rw [Matrix.mul_add]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hWJA, hWJN, Matrix.zero_mul, add_zero]
  have hcW0 : cT c W = 0 := by
    calc cT c W = cT c W * J * J⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv J hJ, Matrix.mul_one]
      _ = 0 := by rw [hWJ, Matrix.zero_mul]
  have hW0 : W = 0 := by
    rw [← cT_cT_invol c hc W, hcW0]; ext i j; simp [cT]
  set X := B * G * A with hXdef
  have hGA : G * A = A * X := by
    calc G * A = (A * B + N) * G * A := by rw [hsplit, Matrix.one_mul]
      _ = A * X + W := by rw [hXdef, hWdef]; simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = A * X := by rw [hW0, add_zero]
  refine ⟨?_, ?_⟩
  · calc G = G * (A * B + N) := by rw [hsplit, Matrix.mul_one]
      _ = G * A * B + G * N := by rw [Matrix.mul_add, Matrix.mul_assoc]
      _ = A * X * B + N := by rw [hGA, hN]
      _ = emb A B X := by
          rw [emb, hNdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]; abel
  · calc cT c X * H * X = cT c X * (cT c A * J * A) * X := by rw [hAJA]
      _ = cT c (A * X) * J * (A * X) := by rw [cT_mul c A X]; simp only [Matrix.mul_assoc]
      _ = cT c (G * A) * J * (G * A) := by rw [hGA]
      _ = cT c A * (cT c G * J * G) * A := by rw [cT_mul c G A]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hG, hAJA]

end GlobalTheory.PlaneSU
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial

namespace GlobalTheory.EtC.GmStep

variable (R : Type) [CommRing R]

def rowD (E : Spc) (F : Shv R) (s : ℤ) (p : ℕ) :
    H R (disc.obj (E.obj (op ⦋p⦌))) F s →+ H R (disc.obj (E.obj (op ⦋p + 1⦌))) F s :=
  ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) • pull R (disc.map (E.δ j)) F s

def RowExact (E : Spc) (F : Shv R) (s : ℤ) (p : ℕ) : Prop :=
  ∀ y : H R (disc.obj (E.obj (op ⦋p + 1⦌))) F s, rowD R E F s (p + 1) y = 0 → ∃ z, rowD R E F s p z = y

variable {R}

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
private theorem map_rowDifferential_of_commute_faces_lemma {E E' : _root_.GlobalTheory.EtC.Spc}
    {F F' : _root_.GlobalTheory.EtC.Shv R} {s s' : ℤ}
    (φ : ∀ p : ℕ, _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s →+
      _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E'.obj (op ⦋p⦌))) F' s')
    (hc : ∀ (p : ℕ) (j : Fin (p + 2))
      (y : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s),
      φ (p + 1) (_root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E.δ j)) F s y) =
        _root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E'.δ j)) F' s' (φ p y))
    (p : ℕ) (y : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s) :
    φ (p + 1) (_root_.GlobalTheory.EtC.GmStep.rowD R E F s p y) =
      _root_.GlobalTheory.EtC.GmStep.rowD R E' F' s' p (φ p y) := by
  change φ (p + 1) ((AddMonoidHom.eval y) (∑ j : Fin (p + 2),
      ((-1 : ℤ) ^ (j : ℕ)) • pull R (disc.map (E.δ j)) F s)) =
    (AddMonoidHom.eval (φ p y)) (∑ j : Fin (p + 2),
      ((-1 : ℤ) ^ (j : ℕ)) • pull R (disc.map (E'.δ j)) F' s')
  simp only [map_sum, map_zsmul]
  exact Finset.sum_congr rfl fun j _ => congrArg (fun x => ((-1 : ℤ) ^ (j : ℕ)) • x) (hc p j y)


open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.rowExact_transfer {E E' : _root_.GlobalTheory.EtC.Spc}
    {F F' : _root_.GlobalTheory.EtC.Shv R} {s s' : ℤ}
    (φ : ∀ p : ℕ, _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s →+
      _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E'.obj (op ⦋p⦌))) F' s')
    (hφ : ∀ p, Function.Bijective (φ p))
    (hc : ∀ (p : ℕ) (j : Fin (p + 2))
      (y : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s),
      φ (p + 1) (_root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E.δ j)) F s y) =
        _root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E'.δ j)) F' s' (φ p y))
    (p : ℕ) (h : _root_.GlobalTheory.EtC.GmStep.RowExact R E F s p) : _root_.GlobalTheory.EtC.GmStep.RowExact R E' F' s' p := by
  intro y' hy'
  obtain ⟨y, rfl⟩ := (hφ (p + 1)).2 y'
  have hy : _root_.GlobalTheory.EtC.GmStep.rowD R E F s (p + 1) y = 0 := by
    apply (hφ (p + 1 + 1)).1
    rw [map_rowDifferential_of_commute_faces_lemma φ hc, hy', map_zero]
  obtain ⟨z, rfl⟩ := h y hy
  exact ⟨φ p z, (map_rowDifferential_of_commute_faces_lemma φ hc p z).symm⟩

def laurentMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : LaurentPolynomial A →+* LaurentPolynomial B :=
  LaurentPolynomial.eval₂ ((LaurentPolynomial.C : B →+* LaurentPolynomial B).comp f) (laurentVarUnit B)

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_C {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    _root_.GlobalTheory.EtC.GmStep.laurentMap f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) := by
  simp [_root_.GlobalTheory.EtC.GmStep.laurentMap, LaurentPolynomial.eval₂_C]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_T {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (m : ℤ) :
    _root_.GlobalTheory.EtC.GmStep.laurentMap f (LaurentPolynomial.T m) = LaurentPolynomial.T m := by
  have hu : ((_root_.GlobalTheory.EtC.laurentVarUnit B : (LaurentPolynomial B)ˣ) :
      LaurentPolynomial B) = LaurentPolynomial.T 1 := rfl
  have hinv : (((_root_.GlobalTheory.EtC.laurentVarUnit B)⁻¹ : (LaurentPolynomial B)ˣ) :
      LaurentPolynomial B) = LaurentPolynomial.T (-1) := by
    rw [← Units.inv_mul_cancel_left (_root_.GlobalTheory.EtC.laurentVarUnit B)
      (LaurentPolynomial.T (-1)), hu, ← LaurentPolynomial.T_add]
    simp
  rw [_root_.GlobalTheory.EtC.GmStep.laurentMap, LaurentPolynomial.eval₂_T]
  refine Int.induction_on m ?_ (fun k ih => ?_) (fun k ih => ?_)
  · simp
  · rw [zpow_add_one, Units.val_mul, ih, hu, ← LaurentPolynomial.T_add]
  · rw [zpow_sub_one, Units.val_mul, ih, hinv, ← LaurentPolynomial.T_add, sub_eq_add_neg]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_comp_C {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (_root_.GlobalTheory.EtC.GmStep.laurentMap f).comp LaurentPolynomial.C =
      (LaurentPolynomial.C : B →+* LaurentPolynomial B).comp f :=
  RingHom.ext fun a => _root_.GlobalTheory.EtC.GmStep.laurentMap_C f a

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_coeff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (p : LaurentPolynomial A) :
    (_root_.GlobalTheory.EtC.GmStep.laurentMap f p).coeff = Finsupp.mapRange f f.map_zero p.coeff := by
  refine LaurentPolynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add (f := _), AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, hp, hq,
      Finsupp.mapRange_add (map_add f)]
  · rw [map_mul, _root_.GlobalTheory.EtC.GmStep.laurentMap_C, _root_.GlobalTheory.EtC.GmStep.laurentMap_T,
      ← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.mapRange_single]


open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_isIntegral {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.IsIntegral) : (_root_.GlobalTheory.EtC.GmStep.laurentMap f).IsIntegral := by
  letI := (_root_.GlobalTheory.EtC.GmStep.laurentMap f).toAlgebra
  intro x
  change IsIntegral (LaurentPolynomial A) x
  refine LaurentPolynomial.induction_on' x (fun p q hp hq => hp.add hq) (fun n b => ?_)
  refine IsIntegral.mul ?_ ?_
  · obtain ⟨P, hm, hP⟩ := hf b
    refine ⟨P.map LaurentPolynomial.C, hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ ((_root_.GlobalTheory.EtC.GmStep.laurentMap f).comp LaurentPolynomial.C)
      (LaurentPolynomial.C b) P = 0
    rw [_root_.GlobalTheory.EtC.GmStep.laurentMap_comp_C, ← Polynomial.hom_eval₂, hP, map_zero]
  · rw [← _root_.GlobalTheory.EtC.GmStep.laurentMap_T f n]
    exact isIntegral_algebraMap


open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_ker {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (hk : RingHom.ker f ≤ nilradical A) :
    RingHom.ker (_root_.GlobalTheory.EtC.GmStep.laurentMap f) ≤ nilradical (LaurentPolynomial A) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  have hc : ∀ n, f (x.coeff n) = 0 := by
    intro n
    have h := congrArg (fun g => g n) (_root_.GlobalTheory.EtC.GmStep.laurentMap_coeff f x)
    rw [hx] at h
    simpa using h.symm
  rw [← AddMonoidAlgebra.sum_coeff_single x, Finsupp.sum]
  refine Ideal.sum_mem _ fun n _ => ?_
  rw [LaurentPolynomial.single_eq_C_mul_T]
  refine Ideal.mul_mem_right _ _ ?_
  exact mem_nilradical.mpr ((mem_nilradical.mp (hk (RingHom.mem_ker.mpr (hc n)))).map _)


open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.spec_integral_surj {A B : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (hi : φ.IsIntegral) (hk : RingHom.ker φ ≤ nilradical A) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) := by
  refine ⟨IsIntegralHom.SpecMap_iff.mpr hi, ⟨?_⟩⟩
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hi⟩
  intro P
  haveI := P.isPrime
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P.asIdeal (⊥ : Ideal B)
    (fun a ha => nilradical_le_prime P.asIdeal
      (hk (RingHom.mem_ker.mpr (Ideal.mem_bot.mp (Ideal.mem_comap.mp ha)))))
  refine ⟨⟨Q, hQ⟩, ?_⟩
  change PrimeSpectrum.comap φ ⟨Q, hQ⟩ = P
  exact PrimeSpectrum.ext hQP

variable (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']

abbrev baseHom : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A A'))

abbrev laurentHom : Spec (CommRingCat.of (LaurentPolynomial A')) ⟶ Spec (CommRingCat.of (LaurentPolynomial A)) :=
  Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A A')))

def constSq : Arrow.mk (yoneda.map (laurentHom A A')) ⟶ Arrow.mk (yoneda.map (baseHom A A')) :=
  Arrow.homMk (yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : A' →+* LaurentPolynomial A'))))
    (yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : A →+* LaurentPolynomial A)))) (by
      simp only [Arrow.mk_hom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [laurentMap_comp_C])

def cechC : cech (laurentHom A A') ⟶ cech (baseHom A A') := Arrow.mapCechNerve (constSq A A')

def augK (k : ℕ) : disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌)) ⟶ sch.obj (Spec (CommRingCat.of (LaurentPolynomial A))) :=
  disc.map ((cechAug (laurentHom A A')).app (op ⦋k⦌))

def rowOne (q : ℕ) (i : ℤ) (k : ℕ) :
    Ht q (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) 0 (i - 1) →+ Ht q (disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌))) 1 i where
  toFun a := (cup q (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q (i - 1)) 0 a)
    (pull _ (augK A A' k) (tw q 1) 1 (kum q (laurentVar A)))).cast (by ring) (by ring)
  map_zero' := by simp only [map_zero, AddMonoidHom.zero_apply]; exact GmPhi.cast_zero _ _
  map_add' a b := by simp only [map_add (f := _), AddMonoidHom.add_apply]; exact GmPhi.cast_add _ _ _ _

end GlobalTheory.EtC.GmStep

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.HInvIso

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
  exact CategoryTheory.Functor.map_id _ _

theorem pull_spMap_bij {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R (spMap (e : A →+* B)) F n) := by
  have h1 : ∀ x, pull R (spMap (e : A →+* B)) F n (pull R (spMap (e.symm : B →+* A)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp']
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by ext a; simp
    rw [this, spMap_id', pull_id]
  have h2 : ∀ x, pull R (spMap (e.symm : B →+* A)) F n (pull R (spMap (e : A →+* B)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp']
    have : (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A := by ext a; simp
    rw [this, spMap_id', pull_id]
  exact ⟨Function.LeftInverse.injective h2, Function.RightInverse.surjective h1⟩

end GlobalTheory.EtC.HInvIso

namespace GlobalTheory.EtC


open HInvIso in
theorem hInv_of_ringEquiv : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B], (A ≃+* B) → HInv q A → HInv q B := by
  intro q _ A B _ _ e hA i n
  have hsq : (Polynomial.C : B →+* Polynomial B).comp (e : A →+* B) =
      ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B).comp Polynomial.C := by
    ext a; simp
  have hpull : ∀ x, pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n
      (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n x) =
      pull (ZMod q) (spMap ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B)) (tw q i) n
        (pull (ZMod q) (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n x) := by
    intro x
    rw [← pull_comp, ← pull_comp, ← spMap_comp', ← spMap_comp', hsq]
  have hc : Function.Bijective ((pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n) ∘
      (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n)) := by
    have : ((pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n) ∘
      (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n)) =
      (pull (ZMod q) (spMap ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B)) (tw q i) n) ∘
        (pull (ZMod q) (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n) := funext hpull
    rw [this]
    exact (pull_spMap_bij _ _ n).comp (hA i n)
  exact (Function.Bijective.of_comp_iff _ (pull_spMap_bij e _ n)).1 hc

end GlobalTheory.EtC
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

def laurentMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : LaurentPolynomial A →+* LaurentPolynomial B :=
  AddMonoidAlgebra.mapRingHom ℤ f

namespace GmPhiNat

theorem laurentMap_C {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (laurentMap f).comp (LaurentPolynomial.C : A →+* LaurentPolynomial A) = (LaurentPolynomial.C : B →+* LaurentPolynomial B).comp f := by
  refine RingHom.ext fun a => ?_
  change AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a)
  rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.mapRingHom_single]; rfl

theorem laurentMap_T {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n : ℤ) :
    laurentMap f (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  change AddMonoidAlgebra.mapRingHom ℤ f (AddMonoidAlgebra.single n (1 : A)) = AddMonoidAlgebra.single n (1 : B)
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

theorem laurentMap_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    laurentMap (g.comp f) = (laurentMap g).comp (laurentMap f) :=
  AddMonoidAlgebra.mapRingHom_comp _ _

theorem spMap_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem pull_spMap_comp (q : ℕ) {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) (n i : ℤ)
    (x : Ht q (sp A) n i) : pull _ (spMap (g.comp f)) _ n x = pull _ (spMap g) _ n (pull _ (spMap f) _ n x) := by
  rw [spMap_comp, pull_comp]

theorem pull_cast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f (tw q i') n' (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f (tw q i) n x) := by
  subst hn; subst hi; rfl

theorem laurentVar_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Units.map (Spec.map (CommRingCat.ofHom (laurentMap f))).appTop.hom.toMonoidHom (laurentVar A) = laurentVar B := by
  apply Units.ext
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (laurentMap f))
  have h2 := congrArg (fun φ => φ.hom (LaurentPolynomial.T 1)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  simp only [laurentVar, laurentVarUnit, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [← h2, laurentMap_T]

theorem isUnit_gamma (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of (LaurentPolynomial A)), ⊤)) := by
  have h := (hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)).map
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom
  simpa using h

end GmPhiNat


open GmPhiNat in
theorem gmPhi_nat (h6 : DivisorNaturality) (q : ℕ) [NeZero q] {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hq : IsUnit (q : A))
    (i : ℤ) (a : Ht q (sp A) 0 (i - 1)) :
    pull _ (spMap (laurentMap f)) _ 1 (gmPhi q A i a) = gmPhi q B i (pull _ (spMap f) _ 0 a) := by
  obtain ⟨hcup, -, -, hkum⟩ := h6 q
  simp only [gmPhi, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [pull_cast, hcup, ← pull_spMap_comp, ← pull_spMap_comp, laurentMap_C]
  congr 2
  rw [spMap, hkum _ _ (isUnit_gamma q A hq), laurentVar_map]

end GlobalTheory.EtC

end
end

section

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

def ClosureEtaleAt (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] (P : Ideal R) [P.IsPrime] : Prop :=
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  Algebra.Etale (Localization.AtPrime P)
    (TensorProduct R (Localization.AtPrime P) (GlobalTheory.KeyOriginNoeth.closure A R D))

theorem good_iff_etaleAt (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] (ρ : R →+* A) :
    GlobalTheory.KeyOriginNoeth.Good A R D ρ ↔
      ((∀ (P : Ideal R) [P.IsPrime], (P.comap (algebraMap A R)).height ≤ 1 →
          ClosureEtaleAt A R D P) ∧ PointAtZero A R D ρ) := Iff.rfl

end GlobalTheory.KeyOriginEnlarge
end
end
