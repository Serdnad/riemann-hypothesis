module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle604
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle051
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.CDelta

variable {l : ℕ} [hl : Fact l.Prime] {L Q : Type} [CommRing L] [CommRing Q] {i : L →+* Q} {J : Ideal L}


omit hl in
theorem smul_top_eq (n : ℕ) : ((J.map i) ^ n • ⊤ : Submodule Q Q) = (J ^ n).map i := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.map_pow]


omit hl in
theorem eq_of_forall (hc : IsCompl i J) {u v : Q} (h : ∀ n, u - v ∈ (J ^ n).map i) : u = v := by
  refine sub_eq_zero.1 (hc.complete.toIsHausdorff.haus (u - v) fun n => ?_)
  rw [SModEq.sub_mem, sub_zero, smul_top_eq]; exact h n

omit hl in
theorem mem_succ {x : Q} {n : ℕ} (h : x ∈ (J ^ (n + 1)).map i) : x ∈ (J ^ n).map i :=
  Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) h

theorem key (hc : IsCompl i J) (hlJ : (l : L) ∈ J) (D : Delta l L) {x : Q} {a b : L} {n : ℕ}
    (ha : x - i a ∈ (J ^ (n + 1)).map i) (hb : x - i b ∈ (J ^ (n + 1)).map i) :
    i (D.δ a) - i (D.δ b) ∈ (J ^ n).map i := by
  have hab : a - b ∈ J ^ (n + 1) := hc.ker _ _ (by
    have := sub_mem hb ha
    rw [map_sub]; convert this using 1; ring)
  have h := GlobalTheory.T.delta_add_sub_mem_pow_of_mem_pow_succ l L D J hlJ n b (a - b) hab
  rw [add_sub_cancel] at h
  rw [← map_sub]; exact Ideal.mem_map_of_mem _ h

theorem exists_lim (hc : IsCompl i J) (hlJ : (l : L) ∈ J) (D : Delta l L) (x : Q) :
    ∃ z : Q, ∀ (n : ℕ) (a : L), x - i a ∈ (J ^ (n + 1)).map i → z - i (D.δ a) ∈ (J ^ n).map i := by
  choose ap hap using hc.surj x
  obtain ⟨z, hz⟩ := hc.complete.toIsPrecomplete.prec (f := fun n => i (D.δ (ap (n + 1)))) fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_top_eq]
    exact key hc hlJ D (hap (m + 1)) (Ideal.map_mono (Ideal.pow_le_pow_right (by omega)) (hap (n + 1)))
  refine ⟨z, fun n a ha => ?_⟩
  have h1 := hz n
  rw [SModEq.sub_mem, smul_top_eq] at h1
  have h2 := key hc hlJ D (hap (n + 1)) ha
  have := sub_mem h2 h1
  convert this using 1; ring

end GlobalTheory.BSP.CDelta


open GlobalTheory.BSP.CDelta in
theorem GlobalTheory.BSP.exists_delta_completion : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [CommRing L] (Q : Type) [CommRing Q]
    (i : L →+* Q) (J : Ideal L), IsCompl i J → (l : L) ∈ J → ∀ D : Delta l L, ∃ D' : Delta l Q, IsδMap D D' i := by
  intro l _ L _ Q _ i J hc hlJ D
  choose d hd using exists_lim hc hlJ D
  have sep : ∀ u v : W2 l Q, (∀ n, W2.map (Ideal.Quotient.mk ((J ^ n).map i)) u =
      W2.map (Ideal.Quotient.mk ((J ^ n).map i)) v) → u = v := by
    intro u v h
    have h1 : ∀ n, Ideal.Quotient.mk ((J ^ n).map i) u.fst = Ideal.Quotient.mk ((J ^ n).map i) v.fst :=
      fun n => congrArg W2.fst (h n)
    have h2 : ∀ n, Ideal.Quotient.mk ((J ^ n).map i) u.snd = Ideal.Quotient.mk ((J ^ n).map i) v.snd :=
      fun n => congrArg W2.snd (h n)
    exact W2.ext (eq_of_forall hc fun n => Ideal.Quotient.eq.1 (h1 n))
      (eq_of_forall hc fun n => Ideal.Quotient.eq.1 (h2 n))
  have ap : ∀ (x : Q) (n : ℕ) (a : L), x - i a ∈ (J ^ (n + 1)).map i →
      W2.map (Ideal.Quotient.mk ((J ^ n).map i)) (⟨x, d x⟩ : W2 l Q) =
        W2.map ((Ideal.Quotient.mk ((J ^ n).map i)).comp i) (deltaSectionToWittLengthTwo D a) := by
    intro x n a ha
    have h1 : Ideal.Quotient.mk ((J ^ n).map i) x = Ideal.Quotient.mk ((J ^ n).map i) (i a) :=
      Ideal.Quotient.eq.2 (mem_succ ha)
    have h2 : Ideal.Quotient.mk ((J ^ n).map i) (d x) = Ideal.Quotient.mk ((J ^ n).map i) (i (D.δ a)) :=
      Ideal.Quotient.eq.2 (hd x n a ha)
    exact W2.ext h1 h2
  let s : Q →+* W2 l Q :=
    { toFun := fun x => ⟨x, d x⟩
      map_one' := sep _ _ fun n => by
        rw [ap 1 n 1 (by simp), map_one, map_one, map_one]
      map_zero' := sep _ _ fun n => by
        rw [ap 0 n 0 (by simp), map_zero, map_zero, map_zero]
      map_add' := fun x y => sep _ _ fun n => by
        obtain ⟨a, ha⟩ := hc.surj x (n + 1)
        obtain ⟨b, hb⟩ := hc.surj y (n + 1)
        have hab : x + y - i (a + b) ∈ (J ^ (n + 1)).map i := by
          rw [map_add (f := _)]; convert add_mem ha hb using 1; ring
        show W2.map _ (⟨x + y, d (x + y)⟩ : W2 l Q) = W2.map _ ((⟨x, d x⟩ : W2 l Q) + ⟨y, d y⟩)
        rw [ap _ n _ hab, map_add (W2.map (Ideal.Quotient.mk _)), ap x n a ha, ap y n b hb, map_add (deltaSectionToWittLengthTwo D),
          map_add]
      map_mul' := fun x y => sep _ _ fun n => by
        obtain ⟨a, ha⟩ := hc.surj x (n + 1)
        obtain ⟨b, hb⟩ := hc.surj y (n + 1)
        have hab : x * y - i (a * b) ∈ (J ^ (n + 1)).map i := by
          have : x * y - i (a * b) = y * (x - i a) + i a * (y - i b) := by rw [map_mul]; ring
          rw [this]; exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
        show W2.map _ (⟨x * y, d (x * y)⟩ : W2 l Q) = W2.map _ ((⟨x, d x⟩ : W2 l Q) * ⟨y, d y⟩)
        rw [ap _ n _ hab, map_mul (W2.map (Ideal.Quotient.mk _)), ap x n a ha, ap y n b hb, map_mul (deltaSectionToWittLengthTwo D),
          map_mul] }
  refine ⟨deltaStructureOfWittLengthTwoSection s fun _ => rfl, fun a => ?_⟩
  show i (D.δ a) = d (i a)
  exact (eq_of_forall hc fun n => hd (i a) n a (by simp)).symm
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.EnvShape

variable {l : ℕ} [hl : Fact l.Prime] {A : Type} [CommRing A]

theorem C_mem_supp (S : Set ℕ) (c : A) : MvPolynomial.C c ∈ MvPolynomial.supported A S := by
  rw [← MvPolynomial.algebraMap_eq]; exact Subalgebra.algebraMap_mem _ c


omit hl in
theorem cc_mem_ideal {R : Type} [CommRing R] (I : Ideal R) {x : R} (y : R) (hx : x ∈ I) : cc l x y ∈ I := by
  unfold cc
  exact Ideal.sum_mem _ fun k hk =>
    Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hx k (Finset.mem_Ioo.1 hk).1))


omit hl in
theorem cc_mem_sub {R : Type} [CommRing R] [Algebra A R] (S : Subalgebra A R) {x y : R} (hx : x ∈ S)
    (hy : y ∈ S) : cc l x y ∈ S := by
  unfold cc
  exact Subalgebra.sum_mem _ fun k _ => S.mul_mem (S.mul_mem (natCast_mem S _) (S.pow_mem hx _)) (S.pow_mem hy _)

theorem phi_mem (D : Delta l A) (J : Ideal A) (hlJ : (l : A) ∈ J) {e : A} (he : e ∈ J) : D.φ e ∈ J := by
  rw [D.φ_eq]; exact J.add_mem (J.pow_mem_of_mem he _ hl.out.pos) (J.mul_mem_right _ hlJ)

theorem delta_Iio (D : Delta l A) (J : Ideal A) (hlJ : (l : A) ∈ J) (i : ℕ) (s : MvPolynomial ℕ A)
    (hs : s ∈ MvPolynomial.supported A (Set.Iio i)) :
    (polyDelta D).δ s ∈ MvPolynomial.supported A (Set.Iic i) ∧
    ∃ a ∈ MvPolynomial.supported A (Set.Iio i), ∃ b ∈ MvPolynomial.supported A (Set.Iio i),
      (polyDelta D).δ s - (a * MvPolynomial.X i + b) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
  cases i with
  | zero =>
    have h0 : Set.Iio (0:ℕ) = ∅ := by ext; simp
    rw [h0, MvPolynomial.supported_empty, Algebra.mem_bot] at hs
    obtain ⟨c, rfl⟩ := hs
    rw [MvPolynomial.algebraMap_eq, polyDelta_C]
    refine ⟨C_mem_supp _ _, 0, Subalgebra.zero_mem _, MvPolynomial.C (D.δ c), C_mem_supp _ _, ?_⟩
    simp
  | succ i =>
    have h1 : Set.Iio (i+1) = Set.Iic i := by ext; simp [Nat.lt_succ_iff]
    rw [h1] at hs ⊢
    obtain ⟨h2, a, ha, b, hb, h3⟩ := GlobalTheory.T.mvPolynomialDelta_supported_linear_mod_prime l A D i s hs
    have hl' : (l : MvPolynomial ℕ A) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
      have := Ideal.mem_map_of_mem (MvPolynomial.C : A →+* MvPolynomial ℕ A) hlJ
      rwa [map_natCast] at this
    exact ⟨h2, a, ha, b, hb, Ideal.span_le.2 (Set.singleton_subset_iff.2 hl') h3⟩

theorem step_eq (D : Delta l A) (e : A) (k : ℕ) (s : MvPolynomial ℕ A) :
    (polyDelta D).δ (MvPolynomial.C e * MvPolynomial.X k + s) =
      MvPolynomial.C (D.φ e) * MvPolynomial.X (k + 1) +
        (MvPolynomial.X k ^ l * MvPolynomial.C (D.δ e) + (polyDelta D).δ s -
          cc l (MvPolynomial.C e * MvPolynomial.X k) s) := by
  rw [(polyDelta D).δ_add, (polyDelta D).δ_mul, polyDelta_C, polyDelta_X, D.φ_eq]
  simp only [map_add (f := _), map_pow, map_mul, map_natCast]
  unfold cc; ring

theorem shape (D : Delta l A) (J : Ideal A) (d p : A) (hlJ : (l : A) ∈ J) (hd : d ∈ J)
    (hu : IsUnit (D.δ d)) (k : ℕ) :
    ∃ e ∈ J, IsUnit (D.δ e) ∧ ∃ s ∈ MvPolynomial.supported A (Set.Iio k),
      (polyDelta D).δ^[k] (MvPolynomial.C p + MvPolynomial.C d * MvPolynomial.X 0) =
        MvPolynomial.C e * MvPolynomial.X k + s := by
  induction k with
  | zero => exact ⟨d, hd, hu, MvPolynomial.C p, C_mem_supp _ _, by simp [add_comm]⟩
  | succ k ih =>
    obtain ⟨e, he, heu, s, hs, hk⟩ := ih
    have hIic : Set.Iic k = Set.Iio (k+1) := by ext; simp [Nat.lt_succ_iff]
    have hX : MvPolynomial.X k ∈ MvPolynomial.supported A (Set.Iio (k+1)) :=
      by rw [MvPolynomial.supported_eq_adjoin_X]; exact Algebra.subset_adjoin ⟨k, by simp, rfl⟩
    have hδ := (delta_Iio D J hlJ k s hs).1
    rw [hIic] at hδ
    have hs' : s ∈ MvPolynomial.supported A (Set.Iio (k+1)) :=
      MvPolynomial.supported_mono (Set.Iio_subset_Iio (Nat.le_succ k)) hs
    refine ⟨D.φ e, phi_mem D J hlJ he, ?_, MvPolynomial.X k ^ l * MvPolynomial.C (D.δ e) + (polyDelta D).δ s -
      cc l (MvPolynomial.C e * MvPolynomial.X k) s, ?_, ?_⟩
    · rw [GlobalTheory.T.deltaRingStructure_delta_frobenius_comm]; exact heu.map D.φ
    · exact Subalgebra.sub_mem _ (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hX _)
        (C_mem_supp _ _)) hδ) (cc_mem_sub _ (Subalgebra.mul_mem _ (C_mem_supp _ _) hX) hs')
    · rw [Function.iterate_succ_apply', hk, step_eq]

theorem envRel_triangular : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A)
    (d p : A), (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → ∀ i, ∃ (v : Aˣ) (a b : MvPolynomial ℕ A),
    a ∈ MvPolynomial.supported A (Set.Iio i) ∧ b ∈ MvPolynomial.supported A (Set.Iio i) ∧
    envRel D d p i - (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) ∈
      J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
  intro l _ A _ D J d p hlJ hd hu i
  obtain ⟨e, he, heu, s, hs, hi⟩ := shape D J d p hlJ hd hu i
  obtain ⟨-, a, ha, b, hb, hab⟩ := delta_Iio D J hlJ i s hs
  refine ⟨heu.unit, a, b, ha, hb, ?_⟩
  have hrel : envRel D d p i = MvPolynomial.C (D.φ e) * MvPolynomial.X (i + 1) +
      (MvPolynomial.X i ^ l * MvPolynomial.C (D.δ e) + (polyDelta D).δ s -
        cc l (MvPolynomial.C e * MvPolynomial.X i) s) := by
    rw [envRel, Function.iterate_succ_apply', hi, step_eq]
  have hdiff : envRel D d p i - (MvPolynomial.C (heu.unit : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b)
      = MvPolynomial.C (D.φ e) * MvPolynomial.X (i + 1) + ((polyDelta D).δ s - (a * MvPolynomial.X i + b)) -
        cc l (MvPolynomial.C e * MvPolynomial.X i) s := by
    rw [hrel, IsUnit.unit_spec]; ring
  rw [hdiff]
  exact Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _
    (Ideal.mem_map_of_mem _ (phi_mem D J hlJ he))) hab)
    (cc_mem_ideal _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ he)))

end GlobalTheory.EnvShape
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal Matrix

namespace GlobalTheory.FrobIntTensor

section Coord

variable {R O S T : Type} [CommRing R] [CommRing O] [Algebra R O] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] {d : Type} (b : Module.Basis d R O)

def coordT (k : d) : O ⊗[R] S →ₗ[R] S :=
  (TensorProduct.lid R S).toLinearMap ∘ₗ TensorProduct.map (b.coord k) LinearMap.id

theorem coordT_tmul (k : d) (o : O) (s : S) : coordT b k (o ⊗ₜ[R] s) = b.repr o k • s := by
  simp [coordT]

theorem coordT_map (f : S →ₐ[R] T) (k : d) (x : O ⊗[R] S) :
    coordT b k (Algebra.TensorProduct.map (AlgHom.id O O) f x) = f (coordT b k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o s => rw [Algebra.TensorProduct.map_tmul, coordT_tmul, coordT_tmul, AlgHom.id_apply, map_smul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem coordT_mul_tmul (k : d) (z : O ⊗[R] S) (s : S) :
    coordT b k (z * ((1 : O) ⊗ₜ[R] s)) = coordT b k z * s := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o s' => rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, coordT_tmul, coordT_tmul, smul_mul_assoc]
  | add x y hx hy => simp only [add_mul, map_add (f := _), hx, hy]

theorem sum_coordT [Fintype d] (x : O ⊗[R] S) : ∑ k, b k ⊗ₜ[R] coordT b k x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o s =>
    conv_rhs => rw [← b.sum_repr o]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coordT_tmul, TensorProduct.smul_tmul]
  | add x y hx hy => simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

end Coord

section Witt

variable (l : ℕ) [Fact l.Prime]

def valSub : ValuationSubring (Cb l) where
  toSubring := (algebraMap (OCb l) (Cb l)).range
  mem_or_inv_mem' x := by
    rcases (ValuationRing.iff_isInteger_or_isInteger (OCb l) (Cb l)).mp inferInstance x with h | h
    · obtain ⟨y, hy⟩ := h
      exact Or.inl ⟨y, hy⟩
    · obtain ⟨y, hy⟩ := h
      exact Or.inr ⟨y, hy⟩



def toValSub : OCb l →+* valSub l :=
  (algebraMap (OCb l) (Cb l)).codRestrict (valSub l) fun x => ⟨x, rfl⟩

theorem map_toValSub (x : Ainf l) :
    WittVector.map (valSub l).subtype (WittVector.map (toValSub l) x) = inclW l x := by
  ext m
  simp only [WittVector.map_coeff, inclW]
  rfl

theorem mem_range_inclW {n : Type} [Fintype n] (v : n → WCb l) (Y : Matrix n n (Ainf l))
    (h : ∀ i, frobW l (v i) = ∑ j, inclW l (Y i j) * v j) (i : n) : v i ∈ (inclW l).range := by
  have key := GlobalTheory.witt_matrix_coeff_mem_of_frobenius l (valSub l) (Matrix.of fun i (_ : n) => v i)
    (Y.map (WittVector.map (toValSub l))) (Or.inl (by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, map_toValSub]
      rw [WittVector.frobenius_eq_map_frobenius]
      exact h i))
  have hc : ∀ m, ∃ y : OCb l, algebraMap (OCb l) (Cb l) y = (v i).coeff m := fun m => key i i m
  refine ⟨WittVector.mk l fun m => Classical.choose (hc m), ?_⟩
  ext m
  rw [inclW, WittVector.map_coeff, WittVector.coeff_mk]
  exact Classical.choose_spec (hc m)

end Witt

section Main

theorem coordT_inclO {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] {d : Type}
    (b : Module.Basis d ℤ_[l] O) (k : d) (y : OA l O) :
    coordT b k (inclO l O y) = inclW l (coordT b k y) :=
  coordT_map b (inclWA l) k y

theorem mem_range_inclO : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {n : Type} [Fintype n] (v : n → OW l O)
    (Y : Matrix n n (OA l O)), (∀ i, frobOW l O (v i) = (Y.map (inclO l O) *ᵥ v) i) →
    ∀ i, v i ∈ (inclO l O).range := by
  intro l _ O _ _ _ _ n _ v Y h i
  classical
  let b := Module.Free.chooseBasis ℤ_[l] O
  let v' : n × Module.Free.ChooseBasisIndex ℤ_[l] O → WCb l := fun p => coordT b p.2 (v p.1)
  let Yt : Matrix (n × Module.Free.ChooseBasisIndex ℤ_[l] O) (n × Module.Free.ChooseBasisIndex ℤ_[l] O)
      (Ainf l) := fun p q => coordT b p.2 (Y p.1 q.1 * (b q.2 ⊗ₜ[ℤ_[l]] (1 : Ainf l)))
  have hv : ∀ j, v j = ∑ m, (b m ⊗ₜ[ℤ_[l]] (1 : WCb l)) * ((1 : O) ⊗ₜ[ℤ_[l]] v' (j, m)) := by
    intro j
    conv_lhs => rw [← sum_coordT b (v j)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hY : ∀ p, frobW l (v' p) = ∑ q, inclW l (Yt p q) * v' q := by
    rintro ⟨i', k⟩
    have e1 : frobW l (v' (i', k)) = coordT b k (frobOW l O (v i')) := (coordT_map b (frobW l) k (v i')).symm

    rw [e1, h i', Matrix.mulVec, dotProduct, map_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.map_apply]
    conv_lhs => rw [hv j]

    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have e2 : inclO l O (Y i' j) * (b m ⊗ₜ[ℤ_[l]] (1 : WCb l)) =
        inclO l O (Y i' j * (b m ⊗ₜ[ℤ_[l]] (1 : Ainf l))) := by
      rw [map_mul, inclO_tmul, map_one]
    rw [← mul_assoc, e2, coordT_mul_tmul, coordT_inclO]
  have hr : ∀ p, v' p ∈ (inclW l).range := mem_range_inclW l v' Yt hY
  refine ⟨∑ k, b k ⊗ₜ[ℤ_[l]] Classical.choose (hr (i, k)), ?_⟩

  rw [map_sum]
  conv_rhs => rw [← sum_coordT b (v i)]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (inclO_tmul _ _).trans (congrArg (fun w => b k ⊗ₜ[ℤ_[l]] w) (Classical.choose_spec (hr (i, k))))

end Main

end GlobalTheory.FrobIntTensor
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysConst

theorem semi_ext {A B C M N : Type} [CommRing A] [CommRing B] [CommRing C] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) (k : B →+* C)
    (F G : N →+ C) (hF : ∀ (r : B) y, F (r • y) = k r * F y) (hG : ∀ (r : B) y, G (r • y) = k r * G y)
    (hx : ∀ x, F (u x) = G (u x)) (y : N) : F y = G y := by
  letI : Module B C := Module.compHom C k
  let F' : N →ₗ[B] C := { toFun := F, map_add' := F.map_add, map_smul' := hF }
  let G' : N →ₗ[B] C := { toFun := G, map_add' := G.map_add, map_smul' := hG }
  exact LinearMap.congr_fun (h.hom_ext (w := F') (w' := G') hx) y

theorem semi_lift {A B C M N : Type} [CommRing A] [CommRing B] [CommRing C] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) (k : B →+* C)
    (F : M →+ C) (hF : ∀ (r : A) x, F (r • x) = k (f r) * F x) :
    ∃ G : N →+ C, (∀ (r : B) y, G (r • y) = k r * G y) ∧ ∀ x, G (u x) = F x := by
  letI : Module B C := Module.compHom C k
  let F' : M →ₛₗ[f] C := { toFun := F, map_add' := F.map_add, map_smul' := hF }
  obtain ⟨w, hw, -⟩ := h C F'
  exact ⟨w.toAddMonoidHom, fun r y => w.map_smul r y, hw⟩

theorem eq_of_diagonal {l : ℕ} {R C : Type} [CommRing R] [CommRing C] (E : FCrys l R) {P PP S : Obj l R}
    (p₀ p₁ : GlobalTheory.Prism.Hom P PP) (δ : GlobalTheory.Prism.Hom PP S) (hδ : δ.comp p₀ = δ.comp p₁) (k : S.A →+* C)
    (F G : E.M PP →+ C) (hF : ∀ (r : PP.A) y, F (r • y) = k (δ.f r) * F y)
    (hG : ∀ (r : PP.A) y, G (r • y) = k (δ.f r) * G y)
    (hx : ∀ x, F (E.tr p₀ x) = G (E.tr p₁ x)) (y : E.M PP) : F y = G y := by
  obtain ⟨μ, hμ, hμx⟩ := semi_lift (E.tr_bc (δ.comp p₀)) k (F.comp (E.tr p₀).toAddMonoidHom) (fun r x => by
    change F (E.tr p₀ (r • x)) = k (δ.f (p₀.f r)) * F (E.tr p₀ x)
    rw [LinearMap.map_smulₛₗ, hF])
  have hν : ∀ (r : PP.A) y, (μ.comp (E.tr δ).toAddMonoidHom) (r • y) =
      (k.comp δ.f) r * (μ.comp (E.tr δ).toAddMonoidHom) y := fun r y => by
    change μ (E.tr δ (r • y)) = k (δ.f r) * μ (E.tr δ y)
    rw [LinearMap.map_smulₛₗ, hμ]
  have h0 := semi_ext (E.tr_bc p₀) (k.comp δ.f) F _ hF hν (fun x => by
    change _ = μ (E.tr δ (E.tr p₀ x))
    rw [← E.tr_comp, hμx]; rfl) y
  have h1 := semi_ext (E.tr_bc p₁) (k.comp δ.f) G _ hG hν (fun x => by
    change _ = μ (E.tr δ (E.tr p₁ x))
    rw [← E.tr_comp, ← hx]
    have : ∀ q : GlobalTheory.Prism.Hom P S, δ.comp p₀ = q → μ (E.tr q x) = F (E.tr p₀ x) := by
      rintro _ rfl
      exact hμx x
    exact (this _ hδ).symm) y
  exact h0.trans h1.symm

theorem constantCoeff_eq : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (GlobalTheory.BKReal.toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (j₀ : ZMod a → S₀.A →+* K⟦X⟧), δ.comp p₀ = δ.comp p₁ → (∀ τ y, j₀ τ (δ.f y) = PowerSeries.constantCoeff (j τ y)) → (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (GlobalTheory.BKReal.toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (GlobalTheory.BKReal.toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∀ y τ i, PowerSeries.constantCoeff (lam₀ y τ i) = PowerSeries.constantCoeff (lam₁ y τ i) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ EE c _ sh hsh PP S₀ p₀ p₁ δ j j₀ hδ hj _ lam₀ lam₁ h₀ h₁ hx₀ hx₁
    y τ i
  have hc : ∀ f : K⟦X⟧, PowerSeries.constantCoeff (sh f) = f := fun f => by
    simpa using hsh f 0
  let pr : (ZMod a → ι → K⟦X⟧⟦X⟧) →+ K⟦X⟧ :=
    { toFun := fun q => PowerSeries.constantCoeff (q τ i)
      map_zero' := by simp
      map_add' := fun q q' => by simp }
  refine eq_of_diagonal EE p₀ p₁ δ hδ (j₀ τ) (pr.comp lam₀) (pr.comp lam₁) (fun r y => ?_) (fun r y => ?_)
    (fun x => ?_) y
  · change PowerSeries.constantCoeff (lam₀ (r • y) τ i) = _ * PowerSeries.constantCoeff (lam₀ y τ i)
    rw [h₀, map_mul, hj]
  · change PowerSeries.constantCoeff (lam₁ (r • y) τ i) = _ * PowerSeries.constantCoeff (lam₁ y τ i)
    rw [h₁, map_mul, hj]
  · change PowerSeries.constantCoeff (lam₀ (EE.tr p₀ x) τ i) = PowerSeries.constantCoeff (lam₁ (EE.tr p₁ x) τ i)
    rw [hx₀, hx₁, hc, PowerSeries.constantCoeff_C]

end GlobalTheory.CrysConst
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

def cstS : Wq l a →+* (ZMod a → K⟦X⟧) :=
  Pi.ringHom fun τ => (C : K →+* K⟦X⟧).comp ((algebraMap O K).comp (emb t τ).toRingHom)

theorem cstS_apply (w : Wq l a) (τ : ZMod a) : cstS t K w τ = C (algebraMap O K (emb t τ w)) := rfl


variable (a) {K} in
def dpS (e n : ℕ) : ZMod a → K⟦X⟧ := fun _ => monomial n (((n / e).factorial : K)⁻¹)

end GlobalTheory.CrysPrism
end
end
