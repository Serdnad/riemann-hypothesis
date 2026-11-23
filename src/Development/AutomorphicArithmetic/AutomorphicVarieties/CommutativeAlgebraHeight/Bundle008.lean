module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {E' : Type} [Ring E'] [Algebra A E']
  (f : E →ₐ[A] E')

private theorem map_eq_lTensor (S : Type) [CommRing S] [Algebra A S] (z : S ⊗[A] E) :
    Algebra.TensorProduct.map (AlgHom.id S S) f z = f.toLinearMap.lTensor S z := by
  induction z with
  | tmul s x => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

private theorem map_surj (hf : Function.Surjective f) (S : Type) [CommRing S] [Algebra A S] :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id S S) f) := by
  intro y
  obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective S (g := f.toLinearMap) hf y
  exact ⟨x, (map_eq_lTensor f S x).trans hx⟩

private theorem eq_of_map_eq (hf : Function.Surjective f) (hk : ∀ x, f x = 0 → x ∈ D.ker)
    (S : Type) [CommRing S] [Algebra A S] (x y : S ⊗[A] E)
    (h : Algebra.TensorProduct.map (AlgHom.id S S) f x = Algebra.TensorProduct.map (AlgHom.id S S) f y) :
    D.D S x = D.D S y := by
  have hex := lTensor_exact S (LinearMap.exact_subtype_ker_map f.toLinearMap) hf
  have h0 : f.toLinearMap.lTensor S (x - y) = 0 := by
    rw [← map_eq_lTensor, map_sub, h, sub_self]
  obtain ⟨w, hw⟩ := (hex _).1 h0
  have key : ∀ (w : S ⊗[A] (LinearMap.ker f.toLinearMap)) (y : S ⊗[A] E),
      D.D S (y + (LinearMap.ker f.toLinearMap).subtype.lTensor S w) = D.D S y := by
    intro w
    induction w with
    | tmul s k =>
      intro y
      have := (D.mem_ker.1 (hk k.1 k.2)) S y (s ⊗ₜ 1) 1
      simpa using this
    | add a b ha hb => intro y; rw [LinearMap.map_add (f := _), ← add_assoc, hb, ha]
  rw [← key w y, hw, add_sub_cancel]

private theorem map_map_swap (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (g : B →ₐ[A] B')
    (x : B ⊗[A] E) :
    Algebra.TensorProduct.map (AlgHom.id B' B') f (Algebra.TensorProduct.map g (AlgHom.id A E) x) =
      Algebra.TensorProduct.map g (AlgHom.id A E') (Algebra.TensorProduct.map (AlgHom.id B B) f x) := by
  induction x with
  | tmul s x => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end

theorem UpperTheory.V.CA.d_factor :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {E' : Type} [Ring E'] [Algebra A E'] (f : E →ₐ[A] E'), Function.Surjective f → (∀ x, f x = 0 → x ∈ D.ker) → ∃! D' : Det n A E', D'.pull f = D := by
  intro n A E _ _ _ D E' _ _ f hf hk
  have hs := map_surj f hf
  have he := eq_of_map_eq D f hf hk
  have hσ : ∀ (S : Type) [CommRing S] [Algebra A S] (x : S ⊗[A] E),
      D.D S (Function.surjInv (hs S) (Algebra.TensorProduct.map (AlgHom.id S S) f x)) = D.D S x :=
    fun S _ _ x => he S _ _ (Function.surjInv_eq _ _)
  let D' : Det n A E' :=
    { D := fun S _ _ =>
        { toFun := fun y => D.D S (Function.surjInv (hs S) y)
          map_one' := by
            rw [← map_one (Algebra.TensorProduct.map (AlgHom.id S S) f), hσ, map_one]
          map_mul' := fun x y => by
            obtain ⟨x, rfl⟩ := hs S x
            obtain ⟨y, rfl⟩ := hs S y
            rw [← map_mul (Algebra.TensorProduct.map (AlgHom.id S S) f), hσ, hσ, hσ, map_mul] }
      nat := fun B B' _ _ _ _ g x => by
        obtain ⟨x, rfl⟩ := hs B x
        change D.D B' (Function.surjInv (hs B') _) = g (D.D B (Function.surjInv (hs B) _))
        rw [← map_map_swap, hσ, hσ, D.nat]
      homog := fun B _ _ b x => by
        obtain ⟨x, rfl⟩ := hs B x
        change D.D B (Function.surjInv (hs B) _) = b ^ n * D.D B (Function.surjInv (hs B) _)
        rw [← map_smul, hσ, hσ, D.homog] }
  refine ⟨D', Det.ext' fun S _ _ x => hσ S x, fun D'' h => Det.ext' fun S _ _ y => ?_⟩
  obtain ⟨x, rfl⟩ := hs S y
  refine Eq.trans ?_ (hσ S x).symm
  rw [← h]
  rfl
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem D_congr {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (B : Type) [CommRing B]
    (i j : Algebra A B) (h : ∀ a, @algebraMap A B _ _ i a = @algebraMap A B _ _ j a) (x : MonoidAlgebra B G) :
    @GDet.D n A G _ _ D B _ i x = @GDet.D n A G _ _ D B _ j x := by
  have : i = j := Algebra.algebra_ext i j h
  subst this; rfl

private theorem ofT_gen {A G : Type} [CommRing A] [Group G] {m : ℕ} (y : Fin m → MonoidAlgebra A G) :
    ofT A G (MvPolynomial (Fin m) A) (Det.gen (A := A) y) = GDet.gen y := by

  simp only [Det.gen, GDet.gen, map_sum, ofT_tmul]
  rfl

private theorem ofT_map {A G : Type} [CommRing A] [Group G] (S : Type) [CommRing S] [Algebra A S]
    (x : S ⊗[A] MonoidAlgebra A G) :
    ofT A G S[X] (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A _) x) =
      MonoidAlgebra.mapRingHom G (C : S →+* S[X]) (ofT A G S x) := by
  induction x with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul s y => ext1; ext1 g; simp [ofT_tmul]

private theorem chiS_eq {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) {m : ℕ}
    (x : MvPolynomial (Fin m) A ⊗[A] MonoidAlgebra A G) :
    D.toDet.chiS (MvPolynomial (Fin m) A) x =
      (D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (ofT A G _ x) := by
  have h : ofT A G (MvPolynomial (Fin m) A)[X] (X ⊗ₜ 1 -
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) A)[X])
        (AlgHom.id A _) x) =
      MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (ofT A G _ x) := by
    rw [map_sub, ofT_map, ofT_tmul, map_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  refine (congrArg (D.D (MvPolynomial (Fin m) A)[X]) h).trans ?_
  exact D_congr D (MvPolynomial (Fin m) A)[X] inferInstance
    ((algebraMap (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) A)[X]).comp MvPolynomial.C).toAlgebra (fun a => rfl) _

private theorem coeff_lid {A G : Type} [CommRing A] [Group G] {m : ℕ} (β : Fin m →₀ ℕ)
    (w : MvPolynomial (Fin m) A ⊗[A] MonoidAlgebra A G) (g : G) :
    (TensorProduct.lid A (MonoidAlgebra A G) ((MvPolynomial.lcoeff A β).rTensor _ w)).coeff g =
      AddMonoidAlgebra.coeff ((ofT A G _ w).coeff g) β := by
  induction w with
  | add a b ha hb => simp only [map_add (f := _), MonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_add, ha, hb]
  | tmul s y => simp [ofT_tmul, mul_comm s, MvPolynomial.coeff_C_mul, mul_comm (y.coeff g)]

private theorem chElt_coeff {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) {m : ℕ}
    (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ) (g : G) :
    (D.toDet.chElt y β).coeff g = AddMonoidAlgebra.coeff ((Polynomial.aeval (GDet.gen y)
        ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y))).coeff g)
      β := by
  rw [Det.chElt, coeff_lid, chiS_eq, ← Polynomial.aeval_algHom_apply, ofT_gen]

theorem UpperTheory.V.CA.d_toDet_CH :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G), D.toDet.CH = TwoSidedIdeal.span D.CH := by
  intro n A G _ _ D
  rw [Det.CH]
  congr 1
  ext1 z
  constructor
  · rintro ⟨m, y, β, rfl⟩
    exact ⟨m, y, β, chElt_coeff D y β⟩
  · rintro ⟨m, y, β, h⟩
    refine ⟨m, y, β, ?_⟩
    ext g
    rw [h, chElt_coeff]
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_toDet_ofRep :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G], (∀ ρ : G →* Matrix (Fin n) (Fin n) A, (GDet.ofRep ρ).toDet = Det.ofRep (Fintype.card_fin n) (GDet.repAlg ρ A)) ∧ ∀ (D : GDet n A G) (H : Type) [Group H] (φ : H →* G), (D.comap φ).toDet = D.toDet.pull (MonoidAlgebra.mapDomainAlgHom A A φ) := by
  intro n A G _ _
  refine ⟨fun ρ => Det.ext' fun S _ _ x => ?_, fun D H _ φ => Det.ext' fun S _ _ x => ?_⟩
  · change (GDet.repAlg ρ S (ofT A G S x)).det = (Det.repS (GDet.repAlg ρ A) S x).det
    congr 1
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul s y =>
      rw [ofT_tmul, Det.repS_tmul, map_smul]
      congr 1
      induction y using MonoidAlgebra.induction_linear with
      | zero => ext i j; simp
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]; ext i j; simp
      | single g r => ext i j; simp [GDet.repAlg]
  · change D.D S (MonoidAlgebra.mapDomainRingHom S φ (ofT A H S x)) =
      D.D S (ofT A G S (Algebra.TensorProduct.map (AlgHom.id S S) (MonoidAlgebra.mapDomainAlgHom A A φ) x))
    congr 1
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul s y =>
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
      | single g r => simp [ofT_tmul]
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section SlopeTestRemainingChoices

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E]

private theorem unopS_tmul (S : Type) [CommRing S] [Algebra A S] (s : S) (a : Eᵐᵒᵖ) :
    Det.unopS A E S (s ⊗ₜ a) = s ⊗ₜ a.unop := by
  simp [Det.unopS]

private theorem unopS_surj (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E) :
    ∃ z, Det.unopS A E S z = y := by
  induction y with
  | tmul s a => exact ⟨s ⊗ₜ MulOpposite.op a, unopS_tmul S s _⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩

private theorem op_D (D : Det n A E) (S : Type) [CommRing S] [Algebra A S] (x : S ⊗[A] Eᵐᵒᵖ) :
    D.op.D S x = D.D S (Det.unopS A E S x) := rfl

private theorem unopS_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T] (φ : S →ₐ[A] T)
    (x : S ⊗[A] Eᵐᵒᵖ) :
    Det.unopS A E T (Algebra.TensorProduct.map φ (AlgHom.id A _) x) =
      Algebra.TensorProduct.map φ (AlgHom.id A E) (Det.unopS A E S x) := by
  induction x with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul s a => simp [Det.unopS]

private theorem op_chiS (D : Det n A E) (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] Eᵐᵒᵖ) :
    D.op.chiS S y = D.chiS S (Det.unopS A E S y) := by
  unfold Det.chiS
  rw [op_D, map_sub, unopS_map, unopS_tmul, MulOpposite.unop_one]

private theorem unopS_pow (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] Eᵐᵒᵖ) (k : ℕ) :
    Det.unopS A E S (y ^ k) = Det.unopS A E S y ^ k := by
  induction k with
  | zero => simp [Det.unopS, Algebra.TensorProduct.one_def]
  | succ k ih => rw [pow_succ, Det.unopS_mul, ih, pow_succ']

private theorem unopS_aeval (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] Eᵐᵒᵖ) (p : Polynomial S) :
    Det.unopS A E S (Polynomial.aeval y p) = Polynomial.aeval (Det.unopS A E S y) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | monomial k s =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, unopS_pow]

private theorem unopS_gen {k : ℕ} (x : Fin k → Eᵐᵒᵖ) :
    Det.unopS A E _ (Det.gen (A := A) x) = Det.gen (A := A) fun a => (x a).unop := by
  unfold Det.gen

  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => unopS_tmul _ _ _

private theorem lid_unopS (S : Type) [CommRing S] [Algebra A S] (f : S →ₗ[A] A) (y : S ⊗[A] Eᵐᵒᵖ) :
    (TensorProduct.lid A Eᵐᵒᵖ (f.rTensor Eᵐᵒᵖ y)).unop =
      TensorProduct.lid A E (f.rTensor E (Det.unopS A E S y)) := by
  induction y with
  | add a b ha hb => simp only [map_add (f := _), MulOpposite.unop_add, ha, hb]
  | tmul s a => simp [unopS_tmul]

private theorem op_chElt (D : Det n A E) {k : ℕ} (x : Fin k → Eᵐᵒᵖ) (α : Fin k →₀ ℕ) :
    (D.op.chElt x α).unop = D.chElt (fun a => (x a).unop) α := by
  unfold Det.chElt
  rw [lid_unopS, unopS_aeval, op_chiS, unopS_gen]

private theorem unop_mem_CH (D : Det n A E) {x : Eᵐᵒᵖ} (h : x ∈ D.op.CH) : x.unop ∈ D.CH := by
  unfold Det.CH at h
  induction h using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨k, y, α, rfl⟩ := hx
    exact TwoSidedIdeal.subset_span ⟨k, _, α, op_chElt D y α⟩
  | zero => exact D.CH.zero_mem
  | add x y _ _ hx hy => exact D.CH.add_mem hx hy
  | neg x _ hx => exact D.CH.neg_mem hx
  | left_absorb a x _ hx => exact D.CH.mul_mem_right _ _ hx
  | right_absorb b x _ hx => exact D.CH.mul_mem_left _ _ hx

private theorem op_mem_CH (D : Det n A E) {x : E} (h : x ∈ D.CH) : MulOpposite.op x ∈ D.op.CH := by
  unfold Det.CH at h
  induction h using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨k, y, α, rfl⟩ := hx
    exact TwoSidedIdeal.subset_span ⟨k, fun a => MulOpposite.op (y a), α,
      (congrArg MulOpposite.op (op_chElt D (fun a => MulOpposite.op (y a)) α)).symm⟩
  | zero => exact D.op.CH.zero_mem
  | add x y _ _ hx hy => exact D.op.CH.add_mem hx hy
  | neg x _ hx => exact D.op.CH.neg_mem hx
  | left_absorb a x _ hx => exact D.op.CH.mul_mem_right _ _ hx
  | right_absorb b x _ hx => exact D.op.CH.mul_mem_left _ _ hx

end SlopeTestRemainingChoices

theorem UpperTheory.V.CA.d_op :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E), (∀ x, D.op.chi (MulOpposite.op x) = D.chi x) ∧ (∀ x, MulOpposite.op x ∈ D.op.ker ↔ x ∈ D.ker) ∧ ∀ x, MulOpposite.op x ∈ D.op.CH ↔ x ∈ D.CH := by
  intro n A E _ _ _ D
  refine ⟨fun x => ?_, fun x => ?_, fun x => ⟨fun h => unop_mem_CH D h, op_mem_CH D⟩⟩
  · unfold Det.chi
    rw [op_D, map_sub, unopS_tmul, unopS_tmul, MulOpposite.unop_one, MulOpposite.unop_op]
  · rw [Det.mem_ker, Det.mem_ker]
    constructor
    · intro h S _ _ y u v
      obtain ⟨y, rfl⟩ := unopS_surj S y
      obtain ⟨u, rfl⟩ := unopS_surj S u
      obtain ⟨v, rfl⟩ := unopS_surj S v
      have := h S y v u
      rw [op_D, op_D, map_add (f := _), Det.unopS_mul, Det.unopS_mul, unopS_tmul, MulOpposite.unop_op, ← mul_assoc] at this
      exact this
    · intro h S _ _ y u v
      rw [op_D, op_D, map_add (f := _), Det.unopS_mul, Det.unopS_mul, unopS_tmul, MulOpposite.unop_op, ← mul_assoc]
      exact h S _ _ _
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_ker_ss :
    ∀ {n : ℕ} {k E ι : Type} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E] [Fintype ι] [DecidableEq ι] (h : Fintype.card ι = n) (r : E →ₐ[k] Matrix ι ι k), IsSemisimpleRing r.range → ∀ x, x ∈ (Det.ofRep h r).ker ↔ r x = 0 := by
  intro n k E ι _ _ _ _ _ _ h r hss x
  rw [Det.mem_ker]
  constructor
  · intro hx
    obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent
      (Ideal.span {(⟨r x, x, rfl⟩ : r.range)})
    have h1 : e ∈ Ideal.span {(⟨r x, x, rfl⟩ : r.range)} := hI ▸ Ideal.subset_span rfl
    have h2 : (⟨r x, x, rfl⟩ : r.range) ∈ Ideal.span {e} := hI ▸ Ideal.subset_span rfl
    obtain ⟨⟨a, u, rfl⟩, ha⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h2
    have ha' : r u * r x = (e : Matrix ι ι k) := congrArg Subtype.val ha
    have hb' : (b : Matrix ι ι k) * (e : Matrix ι ι k) = r x := congrArg Subtype.val hb
    have he' : (e : Matrix ι ι k) * e = e := congrArg Subtype.val he
    have h3 : (Det.repS r k (1 + (1 ⊗ₜ (-u)) * (1 ⊗ₜ x) * 1)).det = (Det.repS r k 1).det :=
      hx k 1 (1 ⊗ₜ (-u)) 1
    have h4 : Det.repS r k (1 + (1 ⊗ₜ (-u)) * (1 ⊗ₜ x) * 1) = 1 - (e : Matrix ι ι k) := by
      rw [map_add (f := _), map_mul, map_mul, map_one, Det.repS_tmul, Det.repS_tmul, ← ha']
      simp [sub_eq_add_neg]
    rw [h4, map_one, Matrix.det_one] at h3
    have h5 : IsUnit (1 - (e : Matrix ι ι k)) := by
      rw [Matrix.isUnit_iff_isUnit_det, h3]; exact isUnit_one
    have h6 : (e : Matrix ι ι k) = 0 := by
      apply h5.mul_left_cancel
      rw [sub_mul, one_mul, he', sub_self, mul_zero]
    rw [← hb', h6, mul_zero]
  · intro hx S _ _ y u v
    show (Det.repS r S (y + u * (1 ⊗ₜ x) * v)).det = (Det.repS r S y).det
    rw [map_add (f := _), map_mul, map_mul, Det.repS_tmul, hx]
    simp
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem chiS_ofRep {n : ℕ} {A E ι : Type} [CommRing A] [Ring E] [Algebra A E] [Fintype ι] [DecidableEq ι]
    (h : Fintype.card ι = n) (r : E →ₐ[A] Matrix ι ι A) (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E) :
    (Det.ofRep h r).chiS S y = (Det.repS r S y).charpoly := by
  have h1 : Det.repS r (Polynomial S)
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S (Polynomial S)) (AlgHom.id A E) y) =
      (Det.repS r S y).map Polynomial.C := by
    induction y with
    | tmul s z =>
      ext1 a b
      simp [Det.repS_tmul, Polynomial.single_eq_monomial]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), Matrix.map_add _ (map_add _)]
  change (Det.repS r (Polynomial S) _).det = _
  rw [map_sub, h1, Det.repS_tmul, Matrix.charpoly, Matrix.charmatrix]
  congr 2
  ext1 a b
  by_cases hab : a = b <;>
    simp [hab, Matrix.one_apply, Matrix.diagonal_apply, Polynomial.single_eq_monomial]

private theorem chi_ofRep {n : ℕ} {A E ι : Type} [CommRing A] [Ring E] [Algebra A E] [Fintype ι] [DecidableEq ι]
    (h : Fintype.card ι = n) (r : E →ₐ[A] Matrix ι ι A) (x : E) :
    (Det.ofRep h r).chi x = (r x).charpoly := by
  change (Det.repS r (Polynomial A) _).det = _
  rw [map_sub, Det.repS_tmul, Det.repS_tmul, Matrix.charpoly, Matrix.charmatrix]
  congr 2
  · ext1 a b
    by_cases hab : a = b <;> simp [hab, Matrix.one_apply, Matrix.diagonal_apply]
  · ext1 a b
    simp

private theorem coeff_repS {σ A E ι : Type} [CommRing A] [Ring E] [Algebra A E] [Fintype ι] [DecidableEq ι]
    (r : E →ₐ[A] Matrix ι ι A) (α : σ →₀ ℕ) (z : MvPolynomial σ A ⊗[A] E) :
    r (TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E z)) =
      (Det.repS r (MvPolynomial σ A) z).map (AddMonoidAlgebra.coeff · α) := by
  induction z with
  | tmul s z =>
    ext a b
    simp only [Det.repS_tmul, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, MvPolynomial.algebraMap_eq]
    rw [mul_comm s, MvPolynomial.coeff_C_mul]
    simp [mul_comm]
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), Matrix.map_add _ (MvPolynomial.coeff_add α)]

theorem UpperTheory.V.CA.d_ofRep :
    ∀ {n : ℕ} {A E ι : Type} [CommRing A] [Ring E] [Algebra A E] [Fintype ι] [DecidableEq ι] (h : Fintype.card ι = n) (r : E →ₐ[A] Matrix ι ι A) (x : E), (Det.ofRep h r).chi x = (r x).charpoly ∧ (Det.ofRep h r).val x = (r x).det ∧ (1 ≤ n → (Det.ofRep h r).tr x = (r x).trace) ∧ (x ∈ (Det.ofRep h r).CH → r x = 0) := by
  intro n A E ι _ _ _ _ _ h r x
  refine ⟨chi_ofRep h r x, ?_, fun hn => ?_, fun hx => ?_⟩
  · change (Det.repS r A (1 ⊗ₜ x)).det = _
    rw [Det.repS_tmul]
    simp
  · haveI : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    rw [Det.tr, Det.lam, chi_ofRep, Matrix.trace_eq_neg_charpoly_coeff, h]
    simp
  · have hle : (Det.ofRep h r).CH ≤ TwoSidedIdeal.ker r := by
      rw [Det.CH, TwoSidedIdeal.span_le]
      rintro z ⟨k, y, α, rfl⟩
      change _ ∈ TwoSidedIdeal.ker r
      rw [TwoSidedIdeal.mem_ker, Det.chElt, coeff_repS, chiS_ofRep, ← Polynomial.aeval_algHom_apply,
        Matrix.aeval_self_charpoly]
      ext a b
      simp
    exact (TwoSidedIdeal.mem_ker r).1 (hle hx)
end
