module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle067
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Ideal.GoingUp
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim

@[expose] public section

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem determinant_evaluation_aeval {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E)
    (B : Type) [CommRing B] [Algebra A B] (b : B) :
    D.D B (1 + (b - 1) ⊗ₜ e) = aeval b (D.D A[X] (1 + (X - 1) ⊗ₜ e)) := by
  rw [← D.nat]
  congr 1
  simp

private theorem coeff_aeval_C_mul_X' {A : Type} [CommRing A] (P : A[X]) (a : A[X]) (j : ℕ) :
    (aeval (Polynomial.C a * Polynomial.X : A[X][X]) P).coeff j = Polynomial.C (P.coeff j) * a ^ j := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, map_add (f := _), add_mul]
  | monomial i c =>
    have e1 : aeval (Polynomial.C a * Polynomial.X : A[X][X]) (monomial i c) =
        Polynomial.C (Polynomial.C c * a ^ i) * Polynomial.X ^ i := by
      rw [aeval_monomial, mul_pow, ← Polynomial.C_pow, Polynomial.algebraMap_apply, Polynomial.algebraMap_apply]
      simp [mul_assoc]
    rw [e1, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_monomial]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]

private theorem aeval_C_X_eq_C {A : Type} [CommRing A] (P : A[X]) :
    aeval (Polynomial.C (X : A[X]) : A[X][X]) P = Polynomial.C P := by
  have := Polynomial.aeval_algHom_apply (Polynomial.CAlgHom (R := A) (A := A[X])) (X : A[X]) P
  simpa [Polynomial.aeval_X_left_apply] using this

private theorem pow_aux {n : ℕ} {A E : Type} [CommRing A] [IsLocalRing A] [Ring E] [Algebra A E]
    (D : Det n A E) (e : E) (he : IsIdempotentElem e) :
    ∃ r, D.D A[X] (1 + (X - 1) ⊗ₜ e) = X ^ r := by
  set P := D.D A[X] (1 + (X - 1) ⊗ₜ e) with hP
  have ev : ∀ (B : Type) [CommRing B] [Algebra A B] (b : B), aeval b P = D.D B (1 + (b - 1) ⊗ₜ e) :=
    fun B _ _ b => (determinant_evaluation_aeval D e B b).symm
  have mul : ∀ (B : Type) [CommRing B] [Algebra A B] (s t : B), aeval (s * t) P = aeval s P * aeval t P := by
    intro B _ _ s t
    rw [ev, ev, ev, ← map_mul]
    congr 1
    have key : ∀ u v : B, (1 + u ⊗ₜ[A] e : B ⊗[A] E) * (1 + v ⊗ₜ[A] e) = 1 + (u + v + u * v) ⊗ₜ[A] e := by
      intro u v
      simp only [mul_add, add_mul, one_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul, he.eq, add_tmul]
      abel
    rw [key]
    congr 2
    ring
  have hcoef : ∀ j, Polynomial.C (P.coeff j) * X ^ j = P * Polynomial.C (P.coeff j) := by
    intro j
    have hm := mul A[X][X] (Polynomial.C X) Polynomial.X
    have h1 : (Polynomial.X : A[X][X]) = Polynomial.C 1 * Polynomial.X := by simp
    have cj := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q j) hm
    rw [coeff_aeval_C_mul_X', aeval_C_X_eq_C, Polynomial.coeff_C_mul, h1, coeff_aeval_C_mul_X', one_pow, mul_one] at cj
    exact cj
  have h1 : P.eval 1 = 1 := by
    have := ev A 1
    rw [sub_self, zero_tmul, add_zero, map_one] at this
    rw [← Polynomial.coe_aeval_eq_eval]
    exact this
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (P.coeff j) := by
    by_contra hcon
    push_neg at hcon
    have hmem : P.eval 1 ∈ maximalIdeal A := by
      rw [Polynomial.eval_eq_sum_range]
      refine Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_right _ _ ?_)
      exact (mem_maximalIdeal _).2 (hcon i)
    rw [h1] at hmem
    exact (mem_maximalIdeal _).1 hmem isUnit_one
  refine ⟨j, ?_⟩
  have hu : IsUnit (Polynomial.C (P.coeff j)) := hj.map Polynomial.C
  apply hu.mul_left_cancel
  rw [hcoef j, mul_comm]

theorem UpperTheory.V.CA.d_idem_rank :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [IsLocalRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E), IsIdempotentElem e → ∃ r ≤ n, D.D A[X] (1 + X ⊗ₜ e) = (1 + X) ^ r := by
  intro n A E _ _ _ _ D e he
  obtain ⟨r, hr⟩ := pow_aux D e he
  obtain ⟨r', hr'⟩ := pow_aux D (1 - e) he.one_sub
  refine ⟨r, ?_, ?_⟩
  · have hz : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
    have step : ∀ a : A[X], (1 + a ⊗ₜ[A] (1 - e) : A[X] ⊗[A] E) * (1 + a ⊗ₜ[A] e) = 1 + a ⊗ₜ[A] (1 : E) := by
      intro a
      rw [mul_add, add_mul, add_mul, one_mul, one_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul, hz,
        tmul_zero, add_zero, add_assoc, ← tmul_add, sub_add_cancel]
    have key : (1 + (X - 1) ⊗ₜ[A] (1 - e) : A[X] ⊗[A] E) * (1 + (X - 1) ⊗ₜ[A] e) =
        (X : A[X]) • (1 : A[X] ⊗[A] E) := by
      rw [step, Algebra.TensorProduct.one_def, ← add_tmul, add_sub_cancel, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one]
    have h2 := congrArg (D.D A[X]) key
    rw [map_mul, hr, hr', D.homog, map_one, mul_one, ← pow_add] at h2
    have h3 := congrArg Polynomial.natDegree h2
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at h3
    omega
  · have h4 := determinant_evaluation_aeval D e A[X] (1 + X)
    have h5 : (1 + X : A[X]) - 1 = X := by ring
    rw [h5, hr, map_pow, aeval_X] at h4
    exact h4
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_comm :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (S : Type) [CommRing S] [Algebra A S] (x y : S ⊗[A] E), D.D S (1 + x * y) = D.D S (1 + y * x) := by
  intro n A E _ _ _ D S _ _ x y
  let i : S →ₐ[A] S[X] := IsScalarTower.toAlgHom A S S[X]
  let ι := Algebra.TensorProduct.map i (AlgHom.id A E)
  let ev : S → (S[X] →ₐ[A] S) := fun c => (Polynomial.aeval c : S[X] →ₐ[S] S).restrictScalars A
  let π := fun c => Algebra.TensorProduct.map (ev c) (AlgHom.id A E)
  have hπι : ∀ c z, π c (ι z) = z := by
    intro c z
    induction z with
    | tmul s e => simp [π, ι, ev, i]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  let t : S[X] ⊗[A] E := X ⊗ₜ 1
  have ht : ∀ c, π c t = c ⊗ₜ 1 := by
    intro c
    simp [π, t, ev]
  let u : S[X] ⊗[A] E := 1 + t * ι (x - 1)
  have hu0 : π 0 u = 1 := by
    simp only [u, map_add (f := _), map_mul, map_one, hπι, ht]
    simp
  have hu1 : π 1 u = x := by
    simp only [u, map_add (f := _), map_mul, map_one, hπι, ht]
    rw [← Algebra.TensorProduct.one_def]
    simp
  have hc : (D.D S[X] u).coeff 0 = 1 := by
    have h := D.nat S[X] S (ev 0) u
    change D.D S (π 0 u) = _ at h
    rw [hu0, map_one] at h
    rw [h]
    simp [ev, Polynomial.coeff_zero_eq_eval_zero]
  have hnz : D.D S[X] u ∈ nonZeroDivisors S[X] :=
    Polynomial.mem_nonzeroDivisors_of_coeff_mem 0 (by rw [hc]; exact one_mem _)
  have key : D.D S[X] (1 + u * ι y) = D.D S[X] (1 + ι y * u) := by
    have h : (1 + u * ι y) * u = u * (1 + ι y * u) := by noncomm_ring
    have h2 := congrArg (D.D S[X]) h
    rw [map_mul, map_mul, mul_comm (D.D S[X] u)] at h2
    exact (mul_cancel_right_mem_nonZeroDivisors hnz).1 h2
  have h := congrArg (ev 1) key
  rw [← D.nat, ← D.nat] at h
  change D.D S (π 1 _) = D.D S (π 1 _) at h
  simpa only [map_add (f := _), map_mul, map_one, hπι, hu1] using h
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem gdet_inst {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (B : Type) [CommRing B]
    (i j : Algebra A B) (h : ∀ a, @algebraMap A B _ _ i a = @algebraMap A B _ _ j a) (x : MonoidAlgebra B G) :
    @GDet.D n A G _ _ D B _ i x = @GDet.D n A G _ _ D B _ j x := by
  have : i = j := Algebra.algebra_ext _ _ h
  subst this
  rfl

private theorem gdet_chi {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {B : Type} [CommRing B] (f : A →+* B) (y : MonoidAlgebra A G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f := by
  letI : Algebra A B[X] := ((algebraMap B B[X]).comp f).toAlgebra
  let φ : A[X] →ₐ[A] B[X] :=
    { Polynomial.mapRingHom f with
      commutes' := fun a => by
        change Polynomial.map f (C a) = C (f a)
        exact Polynomial.map_C f }
  have h := D.nat A[X] B[X] φ (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
  refine Eq.trans ?_ h
  change D.D B[X] _ = D.D B[X] _
  congr 1
  have hφ : (φ : A[X] →+* B[X]) = Polynomial.mapRingHom f := rfl
  rw [hφ]
  ext g : 2
  simp

theorem UpperTheory.V.CA.d_gmap :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G), D.map (RingHom.id A) = D ∧ (∀ {B C : Type} [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C), (D.map f).map g = D.map (g.comp f)) ∧ (∀ {B : Type} [CommRing B] (f : A →+* B) (y : MonoidAlgebra A G), (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f ∧ ∀ i, (D.map f).lam i (MonoidAlgebra.mapRingHom G f y) = f (D.lam i y)) ∧ ∀ {B : Type} [CommRing B] (f : A →+* B) (ρ : G →* Matrix (Fin n) (Fin n) A), (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  intro n A G _ _ D
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact GDet.ext fun B _ j x =>
      gdet_inst D B ((algebraMap A B).comp (RingHom.id A)).toAlgebra j (fun _ => rfl) x
  · intro B C _ _ f g
    exact GDet.ext fun S _ _ x => gdet_inst D S _ _ (fun _ => rfl) x
  · intro B _ f y
    refine ⟨gdet_chi D f y, fun i => ?_⟩
    simp only [GDet.lam, gdet_chi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]
  · intro B _ f ρ
    refine GDet.ext fun S _ _ x => ?_
    letI : Algebra A S := ((algebraMap B S).comp f).toAlgebra
    change (GDet.repAlg ρ S x).det = (GDet.repAlg (f.mapMatrix.toMonoidHom.comp ρ) S x).det
    congr 2
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem aeval_mul_homog {n : ℕ} {A G S : Type} [CommRing A] [CommRing S] [Algebra A S]
    {P : MvPolynomial G A} (hP : P.IsHomogeneous n) (b : S) (x : G → S) :
    MvPolynomial.aeval (fun g => b * x g) P = b ^ n * MvPolynomial.aeval x P :=
  _root_.UpperTheory.Reformulated.B.Qk4.aeval_mul_homog hP b x

theorem UpperTheory.V.CA.u_poly :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [Fintype G] [DecidableEq G] (P : MvPolynomial G A), P.IsHomogeneous n → MvPolynomial.eval (Pi.single 1 1) P = 1 → MvPolynomial.aeval (fun g : G => ∑ a : G, (MvPolynomial.X (Sum.inl a) * MvPolynomial.X (Sum.inr (a⁻¹ * g)) : MvPolynomial (G ⊕ G) A)) P = MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr P → ∃ D : GDet n A G, ∀ (S : Type) [CommRing S] [Algebra A S] (y : MonoidAlgebra S G), D.D S y = MvPolynomial.aeval (fun g => y.coeff g) P := by
  intro n A G _ _ _ _ P hP h1 hm
  refine ⟨⟨fun S _ _ => ⟨⟨fun y => MvPolynomial.aeval (fun g => y.coeff g) P, ?_⟩, ?_⟩, ?_, ?_⟩, fun S _ _ y => rfl⟩
  · have h : (fun g => (1 : MonoidAlgebra S G).coeff g) =
        fun g => Algebra.ofId A S ((Pi.single 1 1 : G → A) g) := by
      funext g
      by_cases hg : g = 1
      · subst hg; simp [MonoidAlgebra.one_def]
      · simp [MonoidAlgebra.one_def, hg]
    rw [h, ← MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_eq_eval, h1, map_one]
  · intro x y
    have h := congrArg (MvPolynomial.aeval (R := A) (Sum.elim (fun g => x.coeff g) (fun g => y.coeff g))) hm
    rw [map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_rename, MvPolynomial.comp_aeval_apply] at h
    refine Eq.trans ?_ h
    change MvPolynomial.aeval _ P = _
    congr 2
    funext g
    rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype] <;> simp
  · intro S T _ _ _ _ f x
    change MvPolynomial.aeval _ P = f (MvPolynomial.aeval _ P)
    rw [MvPolynomial.comp_aeval_apply]
    congr 2
  · intro S _ _ b x
    change MvPolynomial.aeval _ P = b ^ n * (MvPolynomial.aeval _ P)
    rw [← aeval_mul_homog hP]
    congr 2
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

theorem UpperTheory.V.CA.inj_dim :
    ∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (d : ℕ), ringKrullDim A = d → ringKrullDim B = d → Function.Injective (algebraMap A B) := by
  intro A B _ _ _ _ _ d hA hB
  by_contra hni
  obtain ⟨r, hr, hr0⟩ : ∃ r : A, algebraMap A B r = 0 ∧ r ≠ 0 := by
    rw [injective_iff_map_eq_zero] at hni
    push_neg at hni
    exact hni
  have hrz : r ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero hr0
  let g : (A ⧸ Ideal.span {r}) →+* B := Ideal.Quotient.lift (Ideal.span {r}) (algebraMap A B) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hr, mul_zero])
  letI : Algebra (A ⧸ Ideal.span {r}) B := g.toAlgebra
  haveI : Algebra.IsIntegral (A ⧸ Ideal.span {r}) B := by
    refine ⟨fun b => ?_⟩
    obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := A) b
    refine ⟨p.map (Ideal.Quotient.mk _), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.algebraMap_toAlgebra, Ideal.Quotient.lift_comp_mk]
    exact hpb
  have h1 : ringKrullDim B ≤ ringKrullDim (A ⧸ Ideal.span {r}) :=
    Order.krullDim_le_of_strictMono
      (fun P => (⟨Ideal.comap (algebraMap (A ⧸ Ideal.span {r}) B) P.asIdeal, inferInstance⟩ :
        PrimeSpectrum _))
      (fun P Q h => Ideal.IsIntegral.comap_lt_comap h)
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hrz
  rw [hA] at h2
  rw [hB] at h1
  have h3 : ((d : WithBot ℕ∞) + 1) ≤ d := le_trans (add_le_add_left h1 1) h2
  norm_cast at h3
  omega
end
