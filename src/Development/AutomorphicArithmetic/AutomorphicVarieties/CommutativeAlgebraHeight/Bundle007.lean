module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
public import Mathlib.LinearAlgebra.Matrix.Swap
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
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.RingTheory.MatrixAlgebra
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section SlopeTestRemainingChoices

variable {n : ℕ} {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
  (F : ∀ (S : Type) [CommRing S] [Algebra k S], Matrix ι ι S →* S)
  (nat : ∀ (S T : Type) [CommRing S] [Algebra k S] [CommRing T] [Algebra k T] (f : S →ₐ[k] T) (M : Matrix ι ι S),
    F T (M.map f) = f (F S M))
  (hom : ∀ (S : Type) [CommRing S] [Algebra k S] (b : S) (M : Matrix ι ι S), F S (b • M) = b ^ n * F S M)

include nat in
private theorem dm_transv (S : Type) [CommRing S] [Algebra k S] {i j : ι} (hij : i ≠ j) (s : S) :
    F S (Matrix.transvection i j s) = 1 := by
  have hm : ∀ (S : Type) [CommRing S] [Algebra k S] (s : S),
      F S (Matrix.transvection i j s) = aeval s (F k[X] (Matrix.transvection i j X)) := by
    intro S _ _ s
    rw [← nat]
    congr 1
    ext a b
    simp only [Matrix.transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, map_add (f := _)]
    split_ifs <;> simp
  have hu : IsUnit (F k[X] (Matrix.transvection i j X)) := by
    refine IsUnit.of_mul_eq_one (F k[X] (Matrix.transvection i j (-X))) ?_
    rw [← map_mul, Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel, Matrix.transvection_zero, map_one]
  obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.1 hu
  have h0 := hm k 0
  rw [Matrix.transvection_zero, map_one, ← hc] at h0
  rw [hm, ← hc]
  simp at h0
  simp [← h0]

private theorem dm_diag_prod (S : Type) [CommRing S] [Algebra k S] (d : ι → S) :
    F S (Matrix.diagonal d) = ∏ i, F S (Matrix.diagonal (Pi.mulSingle i (d i))) := by
  have := map_prod ((F S).comp (Matrix.diagonalRingHom ι S).toMonoidHom) (fun i => Pi.mulSingle i (d i)) Finset.univ
  rw [Finset.univ_prod_mulSingle] at this
  exact this

include nat in
private theorem dm_single (S : Type) [CommRing S] [Algebra k S] (i : ι) (s : S) :
    F S (Matrix.diagonal (Pi.mulSingle i s)) = aeval s (F k[X] (Matrix.diagonal (Pi.mulSingle i X))) := by
  rw [← nat]
  congr 1
  ext a b
  simp only [Matrix.map_apply, Matrix.diagonal_apply, Pi.mulSingle_apply]
  split_ifs <;> simp

private theorem dm_swap (S : Type) [CommRing S] [Algebra k S] (i j : ι) (s : S) :
    F S (Matrix.diagonal (Pi.mulSingle i s)) = F S (Matrix.diagonal (Pi.mulSingle j s)) := by
  have h : Matrix.swap S i j * Matrix.diagonal (Pi.mulSingle i s) * Matrix.swap S i j =
      Matrix.diagonal (Pi.mulSingle j s) := by
    simp only [Matrix.swap, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, Pi.mulSingle_apply, id, Equiv.symm_swap,
      EmbeddingLike.apply_eq_iff_eq, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  rw [← h, map_mul, map_mul, mul_right_comm, ← map_mul, Matrix.swap_mul_self, map_one, one_mul]

include hom in
private theorem dm_X : ∏ i : ι, F k[X] (Matrix.diagonal (Pi.mulSingle i X)) = X ^ n := by
  have := hom k[X] X 1
  rw [map_one, mul_one, Matrix.smul_one_eq_diagonal, dm_diag_prod] at this
  exact this

include nat hom in
private theorem dm_diag [Nonempty ι] : ∃ m, n = m * Fintype.card ι ∧
    ∀ (S : Type) [CommRing S] [Algebra k S] (d : ι → S), F S (Matrix.diagonal d) = (Matrix.diagonal d).det ^ m := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have h := dm_X F hom
  have hd : F k[X] (Matrix.diagonal (Pi.mulSingle i₀ X)) ∣ X ^ n := h ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ i₀)
  obtain ⟨m, -, u, hu⟩ := (dvd_prime_pow Polynomial.prime_X n).1 hd
  obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.1 u.isUnit
  have h1 := dm_single F nat k i₀ 1
  rw [Pi.mulSingle_one, show (1 : ι → k) = fun _ => 1 from rfl, Matrix.diagonal_one, map_one] at h1
  have h2 := congrArg (aeval (1 : k)) hu
  rw [map_mul, ← h1, ← hc] at h2
  have hc1 : c = 1 := by simpa using h2
  rw [← hc, hc1, map_one, mul_one] at hu
  have hall : ∀ i : ι, F k[X] (Matrix.diagonal (Pi.mulSingle i X)) = X ^ m := fun i => (dm_swap F _ i i₀ _).trans hu
  refine ⟨m, ?_, fun S _ _ d => ?_⟩
  · simp only [hall, Finset.prod_const, Finset.card_univ, ← pow_mul] at h
    have := congrArg natDegree h
    simpa using this.symm
  · rw [dm_diag_prod, Matrix.det_diagonal, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [dm_single F nat, hall]
    simp

include nat hom in
private theorem dm_main [Nonempty ι] : ∃ m, n = m * Fintype.card ι ∧
    ∀ (S : Type) [CommRing S] [Algebra k S] (M : Matrix ι ι S), F S M = M.det ^ m := by
  obtain ⟨m, hm, hd⟩ := dm_diag F nat hom
  refine ⟨m, hm, fun S _ _ M => ?_⟩
  have hK : ∀ (K : Type) [Field K] [Algebra k K] (M : Matrix ι ι K), F K M = M.det ^ m := by
    intro K _ _ M
    refine Matrix.diagonal_transvection_induction (fun M => F K M = M.det ^ m) M (fun d _ => hd K d)
      (fun t => ?_) (fun A B hA hB => ?_)
    · rw [t.det, one_pow]
      exact dm_transv F nat K t.hij t.c
    · rw [map_mul, hA, hB, Matrix.det_mul, mul_pow]
  let R := MvPolynomial (ι × ι) k
  let G : Matrix ι ι R := Matrix.of fun i j => MvPolynomial.X (i, j)
  have hG : F R G = G.det ^ m := by
    apply IsFractionRing.injective R (FractionRing R)
    have := nat R (FractionRing R) (IsScalarTower.toAlgHom k R (FractionRing R)) G
    rw [hK] at this
    rw [map_pow, RingHom.map_det]
    exact this.symm
  have h := nat R S (MvPolynomial.aeval fun p => M p.1 p.2) G
  rw [hG, map_pow, AlgHom.map_det] at h
  have hM : G.map (MvPolynomial.aeval fun p : ι × ι => M p.1 p.2 : R →ₐ[k] S) = M := by
    ext a b
    simp [G, R]
  rw [AlgHom.mapMatrix_apply, hM] at h
  exact h

private theorem dm_rep (S : Type) [CommRing S] [Algebra k S] (y : S ⊗[k] Matrix ι ι k) :
    matrixEquivTensor ι k S (Det.repS (AlgHom.id k _) S y) = y := by
  rw [← AlgEquiv.eq_symm_apply]
  induction y with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul s x =>
    rw [Det.repS_tmul, matrixEquivTensor_apply_symm]
    ext a b
    simp

end SlopeTestRemainingChoices

theorem UpperTheory.V.CA.d_matrix :
    ∀ {n d : ℕ} {k : Type} [Field k] (D : Det n k (Matrix (Fin (d + 1)) (Fin (d + 1)) k)), ∃ m, n = m * (d + 1) ∧ ∀ (S : Type) [CommRing S] [Algebra k S] (y : S ⊗[k] Matrix (Fin (d + 1)) (Fin (d + 1)) k), D.D S y = (Det.repS (AlgHom.id k _) S y).det ^ m := by
  intro n d k _ D
  obtain ⟨m, hm, h⟩ := dm_main (n := n) (k := k) (ι := Fin (d + 1))
    (fun S _ _ => (D.D S).comp (matrixEquivTensor (Fin (d + 1)) k S).toAlgHom.toMonoidHom)
    (fun S T _ _ _ _ f M => by
      change D.D T (matrixEquivTensor _ k T (M.map f)) = f (D.D S (matrixEquivTensor _ k S M))
      rw [← D.nat]
      congr 1

      simp [matrixEquivTensor_apply, map_sum])
    (fun S _ _ b M => by
      change D.D S (matrixEquivTensor _ k S (b • M)) = b ^ n * D.D S (matrixEquivTensor _ k S M)
      rw [← D.homog]
      congr 1
      simp [matrixEquivTensor_apply, Finset.smul_sum, smul_tmul'])
  refine ⟨m, by simpa using hm, fun S _ _ y => ?_⟩
  rw [← h]
  exact congrArg (D.D S) (dm_rep S y).symm
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private noncomputable def piB {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ)
    (B : Type) [CommRing B] [Algebra k B] : MonoidAlgebra B G →ₐ[B] (Fin n → B) :=
  MonoidAlgebra.lift B (Fin n → B) G
    { toFun := fun g i => algebraMap k B (χ i g)
      map_one' := by ext i; simp
      map_mul' := fun g h => by ext i; simp }

private theorem piB_single {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ)
    (B : Type) [CommRing B] [Algebra k B] (g : G) (b : B) (i : Fin n) :
    piB χ B (MonoidAlgebra.single g b) i = b * algebraMap k B (χ i g) := by
  simp [piB]

private theorem piB_map {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ)
    (B : Type) [CommRing B] [Algebra k B] (y : MonoidAlgebra k G) (i : Fin n) :
    piB χ B (MonoidAlgebra.mapRingHom G (algebraMap k B) y) i = algebraMap k B (piB χ k y i) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]
  | single g r => rw [MonoidAlgebra.mapRingHom_single, piB_single, piB_single]; simp

private theorem D_eq {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ)
    (B : Type) [CommRing B] [Algebra k B] (x : MonoidAlgebra B G) :
    (GDet.ofChars χ).D B x = ∏ i, piB χ B x i := by
  change (GDet.repAlg (GDet.diagRep χ) B x).det = _
  rw [← Matrix.det_diagonal]
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [Pi.zero_def]
  | add a b ha hb => simp only [map_add (f := _), ha, hb, Matrix.diagonal_add]; rfl
  | single g r =>
    ext i j
    by_cases h : i = j
    · subst h; simp [GDet.repAlg, GDet.diagRep, piB_single]
    · simp [GDet.repAlg, GDet.diagRep, Matrix.diagonal_apply_ne _ h]

theorem UpperTheory.V.CA.f_chars :
    ∀ {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ), Function.Injective χ → ∃ π : MonoidAlgebra k G →ₐ[k] (Fin n → k), Function.Surjective π ∧ (∀ g i, π (MonoidAlgebra.single g 1) i = χ i g) ∧ (∀ y, (GDet.ofChars χ).Kills y ↔ π y = 0) ∧ ∀ y, (GDet.ofChars χ).chi y = ∏ i, (X - C (π y i)) := by
  intro n k G _ _ χ hχ
  have hs : ∀ g i, piB χ k (MonoidAlgebra.single g 1) i = χ i g := fun g i => by simp [piB_single]
  have hsurj : Function.Surjective (piB χ k) := by
    have hinj : Function.Injective fun i => (Units.coeHom k).comp (χ i) := fun i j h =>
      hχ (MonoidHom.ext fun g => Units.ext (DFunLike.congr_fun h g))
    have hli : LinearIndependent k fun i (g : G) => (χ i g : k) :=
      (linearIndependent_monoidHom G k).comp _ hinj
    have hsp := span_flip_eq_top_iff_linearIndependent.2 hli
    have : LinearMap.range (piB χ k).toLinearMap = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.single g 1, funext (hs g)⟩
    exact LinearMap.range_eq_top.1 this
  refine ⟨piB χ k, hsurj, hs, fun y => ⟨fun h => ?_, fun h B _ _ z => ?_⟩, fun y => ?_⟩
  · ext i
    by_contra hi
    obtain ⟨z, hz⟩ := hsurj fun _ => -(piB χ k y i)⁻¹
    have := h k z
    rw [D_eq, Finset.prod_eq_zero (Finset.mem_univ i)] at this
    · exact zero_ne_one this
    · rw [map_add (f := _), map_mul, map_one, Pi.add_apply, Pi.mul_apply, piB_map, hz]
      have hi' : piB χ k y i ≠ 0 := hi
      simp [hi']
  · rw [D_eq]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [map_add (f := _), map_mul, map_one, Pi.add_apply, Pi.mul_apply, piB_map, h]
    simp
  · unfold GDet.chi
    rw [D_eq]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_sub, Pi.sub_apply, piB_single]
    have := piB_map χ k[X] y i
    rw [Polynomial.algebraMap_eq] at this
    rw [this]
    simp
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_toDet_map :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (B : Type) [CommRing B] [Algebra A B], (D.map (algebraMap A B)).toDet = (D.toDet.baseChange B).pull (toT A G B) := by
  intro n A G _ _ D B _ _
  refine Det.ext' fun S _ _ x => ?_
  letI : Algebra A S := ((algebraMap B S).comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B S := .of_algebraMap_eq fun _ => rfl
  have h : ofT B G S x = ofT A G S (Det.cancel A (MonoidAlgebra A G) B S
      (Algebra.TensorProduct.map (AlgHom.id S S) (toT A G B) x)) := by
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul s y =>
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
      | single g b =>
        rw [Algebra.TensorProduct.map_tmul, toT_single, Det.cancel_tmul, ofT_tmul, ofT_tmul,
          MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single]
        simp
  exact congrArg (D.D S) h
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem bc_D {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type)
    [CommRing B] [Algebra A B] (S : Type) [CommRing S] [Algebra B S] [inst : Algebra A S] [h : IsScalarTower A B S]
    (y : S ⊗[B] (B ⊗[A] E)) : (D.baseChange B).D S y = D.D S (Det.cancel A E B S y) := by
  have e : inst = ((algebraMap B S).comp (algebraMap A B)).toAlgebra :=
    Algebra.algebra_ext _ _ fun a => IsScalarTower.algebraMap_apply A B S a
  subst e
  rfl

private theorem cancel_one {A E : Type} [CommRing A] [Ring E] [Algebra A E] (B : Type)
    [CommRing B] [Algebra A B] (S : Type) [CommRing S] [Algebra B S] [Algebra A S] [IsScalarTower A B S]
    (y : B ⊗[A] E) : Det.cancel A E B S (1 ⊗ₜ y) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B S) (AlgHom.id A E) y := by
  induction y with
  | tmul b z => simp [Det.cancel_tmul]
  | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]

private theorem bc_chi {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type)
    [CommRing B] [Algebra A B] (y : B ⊗[A] E) : (D.baseChange B).chi y = D.chiS B y := by
  unfold Det.chi Det.chiS
  rw [bc_D, map_sub, cancel_one, Algebra.TensorProduct.one_def, Det.cancel_tmul, map_one, mul_one]

private theorem bc_chi_tmul {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type)
    [CommRing B] [Algebra A B] (x : E) : (D.baseChange B).chi (1 ⊗ₜ x) = (D.chi x).map (algebraMap A B) := by
  rw [bc_chi]
  have h := D.nat A[X] B[X] (Polynomial.mapAlgHom (Algebra.ofId A B)) (X ⊗ₜ 1 - 1 ⊗ₜ x)
  unfold Det.chi Det.chiS
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    simp
  · rfl

theorem UpperTheory.V.CA.d_bc :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type) [CommRing B] [Algebra A B], (∀ (S : Type) [CommRing S] [Algebra B S] [Algebra A S] [IsScalarTower A B S] (y : S ⊗[B] (B ⊗[A] E)), (D.baseChange B).D S y = D.D S (Det.cancel A E B S y)) ∧ (∀ y, (D.baseChange B).val y = D.D B y) ∧ (∀ y, (D.baseChange B).chi y = D.chiS B y) ∧ ∀ x : E, (D.baseChange B).chi (1 ⊗ₜ x) = (D.chi x).map (algebraMap A B) ∧ ∀ i, (D.baseChange B).lam i (1 ⊗ₜ x) = algebraMap A B (D.lam i x) := by
  intro n A E _ _ _ D B _ _
  refine ⟨fun S _ _ _ _ y => bc_D D B S y, fun y => ?_, bc_chi D B, fun x => ⟨bc_chi_tmul D B x, fun i => ?_⟩⟩
  · change (D.baseChange B).D B (1 ⊗ₜ y) = _
    rw [bc_D, cancel_one]
    congr 1
    induction y with
    | tmul b z => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  · unfold Det.lam
    rw [bc_chi_tmul, Polynomial.coeff_map]
    simp
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_kills_poly :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E) (M : Set E), Submodule.span A M = ⊤ → (∀ (k : ℕ) (h : Fin k → E), (∀ a, h a ∈ M) → D.D (MvPolynomial (Fin k) A) (1 + Det.gen h * (1 ⊗ₜ x)) = 1) → D.Kills x := by
  intro n A E _ _ _ D x M hM H B _ _ h
  have key : ∀ e : E, ((1 : B) ⊗ₜ[A] e) ∈ Submodule.span B ((fun m : E => (1 : B) ⊗ₜ[A] m) '' M) := by
    intro e
    have he : e ∈ Submodule.span A M := hM ▸ Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [tmul_add]; exact add_mem ha hb
    | smul a y _ hy =>
      rw [tmul_smul, ← algebraMap_smul B]
      exact Submodule.smul_mem _ _ hy
  have hh : h ∈ Submodule.span B ((fun m : E => (1 : B) ⊗ₜ[A] m) '' M) := by
    induction h with
    | add a b ha hb => exact add_mem ha hb
    | tmul b e =>
      have : b ⊗ₜ[A] e = b • ((1 : B) ⊗ₜ[A] e) := by simp [smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (key e)
  obtain ⟨k, f, g, rfl⟩ := Submodule.mem_span_set'.1 hh
  choose m hm hmg using fun i => (g i).2
  have h1 := D.nat _ B (MvPolynomial.aeval f) (1 + Det.gen m * (1 ⊗ₜ x))
  rw [H k m hm, map_one] at h1
  refine Eq.trans (congrArg _ ?_) h1

  simp only [Det.gen, map_add (f := _), map_mul, map_one, map_sum, Algebra.TensorProduct.map_tmul, MvPolynomial.aeval_X,
  AlgHom.id_apply, ← hmg, smul_tmul', smul_eq_mul, mul_one]
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_poly_ext :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (D' : Det n A E) (M : Set E), Submodule.span A M = ⊤ → (∀ (k : ℕ) (x : Fin k → E), (∀ a, x a ∈ M) → D.poly x = D'.poly x) → D = D' := by
  intro n A E _ _ _ D D' M hM h
  refine Det.ext' fun S _ _ y => ?_
  have h1 : ∀ x : E, (1 : S) ⊗ₜ[A] x ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' M) := by
    intro x
    have hx : x ∈ Submodule.span A M := hM ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [tmul_add]; exact add_mem ha hb
    | smul a z _ hz => rw [tmul_smul]; exact Submodule.smul_of_tower_mem _ a hz
  have h2 : y ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' M) := by
    induction y with
    | add a b ha hb => exact add_mem ha hb
    | tmul s x =>
      have : s ⊗ₜ[A] x = s • ((1 : S) ⊗ₜ[A] x) := by simp [smul_tmul']
      rw [this]; exact Submodule.smul_mem _ s (h1 x)
  obtain ⟨k, s, g, rfl⟩ := Submodule.mem_span_set'.1 h2
  choose x hxM hx using fun a => (g a).2
  have h3 : ∑ a, s a • (g a : S ⊗[A] E) =
      Algebra.TensorProduct.map (MvPolynomial.aeval s) (AlgHom.id A E) (Det.gen x) := by

    simp only [Det.gen, map_sum, Algebra.TensorProduct.map_tmul, MvPolynomial.aeval_X, AlgHom.id_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hx a]; simp [smul_tmul']
  rw [h3, D.nat, D'.nat]
  exact congrArg _ (h k x hxM)
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem aeval_X_mul_C_X_monomial {A ι : Type} [CommRing A] (d : ι →₀ ℕ) (c : A) :
    MvPolynomial.aeval (fun a => (X * C (MvPolynomial.X a) : (MvPolynomial ι A)[X])) (MvPolynomial.monomial d c) =
      X ^ (Finsupp.degree d) * C (MvPolynomial.monomial d c) := by
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod,
    map_pow, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  rw [show Finsupp.degree d = ∑ i ∈ d.support, d i from rfl]
  ring

private theorem scale_coeff {A ι : Type} [CommRing A] (P : MvPolynomial ι A) (k : ℕ) :
    (MvPolynomial.aeval (fun a => (X * C (MvPolynomial.X a) : (MvPolynomial ι A)[X])) P).coeff k =
      MvPolynomial.homogeneousComponent k P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [aeval_X_mul_C_X_monomial, Polynomial.coeff_X_pow_mul',
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl), Polynomial.coeff_C]
    split_ifs <;> first | rfl | omega
  | add p q hp hq => rw [map_add (f := _), Polynomial.coeff_add, hp, hq, map_add (f := _)]

theorem UpperTheory.V.CA.d_poly :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {ι : Type} [Fintype ι] (x : ι → E), (D.poly x).IsHomogeneous n ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (s : ι → S), D.D S (∑ a, s a ⊗ₜ x a) = MvPolynomial.aeval s (D.poly x) := by
  intro n A E _ _ _ D ι _ x
  have key : ∀ (S : Type) [CommRing S] [Algebra A S] (f : MvPolynomial ι A →ₐ[A] S),
      D.D S (∑ a, f (MvPolynomial.X a) ⊗ₜ x a) = f (D.poly x) := by
    intro S _ _ f
    rw [Det.poly, ← D.nat]
    congr 1

    simp [Det.gen, map_sum]
  refine ⟨?_, fun S _ _ s => by simpa using key S (MvPolynomial.aeval s)⟩
  let g : MvPolynomial ι A →ₐ[A] (MvPolynomial ι A)[X] := MvPolynomial.aeval fun a => X * C (MvPolynomial.X a)
  let t : MvPolynomial ι A →ₐ[A] (MvPolynomial ι A)[X] := IsScalarTower.toAlgHom A (MvPolynomial ι A) (MvPolynomial ι A)[X]
  have h1 := key _ g
  have h3 := key _ t
  have h2 : (∑ a, g (MvPolynomial.X a) ⊗ₜ[A] x a) = (X : (MvPolynomial ι A)[X]) • ∑ a, t (MvPolynomial.X a) ⊗ₜ[A] x a := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp [g, t]
  rw [h2, D.homog, h3] at h1
  have hc := congrArg (fun p : (MvPolynomial ι A)[X] => p.coeff n) h1
  simp only [g, t, scale_coeff, IsScalarTower.coe_toAlgHom', Polynomial.coeff_X_pow_mul', le_refl, if_true,
    Nat.sub_self] at hc
  have hP : MvPolynomial.homogeneousComponent n (D.poly x) = D.poly x := by
    rw [← hc]
    simp
  exact hP ▸ MvPolynomial.homogeneousComponent_isHomogeneous n _
end
