module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle015
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle017
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle018
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.PrimitiveElement

@[expose] public section

section

open IsLocalRing GlobalTheory.Henselisation

open scoped TensorProduct

namespace GlobalTheory.Henselisation

theorem etNbhd_isDirected (R : Type) [CommRing R] [IsLocalRing R] :
    IsDirected (EtNbhd R) (· ≤ ·) := by
  refine ⟨fun i j => ?_⟩
  let C := i.A ⊗[R] j.A
  haveI : Algebra.Etale R C := Algebra.Etale.comp R i.A C
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := C)).1 inferInstance
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let P : C →ₐ[R] ResidueField R := Algebra.TensorProduct.lift i.pt j.pt (fun _ _ => Commute.all _ _)
  let k : EtNbhd R :=
    { n := n, I := RingHom.ker f, etale := Algebra.Etale.of_equiv e.symm, pt := P.comp e.toAlgHom }
  refine ⟨k, ⟨(e.symm.toAlgHom).comp Algebra.TensorProduct.includeLeft, ?_⟩,
    ⟨(e.symm.toAlgHom).comp Algebra.TensorProduct.includeRight, ?_⟩⟩
  · apply AlgHom.ext; intro a
    show P (e (e.symm _)) = i.pt a
    rw [AlgEquiv.apply_symm_apply]
    change P (a ⊗ₜ[R] (1 : j.A)) = i.pt a
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  · apply AlgHom.ext; intro a
    show P (e (e.symm _)) = j.pt a
    rw [AlgEquiv.apply_symm_apply]
    change P ((1 : i.A) ⊗ₜ[R] a) = j.pt a
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]

end GlobalTheory.Henselisation
end

section

open Matrix Polynomial

noncomputable section

namespace GlobalTheory.LeviDesc.Krylov

theorem pow_dim_eq_neg_sum_charpoly_coeff {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) :
    y ^ r = - ∑ k : Fin r, y.charpoly.coeff k • y ^ (k : ℕ) := by
  have h := Matrix.aeval_self_charpoly y
  have hm := (Matrix.charpoly_monic y).as_sum
  have hd : y.charpoly.natDegree = r := by simpa using Matrix.charpoly_natDegree_eq_dim y
  rw [hd] at hm
  rw [hm] at h

  simp [map_sum, Algebra.smul_def] at h
  rw [Fin.sum_univ_eq_sum_range (fun k => y.charpoly.coeff k • y ^ k)]
  simp only [Algebra.smul_def]
  exact eq_neg_of_add_eq_zero_left h

def companion {F : Type} [Field F] (r : ℕ) (p : F[X]) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => if (j : ℕ) + 1 < r then (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) else - p.coeff i

theorem mul_krylov_eq {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) :
    y * krylov y e = krylov y e * companion r y.charpoly := by
  ext i j
  have hl : (y * krylov y e) i j = (y ^ ((j : ℕ) + 1) *ᵥ e) i := by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp [Matrix.mul_apply, krylov_apply, Matrix.mulVec, dotProduct]
  rw [hl, Matrix.mul_apply]
  by_cases hj : (j : ℕ) + 1 < r
  · simp only [companion, Matrix.of_apply, hj, if_true]
    rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hj⟩ : Fin r)]
    · simp [krylov_apply]
    · intro k _ hk
      have : (k : ℕ) ≠ (j : ℕ) + 1 := fun h => hk (Fin.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hr : (j : ℕ) + 1 = r := by omega
    simp only [companion, Matrix.of_apply, hj, if_false]
    rw [hr, pow_dim_eq_neg_sum_charpoly_coeff y, Matrix.neg_mulVec, Matrix.sum_mulVec]
    simp [krylov_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

theorem krylov_inv_mul_mul_krylov {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F)
    (e : Fin r → F) (h : IsUnit (krylov y e).det) :
    (krylov y e)⁻¹ * y * krylov y e = companion r y.charpoly := by
  rw [Matrix.mul_assoc, mul_krylov_eq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.one_mul]

theorem krylov_conj_eq_of_charpoly_eq {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F)
    (e e' : Fin r → F) (hχ : y.charpoly = y'.charpoly) (h : IsUnit (krylov y e).det)
    (h' : IsUnit (krylov y' e').det) :
    (krylov y e)⁻¹ * y * krylov y e = (krylov y' e')⁻¹ * y' * krylov y' e' := by
  rw [krylov_inv_mul_mul_krylov y e h, krylov_inv_mul_mul_krylov y' e' h', hχ]

end GlobalTheory.LeviDesc.Krylov
end
end

section

open MeasureTheory

namespace GlobalTheory.Cusp.Shear

theorem isFundamentalDomain_image_prod : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (Λ : AddSubgroup V) (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ (A : Set N') (B : Set V), MeasurableSet A → MeasurableSet B →
      (∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A) → (∀ v : V, ∃! w : Λ, (w : V) + v ∈ B) →
      ∀ ν : MeasureTheory.Measure N, MeasureTheory.IsFundamentalDomain (Γ.subgroupOf N)
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker '' (A ×ˢ B)) ν := by
  intro G _ _ _ _ _ _ Γ N N' hle hn V _ _ _ _ _ Λ s π hs hsc hπc hπmul hπs hker hsadd hsΓ hπΓ
    A B hAm hBm hA hB ν
  set e := prodHomeo hle hs hsc hπc hπmul hπs hker with he
  have himg : e '' (A ×ˢ B) = e.symm ⁻¹' (A ×ˢ B) := by
    ext n; constructor
    · rintro ⟨z, hz, rfl⟩; simpa using hz
    · intro h; exact ⟨e.symm n, h, by simp⟩
  have efst : ∀ n : N, (((e.symm n).1 : N') : G) = (n : G) * (s (π n))⁻¹ := fun n => rfl
  have esnd : ∀ n : N, (e.symm n).2 = π n := fun n => rfl
  refine IsFundamentalDomain.mk' ?_ ?_
  · rw [himg]; exact (e.symm.continuous.measurable (hAm.prod hBm)).nullMeasurableSet
  · intro x
    have hmemS : ∀ n : N, n ∈ e '' (A ×ˢ B) ↔ (e.symm n).1 ∈ A ∧ (e.symm n).2 ∈ B := by
      intro n; rw [himg]; rfl
    have hfst : ∀ g : N, (((e.symm (g * x)).1 : N') : G) =
        (g : G) * (s (π g))⁻¹ * (s (π g) * ((x : G) * (s (π x))⁻¹) * (s (π g))⁻¹) := by
      intro g
      rw [efst, hπmul, hsadd]
      simp only [Subgroup.coe_mul]
      group
    have hsnd : ∀ g : N, (e.symm (g * x)).2 = π g + π x := fun g => by rw [esnd, hπmul]
    let c : V → N' := fun w => ⟨s w * ((x : G) * (s (π x))⁻¹) * (s w)⁻¹,
      hn (s w) (hs w) _ (mul_inv_mem hs hπmul hπs hker x)⟩
    obtain ⟨w, hwB, hwu⟩ := hB (π x)
    obtain ⟨δ, hδA, hδu⟩ := hA (c w)
    have hδΓ : ((δ : N') : G) ∈ Γ := Subgroup.mem_subgroupOf.1 δ.2
    let γ0 : Γ.subgroupOf N := ⟨⟨((δ : N') : G) * s w, N.mul_mem (hle (δ : N').2) (hs w)⟩,
      Subgroup.mem_subgroupOf.2 (Γ.mul_mem hδΓ (hsΓ w w.2))⟩
    have hπγ0 : π (γ0 : N) = w := by
      have h : (γ0 : N) = ⟨((δ : N') : G), hle (δ : N').2⟩ * ⟨s w, hs w⟩ := rfl
      rw [h, hπmul, hπs ⟨s w, hs w⟩ w rfl, (hker _).2 (δ : N').2, zero_add]
    refine ⟨γ0, ?_, ?_⟩
    · show (γ0 : N) * x ∈ _
      rw [hmemS, hsnd, hπγ0]
      refine ⟨?_, hwB⟩
      have h : (e.symm ((γ0 : N) * x)).1 = (δ : N') * c w := by
        apply Subtype.ext
        rw [hfst, hπγ0]
        show ((δ : N') : G) * s w * (s w)⁻¹ * _ = ((δ : N') : G) * (s w * ((x : G) * (s (π x))⁻¹) * (s w)⁻¹)
        group
      rw [h]; exact hδA
    · intro γ hγ
      have hγ' : (γ : N) * x ∈ e '' (A ×ˢ B) := hγ
      rw [hmemS, hsnd] at hγ'
      obtain ⟨hγA, hγB⟩ := hγ'
      have hγΓ : ((γ : N) : G) ∈ Γ := Subgroup.mem_subgroupOf.1 γ.2
      have hw : (⟨π (γ : N), hπΓ γ hγΓ⟩ : Λ) = w := hwu _ hγB
      have hwv : π (γ : N) = w := congrArg Subtype.val hw
      have hδN' : ((γ : N) : G) * (s w)⁻¹ ∈ N' := hwv ▸ mul_inv_mem hs hπmul hπs hker γ
      let δγ : Γ.subgroupOf N' := ⟨⟨((γ : N) : G) * (s w)⁻¹, hδN'⟩,
        Subgroup.mem_subgroupOf.2 (Γ.mul_mem hγΓ (Γ.inv_mem (hsΓ w w.2)))⟩
      have h : (δγ : N') * c w = (e.symm ((γ : N) * x)).1 := by
        apply Subtype.ext
        rw [hfst, hwv]
        rfl
      have hδe : δγ = δ := hδu δγ (by show (δγ : N') * c w ∈ A; rw [h]; exact hγA)
      have hv : ((γ : N) : G) * (s w)⁻¹ = ((δ : N') : G) := by
        rw [← hδe]
      apply Subtype.ext; apply Subtype.ext
      show ((γ : N) : G) = ((δ : N') : G) * s w
      rw [← hv]; group

end GlobalTheory.Cusp.Shear
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

abbrev genPt {Y Z : Scheme.{0}} [IrreducibleSpace Y] (π : Y ⟶ Z) : Z := π (genericPoint Y)

abbrev fieldK {Y Z : Scheme.{0}} [IrreducibleSpace Y] (π : Y ⟶ Z)
    (hK : IsField (Z.presheaf.stalk (genPt π))) : Field (Z.presheaf.stalk (genPt π)) :=
  hK.toField

abbrev algKL {Y Z : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ Z) :
    Algebra (Z.presheaf.stalk (genPt π)) Y.functionField :=
  (π.stalkMap (genericPoint Y)).hom.toAlgebra

abbrev algAK {Y Z : Scheme.{0}} [IrreducibleSpace Y] (π : Y ⟶ Z) (U : Z.Opens) (h : genPt π ∈ U) :
    Algebra Γ(Z, U) (Z.presheaf.stalk (genPt π)) :=
  (Z.presheaf.germ U (genPt π) h).hom.toAlgebra

abbrev algBL {Y Z : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ Z) (U : Z.Opens) (h : genPt π ∈ U) :
    Algebra Γ(Y, π ⁻¹ᵁ U) Y.functionField :=
  (Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) h).hom.toAlgebra


open scoped Classical in
def famIdeal {Y Z : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ Z) [IsAffineHom π]
    (hK : IsField (Z.presheaf.stalk (genPt π)))
    (hfd : letI := fieldK π hK; letI := algKL π
      FiniteDimensional (Z.presheaf.stalk (genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens) : Ideal Γ(Z, U) := by
  classical
  exact if h : genPt π ∈ U.1 then
    letI := fieldK π hK; letI := algKL π; letI := algAK π U.1 h; letI := algBL π U.1 h
    GlobalTheory.NormSheaf.normIdeal Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField Γ(Y, π ⁻¹ᵁ U.1)
      (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩)
  else ⊤

end GlobalTheory.NormSheafDescent
end
end

section

open MvPolynomial

noncomputable section

namespace GlobalTheory.NormSheaf

theorem map_normForm_eq_prod (K L Ω : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Field Ω] [Algebra K Ω] (e : Fin (Module.finrank K L) ≃ (L →ₐ[K] Ω)) {m : ℕ} (x : Fin m → L) :
    (normForm K L x).map (algebraMap K Ω) = ∏ j, ∑ i, C (e j (x i)) * X i := by
  classical
  set b := Module.finBasis K L
  let V : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) Ω := .of fun i k => e i (b k)
  have hV : V.det ≠ 0 := by
    have hli := (linearIndependent_algHom_toLinearMap K L Ω).comp e e.injective
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    refine hc0 (funext (Fintype.linearIndependent_iff.1 hli c (b.ext fun k => ?_)))
    have := congrFun hc k
    simpa [V, Matrix.vecMul, dotProduct] using this
  have key : V.map (C : Ω →+* MvPolynomial (Fin m) Ω) *
      (MvPolynomial.map (algebraMap K Ω)).mapMatrix (∑ i, (X i : MvPolynomial (Fin m) K) •
        (Algebra.leftMulMatrix b (x i)).map (C : K →+* MvPolynomial (Fin m) K)) =
      Matrix.diagonal (fun j => ∑ i, C (e j (x i)) * X i) * V.map (C : Ω →+* MvPolynomial (Fin m) Ω) := by
    ext1 j k
    have h (i : Fin m) : e j (x i) * e j (b k) =
        ∑ l, e j (b l) * algebraMap K Ω (Algebra.leftMulMatrix b (x i) l k) := by

      rw [← map_mul, ← b.sum_repr (x i * b k), map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, Algebra.leftMulMatrix_eq_repr_mul, Algebra.smul_def, mul_comm]
    rw [Matrix.diagonal_mul, Matrix.mul_apply]

    simp only [V, Matrix.of_apply, Matrix.map_apply, RingHom.mapMatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, map_mul, map_X, map_C, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [mul_left_comm, ← C_mul, h, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [C_mul]
    ring
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    ← RingHom.map_det] at hd
  rw [normForm, mul_right_cancel₀ (C_eq_zero.not.2 hV) hd]

end GlobalTheory.NormSheaf

noncomputable section

namespace GlobalTheory.NormSheaf

theorem exists_finite_split_normForm : ∀ (A B K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [CharZero K] [Algebra A K] [Algebra B L] [Algebra K L] [FiniteDimensional K L]
    [IsFractionRing A K] [IsFractionRing B L] (φ : A →+* B), φ.Finite →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp φ →
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra A R), Function.Injective (algebraMap A R) ∧ Module.Finite A R ∧
      ∃ σ : Fin (Module.finrank K L) → (B →+* R), (∀ j, (σ j).comp φ = algebraMap A R) ∧
        ∀ (m : ℕ) (g : Fin m → B), ∃ P : MvPolynomial (Fin m) A,
          P.map (algebraMap A K) = GlobalTheory.NormSheaf.normForm K L (fun i => algebraMap B L (g i)) ∧
          P.map (algebraMap A R) = ∏ j, ∑ i, C (σ j (g i)) * X i := by
  intro A B K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ hφ hcomp
  classical
  letI : Algebra A B := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  have hcard : Fintype.card (L →ₐ[K] AlgebraicClosure K) = Module.finrank K L := AlgHom.card K L _
  let e : Fin (Module.finrank K L) ≃ (L →ₐ[K] AlgebraicClosure K) := (Fintype.equivFinOfCardEq hcard).symm
  have hAΩ : algebraMap A (AlgebraicClosure K) = (algebraMap K (AlgebraicClosure K)).comp (algebraMap A K) :=
    IsScalarTower.algebraMap_eq A K _

  let F : Fin (Module.finrank K L) → (B →ₐ[A] AlgebraicClosure K) := fun j =>
    { ((e j).toRingHom.comp (algebraMap B L)) with
      commutes' := fun a => by
        have h1 := congrArg (fun f => f a) hcomp
        simp only [RingHom.coe_comp, Function.comp_apply] at h1
        change e j (algebraMap B L (φ a)) = _
        rw [← h1, AlgHom.commutes, hAΩ, RingHom.comp_apply] }
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := B)
  let S : Set (AlgebraicClosure K) := Set.range fun p : Fin (Module.finrank K L) × s => F p.1 p.2
  let R : Subalgebra A (AlgebraicClosure K) := Algebra.adjoin A S
  have hSfin : S.Finite := Set.finite_range _
  have hSint : ∀ y ∈ S, IsIntegral A y := by
    rintro _ ⟨p, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := A) (p.2 : B)).map (F p.1)
  have hRfin : Module.Finite A R := by
    exact Module.Finite.iff_fg.mpr (fg_adjoin_of_finite hSfin hSint)
  have hmem : ∀ j (y : B), F j y ∈ R := by
    intro j y
    have hy : y ∈ Submodule.span A (s : Set B) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz => exact Algebra.subset_adjoin ⟨(j, ⟨z, hz⟩), rfl⟩
    | zero => simp
    | add u v _ _ hu hv => rw [map_add (f := _)]; exact R.add_mem hu hv
    | smul a u _ hu => rw [map_smul]; exact R.smul_mem hu a
  let σ : Fin (Module.finrank K L) → (B →+* R) := fun j => ((F j).codRestrict R (hmem j)).toRingHom
  have hinjAΩ : Function.Injective (algebraMap A (AlgebraicClosure K)) := by
    rw [hAΩ]
    exact (algebraMap K _).injective.comp (IsFractionRing.injective A K)
  have hval : (algebraMap R (AlgebraicClosure K)).comp (algebraMap A R) = algebraMap A (AlgebraicClosure K) :=
    (IsScalarTower.algebraMap_eq A R _).symm
  refine ⟨R, inferInstance, inferInstance, ?_, hRfin, σ, ?_, ?_⟩
  · intro a b hab
    apply hinjAΩ
    rw [← hval, RingHom.comp_apply, RingHom.comp_apply, hab]
  · intro j
    ext a
    exact congrArg Subtype.val (((F j).codRestrict R (hmem j)).commutes a)
  · intro m g
    let Q : MvPolynomial (Fin m) R := ∏ j, ∑ i, C (σ j (g i)) * X i
    have hQ : Q.map (algebraMap R (AlgebraicClosure K)) =
        (normForm K L (fun i => algebraMap B L (g i))).map (algebraMap K (AlgebraicClosure K)) := by
      rw [map_normForm_eq_prod K L _ e]

      simp only [Q, map_prod, map_sum, map_mul, map_C, map_X]
      rfl
    set N := normForm K L (fun i => algebraMap B L (g i))
    have hcoef : ∀ n, ∃ a : A, algebraMap A K a = N.coeff n := by
      intro n
      have h1 : algebraMap K (AlgebraicClosure K) (N.coeff n) = algebraMap R (AlgebraicClosure K) (Q.coeff n) := by
        rw [← coeff_map, ← coeff_map, hQ]
      have h2 : IsIntegral A (algebraMap R (AlgebraicClosure K) (Q.coeff n)) :=
        (Algebra.IsIntegral.isIntegral (R := A) (Q.coeff n)).map (IsScalarTower.toAlgHom A R (AlgebraicClosure K))
      rw [← h1] at h2
      have h3 : IsIntegral A (N.coeff n) :=
        (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K (AlgebraicClosure K)) (algebraMap K _).injective).1 h2
      exact IsIntegrallyClosed.isIntegral_iff.1 h3
    have hrange : N ∈ Set.range (MvPolynomial.map (algebraMap A K)) := by
      rw [mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.1 hc
      exact hcoef n
    obtain ⟨P, hP⟩ := hrange
    refine ⟨P, hP, ?_⟩
    apply map_injective (algebraMap R (AlgebraicClosure K)) Subtype.val_injective
    rw [map_map, hval, hQ, ← hP, map_map, hAΩ]

end GlobalTheory.NormSheaf
end
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.HilbAff

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {r : ℕ} {T : Scheme.{0}}

abbrev subStr (y : (functor A B r).obj (op T)) : y.2.1.subscheme ⟶ T :=
  y.2.1.subschemeι ≫ pullback.snd _ y.1

def Sec (y : (functor A B r).obj (op T)) (U : T.Opens) : Type :=
  Γ(y.2.1.subscheme, subStr A B y ⁻¹ᵁ U)

instance (y : (functor A B r).obj (op T)) (U : T.Opens) : CommRing (Sec A B y U) :=
  inferInstanceAs (CommRing Γ(y.2.1.subscheme, subStr A B y ⁻¹ᵁ U))

instance (y : (functor A B r).obj (op T)) (U : T.Opens) : Algebra Γ(T, U) (Sec A B y U) :=
  ((subStr A B y).app U).hom.toAlgebra

def gen (y : (functor A B r).obj (op T)) (U : T.Opens) (b : B) : Sec A B y U :=
  ((y.2.1.subschemeι ≫ pullback.fst _ y.1).appLE ⊤ (subStr A B y ⁻¹ᵁ U) (by simp)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)

def coord {N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N)
    (y : (functor A B r).obj (op T)) (U : T.Opens) : (Fin r → Γ(T, U)) →ₗ[Γ(T, U)] Sec A B y U :=
  Fintype.linearCombination Γ(T, U) (fun k => gen A B y U (e (σ k)))

theorem basic_iff {N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N)
    (y : (functor A B r).obj (op T)) :
    Basic A B e σ y ↔ ∀ U : T.affineOpens, Function.Bijective (coord A B e σ y U) := Iff.rfl

end GlobalTheory.HilbAff
end
end

section

noncomputable section

open NumberField

namespace GlobalTheory.HeckeMellin

variable {I : Type} [Fintype I]

def term (n : I → ℤ) (s : ℂ) (v : I → ℂ) (y : I → ℝ) : ℂ :=
  GlobalTheory.HeckeTheta.gauss n (GlobalTheory.HeckeTheta.dil y v) * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))

theorem term_zero {n : I → ℤ} (hn : ∃ i, n i ≠ 0) (s : ℂ) (y : I → ℝ) : term n s 0 y = 0 := by
  have : GlobalTheory.HeckeTheta.dil y (0 : I → ℂ) = 0 := by
    funext i; simp [GlobalTheory.HeckeTheta.dil]
  rw [term, this, GlobalTheory.HeckeTheta.gauss_zero hn, zero_mul]

end GlobalTheory.HeckeMellin
end
end
