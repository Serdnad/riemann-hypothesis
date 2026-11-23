module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.Basic.PEquiv
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.RingTheory.Localization.Module

@[expose] public section

section

namespace GlobalTheory
open Matrix

section HomTriv
variable {k : Type} [Field k] {N : ℕ}

private lemma hom_ne_zero (φ : GL (Fin N) k →* NNReal) (g : GL (Fin N) k) : φ g ≠ 0 := by
  intro h
  have := map_mul φ g g⁻¹
  rw [mul_inv_cancel, map_one, h, zero_mul] at this
  exact one_ne_zero this

private lemma det_diagonal_ne_zero (d : Fin N → k) (hd : ∀ m, d m ≠ 0) :
    (diagonal d).det ≠ 0 := by
  rw [det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun m _ => hd m

private lemma diag_perm (φ : GL (Fin N) k →* NNReal) (σ : Equiv.Perm (Fin N))
    (d : Fin N → k) (hd : ∀ m, d m ≠ 0) :
    φ (nonsingInvUnit (diagonal (d ∘ σ))
        (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero _ fun m => hd (σ m)))) =
      φ (nonsingInvUnit (diagonal d) (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero d hd))) := by
  set G := nonsingInvUnit (diagonal d) (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero d hd))
  have h1 : (σ.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) k) * σ.symm.toPEquiv.toMatrix = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  have h2 : (σ.symm.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) k) * σ.toPEquiv.toMatrix = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  let U : GL (Fin N) k := ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, h1, h2⟩
  have hconj : nonsingInvUnit (diagonal (d ∘ σ))
      (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero _ fun m => hd (σ m))) = U * G * U⁻¹ := by
    apply Units.ext
    show diagonal (d ∘ σ) = σ.toPEquiv.toMatrix * diagonal d * σ.symm.toPEquiv.toMatrix
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix,
      Equiv.symm_symm]
    exact (submatrix_diagonal_equiv d σ).symm
  rw [hconj, map_mul, map_mul, mul_comm (φ U), mul_assoc, ← map_mul, mul_inv_cancel, map_one,
    mul_one]

end HomTriv
end GlobalTheory

namespace GlobalTheory
open Matrix
section HomTriv2
variable {k : Type} [Field k] {N : ℕ}

private lemma diag_conj_transvection (i j : Fin N) (hij : i ≠ j) (y c : k) :
    diagonal (Pi.mulSingle i y) * transvection i j c =
      transvection i j (y * c) * diagonal (Pi.mulSingle i y) := by
  ext a b
  simp only [diagonal_mul, mul_diagonal, transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Pi.mulSingle_apply]
  by_cases ha : a = i <;> by_cases hb : b = j <;> by_cases hab : a = b <;>
    simp_all [eq_comm] <;> ring

private lemma transvection_trivial (φ : GL (Fin N) k →* NNReal) (hx : ∃ x : k, x ≠ 0 ∧ x ≠ 1)
    (i j : Fin N) (hij : i ≠ j) (c : k) (g : GL (Fin N) k)
    (hg : (g : Matrix (Fin N) (Fin N) k) = transvection i j c) : φ g = 1 := by
  obtain ⟨x, hx0, hx1⟩ := hx
  have hdetT : ∀ c : k, (transvection i j c).det ≠ 0 := fun c => by
    rw [det_transvection_of_ne _ _ hij]; exact one_ne_zero
  let T : k → GL (Fin N) k := fun c => nonsingInvUnit _ (isUnit_iff_ne_zero.mpr (hdetT c))
  have hgT : g = T c := Units.ext hg
  have hmulT : ∀ a b, T a * T b = T (a + b) := fun a b =>
    Units.ext (transvection_mul_transvection_same i j hij a b)
  have hscale : ∀ y : k, y ≠ 0 → ∀ c, φ (T (y * c)) = φ (T c) := by
    intro y hy c
    have hd : ∀ m, (Pi.mulSingle i y : Fin N → k) m ≠ 0 := fun m => by
      by_cases hm : m = i
      · rw [hm, Pi.mulSingle_eq_same]; exact hy
      · rw [Pi.mulSingle_eq_of_ne hm]; exact one_ne_zero
    let D : GL (Fin N) k :=
      nonsingInvUnit (diagonal (Pi.mulSingle i y)) (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero _ hd))
    have hc : D * T c = T (y * c) * D := Units.ext (diag_conj_transvection i j hij y c)
    have := congrArg φ hc
    rw [map_mul, map_mul, mul_comm (φ (T (y * c)))] at this
    exact (mul_left_cancel₀ (hom_ne_zero φ D) this).symm
  rw [hgT]
  have key : φ (T c) = φ (T c) * φ (T c) := by
    calc φ (T c) = φ (T (x * c)) := (hscale x hx0 c).symm
      _ = φ (T (c + (x - 1) * c)) := by congr 2; ring
      _ = φ (T c) * φ (T ((x - 1) * c)) := by rw [← hmulT, map_mul]
      _ = φ (T c) * φ (T c) := by rw [hscale (x - 1) (sub_ne_zero.mpr hx1) c]
  have h0 := hom_ne_zero φ (T c)
  exact (mul_right_eq_self₀.mp key.symm).resolve_right h0

end HomTriv2
end GlobalTheory

namespace GlobalTheory
open Matrix
section HomTriv3
variable {k : Type} [Field k] {N : ℕ}

private lemma mulSingle_unit_ne_zero (m : Fin N) (a : kˣ) (t : Fin N) :
    (Pi.mulSingle m (a : k) : Fin N → k) t ≠ 0 := by
  by_cases ht : t = m
  · rw [ht, Pi.mulSingle_eq_same]; exact a.ne_zero
  · rw [Pi.mulSingle_eq_of_ne ht]; exact one_ne_zero

private noncomputable def elemDiag (m : Fin N) (a : kˣ) : GL (Fin N) k :=
  nonsingInvUnit (diagonal (Pi.mulSingle m (a : k)))
    (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero _ (mulSingle_unit_ne_zero m a)))

private lemma elemDiag_coe (m : Fin N) (a : kˣ) :
    (elemDiag m a : Matrix (Fin N) (Fin N) k) = diagonal (Pi.mulSingle m (a : k)) := rfl

private lemma prod_elemDiag (d : Fin N → kˣ) :
    ((((List.finRange N).map fun m => elemDiag m (d m)).prod : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) = diagonal (fun t => (d t : k)) := by
  have h1 : ((((List.finRange N).map fun m => elemDiag m (d m)).prod : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) = ((List.finRange N).map
          ((diagonalRingHom (Fin N) k) ∘ fun m => Pi.mulSingle m (d m : k))).prod := by
    rw [show ((List.finRange N).map
        ((diagonalRingHom (Fin N) k) ∘ fun m => Pi.mulSingle m (d m : k))) =
        (List.finRange N).map ((Units.coeHom (Matrix (Fin N) (Fin N) k)) ∘
          fun m => elemDiag m (d m)) from rfl, List.prod_map_hom]
    rfl
  rw [h1, List.prod_map_hom, ← Fin.prod_univ_def, Finset.univ_prod_mulSingle (fun t => (d t : k))]
  rfl

private lemma elemDiag_swap (φ : GL (Fin N) k →* NNReal) (m m' : Fin N) (a : kˣ) :
    φ (elemDiag m a) = φ (elemDiag m' a) := by
  have hcomp : (Pi.mulSingle m' (a : k) : Fin N → k) ∘ (Equiv.swap m m') =
      Pi.mulSingle m (a : k) := by
    funext t
    simp only [Function.comp_apply, Pi.mulSingle_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have h := diag_perm φ (Equiv.swap m m') _ (mulSingle_unit_ne_zero m' a)
  have he : elemDiag m a = nonsingInvUnit (diagonal ((Pi.mulSingle m' (a : k) : Fin N → k) ∘
      (Equiv.swap m m'))) (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero _
        fun t => mulSingle_unit_ne_zero m' a ((Equiv.swap m m') t))) :=
    Units.ext (by rw [elemDiag_coe]; exact congrArg diagonal hcomp.symm)
  rw [he, h]
  rfl

private lemma elemDiag_trivial (φ : GL (Fin N) k →* NNReal)
    (hφ : ∀ z : kˣ, φ (Matrix.GeneralLinearGroup.scalar (Fin N) z) = 1) (m : Fin N) (a : kˣ) :
    φ (elemDiag m a) = 1 := by
  have hs : Matrix.GeneralLinearGroup.scalar (Fin N) a =
      ((List.finRange N).map fun t => elemDiag t ((fun _ => a) t)).prod := by
    apply Units.ext
    rw [prod_elemDiag]
    simp [Matrix.GeneralLinearGroup.scalar]
  have h1 := hφ a
  rw [hs, map_list_prod, List.map_map, ← Fin.prod_univ_def] at h1
  simp only [Function.comp_apply] at h1
  rw [Finset.prod_congr rfl (fun t _ => elemDiag_swap φ t m a), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at h1
  have hN : N ≠ 0 := by rintro rfl; exact m.elim0
  exact (pow_eq_one_iff_of_nonneg zero_le hN).mp h1

private lemma diagonal_trivial (φ : GL (Fin N) k →* NNReal)
    (hφ : ∀ z : kˣ, φ (Matrix.GeneralLinearGroup.scalar (Fin N) z) = 1) (D : Fin N → k)
    (hD : ∀ t, D t ≠ 0) (g : GL (Fin N) k) (hg : (g : Matrix (Fin N) (Fin N) k) = diagonal D) :
    φ g = 1 := by
  let d : Fin N → kˣ := fun t => Units.mk0 (D t) (hD t)
  have : g = ((List.finRange N).map fun m => elemDiag m (d m)).prod :=
    Units.ext (by rw [prod_elemDiag, hg]; rfl)
  rw [this, map_list_prod, List.map_map, ← Fin.prod_univ_def]
  exact Finset.prod_eq_one fun m _ => elemDiag_trivial φ hφ m (d m)

theorem gl_hom_nnreal_trivial_of_scalar :
    ∀ (k : Type) [Field k], (∃ x : k, x ≠ 0 ∧ x ≠ 1) → ∀ (N : ℕ) (φ : GL (Fin N) k →* NNReal),
      (∀ z : kˣ, φ (Matrix.GeneralLinearGroup.scalar (Fin N) z) = 1) → ∀ g, φ g = 1 := by
  intro k _ hx N φ hφ g
  have hdet : (g : Matrix (Fin N) (Fin N) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  refine diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ g : GL (Fin N) k, (g : Matrix (Fin N) (Fin N) k) = M → φ g = 1)
    (g : Matrix (Fin N) (Fin N) k) hdet ?_ ?_ ?_ g rfl
  · intro D hD h hh
    rw [det_diagonal] at hD
    exact diagonal_trivial φ hφ D (fun t => (Finset.prod_ne_zero_iff.mp hD) t (Finset.mem_univ t)) h hh
  · intro t h hh
    exact transvection_trivial φ hx t.i t.j t.hij t.c h hh
  · intro A B hA hB hPA hPB h hh
    let uA : GL (Fin N) k := nonsingInvUnit A (isUnit_iff_ne_zero.mpr hA)
    let uB : GL (Fin N) k := nonsingInvUnit B (isUnit_iff_ne_zero.mpr hB)
    have : h = uA * uB := Units.ext hh
    rw [this, map_mul, hPA uA rfl, hPB uB rfl, mul_one]

end HomTriv3
end GlobalTheory
end

section

noncomputable section
open Matrix Module

namespace GlobalTheory.StableLattice

theorem lift_of_integral {O K : Type} [CommRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) {Γ : Type} [Group Γ] {n : ℕ}
    (φ : Γ →* GL (Fin n) K)
    (h : ∀ g i j, ((φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ (algebraMap O K).range) :
    ∃ r : Γ →* GL (Fin n) O, ∀ g, Matrix.GeneralLinearGroup.map (algebraMap O K) (r g) = φ g := by
  classical
  let f : O →+* K := algebraMap O K
  have h' : ∀ g i j, ∃ x : O, f x = ((φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j :=
    fun g i j => RingHom.mem_range.1 (h g i j)
  choose c hc using h'
  let M : Γ → Matrix (Fin n) (Fin n) O := fun g => Matrix.of fun i j => c g i j
  have hmi : Function.Injective (f.mapMatrix : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) K) :=
    fun A B hAB => Matrix.ext fun i j => hinj (by simpa using congrFun (congrFun hAB i) j)
  have hM : ∀ g, f.mapMatrix (M g) = ((φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    fun g => Matrix.ext fun i j => hc g i j
  let ρ : Γ →* GL (Fin n) O :=
    { toFun := fun g => ⟨M g, M g⁻¹,
        hmi (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]),
        hmi (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩
      map_one' := Units.ext (hmi (by rw [hM, map_one, Units.val_one, Units.val_one, map_one]))
      map_mul' := fun g h => Units.ext (hmi (by
        show f.mapMatrix (M (g * h)) = f.mapMatrix (M g * M h)
        rw [map_mul, hM, hM, hM, map_mul, Units.val_mul])) }
  exact ⟨ρ, fun g => Units.ext (hM g)⟩

theorem exists_conj_integral {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {Γ : Type} [Group Γ] {n : ℕ} (σ : Γ →* GL (Fin n) (FractionRing O)) (T : Finset Γ)
    (hT : ∀ x : Γ, ∃ t ∈ T, ∀ i j, ((σ (t⁻¹ * x) : GL (Fin n) (FractionRing O)) :
      Matrix (Fin n) (Fin n) (FractionRing O)) i j ∈ (algebraMap O (FractionRing O)).range) :
    ∃ P : GL (Fin n) (FractionRing O), ∀ g i j,
      ((P⁻¹ * σ g * P : GL (Fin n) (FractionRing O)) : Matrix (Fin n) (Fin n) (FractionRing O)) i j
        ∈ (algebraMap O (FractionRing O)).range := by
  classical
  let K := FractionRing O
  let S : Γ → Matrix (Fin n) (Fin n) K := fun g => ((σ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  let gen : T × Fin n → (Fin n → K) := fun p => S p.1 *ᵥ Pi.single p.2 1
  let M : Submodule O (Fin n → K) := Submodule.span O (Set.range gen)
  have hA : ∀ t (ht : t ∈ T), ∀ w : Fin n → K, (∀ k, w k ∈ (algebraMap O K).range) → S t *ᵥ w ∈ M := by
    intro t ht w hw
    choose u hu using fun k => RingHom.mem_range.1 (hw k)
    have : S t *ᵥ w = ∑ k, u k • gen (⟨t, ht⟩, k) := by
      ext a
      simp only [gen, Matrix.mulVec_single_one]
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, Matrix.col_apply, Algebra.smul_def,
        Matrix.mulVec, dotProduct, ← hu]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have he : ∀ i, (Pi.single i 1 : Fin n → K) ∈ M := by
    intro i
    obtain ⟨t, ht, hU⟩ := hT 1
    have h1 : S t * S (t⁻¹ * 1) = 1 := by
      simp only [S]
      rw [← Units.val_mul, ← map_mul, mul_one, mul_inv_cancel, map_one, Units.val_one]
    have : (Pi.single i 1 : Fin n → K) = S t *ᵥ (S (t⁻¹ * 1) *ᵥ Pi.single i 1) := by
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    rw [this]
    refine hA t ht _ fun k => ?_
    rw [Matrix.mulVec_single_one]
    exact hU k i
  have hstab : ∀ g, ∀ x ∈ M, S g *ᵥ x ∈ M := by
    intro g
    let A : (Fin n → K) →ₗ[O] (Fin n → K) := (Matrix.toLin' (S g)).restrictScalars O
    have hle : M.map A ≤ M := by
      rw [Submodule.map_span_le]
      rintro _ ⟨⟨⟨t, ht⟩, i⟩, rfl⟩
      obtain ⟨t', ht', hU⟩ := hT (g * t)
      have h1 : S g * S t = S t' * S (t'⁻¹ * (g * t)) := by
        simp only [S]
        rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel_left]
      show S g *ᵥ (S t *ᵥ Pi.single i 1) ∈ M
      rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec]
      refine hA t' ht' _ fun k => ?_
      rw [Matrix.mulVec_single_one]
      exact hU k i
    intro x hx
    exact hle ⟨x, hx, rfl⟩
  haveI : Module.Finite O M := Module.Finite.span_of_finite (R := O) (Set.finite_range gen)
  haveI : Module.Free O M := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex O M
  let b : Basis ι O M := Module.Free.chooseBasis O M
  let v : ι → (Fin n → K) := fun i => (b i : Fin n → K)
  have hcoord : ∀ x (hx : x ∈ M), x = ∑ i, algebraMap O K (b.repr ⟨x, hx⟩ i) • v i := by
    intro x hx
    have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at this
    simp only [algebraMap_smul, v]
    exact this.symm
  have hli : LinearIndependent K v :=
    (LinearIndependent.iff_fractionRing O K).1 (b.linearIndependent.map' M.subtype M.ker_subtype)
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply, hcoord _ (he i)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let bK : Basis ι K (Fin n → K) := Basis.mk hli hsp
  have hrep : ∀ x (hx : x ∈ M) k, bK.repr x k = algebraMap O K (b.repr ⟨x, hx⟩ k) := by
    intro x hx k
    have h1 : x = bK.equivFun.symm (fun i => algebraMap O K (b.repr ⟨x, hx⟩ i)) := by
      rw [Basis.equivFun_symm_apply]
      simp only [bK, Basis.coe_mk]
      exact hcoord x hx
    rw [← Basis.equivFun_apply]
    conv_lhs => rw [h1]
    rw [LinearEquiv.apply_symm_apply]
  have hcard : Fintype.card ι = n :=
    (Module.finrank_eq_card_basis bK).symm.trans (Module.finrank_fin_fun K)
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let bK' : Basis (Fin n) K (Fin n → K) := bK.reindex e
  let E := Pi.basisFun K (Fin n)
  let Pu : GL (Fin n) K := ⟨E.toMatrix bK', bK'.toMatrix E, E.toMatrix_mul_toMatrix_flip bK',
    bK'.toMatrix_mul_toMatrix_flip E⟩
  refine ⟨Pu, fun g i j => ?_⟩
  have hmat : ((Pu⁻¹ * σ g * Pu : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      LinearMap.toMatrix bK' bK' (Matrix.toLin' (S g)) := by
    rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := bK') (c := bK') (b' := E) (c' := E),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    simp only [Units.val_mul]
    rfl
  have hmem : S g *ᵥ bK' j ∈ M := by
    refine hstab g _ ?_
    simp only [bK', Basis.reindex_apply, bK, Basis.coe_mk, v]
    exact (b _).2
  rw [hmat, LinearMap.toMatrix_apply, Matrix.toLin'_apply, Basis.repr_reindex_apply, hrep _ hmem]
  exact ⟨_, rfl⟩

end GlobalTheory.StableLattice
end
end

section

open Matrix

namespace GlobalTheory

theorem GL_inv_mul_congr_one : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {N : ℕ} (π : K), π ≠ 0 → Valued.v π < 1 →
  ∀ (a a₁ : GL (Fin N) K), (∀ i j, Valued.v (π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) →
    (∀ i j, Valued.v (π⁻¹ * ((a₁ : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) →
    ∀ i j, Valued.v (π⁻¹ * (((a⁻¹ * a₁ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1 := by
  intro K _ _ N π hπ0 hπ a a₁ ha ha₁
  set v : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v with hv
  let S : Subring K := v.integer
  have hpS : π ∈ S := (Valuation.mem_integer_iff _ _).2 hπ.le
  let p : S := ⟨π, hpS⟩
  let B : Matrix (Fin N) (Fin N) S := fun i j =>
    ⟨π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j, (Valuation.mem_integer_iff _ _).2 (ha i j)⟩
  let B₁ : Matrix (Fin N) (Fin N) S := fun i j =>
    ⟨π⁻¹ * ((a₁ : Matrix (Fin N) (Fin N) K) - 1) i j, (Valuation.mem_integer_iff _ _).2 (ha₁ i j)⟩
  let f : S →+* K := S.subtype
  let A' : Matrix (Fin N) (Fin N) S := 1 + p • B
  have hA : f.mapMatrix A' = (a : Matrix (Fin N) (Fin N) K) := by
    ext i j
    have h1 : (((1 : Matrix (Fin N) (Fin N) S) i j : S) : K) = (1 : Matrix (Fin N) (Fin N) K) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    change ((A' i j : S) : K) = _
    change (((1 + p • B) i j : S) : K) = _
    rw [Matrix.add_apply, Matrix.smul_apply, Subring.coe_add, smul_eq_mul, Subring.coe_mul, h1]
    change _ + π * (π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j) = _
    rw [← mul_assoc, mul_inv_cancel₀ hπ0, one_mul, Matrix.sub_apply]
    ring
  have hB : (a₁ : Matrix (Fin N) (Fin N) K) - a = π • f.mapMatrix (B₁ - B) := by
    ext i j
    rw [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, smul_eq_mul]
    change _ = π * (((B₁ i j - B i j : S)) : K)
    rw [AddSubgroupClass.coe_sub]
    change _ = π * (π⁻¹ * ((a₁ : Matrix (Fin N) (Fin N) K) - 1) i j - π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j)
    rw [← mul_sub, ← mul_assoc, mul_inv_cancel₀ hπ0, one_mul, Matrix.sub_apply, Matrix.sub_apply]
    ring
  let I : Ideal S := Ideal.span {p}
  have hp : Ideal.Quotient.mk I p = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have hdet1 : A'.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det]
    have hm : (Ideal.Quotient.mk I).mapMatrix A' = 1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp only [A', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, hp, zero_mul,
        add_zero, Matrix.one_apply]
      split_ifs <;> simp
    rw [hm, det_one, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hdet1
  have hvd : v (f A'.det) = 1 := by
    have hlt : v (f (A'.det - 1)) < 1 := by
      rw [← hc, map_mul, map_mul]
      have hc' : v (f c) ≤ 1 := (Valuation.mem_integer_iff _ _).1 c.2
      calc v (f c) * v (f p) ≤ 1 * v (f p) := mul_le_mul_of_nonneg_right hc' zero_le'
        _ = v π := one_mul _
        _ < 1 := hπ
    have he : f A'.det = 1 + f (A'.det - 1) := by rw [map_sub, map_one]; ring
    rw [he, Valuation.map_add_eq_of_lt_left v (by rwa [v.map_one]), v.map_one]
  have hu : IsUnit A'.det := (Valuation.integer.integers v).isUnit_of_one' hvd
  have hinv : (a : Matrix (Fin N) (Fin N) K) * f.mapMatrix A'⁻¹ = 1 := by
    rw [← hA, ← map_mul, Matrix.mul_nonsing_inv _ hu, map_one]
  have hainv : ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = f.mapMatrix A'⁻¹ := by
    calc ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
        = ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * ((a : Matrix (Fin N) (Fin N) K) * f.mapMatrix A'⁻¹) := by
          rw [hinv, mul_one]
      _ = _ := by rw [← mul_assoc, Units.inv_mul, one_mul]
  have key : ((a⁻¹ * a₁ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) - 1 = π • f.mapMatrix (A'⁻¹ * (B₁ - B)) := by
    calc ((a⁻¹ * a₁ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) - 1
        = ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * a₁ - ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * a := by
          rw [Units.val_mul, Units.inv_mul]
      _ = ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * ((a₁ : Matrix (Fin N) (Fin N) K) - a) := by rw [Matrix.mul_sub]
      _ = ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * (π • f.mapMatrix (B₁ - B)) := by rw [hB]
      _ = π • (((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * f.mapMatrix (B₁ - B)) := by rw [Matrix.mul_smul]
      _ = _ := by rw [map_mul, hainv]
  intro i j
  rw [key, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hπ0, one_mul,
    RingHom.mapMatrix_apply, Matrix.map_apply]
  exact (Valuation.mem_integer_iff _ _).1 ((A'⁻¹ * (B₁ - B)) i j).2

end GlobalTheory
end
