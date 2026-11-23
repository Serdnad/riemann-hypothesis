module

public import ReciprocityTheory.DualLattices.Bundle025
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
public import ReciprocityTheory.DualLattices.UpSmith

@[expose] public section

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section F3b

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

def sumX (D : Lifts H U X) : (Ix g → R) →ₗ[R] augIdeal H.AA.carrier where
  toFun c := ⟨∑ k, c k • xL D k, Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (D.x_mem k)⟩
  map_add' c c' := by apply Subtype.ext; simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by apply Subtype.ext; simp [Finset.smul_sum, smul_smul]

omit [Fact p.Prime] in
lemma mem_pP {n : ℕ} (w : Fin n → R) :
    w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n → R)) ↔ ∃ w', w = (p : R) • w' := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w', _, hw'⟩
    exact ⟨w', hw'.symm⟩
  · rintro ⟨w', hw'⟩
    exact ⟨w', Submodule.mem_top, hw'.symm⟩

omit [Fact p.Prime] in
lemma mulVec_mem_pP {n n' : ℕ} (M : Matrix (Fin n') (Fin n) R) {w : Fin n → R}
    (hw : w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n → R))) :
    M *ᵥ w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n' → R)) := by
  obtain ⟨w', rfl⟩ := (mem_pP w).1 hw
  exact (mem_pP _).2 ⟨M *ᵥ w', Matrix.mulVec_smul M (p : R) w'⟩

lemma εL_eq_zero_of_r (U : UnramData p g v R O σ cp H) {τ : Fin U.m} (h : U.r τ = 0) :
    U.εL τ = 0 := by
  obtain ⟨e⟩ := U.rank τ
  haveI : Subsingleton (Fin (U.r τ) → R) := by rw [h]; infer_instance
  haveI : Subsingleton (LinearMap.range (Matrix.mulVecLin (U.εL τ))) := e.toEquiv.subsingleton
  ext i j
  have h1 : (⟨U.εL τ *ᵥ Pi.single j 1, LinearMap.mem_range_self _ _⟩ :
      LinearMap.range (Matrix.mulVecLin (U.εL τ))) = 0 := Subsingleton.elim _ _
  have h2 := congrArg (fun x : LinearMap.range (Matrix.mulVecLin (U.εL τ)) => (x : Fin g → R) i) h1
  simpa [Matrix.mulVec_single_one] using h2

lemma phi_x_grade (hS : HodgeTateSetting p v R O σ cp) (D : Lifts H U X) (k : Ix g) (τ : Fin U.m)
    (hτ : τ ≠ D.κ k) (l : Fin g → R)
    (hl : H.φ ⟨xL D k, D.x_mem k⟩ = Submodule.Quotient.mk l) :
    (U.εL τ)ᵀ *ᵥ l ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin g → R)) := by
  by_cases hτκ : ∃ j, D.κ j = τ
  · obtain ⟨j', rfl⟩ := hτκ
    obtain ⟨k', hk'⟩ := D.sep j' k hτ
    have hf' : ∀ t, ((U.sg (D.κ k) (D.b k') • (⟨xL D k, D.x_mem k⟩ : augIdeal H.AA.carrier) :
        augIdeal H.AA.carrier) : Nb p g → C) (red p g t) =
        ((⟨xL D k, D.x_mem k⟩ : augIdeal H.AA.carrier) : Nb p g → C) (red p g (H.ρ (D.b k') *ᵥ t)) := by
      intro t
      simp only [Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def, xL]
      rw [D.eig k k' t]
      ring
    have h1 := H.cotangent_linear (D.b k') _ _ l hf' hl
    rw [map_smul, hl, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h1
    have h2 := mulVec_mem_pP (U.εL (D.κ j'))ᵀ h1
    have e : (U.εL (D.κ j'))ᵀ *ᵥ (U.sg (D.κ k) (D.b k') • l - (H.ρL (D.b k'))ᵀ *ᵥ l) =
        (U.sg (D.κ k) (D.b k') - U.sg (D.κ j') (D.b k')) • ((U.εL (D.κ j'))ᵀ *ᵥ l) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, U.εL_eig,
        Matrix.transpose_smul, Matrix.smul_mulVec, sub_smul]
    rw [e] at h2
    have hv : v (algebraMap R C (U.sg (D.κ k) (D.b k') - U.sg (D.κ j') (D.b k'))) = 1 := by
      rw [← neg_sub, map_neg, Valuation.map_neg]
      exact hk'
    have hunit : IsUnit (U.sg (D.κ k) (D.b k') - U.sg (D.κ j') (D.b k')) := by
      refine hS.integers.isUnit_of_one ?_ hv
      exact Ne.isUnit fun h0 => by rw [h0, Valuation.map_zero] at hv; exact zero_ne_one hv
    obtain ⟨u, hu⟩ := hunit
    have h3 := Submodule.smul_mem _ (↑u⁻¹ : R) h2
    rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h3
  · push_neg at hτκ
    rw [εL_eq_zero_of_r U (D.r_zero τ hτκ), Matrix.transpose_zero, Matrix.zero_mulVec]
    exact Submodule.zero_mem _

end F3b

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section FrobA

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

private theorem hasLen_of_linearEquiv {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    {x : NNReal} (e : M ≃ₗ[R] M') (h : HasLen v R M' x) : HasLen v R M x := by
  obtain ⟨m, c, ⟨φ⟩, hx⟩ := h
  exact ⟨m, c, ⟨e.trans φ⟩, hx⟩

lemma coefX_int (D : Lifts H U X) (hdet : (valM D).det ≠ 0)
    (hbasis : H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val))
    {f : Nb p g → C} (hf : f ∈ H.AA.carrier) :
    ∃ r : Nb p g → R, coefX D f = algebraMap R C ∘ r := by
  rw [hbasis] at hf
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hf
  refine ⟨r, ?_⟩
  have hfv : f = valM D *ᵥ (algebraMap R C ∘ r) := by
    rw [← hr]
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, valM, Matrix.of_apply,
      Function.comp_apply, monX, xL, Algebra.smul_def]
    exact Finset.sum_congr rfl fun α _ => mul_comm _ _
  rw [coefX, hfv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

lemma xL_pow_mem (D : Lifts H U X) (hp : 2 ≤ p) (j : Ix g) :
    (fun y => xL D j y ^ p) ∈ sqIdeal (augIdeal H.AA.carrier) := by
  have hx : xL D j ∈ augIdeal H.AA.carrier := D.x_mem j
  have hxA : xL D j ∈ H.AA.carrier := hx.1
  have hx0 : xL D j 0 = 0 := hx.2
  have hpow : ∀ n : ℕ, xL D j ^ (n + 1) ∈ augIdeal H.AA.carrier := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · rw [pow_succ]
        exact H.AA.mul_mem _ _ ih.1 hxA
      · show (xL D j ^ (n + 1 + 1)) 0 = 0
        rw [Pi.pow_apply, hx0, zero_pow (by omega)]
  have heq : (fun y => xL D j y ^ p) = xL D j * xL D j ^ (p - 1 - 1 + 1) := by
    funext y
    rw [Pi.mul_apply, Pi.pow_apply, ← pow_succ']
    congr 1
    omega
  rw [heq]
  exact Submodule.subset_span ⟨_, hx, _, hpow _, rfl⟩

def blockEquiv (D : Lifts H U X) (τ : Fin U.m) :
    blockL D τ ≃ₗ[R] ({l // D.κ l = τ} → R) where
  toFun c l := c.1 l.1
  invFun d := ⟨fun k => if h : D.κ k = τ then d ⟨k, h⟩ else 0, fun k hk => by simp [hk]⟩
  left_inv c := by
    apply Subtype.ext
    funext k
    by_cases h : D.κ k = τ
    · simp [h]
    · simp [h, c.2 k h]
  right_inv d := by funext l; simp [l.2]
  map_add' c c' := rfl
  map_smul' r c := rfl

end FrobA

theorem frob_of (h1 : LiftMonomialDeterminantStatement) (h2 : FrobeniusBlockStatement) (h3 : FrobeniusLengthBoundStatement) :
    EigenLiftsFrobeniusStatement := by
  unfold EigenLiftsFrobeniusStatement
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U X D hbasis i
  have hv := hS.integers
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdet := h1 p g C v R O σ cp hS H U X D
  obtain ⟨h2a, h2b⟩ := h2 p g C v R O σ cp hp2 hS H U X D
  have hsq : sqIdeal (augIdeal H.AA.carrier) ≤ H.AA.carrier := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, hf, f', hf', rfl⟩
    exact H.AA.mul_mem _ _ hf.1 hf'.1
  have hfS : ∀ j, (fun y => xL D j y ^ p) ∈ sqIdeal (augIdeal H.AA.carrier) :=
    fun j => xL_pow_mem D hp j
  have hrex : ∀ j : Ix g, ∃ r : Nb p g → R,
      coefX D (fun y => xL D j y ^ p) = algebraMap R C ∘ r :=
    fun j => coefX_int D hdet hbasis (hsq (hfS j))
  choose r hr using hrex
  let c : Ix g → Ix g → R := fun j k => if D.κ k = U.φ i then r j (Pi.single k 1) else 0
  have hc : ∀ j, D.κ j = i → ∀ k, algebraMap R C (c j k) = linX D (fun y => xL D j y ^ p) k := by
    intro j hj k
    by_cases hk : D.κ k = U.φ i
    · simp only [c, if_pos hk, linX, hr j, Function.comp_apply]
    · simp only [c, if_neg hk, map_zero]
      exact (h2a j k (by rw [hj]; exact hk)).symm
  have hcard : Fintype.card {j // D.κ j = i} = Fintype.card {l // D.κ l = U.φ i} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, D.card_phi i]
  let e'' : {j // D.κ j = i} ≃ {l // D.κ l = U.φ i} := Fintype.equivOfCardEq hcard
  let eτ : {l // D.κ l = U.φ i} ≃ Fin (Fintype.card {l // D.κ l = U.φ i}) := Fintype.equivFin _
  let σE : Fin (Fintype.card {l // D.κ l = U.φ i}) ≃ {j // D.κ j = i} := eτ.symm.trans e''.symm
  let Y : Matrix (Fin (Fintype.card {l // D.κ l = U.φ i})) (Fin (Fintype.card {l // D.κ l = U.φ i})) R :=
    fun a b => c (σE b).1 (eτ.symm a).1
  let Ψ : blockL D (U.φ i) ≃ₗ[R] (Fin (Fintype.card {l // D.κ l = U.φ i}) → R) :=
    (blockEquiv D (U.φ i)).trans (LinearEquiv.funCongrLeft R R eτ.symm)
  let N : Submodule R (Ix g → R) :=
    ((LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap).map (blockL D (U.φ i)).subtype
  have hcomap : N.comap (blockL D (U.φ i)).subtype = (LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap :=
    Submodule.comap_map_eq_of_injective (blockL D (U.φ i)).injective_subtype _
  have hmapΨ : ((LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap).map Ψ.toLinearMap = LinearMap.range Y.mulVecLin :=
    Submodule.map_comap_eq_of_surjective Ψ.surjective _
  have hlen : HasLen v R (blockL D (U.φ i) ⧸ N.comap (blockL D (U.φ i)).subtype)
      (v (algebraMap R C Y.det)) := by
    rw [hcomap]
    exact hasLen_of_linearEquiv (Submodule.Quotient.equiv _ _ Ψ hmapΨ) (Smith.hasLen_coker_det hv Y)
  have hNle : N ≤ blockL D (U.φ i) := Submodule.map_subtype_le _ _
  have hreal : ∀ x ∈ N, ∃ f ∈ sqIdeal (augIdeal H.AA.carrier),
      ∀ k, algebraMap R C (x k) = linX D f k := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hy)
    refine ⟨∑ b, w b • (fun t => xL D (σE b).1 t ^ p),
      Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hfS _), ?_⟩
    intro k
    have hyΨ : y = Ψ.symm (Y.mulVecLin w) := by rw [hw]; exact (Ψ.symm_apply_apply y).symm
    have hyk : (y : Ix g → R) k = ∑ b, c (σE b).1 k * w b := by
      rw [hyΨ]
      by_cases h : D.κ k = U.φ i
      · show (if h' : D.κ k = U.φ i then (Y.mulVecLin w) (eτ ⟨k, h'⟩) else 0) = _
        rw [dite_eq_left h]
        show ∑ b, Y (eτ ⟨k, h⟩) b * w b = _
        simp only [Y, Equiv.symm_apply_apply]
      · show (if h' : D.κ k = U.φ i then (Y.mulVecLin w) (eτ ⟨k, h'⟩) else 0) = _
        rw [dite_eq_right h]
        simp [c, h]
    show algebraMap R C ((y : Ix g → R) k) = _

    rw [hyk, map_sum]
    simp only [linX, coefX, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← algebraMap_smul C (w b), Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul,
      mul_comm]
    congr 1
    exact hc (σE b).1 (σE b).2 k
  have hYdet : v (algebraMap R C Y.det) = X i ^ p / X (U.φ i) := by
    rw [RingHom.map_det]
    have hYZ : (algebraMap R C).mapMatrix Y = (Matrix.of fun j l : {j // D.κ j = i} =>
        linX D (fun y => xL D j.1 y ^ p) (e'' l).1)ᵀ.submatrix σE σE := by
      ext a b
      show algebraMap R C (c (σE b).1 (eτ.symm a).1) =
        linX D (fun y => xL D (σE b).1 y ^ p) (e'' (σE a)).1
      rw [hc (σE b).1 (σE b).2]
      simp [σE]
    rw [hYZ, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
    exact h2b i e''
  have hz := h3 p g C v R O σ cp hp2 hS H U X D hdet hbasis (U.φ i) N _ hNle hreal hlen
  rw [hYdet] at hz
  have hXne : X (U.φ i) ≠ 0 := by
    rw [← D.ε_prod (U.φ i)]
    exact Finset.prod_ne_zero_iff.mpr fun j _ =>
      (Valuation.ne_zero_iff v).mpr ((map_ne_zero_iff _ hinj).mpr (D.ε_ne j))
  rw [div_le_iff₀ (pos_iff_ne_zero.mpr hXne)] at hz
  exact hz.trans_eq (mul_comm _ _)

end ReciprocityTheory.PGsh.Up
end
end
