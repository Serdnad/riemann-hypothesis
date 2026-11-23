module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Perfectoid.Untilt
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.NumberTheory.ModularForms.Derivative
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
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

namespace ReciprocityTheory.PGsh

open Matrix

section

variable {K : Type} [Field K] (v : Valuation K NNReal) {ι : Type} [Fintype ι] [DecidableEq ι]

def IsIntegralMat (U : Matrix ι ι K) : Prop := ∀ i j, v (U i j) ≤ 1

def IsIntegralVec (c : ι → K) : Prop := ∀ j, v (c j) ≤ 1

variable {v}

theorem IsIntegralMat.det_le_one {U : Matrix ι ι K} (hU : IsIntegralMat v U) : v U.det ≤ 1 := by
  rw [Matrix.det_apply']
  refine v.map_sum_le fun σ _ => ?_
  rw [map_mul, map_prod]
  have hs : v ((Equiv.Perm.sign σ : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  rw [hs, one_mul]
  exact Finset.prod_le_one₀ (fun _ _ => zero_le) fun i _ => hU _ _

private theorem nnreal_mul_le_one {a b : NNReal} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 := by
  simpa using mul_le_mul ha hb (zero_le) zero_le_one

theorem IsIntegralMat.mulVec {U : Matrix ι ι K} {c : ι → K} (hU : IsIntegralMat v U)
    (hc : IsIntegralVec v c) : IsIntegralVec v (U *ᵥ c) := by
  intro i
  show v (∑ j, U i j * c j) ≤ 1
  exact v.map_sum_le fun j _ => by rw [map_mul]; exact _root_.ReciprocityTheory.PGsh.nnreal_mul_le_one (hU i j) (hc j)

theorem isIntegralVec_single (j : ι) : IsIntegralVec v (Pi.single j (1 : K)) := by
  intro k
  by_cases hk : k = j
  · subst hk; simp
  · simp [hk]

end

structure Lat {K : Type} [Field K] (v : Valuation K NNReal) (ι : Type) [Fintype ι]
    [DecidableEq ι] where

  B : Matrix ι ι K
  det_ne : B.det ≠ 0

namespace Lat

variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]

def pts (L : Lat v ι) : Set (ι → K) := {x | ∃ c, IsIntegralVec v c ∧ x = L.B *ᵥ c}

def std (v : Valuation K NNReal) (ι : Type) [Fintype ι] [DecidableEq ι] : Lat v ι :=
  ⟨1, by simp⟩

theorem isUnit_det (L : Lat v ι) : IsUnit L.B.det :=
  isUnit_iff_ne_zero.mpr L.det_ne

theorem pts_subset_iff (L' L : Lat v ι) :
    L'.pts ⊆ L.pts ↔ IsIntegralMat v (L.B⁻¹ * L'.B) := by
  constructor
  · intro h i j
    obtain ⟨c, hc, hx⟩ := h ⟨Pi.single j 1, ReciprocityTheory.PGsh.isIntegralVec_single j, rfl⟩
    have hM : (L.B⁻¹ * L'.B) *ᵥ Pi.single j 1 = c := by
      rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_det L), Matrix.one_mulVec]
    have e := congrFun hM i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at e
    rw [e]
    exact hc i
  · intro hM x ⟨c, hc, hx⟩
    refine ⟨(L.B⁻¹ * L'.B) *ᵥ c, hM.mulVec hc, ?_⟩
    rw [hx, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_det L),
      Matrix.one_mul]

theorem v_det_eq_one_of_integral {U V : Matrix ι ι K} (hU : IsIntegralMat v U)
    (hV : IsIntegralMat v V) (hUV : U * V = 1) : v U.det = 1 := by
  refine le_antisymm hU.det_le_one ?_
  calc (1 : NNReal) = v U.det * v V.det := by
        rw [← map_mul, ← Matrix.det_mul, hUV, Matrix.det_one, map_one]
    _ ≤ v U.det * 1 := mul_le_mul_of_nonneg_left hV.det_le_one (zero_le)
    _ = v U.det := mul_one _

private theorem valuation_lat_det_ne_zero (L : ReciprocityTheory.PGsh.Lat v ι) : v L.B.det ≠ 0 :=
  (Valuation.ne_zero_iff v).mpr L.det_ne

private theorem valuation_det_inv_mul_eq_div (L' L : ReciprocityTheory.PGsh.Lat v ι) :
    v (L.B⁻¹ * L'.B).det = v L'.B.det / v L.B.det := by
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_mul, map_inv₀,
    div_eq_inv_mul]

theorem v_det_eq_of_pts_eq {L₁ L₂ : Lat v ι} (h : L₁.pts = L₂.pts) :
    v L₁.B.det = v L₂.B.det := by
  have h₁ := (pts_subset_iff L₁ L₂).mp h.subset
  have h₂ := (pts_subset_iff L₂ L₁).mp h.symm.subset
  have hMN : (L₂.B⁻¹ * L₁.B) * (L₁.B⁻¹ * L₂.B) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc L₁.B,
      Matrix.mul_nonsing_inv _ (isUnit_det L₁), Matrix.one_mul,
      Matrix.nonsing_inv_mul _ (isUnit_det L₂)]
  have := v_det_eq_one_of_integral h₁ h₂ hMN
  rw [valuation_det_inv_mul_eq_div] at this
  exact (div_eq_one_iff_eq (valuation_lat_det_ne_zero L₂)).mp this

end Lat

section colen

variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def colen (L' L : Lat v ι) : NNReal := v L'.B.det / v L.B.det

theorem colen_eq_v_det (L' L : Lat v ι) : colen L' L = v (L.B⁻¹ * L'.B).det := by
  rw [_root_.ReciprocityTheory.PGsh.Lat.valuation_det_inv_mul_eq_div]
  rfl

theorem colen_congr {L₁' L₂' L₁ L₂ : Lat v ι} (h' : L₁'.pts = L₂'.pts) (h : L₁.pts = L₂.pts) :
    colen L₁' L₁ = colen L₂' L₂ := by
  unfold colen
  rw [ReciprocityTheory.PGsh.Lat.v_det_eq_of_pts_eq h', ReciprocityTheory.PGsh.Lat.v_det_eq_of_pts_eq h]

end colen

end ReciprocityTheory.PGsh
end

section

noncomputable section

open Ideal

namespace ReciprocityTheory.PGsh

variable {p : ℕ} [hp : Fact p.Prime]

section Untilt

variable {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

private lemma pow_p_pow_eq (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) (n : ℕ) :
    f n ^ p ^ n = f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, hf, ih]

lemma untilt_eq_of_coeff (x : PreTilt O p) (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n)
    (hx : ∀ n, Perfection.coeff (ModP O p) p n x = Ideal.Quotient.mk (span {(p : O)}) (f n)) :
    x.untilt = f 0 := by
  show Perfection.teichmuller p (span {(p : O)}) x = f 0
  exact Perfection.teichmuller_spec fun n => ⟨f n, (hx n).symm, by rw [pow_p_pow_eq f hf n]⟩

def ofRoots (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) : PreTilt O p :=
  ⟨fun n => Ideal.Quotient.mk (span {(p : O)}) (f n), fun n => by
    show (Ideal.Quotient.mk (span {(p : O)}) (f (n + 1))) ^ p = _
    rw [← map_pow, hf]⟩

lemma coeff_ofRoots (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) (n : ℕ) :
    Perfection.coeff (ModP O p) p n (ofRoots f hf) = Ideal.Quotient.mk (span {(p : O)}) (f n) :=
  rfl

lemma untilt_ofRoots (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) :
    (ofRoots f hf).untilt = f 0 :=
  untilt_eq_of_coeff _ f hf (coeff_ofRoots f hf)

lemma untilt_symm_ofRoots (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) :
    ((_root_.frobeniusEquiv (PreTilt O p) p).symm (ofRoots f hf)).untilt = f 1 := by
  apply untilt_eq_of_coeff _ (fun n => f (n + 1)) (fun n => hf (n + 1))
  intro n
  rw [← PreTilt.coeff_def, PreTilt.coeff_frobeniusEquiv_symm, PreTilt.coeff_def]
  rfl

end Untilt

section Roots

variable (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal)
  (O : Type) [CommRing O] [Algebra O C]

private lemma le_one_of_pow (hv : v.Integers O) {z : C} {w : O} (h : z ^ p = algebraMap O C w) :
    v z ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have h1 : 1 < v z ^ p := one_lt_pow₀ hlt hp.out.ne_zero
  rw [← map_pow, h] at h1
  exact absurd (hv.map_le_one w) (not_le.2 h1)

lemma exists_root (hv : v.Integers O) (x : O) : ∃ y : O, y ^ p = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C x) hp.out.pos
  obtain ⟨y, rfl⟩ := hv.exists_of_le_one (le_one_of_pow C v O hv hz)
  exact ⟨y, hv.hom_inj (by rw [map_pow, hz])⟩

lemma exists_primitiveRoot [CharZero C] (hv : v.Integers O) :
    ∃ ζ : O, IsPrimitiveRoot ζ p := by
  have : NeZero (p : C) := ⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p C)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos p C hp.out.pos))
  have hzp : IsPrimitiveRoot z p := Polynomial.isRoot_cyclotomic_iff.1 hz
  have hz1 : z ^ p = algebraMap O C 1 := by rw [hzp.pow_eq_one, map_one]
  obtain ⟨y, rfl⟩ := hv.exists_of_le_one (le_one_of_pow C v O hv hz1)
  exact ⟨y, (IsPrimitiveRoot.map_iff_of_injective hv.hom_inj).1 hzp⟩

private def rootSeq (r : O → O) (c : O) : ℕ → O
  | 0 => c
  | n + 1 => r (rootSeq r c n)

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

theorem exists_pflat (hv : v.Integers O) : ∃ pflat : PreTilt O p, pflat.untilt = (p : O) := by
  choose r hr using exists_root (p := p) C v O hv
  exact ⟨ofRoots (rootSeq O r p) (fun n => hr _), untilt_ofRoots _ _⟩

theorem exists_eps [CharZero C] (hv : v.Integers O) :
    ∃ ε : PreTilt O p,
      IsPrimitiveRoot (((_root_.frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p := by
  choose r hr using exists_root (p := p) C v O hv
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot (p := p) C v O hv
  let f : ℕ → O := fun n => Nat.casesOn n 1 (fun m => rootSeq O r ζ m)
  have hf : ∀ n, f (n + 1) ^ p = f n := by
    intro n
    cases n with
    | zero => exact hζ.pow_eq_one
    | succ m => exact hr _
  refine ⟨ofRoots f hf, ?_⟩
  rw [untilt_symm_ofRoots]
  exact hζ

end Roots

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.RankA

variable {S : Type} [CommRing S]

lemma col_mem_range {m n : Type} [Fintype n] [DecidableEq n] (A : Matrix m n S) (y : n) :
    (fun x => A x y) ∈ LinearMap.range A.mulVecLin :=
  ⟨Pi.single y 1, by ext x; simp⟩

lemma factor_of_basis {m n ι : Type} [Fintype ι] (A : Matrix m n S)
    (M : Submodule S (m → S)) (b : Module.Basis ι S M) (hA : ∀ y, (fun x => A x y) ∈ M) :
    A = (Matrix.of fun x l => (b l : m → S) x) *
      Matrix.of fun l y => b.repr ⟨fun x => A x y, hA y⟩ l := by
  ext x y
  have h := congrArg (fun z : M => (z : m → S) x) (b.sum_repr ⟨fun x => A x y, hA y⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rw [← h]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

lemma rank_map_le [StrongRankCondition S] {K : Type} [Field K] (f : S →+* K) {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n S) [Module.Free S (LinearMap.range A.mulVecLin)]
    [Module.Finite S (LinearMap.range A.mulVecLin)] :
    (A.map f).rank ≤ Module.finrank S (LinearMap.range A.mulVecLin) := by
  obtain ⟨N, hN, P, Q, hPQ⟩ : ∃ N, N = Module.finrank S (LinearMap.range A.mulVecLin) ∧
      ∃ (P : Matrix m (Fin N) S) (Q : Matrix (Fin N) n S), A = P * Q :=
    ⟨_, rfl, _, _, factor_of_basis A _ (Module.finBasis S _) (col_mem_range A)⟩
  rw [← hN]
  have h : A.map f = P.map f * Q.map f := by rw [hPQ, Matrix.map_mul]
  rw [h]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))

lemma sum_finrank {ι m : Type} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]
    [StrongRankCondition S] (e : m → Matrix ι ι S)
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (hsum : ∑ i, e i = 1)
    [∀ i, Module.Free S (LinearMap.range (e i).mulVecLin)]
    [∀ i, Module.Finite S (LinearMap.range (e i).mulVecLin)] :
    ∑ i, Module.finrank S (LinearMap.range (e i).mulVecLin) = Fintype.card ι := by
  let M : m → Submodule S (ι → S) := fun i => LinearMap.range (e i).mulVecLin
  have hmem : ∀ i j (y : M j), e i *ᵥ (y : ι → S) = if i = j then (y : ι → S) else 0 := by
    intro i j y
    obtain ⟨z, hz⟩ := y.2
    simp only [Matrix.mulVecLin_apply] at hz
    rw [← hz, mulVec_mulVec, horth]
    split_ifs with h
    · subst h; rfl
    · exact zero_mulVec _
  have hsum' : ∀ x : ι → S, ∑ i, e i *ᵥ x = x := by
    intro x
    rw [← Matrix.sum_mulVec, hsum, one_mulVec]
  let E : (ι → S) ≃ₗ[S] ((i : m) → M i) :=
    { toFun := fun x i => ⟨e i *ᵥ x, x, rfl⟩
      map_add' := fun x y => by ext i : 1; apply Subtype.ext; simp [mulVec_add]
      map_smul' := fun c x => by ext i : 1; apply Subtype.ext; simp [mulVec_smul]
      invFun := fun y => ∑ i, (y i : ι → S)
      left_inv := fun x => hsum' x
      right_inv := fun y => by
        ext i : 1; apply Subtype.ext
        simp only [Matrix.mulVec_sum, hmem, Finset.sum_ite_eq, Finset.mem_univ, if_true] }
  have h1 := E.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype] at h1
  exact h1.symm

lemma free_range_idem [IsLocalRing S] {ι : Type} [Fintype ι] [DecidableEq ι] (e : Matrix ι ι S)
    (he : e * e = e) :
    Module.Free S (LinearMap.range e.mulVecLin) ∧ Module.Finite S (LinearMap.range e.mulVecLin) := by
  let s : (ι → S) →ₗ[S] LinearMap.range e.mulVecLin := e.mulVecLin.rangeRestrict
  have hs : s ∘ₗ (LinearMap.range e.mulVecLin).subtype = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨_, y, rfl⟩ := x
    simp [s, Matrix.mulVec_mulVec, he]
  have : Module.Projective S (LinearMap.range e.mulVecLin) :=
    Module.Projective.of_split (LinearMap.range e.mulVecLin).subtype s hs
  have : Module.Finite S (LinearMap.range e.mulVecLin) :=
    Module.Finite.of_surjective s (LinearMap.surjective_rangeRestrict _)
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

end ReciprocityTheory.PGsh.Up.RankA
end
end

section

open UpperHalfPlane hiding I
open Complex Filter Function
open scoped Real Manifold Topology

namespace ReciprocityTheory.PGsh

local notation "𝕢" => Periodic.qParam

lemma qParam_one_pow_eq_cexp (z : ℂ) (m : ℕ) :
    𝕢 1 z ^ m = cexp (2 * π * I * m * z) := by
  rw [Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem hasSum_normalizedDeriv {F : ℍ → ℂ} {c : ℕ → ℂ}
    (hF : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 1 τ ^ m) (F τ)) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ ((m : ℂ) * c m) • 𝕢 1 τ ^ m)
      (Derivative.normalizedDerivOfComplex F τ) := by
  set y0 : ℝ := τ.im / 2 with hy0
  have hy0pos : 0 < y0 := by have := τ.im_pos; positivity
  have hy0lt : y0 < τ.im := by have := τ.im_pos; rw [hy0]; linarith
  let τ0 : ℍ := ⟨(y0 : ℂ) * I, by simpa using hy0pos⟩
  have hτ0im : (τ0 : ℂ).im = y0 := by simp [τ0]
  set r : ℝ := ‖𝕢 1 (τ0 : ℂ)‖ with hr
  have hsum : Summable (fun m : ℕ ↦ ‖c m‖ * r ^ m) := by
    have := (hF τ0).summable.norm
    refine this.congr fun m ↦ ?_
    rw [norm_smul, norm_pow]
  set U : Set ℂ := {z : ℂ | y0 < z.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hτU : (τ : ℂ) ∈ U := by simpa [hU] using hy0lt
  let G : ℕ → ℂ → ℂ := fun m z ↦ c m * cexp (2 * π * I * m * z)
  have hGd : ∀ m, DifferentiableOn ℂ (G m) U := fun m ↦ by
    intro z _
    exact (by fun_prop : Differentiable ℂ (G m)).differentiableAt.differentiableWithinAt
  have hGle : ∀ m (z : ℂ), z ∈ U → ‖G m z‖ ≤ ‖c m‖ * r ^ m := by
    intro m z hz
    simp only [G, norm_mul, ← qParam_one_pow_eq_cexp, norm_pow]
    gcongr
    rw [hr, Periodic.norm_qParam, Periodic.norm_qParam, Real.exp_le_exp, hτ0im]
    have : y0 < z.im := hz
    have := Real.pi_pos
    nlinarith
  have hmain := hasSum_deriv_of_summable_norm hsum hGd hUo hGle hτU
  have heq : (fun w : ℂ ↦ ∑' m, G m w) =ᶠ[𝓝 (τ : ℂ)] F ∘ ofComplex := by
    filter_upwards [hUo.mem_nhds hτU] with w hw
    have hw0 : 0 < w.im := lt_trans hy0pos hw
    simp only [comp_apply, ofComplex_apply_of_im_pos hw0]
    rw [← (hF ⟨w, hw0⟩).tsum_eq]
    refine tsum_congr fun m ↦ ?_
    simp [G, qParam_one_pow_eq_cexp]
  rw [heq.deriv_eq] at hmain
  have hderiv : ∀ m, deriv (G m) τ = 2 * π * I * m * (c m * cexp (2 * π * I * m * τ)) := by
    intro m
    have h1 : HasDerivAt (fun z : ℂ ↦ 2 * π * I * m * z) (2 * π * I * m) (τ : ℂ) := by
      simpa using (hasDerivAt_id (τ : ℂ)).const_mul (2 * π * I * m)
    have h2 := (h1.cexp).const_mul (c m)
    rw [h2.deriv]
    ring
  simp only [hderiv] at hmain
  have hfin := hmain.mul_left (2 * π * I)⁻¹
  unfold Derivative.normalizedDerivOfComplex
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  refine hfin.congr_fun fun m ↦ ?_
  rw [smul_eq_mul, qParam_one_pow_eq_cexp]
  field_simp

end ReciprocityTheory.PGsh
end
