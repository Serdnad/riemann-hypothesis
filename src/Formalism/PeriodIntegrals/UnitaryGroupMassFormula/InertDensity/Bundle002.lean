module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.AnisoPeelAlt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.ExistsTraceNeZero
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

section

open Finset

noncomputable section

namespace DensInertW

def cgComb {L : Type} [Field L] {m n : ℕ} (Q : Matrix (Fin m) (Fin m) L) (X : Fin m → Fin n → L) :
    Fin m → Fin n → L :=
  fun i => ∑ k, Q i k • X k

theorem cg_comb_comb {L : Type} [Field L] {m n : ℕ} (P Q : Matrix (Fin m) (Fin m) L)
    (X : Fin m → Fin n → L) : cgComb P (cgComb Q X) = cgComb (P * Q) X := by
  funext i
  simp only [cgComb, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem cg_comb_one {L : Type} [Field L] {m n : ℕ} (X : Fin m → Fin n → L) :
    cgComb (1 : Matrix (Fin m) (Fin m) L) X = X := by
  funext i
  simp [cgComb, Matrix.one_apply, ite_smul]

theorem cg_mem {L : Type} [Field L] {m n : ℕ} (Q : Matrix (Fin m) (Fin m) L)
    (X : Fin m → Fin n → L) (W : Submodule L (Fin n → L)) (hX : ∀ i, X i ∈ W) :
    ∀ i, cgComb Q X i ∈ W := by
  intro i
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hX k)

theorem cg_lincomb {L : Type} [Field L] {m n : ℕ} (Q : Matrix (Fin m) (Fin m) L)
    (X : Fin m → Fin n → L) (g : Fin m → L) :
    ∑ i, g i • cgComb Q X i = ∑ k, (Matrix.vecMul g Q) k • X k := by
  simp only [cgComb, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
  exact Finset.sum_comm

theorem cg_indep {L : Type} [Field L] {m n : ℕ} (Q : Matrix (Fin m) (Fin m) L)
    (X : Fin m → Fin n → L) (hQ : Q.det ≠ 0) (hX : LinearIndependent L X) :
    LinearIndependent L (cgComb Q X) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro g hg i
  rw [cg_lincomb] at hg
  have h0 : Matrix.vecMul g Q = 0 := funext (hX _ hg)
  have hg' : g = Matrix.vecMul (Matrix.vecMul g Q) Q⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hQ.isUnit, Matrix.vecMul_one]
  rw [hg', h0, Matrix.zero_vecMul, Pi.zero_apply]

theorem cg_hf_left {L : Type} [Field L] {m n : ℕ} (q : ℕ) (M : Matrix (Fin n) (Fin n) L)
    (c : Fin m → L) (x : Fin m → Fin n → L) (y : Fin n → L) :
    hf q M (∑ k, c k • x k) y = ∑ k, c k * hf q M (x k) y := by
  have e1 : ∀ a b, (∑ k, c k * x k a) * M a b * y b ^ q =
      ∑ k, c k * (x k a * M a b * y b ^ q) := fun a b => by
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e1, Finset.mul_sum]
  calc _ = ∑ a, ∑ k, ∑ b, c k * (x k a * M a b * y b ^ q) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem cg_hf_right (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] {m n : ℕ}
    (M : Matrix (Fin n) (Fin n) L) (c : Fin m → L) (x : Fin n → L) (y : Fin m → Fin n → L) :
    hf (Fintype.card K) M x (∑ l, c l • y l) =
      ∑ l, c l ^ Fintype.card K * hf (Fintype.card K) M x (y l) := by
  obtain ⟨p, hch⟩ := CharP.exists K
  obtain ⟨n, hp, hq⟩ := FiniteField.card K p
  haveI := Fact.mk hp
  haveI : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hfr : ∀ (s : Finset (Fin m)) (f : Fin m → L),
      (∑ i ∈ s, f i) ^ Fintype.card K = ∑ i ∈ s, f i ^ Fintype.card K := by
    intro s f
    rw [hq]
    first
    | exact sum_pow_char_pow s f
    | (haveI : ExpChar L p := ExpChar.prime hp
       have h := map_sum (iterateFrobenius L p n) f s
       simp only [iterateFrobenius_def] at h
       exact h)
    | (haveI : ExpChar L p := ExpChar.prime hp
       simp)
  have hfrob : ∀ b, (∑ l, c l * y l b) ^ Fintype.card K =
      ∑ l, c l ^ Fintype.card K * y l b ^ Fintype.card K := by
    intro b
    rw [hfr]
    simp [mul_pow]
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hfrob, Finset.mul_sum]
  calc _ = ∑ a, ∑ l, ∑ b, x a * M a b * (c l ^ Fintype.card K * y l b ^ Fintype.card K) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, x a * M a b * (c l ^ Fintype.card K * y l b ^ Fintype.card K) :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => by ring

theorem cg_gram (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] {m n : ℕ}
    (M : Matrix (Fin n) (Fin n) L) (Q G : Matrix (Fin m) (Fin m) L) (X : Fin m → Fin n → L)
    (hX : ∀ k l, hf (Fintype.card K) M (X k) (X l) = G k l) (i j : Fin m) :
    hf (Fintype.card K) M (cgComb Q X i) (cgComb Q X j) =
      (Q * G * (Q.map (fun y => y ^ Fintype.card K)).transpose) i j := by
  show hf (Fintype.card K) M (∑ k, Q i k • X k) (∑ l, Q j l • X l) = _
  rw [cg_hf_left]
  simp only [cg_hf_right K L, hX, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ l, ∑ k, Q i k * (Q j l ^ Fintype.card K * G k l) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem cg_map_mul (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] {m : ℕ}
    (A C : Matrix (Fin m) (Fin m) L) :
    (A * C).map (fun y => y ^ Fintype.card K) =
      A.map (fun y => y ^ Fintype.card K) * C.map (fun y => y ^ Fintype.card K) := by
  obtain ⟨p, hch⟩ := CharP.exists K
  obtain ⟨n, hp, hq⟩ := FiniteField.card K p
  haveI := Fact.mk hp
  haveI : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hfr : ∀ (s : Finset (Fin m)) (f : Fin m → L),
      (∑ i ∈ s, f i) ^ Fintype.card K = ∑ i ∈ s, f i ^ Fintype.card K := by
    intro s f
    rw [hq]
    first
    | exact sum_pow_char_pow s f
    | (haveI : ExpChar L p := ExpChar.prime hp
       have h := map_sum (iterateFrobenius L p n) f s
       simp only [iterateFrobenius_def] at h
       exact h)
    | (haveI : ExpChar L p := ExpChar.prime hp
       simp)
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [hfr]
  simp [mul_pow]

theorem repCountCongruenceInvariant : Congr := by
  intro K L _ _ _ _ _ _ n M W m B P hP
  have hdet : P.det ≠ 0 := hP.ne_zero
  have hq1 : 0 < Fintype.card K := Fintype.card_pos
  have hmap1 : (1 : Matrix (Fin m) (Fin m) L).map (fun y => y ^ Fintype.card K) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, zero_pow hq1.ne']
  have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hPinv' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hinj : Function.Injective (fun X : Fin m → Fin n → L => cgComb P X) := fun X Y h => by
    have h2 := congrArg (cgComb P⁻¹) h
    simpa [cg_comb_comb, hPinv', cg_comb_one] using h2
  have e : (P.map (fun y => y ^ Fintype.card K)).transpose *
      (P⁻¹.map (fun y => y ^ Fintype.card K)).transpose = 1 := by
    rw [← Matrix.transpose_mul, ← cg_map_mul K L, hPinv', hmap1, Matrix.transpose_one]
  have e2 : P⁻¹ * (P * B * (P.map (fun y => y ^ Fintype.card K)).transpose) *
      (P⁻¹.map (fun y => y ^ Fintype.card K)).transpose = B := by
    simp only [Matrix.mul_assoc, e, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hPinv', Matrix.one_mul]
  unfold cntT
  convert Set.ncard_image_of_injective _ hinj using 2
  ext Y
  constructor
  · rintro ⟨hW, hI, hG⟩
    refine ⟨cgComb P⁻¹ Y, ⟨cg_mem _ _ _ hW,
      cg_indep _ _ (Matrix.isUnit_nonsing_inv_det P hP).ne_zero hI, fun i j => ?_⟩, ?_⟩
    · rw [cg_gram K L M P⁻¹ _ Y hG, e2]
    · show cgComb P (cgComb P⁻¹ Y) = Y
      rw [cg_comb_comb, hPinv, cg_comb_one]
  · rintro ⟨X, ⟨hW, hI, hG⟩, rfl⟩
    exact ⟨cg_mem _ _ _ hW, cg_indep _ _ hdet hI, fun i j => cg_gram K L M P B X hG i j⟩

end DensInertW
end
end

section

open Finset Module

noncomputable section

namespace DensInertW

section form
variable {L : Type} [Field L] {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}

theorem val_add_left (x x' y : Fin n → L) : hf q M (x + x') y = hf q M x y + hf q M x' y := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem val_smul_left (c : L) (x y : Fin n → L) : hf q M (c • x) y = c * hf q M x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem val_sub_left (x x' y : Fin n → L) : hf q M (x - x') y = hf q M x y - hf q M x' y := by
  simp only [hf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem val_smul_right (x : Fin n → L) (c : L) (y : Fin n → L) :
    hf q M x (c • y) = c ^ q * hf q M x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

def valL (q : ℕ) (M : Matrix (Fin n) (Fin n) L) (y : Fin n → L) : (Fin n → L) →ₗ[L] L where
  toFun x := hf q M x y
  map_add' x x' := val_add_left x x' y
  map_smul' c x := by simp only [val_smul_left, smul_eq_mul, RingHom.id_apply]

theorem valL_apply (y x : Fin n → L) : valL q M y x = hf q M x y := rfl

def valPerp (q : ℕ) (M : Matrix (Fin n) (Fin n) L) (W : Submodule L (Fin n → L))
    (e : Fin n → L) : Submodule L (Fin n → L) :=
  (LinearMap.ker ((valL q M e).domRestrict W)).map W.subtype

theorem mem_valPerp {W : Submodule L (Fin n → L)} {e v : Fin n → L} :
    v ∈ valPerp q M W e ↔ v ∈ W ∧ hf q M v e = 0 := by
  simp only [valPerp, Submodule.mem_map, LinearMap.mem_ker, LinearMap.domRestrict_apply,
    valL_apply, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hv, h⟩
    exact ⟨⟨v, hv⟩, h, rfl⟩

theorem finrank_valPerp {W : Submodule L (Fin n → L)} {e : Fin n → L} (he : e ∈ W)
    (hb : hf q M e e ≠ 0) : finrank L (valPerp q M W e) + 1 = finrank L W := by
  have hsurj : LinearMap.range ((valL q M e).domRestrict W) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    refine ⟨⟨(t / hf q M e e) • e, W.smul_mem _ he⟩, ?_⟩
    simp only [LinearMap.domRestrict_apply, valL_apply, val_smul_left]
    exact div_mul_cancel₀ t hb
  have h := LinearMap.finrank_range_add_finrank_ker ((valL q M e).domRestrict W)
  rw [hsurj, finrank_top, finrank_self] at h
  rw [valPerp, Submodule.finrank_map_subtype_eq]
  omega

end form

section formK
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] {n : ℕ}
  {M : Matrix (Fin n) (Fin n) L}

theorem val_add_right (x y y' : Fin n → L) :
    hf (Fintype.card K) M x (y + y') =
      hf (Fintype.card K) M x y + hf (Fintype.card K) M x y' := by
  simp only [hf, Pi.add_apply, frob_add, mul_add, Finset.sum_add_distrib]

theorem val_symm [Fintype L] (h2 : finrank K L = 2) (hM : IsHerm (Fintype.card K) M)
    (x y : Fin n → L) : hf (Fintype.card K) M y x = (hf (Fintype.card K) M x y) ^ Fintype.card K := by
  unfold hf
  rw [frob_sum]
  simp_rw [frob_sum, mul_pow, frob_frob h2]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [← hM]
  ring

theorem val_fixed [Fintype L] (h2 : finrank K L = 2) (hM : IsHerm (Fintype.card K) M)
    (x : Fin n → L) : (hf (Fintype.card K) M x x) ^ Fintype.card K = hf (Fintype.card K) M x x :=
  (val_symm h2 hM x x).symm

theorem val_aniso [Fintype L] (h2 : finrank K L = 2) (hM : IsHerm (Fintype.card K) M)
    {W : Submodule L (Fin n → L)} (hW : NonDeg (Fintype.card K) M W) (hne : W ≠ ⊥) :
    ∃ e ∈ W, hf (Fintype.card K) M e e ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨v, hv, hwv⟩ : ∃ v ∈ W, hf (Fintype.card K) M w v ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (hW w hw h)
  obtain ⟨c, hc⟩ := exists_trace_ne_zero h2 _ (pow_ne_zero (Fintype.card K) hwv)
  apply hc
  have h := hcon (w + c • v) (W.add_mem hw (W.smul_mem c hv))
  simp only [val_add_left, val_add_right, val_smul_left, val_smul_right] at h
  rw [hcon w hw, hcon v hv, val_symm h2 hM w v] at h
  rw [mul_pow, frob_frob h2]
  linear_combination h

theorem val_expand [Fintype L] (h2 : finrank K L = 2) (hM : IsHerm (Fintype.card K) M)
    (e w : Fin n → L) (hwe : hf (Fintype.card K) M w e = 0) (l : L) :
    hf (Fintype.card K) M (l • e + w) (l • e + w) =
      l ^ (Fintype.card K + 1) * hf (Fintype.card K) M e e + hf (Fintype.card K) M w w := by
  have hq := one_lt_q (K := K)
  have hew : hf (Fintype.card K) M e w = 0 := by
    rw [val_symm h2 hM w e, hwe, zero_pow (by omega)]
  simp only [val_add_left, val_add_right, val_smul_left, val_smul_right, hwe, hew]
  ring

theorem nondeg_valPerp [Fintype L] (h2 : finrank K L = 2) (hM : IsHerm (Fintype.card K) M)
    {W : Submodule L (Fin n → L)} (hW : NonDeg (Fintype.card K) M W) {e : Fin n → L}
    (he : e ∈ W) (hb : hf (Fintype.card K) M e e ≠ 0) :
    NonDeg (Fintype.card K) M (valPerp (Fintype.card K) M W e) := by
  intro w hw hall
  rw [mem_valPerp] at hw
  apply hW w hw.1
  intro v hv
  have hv' : v - (hf (Fintype.card K) M v e / hf (Fintype.card K) M e e) • e ∈
      valPerp (Fintype.card K) M W e := by
    rw [mem_valPerp]
    refine ⟨W.sub_mem hv (W.smul_mem _ he), ?_⟩
    rw [val_sub_left, val_smul_left, div_mul_cancel₀ _ hb, sub_self]
  have h1 := hall _ hv'
  have hv2 : v = (hf (Fintype.card K) M v e / hf (Fintype.card K) M e e) • e +
      (v - (hf (Fintype.card K) M v e / hf (Fintype.card K) M e e) • e) := by abel
  rw [hv2, val_add_right, val_smul_right, hw.2, h1]
  ring

theorem val_fibre [Fintype L] [DecidableEq L] (h2 : finrank K L = 2) (b t : L) (hb : b ≠ 0)
    (hbq : b ^ Fintype.card K = b) (ht : t ^ Fintype.card K = t) :
    #{l : L | l ^ (Fintype.card K + 1) * b = t} = if t = 0 then 1 else Fintype.card K + 1 := by
  have e : (univ.filter fun l : L => l ^ (Fintype.card K + 1) * b = t) =
      univ.filter fun l : L => l ^ (Fintype.card K + 1) = t / b :=
    filter_congr (fun l _ => (eq_div_iff hb).symm)
  rw [e]
  split_ifs with h0
  · rw [h0, zero_div]
    exact card_norm_zero _
  · exact card_norm_fibre h2 _ (div_ne_zero h0 hb) (by rw [div_pow, ht, hbq])

end formK

end DensInertW
end
end
