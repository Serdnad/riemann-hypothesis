module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle660
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle010
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle078
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle079
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

section

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem relIndex_pi_univ {ι : Type} [Fintype ι] {G : Type} [AddCommGroup G] (I J : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ J).relIndex (AddSubgroup.pi Set.univ I) = ∏ a, (J a).relIndex (I a) := by
  classical
  let φ : (AddSubgroup.pi Set.univ I) →+ ∀ a, (I a ⧸ (J a).addSubgroupOf (I a)) :=
    { toFun := fun x a => QuotientAddGroup.mk (⟨(x : ι → G) a, x.2 a (Set.mem_univ a)⟩ : I a)
      map_zero' := by funext a; rfl
      map_add' := fun x y => by funext a; rfl }
  have hsurj : Function.Surjective φ := by
    intro c
    choose y hy using fun a => QuotientAddGroup.mk_surjective (c a)
    refine ⟨⟨fun a => (y a : G), fun a _ => (y a).2⟩, ?_⟩
    funext a
    show QuotientAddGroup.mk (⟨(y a : G), _⟩ : I a) = c a
    rw [← hy a]
  have hker : φ.ker = (AddSubgroup.pi Set.univ J).addSubgroupOf (AddSubgroup.pi Set.univ I) := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h a _
      have := congrFun h a
      simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, QuotientAddGroup.eq_zero_iff,
        AddSubgroup.mem_addSubgroupOf] at this
      exact this
    · intro h
      funext a
      simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, QuotientAddGroup.eq_zero_iff,
        AddSubgroup.mem_addSubgroupOf]
      exact h a (Set.mem_univ a)
  unfold AddSubgroup.relIndex AddSubgroup.index
  rw [← hker, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv, Nat.card_pi]

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def scaledInt (c : L) : AddSubgroup L := (intL L).toAddSubgroup.comap (AddMonoidHom.mulLeft c)

theorem mem_scaledInt {c x : L} : x ∈ scaledInt c ↔ c * x ∈ intL L := Iff.rfl

theorem mulLeft_surjective {c : L} (hc : c ≠ 0) : Function.Surjective (AddMonoidHom.mulLeft c) :=
  fun y => ⟨c⁻¹ * y, by simp [AddMonoidHom.mulLeft, mul_inv_cancel_left₀ hc]⟩

theorem mulLeft_injective {c : L} (hc : c ≠ 0) : Function.Injective (AddMonoidHom.mulLeft c) :=
  fun x y h => mul_left_cancel₀ hc h

theorem relIndex_scaledInt {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (d : ℕ) :
    (intL L).toAddSubgroup.relIndex (scaledInt (ϖ ^ d)) = q ^ (2 * d) := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hϖ : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega

  have h1 : (intL L).toAddSubgroup.relIndex (scaledInt ϖ) = q ^ 2 := by
    have hm : ((scaledInt ϖ).map (AddMonoidHom.mulLeft ϖ)) = (intL L).toAddSubgroup :=
      AddSubgroup.map_comap_eq_self_of_surjective (mulLeft_surjective h0) _
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ (mulLeft_injective h0), hm]
    exact intIndex L ϖ σ q hU
  induction d with
  | zero =>
    have : scaledInt (ϖ ^ 0) = (intL L).toAddSubgroup := by
      ext x; simp [mem_scaledInt]
    rw [this, AddSubgroup.relIndex_self]; simp
  | succ d ih =>
    have hle1 : (intL L).toAddSubgroup ≤ scaledInt (ϖ ^ d) := fun x hx =>
      mul_mem (pow_mem hϖ d) hx
    have hle2 : scaledInt (ϖ ^ d) ≤ scaledInt (ϖ ^ (d + 1)) := fun x hx => by
      rw [mem_scaledInt] at hx ⊢
      rw [pow_succ, mul_comm _ ϖ, mul_assoc]
      exact mul_mem hϖ hx
    have hc : scaledInt (ϖ ^ (d + 1)) = (scaledInt ϖ).comap (AddMonoidHom.mulLeft (ϖ ^ d)) := by
      ext x
      simp only [AddSubgroup.mem_comap, mem_scaledInt]
      rw [pow_succ, mul_comm _ ϖ, mul_assoc]
      exact Iff.rfl
    have hstep : (scaledInt (ϖ ^ d)).relIndex (scaledInt (ϖ ^ (d + 1))) = q ^ 2 := by
      rw [hc, scaledInt, AddSubgroup.relIndex_comap,
        AddSubgroup.map_comap_eq_self_of_surjective (mulLeft_surjective (pow_ne_zero d h0)), h1]
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2, ih, hstep]
    ring

end

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem intV_vecMul {r : Fin n → L} {M : Matrix (Fin n) (Fin n) L} (hr : r ∈ intV L n) (hM : IsInt M) :
    r ᵥ* M ∈ intV L n := by
  rw [mem_intV] at hr ⊢
  intro j
  simp only [Matrix.vecMul, dotProduct]
  exact Subring.sum_mem _ fun i _ => mul_mem (hr i) (hM i j)

theorem preLat_diagonal (ϖ : L) (d : Fin n → ℕ) :
    preLat (Matrix.diagonal fun i => ϖ ^ d i) = AddSubgroup.pi Set.univ fun i => scaledInt (ϖ ^ d i) := by
  ext r
  rw [mem_preLat, AddSubgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, mem_scaledInt, Matrix.vecMul_diagonal, mul_comm (r _)]

theorem latIndex_diagonal {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (d : Fin n → ℕ) :
    (intV L n).relIndex (preLat (Matrix.diagonal fun i => ϖ ^ d i)) = q ^ (2 * ∑ i, d i) := by
  rw [preLat_diagonal, intV, relIndex_pi_univ]
  simp only [relIndex_scaledInt hU, Finset.mul_sum, Finset.prod_pow_eq_pow_sum]

theorem relIndex_preLat_mul {A D a a' : Matrix (Fin n) (Fin n) L} (ha : IsInt a) (ha' : IsInt a') (ea : a' * a = 1)
    (hpre : ∀ r, r ∈ preLat A ↔ r ᵥ* a ∈ preLat D) :
    (intV L n).relIndex (preLat A) = (intV L n).relIndex (preLat D) := by
  have ea2 : a * a' = 1 := mul_eq_one_comm.1 ea
  let f : (Fin n → L) →+ (Fin n → L) := a.vecMulLinear.toAddMonoidHom
  have hf : ∀ r, f r = r ᵥ* a := fun r => rfl
  have hsurj : Function.Surjective f := fun y => ⟨y ᵥ* a', by rw [hf, Matrix.vecMul_vecMul, ea, Matrix.vecMul_one]⟩
  have h1 : preLat A = (preLat D).comap f := by
    ext r; rw [AddSubgroup.mem_comap, hf]; exact hpre r
  have h2 : intV L n = (intV L n).comap f := by
    ext r
    rw [AddSubgroup.mem_comap, hf]
    refine ⟨fun h => intV_vecMul h ha, fun h => ?_⟩
    have := intV_vecMul h ha'
    rwa [Matrix.vecMul_vecMul, ea2, Matrix.vecMul_one] at this
  rw [h1, h2, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hsurj, ← h2]

end

theorem latIndex_of_smith : Smith → LatIndex := by
  intro hS L _ _ ϖ σ q n hU A k hA hdet
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hA0 : A.det ≠ 0 := fun h => by
    rw [h, map_zero] at hdet; exact WithZero.exp_ne_zero hdet.symm
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩ := hS L ϖ n hv A hA0
  set D := Matrix.diagonal fun i => ϖ ^ d i with hD
  have ea2 : a * a' = 1 := mul_eq_one_comm.1 ea
  have eb2 : b' * b = 1 := mul_eq_one_comm.1 eb

  have hDint : IsInt D := by
    have : D = a' * (a * D * b) * b' := by
      rw [show a' * (a * D * b) * b' = (a' * a) * D * (b * b') by simp only [Matrix.mul_assoc], ea, eb,
        Matrix.one_mul, Matrix.mul_one]
    rw [this]
    exact (ha'.mul hA).mul hb'
  have hvz : ∀ z : ℤ, Valued.v (ϖ ^ z) = WithZero.exp (-z) := fun z => by
    rw [map_zpow₀, hv, ← WithZero.exp_zsmul]; congr 1; simp
  have hd : ∀ i, 0 ≤ d i := fun i => by
    have h := hDint i i
    rw [hD, Matrix.diagonal_apply_eq] at h
    have h' : Valued.v (ϖ ^ d i) ≤ 1 := h
    rw [hvz, ← WithZero.exp_zero, WithZero.exp_le_exp] at h'
    omega
  set e : Fin n → ℕ := fun i => (d i).toNat with he
  have hde : ∀ i, d i = (e i : ℤ) := fun i => (Int.toNat_of_nonneg (hd i)).symm
  have hDe : D = Matrix.diagonal fun i => ϖ ^ e i := by
    rw [hD]; congr 1; funext i; rw [hde i, zpow_natCast]

  have hk : k = ∑ i, e i := by
    have hva : Valued.v a.det = 1 := v_det_eq_one ha ha' ea2
    have hvb : Valued.v b.det = 1 := v_det_eq_one hb hb' eb
    rw [Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, hva, hvb, one_mul, mul_one, hDe,
      Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum, ← zpow_natCast, hvz, WithZero.exp_inj] at hdet
    exact_mod_cast (neg_inj.1 hdet).symm

  have hpre : ∀ r, r ∈ preLat (a * D * b) ↔ r ᵥ* a ∈ preLat D := fun r => by
    show r ᵥ* (a * D * b) ∈ intV L n ↔ (r ᵥ* a) ᵥ* D ∈ intV L n
    rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
    refine ⟨fun h => ?_, fun h => intV_vecMul h hb⟩
    have := intV_vecMul h hb'
    rwa [Matrix.vecMul_vecMul, eb, Matrix.vecMul_one] at this
  rw [relIndex_preLat_mul ha ha' ea hpre, hDe, latIndex_diagonal hU, hk]

end GlobalTheory.InertZeta
end
end

section

noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem blk_mono {i j : Fin (N + 2)} (h : j ≤ i) : blk N j ≤ blk N i := by
  rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;> simp
  all_goals first
    | (rw [Fin.le_iff_val_le_val] at h; have := i'.2; simp at h; omega)
    | (rw [Fin.le_iff_val_le_val] at h; simp at h; done)
    | (rw [Fin.le_iff_val_le_val] at h; simp at h; omega)

theorem levi_ext {ϖ : L} {a : ℤ} {g₀ : GU σ N} {m m' : GU σ (N + 2)} (h : IsLeviElt ϖ a g₀ m)
    (h' : IsLeviElt ϖ a g₀ m') : m = m' := by
  apply mat_injective
  funext i j
  by_cases hij : blk N i = blk N j
  · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;>
      simp at hij
    · rw [h.2.1, h'.2.1]
    · rw [h.2.2.2 i' j', h'.2.2.2 i' j']
    · rw [h.2.2.1, h'.2.2.1]
  · rw [h.1 i j hij, h'.1 i j hij]

theorem levi_mul {ϖ : L} (hϖ : ϖ ≠ 0) {a a' : ℤ} {g g' : GU σ N} {m m' : GU σ (N + 2)} (h : IsLeviElt ϖ a g m)
    (h' : IsLeviElt ϖ a' g' m') : IsLeviElt ϖ (a + a') (g * g') (m * m') := by
  have e : ∀ i j, mat (m * m') i j = mat m i 0 * mat m' 0 j + ∑ l, mat m i (mid l) * mat m' (mid l) j +
      mat m i (Fin.last (N + 1)) * mat m' (Fin.last (N + 1)) j := fun i j => by
    rw [mat_mul, Matrix.mul_apply, sum_idx (fun l => mat m i l * mat m' l j)]
  have z : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := h.1
  have z' : ∀ i j, blk N i ≠ blk N j → mat m' i j = 0 := h'.1
  refine ⟨mul_mem h.1 h'.1, ?_, ?_, fun i j => ?_⟩
  · rw [e, h.2.1, h'.2.1, z 0 (Fin.last (N + 1)) (by simp), zero_mul, add_zero,
      Finset.sum_eq_zero (fun l _ => by rw [z 0 (mid l) (by simp), zero_mul]), add_zero, zpow_add₀ hϖ]
  · rw [e, h.2.2.1, h'.2.2.1, z (Fin.last (N + 1)) 0 (by simp), zero_mul, zero_add,
      Finset.sum_eq_zero (fun l _ => by rw [z (Fin.last (N + 1)) (mid l) (by simp), zero_mul]), zero_add,
      neg_add, zpow_add₀ hϖ]
  · rw [e, z (mid i) 0 (by simp), z (mid i) (Fin.last (N + 1)) (by simp), zero_mul, zero_mul, zero_add, add_zero,
      mat_mul, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h.2.2.2, h'.2.2.2]

end

theorem sphTrans (hL : LeviExists) : SphTrans := by
  intro L _ _ ϖ σ q N r hU hr α φ φ₀ hα hsph h1 hsph₀ h10 a g₀ m hm u hu
  have hϖ : ϖ ≠ 0 := by
    intro h; have := hU.2.2.2.1; rw [h, Valuation.map_zero] at this; exact WithZero.zero_ne_coe this
  obtain ⟨b₀, k₀, hb₀, hk₀, rfl⟩ := P.fIwasawa_iwasawa σ hU.1 hU.2.1 g₀
  obtain ⟨mb, hmb⟩ := hL L ϖ σ q N hU a b₀
  obtain ⟨mk, hmk⟩ := hL L ϖ σ q N hU 0 k₀
  have hm' : m = mb * mk := by
    have := levi_mul hϖ hmb hmk
    rw [add_zero] at this
    exact levi_ext hm this
  subst hm'

  have hmkK : mk ∈ KU σ (N + 2) := by
    rw [mem_KU_iff hU.2.1]
    intro i j
    by_cases hij : blk N i = blk N j
    · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;>
        simp at hij
      · rw [hmk.2.1, zpow_zero]; exact one_mem _
      · rw [hmk.2.2.2 i' j']; exact P.fSatake_K_int hk₀ i' j'
      · rw [hmk.2.2.1, neg_zero, zpow_zero]; exact one_mem _
    · rw [hmk.1 i j hij]; exact zero_mem _
  set v := mk * u * mk⁻¹ with hv
  have hvR : v ∈ radQ σ N := (leviRad L σ (N + 2) (blk N) hU.2.1 mk hmk.1 u hu).1
  have hdiag : ∀ i j, blk N j ≤ blk N i → mat (mb * v) i j = mat mb i j :=
    fun i j h => levi_mul_rad_apply hmb.1 hvR h
  have hB : IsBorelU (mb * v) := by
    intro i j hji
    show mat (mb * v) i j = 0
    rw [hdiag i j (blk_mono hji.le)]
    by_cases hij : blk N i = blk N j
    · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;>
        simp at hij
      · exact absurd hji (lt_irrefl _)
      · rw [hmb.2.2.2 i' j']
        exact hb₀ i' j' (by rw [Fin.lt_iff_val_lt_val] at hji ⊢; simpa using hji)
      · exact absurd hji (lt_irrefl _)
    · exact hmb.1 i j hij
  have e1 : mb * mk * u = (mb * v) * 1 * mk := by rw [hv]; group
  have hφ : φ (mb * mk * u) = chiDeltaU q α (mb * v) := by
    rw [e1, hsph _ _ _ hB hmkK, h1, mul_one]
  have hφ₀ : φ₀ (b₀ * k₀) = chiDeltaU q (Fin.tail α) b₀ := by
    have := hsph₀ b₀ 1 k₀ hb₀ hk₀
    rwa [mul_one, h10, mul_one] at this
  rw [hφ, hφ₀]
  unfold chiDeltaU
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [dite_eq_left (by simp)]
    have e0 : (⟨(0 : Fin (r + 1)).val, by simp⟩ : Fin (N + 2)) = 0 := rfl
    rw [e0]
    show α 0 ^ ordL (mat (mb * v) 0 0) * (q : ℂ) ^ (-ordL (mat (mb * v) 0 0) * (((N + 2 : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ))) = _
    rw [hdiag 0 0 le_rfl, hmb.2.1, P.fSatake_ord_zpow hU.2.2.2.1]
    congr 2
    push_cast
    ring
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hiN : i.val < N := by have := i.2; omega
    rw [dite_eq_left (by simp; omega), dite_eq_left hiN]
    have ei : (⟨(Fin.succ i).val, by simp; omega⟩ : Fin (N + 2)) = mid ⟨i.val, hiN⟩ := by
      ext; simp
    rw [ei]
    show α i.succ ^ ordL (mat (mb * v) (mid ⟨i.val, hiN⟩) (mid ⟨i.val, hiN⟩)) *
      (q : ℂ) ^ (-ordL (mat (mb * v) (mid ⟨i.val, hiN⟩) (mid ⟨i.val, hiN⟩)) *
        (((N + 2 : ℕ) : ℤ) - 1 - 2 * ((i.succ.val : ℕ) : ℤ))) = _
    rw [hdiag _ _ le_rfl, hmb.2.2.2]
    show _ = Fin.tail α i ^ ordL (mat b₀ ⟨i.val, hiN⟩ ⟨i.val, hiN⟩) *
      (q : ℂ) ^ (-ordL (mat b₀ ⟨i.val, hiN⟩ ⟨i.val, hiN⟩) * ((N : ℤ) - 1 - 2 * ((i.val : ℕ) : ℤ)))
    congr 2
    simp only [Fin.val_succ]
    push_cast
    ring

end GlobalTheory.InertZeta

end
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.adelic_quotient_compact_of_bounded_matrices : GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.CompactOfMatBounded := by
  first | exact @GlobalTheory.RegSS.CptQuot.compactOfMatBounded | exact GlobalTheory.RegSS.CptQuot.compactOfMatBounded | (intros; apply GlobalTheory.RegSS.CptQuot.compactOfMatBounded <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.centraliser_points_bounded_of_normOne_bounded : GlobalTheory.RegSS.MatOfNormBounded := by
  first | exact @GlobalTheory.RegSS.MatBd.matOfNormBounded | exact GlobalTheory.RegSS.MatBd.matOfNormBounded | (intros; apply GlobalTheory.RegSS.MatBd.matOfNormBounded <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.cyclicVector_semilocal_of_cyclicVector_field : GlobalTheory.RegSS.CyclicField → GlobalTheory.RegSS.CyclicSemilocal := by
  first | exact @GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField | exact GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField | (intros; apply GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.regularSemisimple_centralizer_points_of_commutant_adjoint : GlobalTheory.RegSS.PointsCommutant → GlobalTheory.RegSS.PointsAdjoint → GlobalTheory.RegSS.PointsCentraliser := by
  first | exact @GlobalTheory.RegSS.pointsCentraliser_of_commutant_of_adjoint | exact GlobalTheory.RegSS.pointsCentraliser_of_commutant_of_adjoint | (intros; apply GlobalTheory.RegSS.pointsCentraliser_of_commutant_of_adjoint <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.regularSemisimple_selfAdjointPart_tensor_bijective : GlobalTheory.RegSS.PlusTensorBijective := by
  first | exact @GlobalTheory.RegSS.plusTensorBijective | exact GlobalTheory.RegSS.plusTensorBijective | (intros; apply GlobalTheory.RegSS.plusTensorBijective <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.regularSemisimple_tensor_involution_adjoint : GlobalTheory.RegSS.PointsAdjoint := by
  first | exact @GlobalTheory.RegSS.pointsAdjoint | exact GlobalTheory.RegSS.pointsAdjoint | (intros; apply GlobalTheory.RegSS.pointsAdjoint <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.adelic_quotient_not_compact_of_split_idempotent : GlobalTheory.RegSS.IdempotentDet → GlobalTheory.RegSS.NotCompactOfIdempotent := by
  first | exact @GlobalTheory.RegSS.notCompactOfIdempotent_of | exact GlobalTheory.RegSS.notCompactOfIdempotent_of | (intros; apply GlobalTheory.RegSS.notCompactOfIdempotent_of <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.finiteAlgebraAdelicLattice_proof : GlobalTheory.RegSS.TensorLattice := by
  first | exact @GlobalTheory.RegSSLattice.tensorLattice | exact GlobalTheory.RegSSLattice.tensorLattice | (intros; apply GlobalTheory.RegSSLattice.tensorLattice <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.normOfUnitBounded_of_tensorLattice' : GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.NormOfUnitBounded := by
  first | exact @GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice | exact GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice | (intros; apply GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.normOne_small_multiples_by_cocompact_subgroup : GlobalTheory.RegSS.NormOnePacking := by
  first | exact @GlobalTheory.RegSS.normOnePacking | exact GlobalTheory.RegSS.normOnePacking | (intros; apply GlobalTheory.RegSS.normOnePacking <;> assumption)
end
