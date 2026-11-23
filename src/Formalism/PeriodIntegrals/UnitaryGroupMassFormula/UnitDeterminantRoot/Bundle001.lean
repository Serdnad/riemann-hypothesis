module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobalLUnit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI

theorem unitDetRoot_of (h1 : DetInK) (h2 : LocalStd) (h3 : GlobalLUnit) (h4 : NormOne)
    (h5 : RootStep) (h6 : ConjMem) (h7 : ConjLUnit) : PI.UnitDetRoot := by
  intro a b c d ha hd lam hlam hOK m _ _ Λa hSD hθ hi1 hi2
  have hH : Hyp a b c d ha hd lam hlam m Λa := ⟨hOK, hSD, hθ, hi1, hi2⟩
  obtain ⟨γ, hγK, hγ0, n, hn, hγ⟩ := h3 a b c d ha hd lam hlam m Λa hH
  have hγc0 : conj γ ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hγ0
  have hβK : γ / conj γ ∈ KF b d := div_mem hγK (h6 b d γ hγK)
  have hββ : γ / conj γ * conj (γ / conj γ) = 1 := by
    rw [map_div₀, Complex.conj_conj]
    field_simp
  obtain ⟨κ, hκN, hκalg, hκσ⟩ := h5 a b c d hOK (γ / conj γ) hβK hββ (4 * n) (by omega)
  refine ⟨κ, ?_, hκalg, hκσ, ?_⟩
  · rintro rfl
    rw [zero_pow (by omega), eq_comm, inv_eq_zero, div_eq_zero_iff] at hκN
    exact hκN.elim hγ0 hγc0
  · intro l _ ι δ hIso hidx1 hnl hidx2
    have hA : admitted a b d ha hd lam hlam m Λa δ := ⟨hIso, hidx1, hidx2⟩
    have hEq := h2 a b c d ha hd lam hlam m Λa hH l δ hA hnl
    have hU := hγ l δ hA hEq
    have n1 := h4 l ι _ hU
    have n2 := h4 l ι _ (h7 l _ hU)
    obtain ⟨-, hdd⟩ := h1 a b c d ha hd lam hlam m Λa hH δ hA
    set D := LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) with hD
    have hD0 : D ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hdd
      exact zero_ne_one hdd
    have hDc : conj D = D⁻¹ := eq_inv_of_mul_eq_one_right hdd
    have hu0 : 0 < ‖ι D‖ := norm_pos_iff.mpr ((map_ne_zero ι).mpr hD0)
    have hDc0 : conj D ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hD0
    have n1' : ‖ι γ‖ = ‖ι D‖ ^ n := by
      have e : γ = (γ / D ^ n) * D ^ n := by field_simp
      rw [e, map_mul, norm_mul, n1, one_mul, map_pow, norm_pow]
    have n2' : ‖ι (conj γ)‖ = ‖ι D‖⁻¹ ^ n := by
      have e : conj γ = conj (γ / D ^ n) * (conj D) ^ n := by
        rw [map_div₀, map_pow]
        field_simp
      rw [e, map_mul, norm_mul, n2, one_mul, map_pow, norm_pow, hDc, map_inv₀, norm_inv]
    have e3 : ‖ι κ‖ ^ (4 * n) = ‖ι (conj γ)‖ / ‖ι γ‖ := by
      rw [← norm_pow, ← map_pow, hκN, inv_div, map_div₀, norm_div]
    have ht : (‖ι κ‖ ^ 2 * ‖ι D‖) ^ (2 * n) = 1 := by
      rw [mul_pow, ← pow_mul, show 2 * (2 * n) = 4 * n by ring, e3, n1', n2', inv_pow]
      field_simp
      ring
    exact (pow_eq_one_iff_of_nonneg (by positivity) (by omega)).mp ht

end PI.UnitaryGroupMassFormula.UnitDetRoot
end
end

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI

lemma det_mem_of_entries {m : Type} [Fintype m] [DecidableEq m] {S : IntermediateField ℚ ℂ}
    (U : Matrix m m ℂ) (h : ∀ i j, U i j ∈ S) : U.det ∈ S := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

lemma theta_mem (b : ℤ) (d : ℕ) : UnitDetRootDefs.cmTheta b d ∈ KF b d :=
    IntermediateField.mem_adjoin_simple_self ℚ (UnitDetRootDefs.cmTheta b d)

lemma single_mem_stdLat {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [DecidableEq m] (j : m) :
    Pi.single j (lam * a) ∈ UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m := by
  rw [UnitDetRootDefs.stdLat, AddSubgroup.mem_pi]
  intro i _
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same]
    exact (UnitDetRootDefs.cmL a b d ha hd lam hlam).ω₁_mem_lattice
  · rw [Pi.single_eq_of_ne h]
    exact zero_mem _

lemma entries_mem {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [Fintype m] [DecidableEq m] {Λa : AddSubgroup (m → ℂ)}
    (hH : Hyp a b c d ha hd lam hlam m Λa) {δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)} (hA : admitted a b d ha hd lam hlam m Λa δ)
    (i j : m) : LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) i j ∈ KF b d := by
  have he : Pi.single j (lam * a) ∈ UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m :=
    single_mem_stdLat j
  obtain ⟨n1, hn1, -, h1⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hH.2.2.2.2 he
  have h2 : (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (n1 • Pi.single j (lam * a)) ∈
      UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa :=
    AddSubgroup.mem_map_of_mem _ h1.1
  obtain ⟨n2, hn2, -, h3⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hA.2.1 h2
  have h4 := (AddSubgroup.mem_inf.mp h3).1
  rw [UnitDetRootDefs.stdLat, AddSubgroup.mem_pi] at h4
  have h5 := h4 i (Set.mem_univ _)
  rw [Submodule.mem_toAddSubgroup, PeriodPair.mem_lattice] at h5
  obtain ⟨p, q, hpq⟩ := h5
  have hs : Pi.single j (lam * (a : ℂ)) = (lam * (a : ℂ)) • Pi.single j (1 : ℂ) := by
    ext k
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hs, map_nsmul, map_smul, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    nsmul_eq_mul, nsmul_eq_mul] at hpq
  change (p : ℂ) * (lam * a) + q * (lam * UnitDetRootDefs.cmTheta b d) = _ at hpq
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hN : (n2 : ℂ) * n1 * a ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hn2.ne') (by exact_mod_cast hn1.ne')) ha0
  have hM : LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) i j =
      ((p : ℂ) * a + q * UnitDetRootDefs.cmTheta b d) / ((n2 : ℂ) * n1 * a) := by
    rw [LinearMap.toMatrix'_apply, eq_div_iff hN]
    apply mul_left_cancel₀ hlam
    simp only [LinearEquiv.coe_coe] at hpq ⊢
    linear_combination -hpq
  rw [hM]
  exact div_mem (add_mem (mul_mem (intCast_mem _ _) (natCast_mem _ _))
    (mul_mem (intCast_mem _ _) (theta_mem b d)))
    (mul_mem (mul_mem (natCast_mem _ _) (natCast_mem _ _)) (natCast_mem _ _))

private lemma stdH_apply_lemma (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (z w : m → ℂ) :
    UnitDetRootDefs.stdH L m z w = ((UnitDetRootDefs.area L : ℝ) : ℂ)⁻¹ * ∑ i, z i * conj (w i) := by
  simp only [UnitDetRootDefs.stdH, UnitDetRootDefs.matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
    ring
  · intro j _ hji
    rw [if_neg (Ne.symm hji)]
    ring
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma unitary_det {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [Fintype m] [DecidableEq m] {δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)}
    (hiso : UnitDetRootDefs.IsIsom (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m)
      (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))) :
    LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) * conj (LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))) = 1 := by
  have hA0 : ((UnitDetRootDefs.area (UnitDetRootDefs.cmL a b d ha hd lam hlam) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, UnitDetRootDefs.area, abs_ne_zero]
    change (conj (lam * (a : ℂ)) * (lam * UnitDetRootDefs.cmTheta b d)).im ≠ 0
    have e : conj (lam * (a : ℂ)) * (lam * UnitDetRootDefs.cmTheta b d) =
        ((Complex.normSq lam * a : ℝ) : ℂ) * UnitDetRootDefs.cmTheta b d := by
      rw [map_mul, Complex.conj_natCast]
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      ring
    rw [e, Complex.im_ofReal_mul]
    have hθ : (UnitDetRootDefs.cmTheta b d).im = Real.sqrt d / 2 := by
      simp [UnitDetRootDefs.cmTheta]
    rw [hθ]
    have h1 : 0 < Complex.normSq lam := Complex.normSq_pos.mpr hlam
    have h2 : (0 : ℝ) < a := by exact_mod_cast ha
    have h3 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    exact (mul_pos (mul_pos h1 h2) (by positivity)).ne'
  have hU : (LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))).transpose *
      (LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))).map (starRingEnd ℂ) = 1 := by
    ext k l
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Matrix.map_apply, LinearMap.toMatrix'_apply]
    have h := hiso (Pi.single k 1) (Pi.single l 1)
    rw [stdH_apply_lemma, stdH_apply_lemma] at h
    rw [mul_left_cancel₀ (inv_ne_zero hA0) h]
    rw [Finset.sum_eq_single k (fun i _ hik => by rw [Pi.single_eq_of_ne hik, zero_mul])
      (fun hk => absurd (Finset.mem_univ k) hk), Pi.single_eq_same, one_mul, Pi.single_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  have hd' := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd'
  rw [← LinearMap.det_toMatrix', RingHom.map_det, RingHom.mapMatrix_apply]
  exact hd'

theorem detInK : DetInK := by
  intro a b c d ha hd lam hlam m _ _ Λa hH δ hA
  refine ⟨?_, unitary_det hA.1⟩
  rw [← LinearMap.det_toMatrix']
  exact det_mem_of_entries _ (entries_mem hH hA)

end PI.UnitaryGroupMassFormula.UnitDetRoot
end
end

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI

section Basic

variable {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}

lemma cmL_ω₁ : (UnitDetRootDefs.cmL a b d ha hd lam hlam).ω₁ = lam * a := by simp [UnitDetRootDefs.cmL, UnitDetRootDefs.scalePair, UnitDetRootDefs.cmPair]

lemma cmL_ω₂ : (UnitDetRootDefs.cmL a b d ha hd lam hlam).ω₂ = lam * UnitDetRootDefs.cmTheta b d := by simp [UnitDetRootDefs.cmL, UnitDetRootDefs.scalePair, UnitDetRootDefs.cmPair]

lemma mem_cmL {x : ℂ} :
    x ∈ (UnitDetRootDefs.cmL a b d ha hd lam hlam).lattice ↔ ∃ p q : ℤ, x = lam * ((p : ℂ) * a + (q : ℂ) * UnitDetRootDefs.cmTheta b d) := by
  rw [PeriodPair.mem_lattice, cmL_ω₁, cmL_ω₂]
  constructor
  · rintro ⟨p, q, h⟩; exact ⟨p, q, by rw [← h]; ring⟩
  · rintro ⟨p, q, h⟩; exact ⟨p, q, by rw [h]; ring⟩

lemma mem_stdLat {m : Type} {L : PeriodPair} {x : m → ℂ} : x ∈ UnitDetRootDefs.stdLat L m ↔ ∀ i, x i ∈ L.lattice := by
  simp [UnitDetRootDefs.stdLat, AddSubgroup.mem_pi]

lemma theta_re' : (UnitDetRootDefs.cmTheta b d).re = (b : ℝ) / 2 := by simp [UnitDetRootDefs.cmTheta]

lemma theta_im' : (UnitDetRootDefs.cmTheta b d).im = Real.sqrt d / 2 := by simp [UnitDetRootDefs.cmTheta]

lemma area_cmL : UnitDetRootDefs.area (UnitDetRootDefs.cmL a b d ha hd lam hlam) = Complex.normSq lam * a * (Real.sqrt d / 2) := by
  rw [UnitDetRootDefs.area, cmL_ω₁, cmL_ω₂]
  have hpos : 0 < Complex.normSq lam * a * (Real.sqrt d / 2) := by
    have h1 : 0 < Complex.normSq lam := Complex.normSq_pos.mpr hlam
    have h2 : (0 : ℝ) < a := by exact_mod_cast ha
    have h3 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    positivity
  have e : (conj (lam * a) * (lam * UnitDetRootDefs.cmTheta b d)).im = Complex.normSq lam * a * (Real.sqrt d / 2) := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.natCast_re,
      Complex.natCast_im, theta_re', theta_im', Complex.normSq_apply, map_mul, map_natCast]
    ring
  rw [e, abs_of_pos hpos]

lemma pair_im (p q p' q' : ℤ) :
    ((lam * ((p : ℂ) * a + (q : ℂ) * UnitDetRootDefs.cmTheta b d)) * conj (lam * ((p' : ℂ) * a + (q' : ℂ) * UnitDetRootDefs.cmTheta b d))).im
      = Complex.normSq lam * a * (Real.sqrt d / 2) * ((q * p' - p * q' : ℤ) : ℝ) := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
    Complex.intCast_re, Complex.intCast_im, Complex.natCast_re, Complex.natCast_im, theta_re', theta_im',
    Complex.normSq_apply, map_mul, map_add, map_intCast, map_natCast]
  push_cast
  ring

end Basic

lemma stdH_apply {m : Type} [Fintype m] [DecidableEq m] (L : PeriodPair) (x y : m → ℂ) :
    UnitDetRootDefs.stdH L m x y = ∑ i, x i * ((UnitDetRootDefs.area L : ℝ) : ℂ)⁻¹ * conj (y i) := by
  simp [UnitDetRootDefs.stdH, UnitDetRootDefs.matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply, Matrix.one_apply]

lemma altE_stdH {m : Type} [Fintype m] [DecidableEq m] (L : PeriodPair) (x y : m → ℂ) :
    UnitDetRootDefs.altE (UnitDetRootDefs.stdH L m) x y = ∑ i, (x i * conj (y i)).im / UnitDetRootDefs.area L := by
  rw [UnitDetRootDefs.altE, stdH_apply, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm (x i), mul_assoc, ← Complex.ofReal_inv, Complex.im_ofReal_mul]
  field_simp

lemma stdLat_le_dual {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [Fintype m] [DecidableEq m] {x : m → ℂ} (hx : x ∈ UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) :
    x ∈ UnitDetRootDefs.dualLat (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) := by
  intro y hy
  rw [mem_stdLat] at hx hy
  choose p q hpq using fun i => (mem_cmL (ha := ha) (hd := hd) (hlam := hlam)).mp (hx i)
  choose p' q' hpq' using fun i => (mem_cmL (ha := ha) (hd := hd) (hlam := hlam)).mp (hy i)
  refine ⟨∑ i, (q i * p' i - p i * q' i), ?_⟩
  rw [altE_stdH]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hpq i, hpq' i, pair_im, area_cmL]
  have h1 : 0 < Complex.normSq lam := Complex.normSq_pos.mpr hlam
  have h2 : (0 : ℝ) < a := by exact_mod_cast ha
  have h3 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  push_cast
  field_simp

lemma nsmul_relIdx_mem {V : Type*} [AddCommGroup V] (H K : AddSubgroup V) {x : V} (hx : x ∈ K) :
    (H.relIndex K) • x ∈ H := by
  have h := (H.addSubgroupOf K).nsmul_index_mem ⟨x, hx⟩
  rw [AddSubgroup.relIndex]
  simpa [AddSubgroup.mem_addSubgroupOf] using h

lemma altE_natsmul {V : Type*} [AddCommGroup V] [Module ℂ V] (H : UnitDetRootDefs.Sesq V) (k : ℕ) (x y : V) :
    UnitDetRootDefs.altE H ((k : ℂ) • x) y = UnitDetRootDefs.altE H x ((k : ℂ) • y) := by
  simp [UnitDetRootDefs.altE, LinearMap.map_smulₛₗ]

lemma mem_imgLat {m : Type} {δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)} {Λ : AddSubgroup (m → ℂ)} {z : m → ℂ} :
    z ∈ UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ ↔ δ.symm z ∈ Λ := by
  simp only [UnitDetRootDefs.imgLat, AddSubgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩; simpa using hw
  · intro h; exact ⟨δ.symm z, h, by simp⟩

theorem localStd : LocalStd := by
  intro a b c d ha hd lam hlam m _ _ Λa hH l _ δ hA hl
  obtain ⟨hok, hsd, hth, hi1, hi2⟩ := hH
  obtain ⟨hiso, hc1, hc2⟩ := hA
  set Lt := UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m with hLt
  set H := UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m with hHdef
  set M := UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa with hM
  set k := UnitDetRootDefs.relIdx Lt M with hk
  have partA : ∀ x ∈ M, (k : ℂ) • x ∈ Lt := by
    intro x hx
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_relIdx_mem Lt M hx
  have hdualM : ∀ z, z ∈ UnitDetRootDefs.dualLat H M → z ∈ M := by
    intro z hz
    rw [hM, mem_imgLat]
    rw [UnitDetRootDefs.IsSelfDual] at hsd
    rw [← hsd]
    intro y hy
    have hδy : δ y ∈ M := by rw [hM, mem_imgLat]; simpa using hy
    obtain ⟨n, hn⟩ := hz (δ y) hδy
    refine ⟨n, ?_⟩
    rw [← hn, UnitDetRootDefs.altE, UnitDetRootDefs.altE, ← hiso (δ.symm z) y]
    simp
  refine ⟨k, hl, fun x hx => hdualM _ ?_, partA⟩
  intro y hy
  rw [altE_natsmul]
  exact stdLat_le_dual hx _ (partA y hy)

end PI.UnitaryGroupMassFormula.UnitDetRoot
end
end
