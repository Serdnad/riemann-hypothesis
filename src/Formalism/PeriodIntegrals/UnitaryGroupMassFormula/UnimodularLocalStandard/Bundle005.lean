module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.CommOfBounded
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem rep_H_smul (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (ξ : ℂ) (z : m → ℂ) :
    stdH L m (ξ • z) (ξ • z) = ξ * conj ξ * stdH L m z z := by
  rw [LinearMap.map_smul₂, LinearMap.map_smulₛₗ]
  simp only [smul_eq_mul]
  ring

theorem rep_tau {m : Type} (a : ℕ) (b c : ℤ) (d : ℕ) (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ) {l : ℕ} (hl : l.Prime) :
    ∃ τ : ℂ, ∃ r s : ℤ, τ + conj τ = 1 ∧ τ * conj τ = (r : ℂ) / s ∧ ¬ (l : ℤ) ∣ s ∧
      ∀ v : m → ℂ, SatMem l Λ v → SatMem l Λ (τ • v) := by
  obtain ⟨hac, -, hd8, -⟩ := hOK
  obtain ⟨k, hk⟩ : ∃ k : ℤ, b = 2 * k + 1 := by
    rcases Int.even_or_odd b with ⟨j, hj⟩ | ⟨j, hj⟩
    · exfalso
      have h4 : (d : ℤ) = 4 * ((a : ℤ) * c - j * j) := by
        rw [hj] at hac
        linear_combination -hac
      generalize (a : ℤ) * c - j * j = t at h4
      omega
    · exact ⟨j, hj⟩
  have hadd := rep_theta_add_conj b d
  have hmul := rep_theta_mul_conj a b c d hac
  refine ⟨cmTheta b d - (k : ℂ), a * c - k * b + k ^ 2, 1, ?_, ?_, ?_, ?_⟩
  · rw [map_sub, map_intCast]
    have hb : (b : ℂ) = 2 * k + 1 := by
      rw [hk]
      push_cast
      ring
    linear_combination hadd + hb
  · rw [map_sub, map_intCast]
    push_cast
    rw [div_one]
    linear_combination hmul - (k : ℂ) * hadd
  · intro h
    have h1 := Int.le_of_dvd one_pos h
    have h2 := hl.one_lt
    omega
  · intro v hv
    unfold SatMem at hv ⊢
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨n, hn, ?_⟩
    rw [smul_comm, sub_smul, Int.cast_smul_eq_zsmul]
    exact Λ.sub_mem (hθ _ hnv) (Λ.zsmul_mem hnv k)

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem rep_coord (a : ℕ) (ha : 0 < a) (b : ℤ) (d : ℕ) (hd : 0 < d) (p q r s : ℝ)
    (h : (p : ℂ) * a + q * cmTheta b d = r * a + s * cmTheta b d) : p = r ∧ q = s := by
  have hs : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [cmTheta] at him hre
  have hqs : q = s := by
    rcases him with h1 | h1
    · exact h1
    · exact absurd h1 (by omega)
  subst hqs
  refine ⟨?_, rfl⟩
  have h3 : p * a = r * a := by linarith
  exact mul_right_cancel₀ ha'.ne' h3

theorem rep_prim_pair (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m) (h : KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀) :
    ∃ xt : m → ℂ, xt ∈ Λ ∧ (∀ j ∈ T, xt j = 0) ∧ ∃ yv : m → ℂ, yv ∈ Λ ∧ ∃ c₂ : ℤ,
      (stdH (cmL a b d ha hd lam hlam) m xt yv).im = c₂ ∧ ¬ (l : ℤ) ∣ c₂ := by
  obtain ⟨hOK, hΛ, hθ, h1, h2, hl, hQ, hi₀, hT⟩ := h
  set L := cmL a b d ha hd lam hlam with hL
  set f := fvec a b d lam x y i₀ with hfdef
  have hfstd : f ∈ stdLat L m := rep_fvec_mem a b d ha hd lam hlam m x y i₀
  unfold relIdx at h1 h2
  set Df := (Λ.relIndex (stdLat L m)).factorial with hDf
  set Nf := ((stdLat L m).relIndex Λ).factorial with hNf
  have hDfΛ : Df • f ∈ Λ :=
    (AddSubgroup.nsmul_mem_of_relIndex_ne_zero_of_dvd h2 hfstd
      (fun j hj hle => Nat.dvd_factorial hj hle)).1
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hlam0 := hlam

  set P : ℕ → Prop := fun j => ((l : ℂ) ^ j)⁻¹ • (Df • f) ∈ Λ with hPdef
  have hex : ∃ j, ¬ P j := by
    by_contra hall
    push_neg at hall
    set K : ℕ := Nf * Df with hK
    have hK0 : K ≠ 0 := Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
    have hdvd : ∀ j : ℕ, (l : ℤ) ^ j ∣ K * x ∧ (l : ℤ) ^ j ∣ K * y := by
      intro j
      have hmem : Nf • (((l : ℂ) ^ j)⁻¹ • (Df • f)) ∈ stdLat L m :=
        (AddSubgroup.nsmul_mem_of_relIndex_ne_zero_of_dvd h1 (hall j)
          (fun j hj hle => Nat.dvd_factorial hj hle)).1
      obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.mp (hmem i₀ (Set.mem_univ i₀))
      rw [rep_omega1, rep_omega2] at hpq
      simp only [hfdef, fvec, Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, smul_eq_mul, Pi.mul_apply, Pi.natCast_apply] at hpq
      have hlj : ((l : ℂ) ^ j) ≠ 0 := pow_ne_zero _ hl0
      have e : ((p : ℝ) : ℂ) * a + ((q : ℝ) : ℂ) * cmTheta b d =
          (((K * x : ℤ) / (l : ℝ) ^ j : ℝ) : ℂ) * a + (((K * y : ℤ) / (l : ℝ) ^ j : ℝ) : ℂ) * cmTheta b d := by
        apply mul_left_cancel₀ hlam
        push_cast
        rw [hK]; push_cast
        linear_combination hpq
      obtain ⟨ep, eq'⟩ := rep_coord a ha b d hd _ _ _ _ e
      have hlj' : ((l : ℝ) ^ j) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
      refine ⟨⟨p, ?_⟩, ⟨q, ?_⟩⟩
      · rw [eq_div_iff hlj'] at ep
        have : ((K * x : ℤ) : ℝ) = ((l ^ j * p : ℤ) : ℝ) := by push_cast at ep ⊢; linear_combination -ep
        exact_mod_cast this
      · rw [eq_div_iff hlj'] at eq'
        have : ((K * y : ℤ) : ℝ) = ((l ^ j * q : ℤ) : ℝ) := by push_cast at eq' ⊢; linear_combination -eq'
        exact_mod_cast this
    set J := K * (x.natAbs + y.natAbs) + 1
    have hJ : K * (x.natAbs + y.natAbs) < l ^ J :=
      lt_of_lt_of_le (Nat.lt_succ_self _) ((Nat.lt_pow_self hl.one_lt).le)
    have hx0 : K * x = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdvd J).1
      rw [Int.natAbs_mul, Int.natAbs_pow]; simp only [Int.natAbs_natCast]
      calc K * x.natAbs ≤ K * (x.natAbs + y.natAbs) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
        _ < l ^ J := hJ
    have hy0 : K * y = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdvd J).2
      rw [Int.natAbs_mul, Int.natAbs_pow]; simp only [Int.natAbs_natCast]
      calc K * y.natAbs ≤ K * (x.natAbs + y.natAbs) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
        _ < l ^ J := hJ
    have hK0' : (K : ℤ) ≠ 0 := by exact_mod_cast hK0
    have hx : x = 0 := (mul_eq_zero.mp hx0).resolve_left hK0'
    have hy : y = 0 := (mul_eq_zero.mp hy0).resolve_left hK0'
    apply hQ; rw [hx, hy]; simp
  classical
  set j₁ := Nat.find hex with hj₁
  have hP0 : P 0 := by simp only [hPdef, pow_zero, inv_one, one_smul]; exact hDfΛ
  have hj₁0 : j₁ ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hj₁, h0] at this
    exact this hP0
  have hPprev : P (j₁ - 1) := by
    have := Nat.find_min hex (show j₁ - 1 < Nat.find hex by omega)
    simpa using this
  have hPj : ¬ P j₁ := Nat.find_spec hex
  set xt := ((l : ℂ) ^ (j₁ - 1))⁻¹ • (Df • f) with hxt
  have hxtΛ : xt ∈ Λ := hPprev
  have hxtT : ∀ j ∈ T, xt j = 0 := by
    intro j hj
    have hne : j ≠ i₀ := by rintro rfl; exact hi₀ hj
    simp [hxt, hfdef, fvec, Pi.single_apply, hne]
  have hdiv : ((l : ℂ)⁻¹) • xt ∉ Λ := by
    rw [hxt, smul_smul, ← mul_inv, ← pow_succ', show j₁ - 1 + 1 = j₁ by omega]
    exact hPj
  refine ⟨xt, hxtΛ, hxtT, ?_⟩
  have hnd : ¬ ∀ yv ∈ Λ, ∃ k : ℤ, altE (stdH L m) ((l : ℂ)⁻¹ • xt) yv = k := by
    intro hall
    apply hdiv
    have : ((l : ℂ)⁻¹ • xt) ∈ dualLat (stdH L m) Λ := hall
    rw [hΛ] at this
    exact this
  push_neg at hnd
  obtain ⟨yv, hyv, hyk⟩ := hnd
  have hxtd : xt ∈ dualLat (stdH L m) Λ := by rw [hΛ]; exact hxtΛ
  obtain ⟨c₂, hc₂⟩ := hxtd yv hyv
  refine ⟨yv, hyv, c₂, hc₂, ?_⟩
  rintro ⟨t, rfl⟩
  apply hyk t
  simp only [altE] at hc₂ ⊢
  have e : (stdH L m ((l : ℂ)⁻¹ • xt) yv) = (((l : ℝ)⁻¹ : ℝ) : ℂ) * stdH L m xt yv := by
    simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]; push_cast; ring
  rw [e, Complex.im_ofReal_mul, hc₂]
  have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne_zero
  push_cast
  field_simp

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

def UnitVecRam : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m]
    [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (x0 y0 : ℤ) (T : Finset m) (i₀ : m),
    KeyHyps a b c d ha hd lam hlam m Λ d x0 y0 T i₀ →
    ∀ x : m → ℂ, SatMem d Λ x → (∀ j ∈ T, x j = 0) →
      (x = 0 ∨ ∃ p q : ℤ, ¬ (d : ℤ) ∣ p ∧ ¬ (d : ℤ) ∣ q ∧
        stdH (cmL a b d ha hd lam hlam) m x x = repKappa a b d ha hd lam hlam * p / q) →
    ∀ z₀ : m → ℂ, SatMem d Λ z₀ → (∀ j ∈ T, z₀ j = 0) → stdH (cmL a b d ha hd lam hlam) m z₀ x = 0 → z₀ ≠ 0 →
    ∃ y : m → ℂ, SatMem d Λ y ∧ (∀ j ∈ T, y j = 0) ∧ stdH (cmL a b d ha hd lam hlam) m y x = 0 ∧
      ∃ p q : ℤ, ¬ (d : ℤ) ∣ p ∧ ¬ (d : ℤ) ∣ q ∧
        stdH (cmL a b d ha hd lam hlam) m y y = repKappa a b d ha hd lam hlam * p / q

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}

lemma isKv_of_sat {m : Type*} [Fintype m] [DecidableEq m] {l : ℕ} (hl : l.Prime) {Λ : AddSubgroup (m → ℂ)}
    (h1 : relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λ ≠ 0) {v : m → ℂ} (hv : SatMem l Λ v) :
    IsKv b d lam v := by
  obtain ⟨n, hln, hn⟩ := hv
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hln (dvd_zero l)
  set S := stdLat (cmL a b d ha hd lam hlam) m
  have hmem : (S.addSubgroupOf Λ).index • (⟨n • v, hn⟩ : Λ) ∈ S.addSubgroupOf Λ :=
    AddSubgroup.nsmul_index_mem _ _
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_nsmul, smul_smul] at hmem
  have hN : (S.addSubgroupOf Λ).index * n ≠ 0 := mul_ne_zero h1 hn0
  exact isKv_of_nsmul hN (isKv_of_mem hmem)

lemma exists_isometry_memLocalizedAt_single (hkey : KeyRep) (hok : CmOK a b c d) (m : Type) [Fintype m] [DecidableEq m]
    (Λa : AddSubgroup (m → ℂ)) (hsd : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λa)
    (hθ : ∀ x ∈ Λa, cmTheta b d • x ∈ Λa)
    (h1 : relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λa ≠ 0)
    (h2 : relIdx Λa (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0)
    {l : ℕ} (hl : l.Prime) (x y : ℤ) (hQ : ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2) (T : Finset m) :
    ∃ g : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
      IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m) (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) ≠ 0 ∧
      relIdx (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 ∧
      ∀ j ∈ T, SatMem l (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d))) := by
  classical
  have himg : ∀ (g : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) (Λ : AddSubgroup (m → ℂ)), (∀ z ∈ Λ, cmTheta b d • z ∈ Λ) →
      ∀ z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ, cmTheta b d • z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ := by
    intro g Λ hΛ z hz
    obtain ⟨w, hw, rfl⟩ := (mem_imgLat_iff g Λ z).1 hz
    exact (mem_imgLat_iff g Λ _).2 ⟨_, hΛ w hw, map_smul g _ w⟩
  have hαK : (lam * ((x * a : ℂ) + y * cmTheta b d)) / lam = (x * a : ℂ) + y * cmTheta b d := by
    field_simp
  have hα0 : lam * ((x * a : ℂ) + y * cmTheta b d) ≠ 0 := by
    intro h0
    rw [alpha_eq (ha := ha) (hd := hd) (hlam := hlam)] at h0
    obtain ⟨hx0, hy0⟩ := LinearIndependent.pair_iff.1 (cmL a b d ha hd lam hlam).indep _ _ h0
    have hx : x = 0 := by exact_mod_cast hx0
    have hy : y = 0 := by exact_mod_cast hy0
    apply hQ
    simp [hx, hy]
  induction T using Finset.induction_on with
  | empty =>
    have hid : ∀ Λ : AddSubgroup (m → ℂ),
        imgLat ((LinearEquiv.refl ℂ (m → ℂ) : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ = Λ := by
      intro Λ
      ext z
      rw [mem_imgLat_iff]
      simp
    refine ⟨LinearEquiv.refl ℂ (m → ℂ), fun _ _ => rfl, ?_, ?_, by simp⟩
    · rw [hid, relIdx, AddSubgroup.relIndex_self]
      exact one_ne_zero
    · rw [hid, relIdx, AddSubgroup.relIndex_self]
      exact one_ne_zero
  | insert i₀ T hi₀ ih =>
    obtain ⟨g, hgI, hg1, hg2, hgT⟩ := ih
    have hc := comm_img g hg1 hg2 h1 h2
    have hsd' := selfDual_img _ g hgI hsd
    have hθ' := himg g Λa hθ
    obtain ⟨v, hvS, hvT, hvv⟩ := hkey a b c d ha hd lam hlam hok m _ hsd' hθ' hc.1 hc.2 l hl x y hQ T i₀ hi₀ hgT
    have hvK : IsKv b d lam v := isKv_of_sat hl hc.1 hvS
    have hK : ∀ s : ℂ, s = 1 ∨ s = -1 →
        IsK b d (s * (lam * ((x * a : ℂ) + y * cmTheta b d)) / lam) := by
      intro s hs
      have hb : IsK b d ((x * a : ℂ) + y * cmTheta b d) :=
        ⟨x * a, y, 1, one_ne_zero, by push_cast; ring⟩
      rcases hs with rfl | rfl
      · rw [one_mul, hαK]
        exact hb
      · rw [neg_one_mul, neg_div, hαK]
        exact isK_neg hb
    have hee : stdH (cmL a b d ha hd lam hlam) m (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d)))
        (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d))) ≠ 0 := by
      rw [stdH_kappa _ hlam, Finset.sum_eq_single i₀ (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
        (fun h => absurd (Finset.mem_univ i₀) h), Pi.single_eq_same]
      exact mul_ne_zero (kappa_ne _ hlam)
        (mul_ne_zero (div_ne_zero hα0 hlam) ((map_ne_zero _).2 (div_ne_zero hα0 hlam)))
    obtain ⟨s, hs, hne⟩ : ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
        stdH (cmL a b d ha hd lam hlam) m v v - stdH (cmL a b d ha hd lam hlam) m v
          (Pi.single i₀ (s * (lam * ((x * a : ℂ) + y * cmTheta b d)))) ≠ 0 := by
      by_cases h : stdH (cmL a b d ha hd lam hlam) m v v - stdH (cmL a b d ha hd lam hlam) m v
          (Pi.single i₀ (1 * (lam * ((x * a : ℂ) + y * cmTheta b d)))) = 0
      · refine ⟨-1, Or.inr rfl, ?_⟩
        rw [neg_one_mul, Pi.single_neg, map_neg]
        rw [one_mul, sub_eq_zero] at h
        rw [sub_neg_eq_add, ← h, ← two_mul, hvv]
        exact mul_ne_zero two_ne_zero hee
      · exact ⟨1, Or.inl rfl, h⟩
    have hss : s * s = 1 := by
      rcases hs with rfl | rfl <;> norm_num
    have hvv' : stdH (cmL a b d ha hd lam hlam) m v v =
        stdH (cmL a b d ha hd lam hlam) m (Pi.single i₀ (s * (lam * ((x * a : ℂ) + y * cmTheta b d))))
          (Pi.single i₀ (s * (lam * ((x * a : ℂ) + y * cmTheta b d)))) := by
      rw [hvv]
      rcases hs with rfl | rfl
      · simp only [one_mul]
      · simp only [neg_one_mul, Pi.single_neg, map_neg, LinearMap.neg_apply, neg_neg]
    obtain ⟨σ, hσI, hσ1, hσ2, hσv, hσfix⟩ :=
      qrefl_to hok v _ hvv' hne hvK (isKv_single (hK s hs) i₀)
    refine ⟨g.trans σ, isom_trans _ g σ hgI hσI, ?_, ?_, ?_⟩
    · rw [imgLat_trans]
      exact (comm_img σ hσ1 hσ2 hg1 hg2).1
    · rw [imgLat_trans]
      exact (comm_img σ hσ1 hσ2 hg1 hg2).2
    · intro j hj
      rw [imgLat_trans]
      rcases Finset.mem_insert.1 hj with rfl | hjT
      · obtain ⟨n, hln, hn⟩ := hvS
        refine ⟨n, hln, (mem_imgLat_iff σ _ _).2 ⟨s • n • v, ?_, ?_⟩⟩
        · rcases hs with rfl | rfl
          · rwa [one_smul]
          · rw [neg_one_smul]
            exact AddSubgroup.neg_mem _ hn
        · rw [map_smul, map_nsmul, hσv, smul_comm, ← Pi.single_smul', smul_eq_mul, ← mul_assoc, hss, one_mul]
      · obtain ⟨n, hln, hn⟩ := hgT j hjT
        refine ⟨n, hln, (mem_imgLat_iff σ _ _).2 ⟨_, hn, ?_⟩⟩
        rw [map_nsmul, hσfix]
        apply stdH_single_zero
        have hne' : j ≠ i₀ := fun h => hi₀ (h ▸ hjT)
        simp [hvT j hjT, Pi.single_eq_of_ne hne']

theorem stepB_of_key (hkey : KeyRep) : StepB := by
  intro a b c d ha hd lam hlam hok m _ _ Λa hsd hθ h1 h2 l hl
  obtain ⟨x, y, hQ⟩ := exists_good_form hok hl
  obtain ⟨g, hgI, hg1, hg2, hgT⟩ := exists_isometry_memLocalizedAt_single hkey hok m Λa hsd hθ h1 h2 hl x y hQ Finset.univ
  have hc := comm_img g hg1 hg2 h1 h2
  have hsd' := selfDual_img _ g hgI hsd
  have hθ' : ∀ z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa, cmTheta b d • z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := (mem_imgLat_iff g Λa z).1 hz
    exact (mem_imgLat_iff g Λa _).2 ⟨_, hθ w hw, map_smul g _ w⟩
  obtain ⟨n, hln, hn⟩ := sat_std_of_all hok hl x y hQ _ hsd' hθ' (fun j => hgT j (Finset.mem_univ j))
  refine ⟨g, hgI, hc.1, ?_, hc.2⟩
  intro hdvd
  have hfi : ((stdLat (cmL a b d ha hd lam hlam) m).addSubgroupOf
      (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa)).FiniteIndex := ⟨hc.1⟩
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card' l hdvd
  have hnq : n • q = 0 := by
    induction q using QuotientAddGroup.induction_on with
    | H w =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
        AddSubgroup.coe_nsmul]
      exact hn w w.2
  have h := addOrderOf_dvd_of_nsmul_eq_zero hnq
  rw [hq] at h
  exact hln h

theorem target_of_key (hkey : KeyRep) : PI.UnimodLocStd := target_of (stepB_of_key hkey) stepC

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end
