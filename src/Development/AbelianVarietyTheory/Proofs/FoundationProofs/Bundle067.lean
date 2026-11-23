module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle026
public import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open GlobalTheory.KummerEisensteinGalois

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

lemma eisF_pow_subst {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (e : ℕ) (a₁ a₂ : ℤ) (n : ℕ) :
    eisF j M (ζ ^ e) a₁ a₂ n = eisF j M ζ a₁ ((e : ℤ) * a₂) n := by
  have h : ∀ x : ℤ, (ζ ^ e) ^ x = ζ ^ ((e : ℤ) * x) := by
    intro x; rw [← zpow_natCast, ← zpow_mul]
  simp only [eisF, const0, coefPos, h, mul_assoc, mul_neg]

lemma smF_pow_subst {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (e : ℕ) (a₁ a₂ : ℤ) (n : ℕ) :
    smF c j M (ζ ^ e) a₁ a₂ n = smF c j M ζ a₁ ((e : ℤ) * a₂) n := by
  simp only [smF, eisF_pow_subst]
  rw [mul_left_comm]

lemma eisF_congr {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (hζ : IsPrimitiveRoot ζ M) (hM : 0 < M)
    (a₁ a₂ a₂' : ℤ) (h : a₂ ≡ a₂' [ZMOD M]) (n : ℕ) :
    eisF j M ζ a₁ a₂ n = eisF j M ζ a₁ a₂' n := by
  have h1 : ζ ^ a₂ = ζ ^ a₂' := zpow_congr_of_modEq hζ hM h
  simp only [eisF, const0, coefPos, zpow_neg, zpow_mul, h1]

lemma smF_congr {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (hζ : IsPrimitiveRoot ζ M) (hM : 0 < M)
    (a₁ a₂ a₂' : ℤ) (h : a₂ ≡ a₂' [ZMOD M]) (n : ℕ) :
    smF c j M ζ a₁ a₂ n = smF c j M ζ a₁ a₂' n := by
  simp only [smF, eisF_congr j M ζ hζ hM a₁ a₂ a₂' h, eisF_congr j M ζ hζ hM _ _ _ (h.mul_left c)]

def diagOneUnit {R : Type} [CommRing R] (b : Rˣ) : GL (Fin 2) R :=
  ⟨Matrix.diagonal ![1, (b : R)], Matrix.diagonal ![1, ((b⁻¹ : Rˣ) : R)],
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp,
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp⟩

lemma diagOneUnit_mul {R : Type} [CommRing R] (a b : Rˣ) : diagOneUnit a * diagOneUnit b = diagOneUnit (a * b) := by
  ext i j
  simp only [diagOneUnit, Matrix.GeneralLinearGroup.coe_mul, Units.val_mk, Matrix.diagonal_mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp

lemma diagOneUnit_one {R : Type} [CommRing R] : diagOneUnit (1 : Rˣ) = 1 := by
  ext i j
  simp only [diagOneUnit, Units.val_mk, Matrix.GeneralLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

lemma coe_mul_diagOneUnit {R : Type} [CommRing R] (γ : GL (Fin 2) R) (b : Rˣ) (i : Fin 2) :
    ((γ * diagOneUnit b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i 0 = (γ : Matrix (Fin 2) (Fin 2) R) i 0 ∧
    ((γ * diagOneUnit b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i 1 = (γ : Matrix (Fin 2) (Fin 2) R) i 1 * b := by
  simp [diagOneUnit, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_diagonal]

lemma det_mul_diagOneUnit {R : Type} [CommRing R] (γ : GL (Fin 2) R) (b : Rˣ) :
    ((γ * diagOneUnit b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det = (γ : Matrix (Fin 2) (Fin 2) R).det * b := by
  simp [diagOneUnit, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two]

lemma smF_rowT_subst {K : Type} [Field K] [CharZero K] (N p m : ℕ) [NeZero p] (c : ℤ) (j : ℕ) (ζ : K)
    (hζ : IsPrimitiveRoot ζ (N * p ^ m)) (hN : 0 < N) (γ : GL (Fin 2) (ZMod (p ^ m))) (b : (ZMod (p ^ m))ˣ) (e : ℕ)
    (he : ((e : ℕ) : ZMod (p ^ m)) = b ∧ ((e : ℕ) : ZMod N) = 1) (i : Fin 2) (w : ℤ × ℤ) :
    smF c j (N * p ^ m) (ζ ^ e) (rowT N p m γ i w).1 (rowT N p m γ i w).2 =
      smF c j (N * p ^ m) ζ (rowT N p m (γ * diagOneUnit b) i w).1 (rowT N p m (γ * diagOneUnit b) i w).2 := by
  funext n
  rw [smF_pow_subst]
  have h1 : (rowT N p m (γ * diagOneUnit b) i w).1 = (rowT N p m γ i w).1 := by
    simp [rowT, (coe_mul_diagOneUnit γ b i).1]
  rw [h1]
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  apply smF_congr c j _ ζ hζ (by positivity)
  simp only [rowT, (coe_mul_diagOneUnit γ b i).2]
  rw [Int.modEq_iff_dvd]
  have h2 : ((p ^ m : ℕ) : ℤ) ∣ (e : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) i 1).val : ℤ) -
      ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) i 1 * b).val : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [he.1, mul_comm]
  have h3 : (N : ℤ) ∣ (e : ℤ) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [he.2, sub_self]
  obtain ⟨u, hu⟩ := h2
  obtain ⟨v, hv⟩ := h3
  refine ⟨-(u + w.2 * v), ?_⟩
  push_cast at hu ⊢
  linear_combination (-(N : ℤ)) * hu - ((p : ℤ) ^ m * w.2) * hv

theorem psum_galois_unitPiece : ∀ (N p m k : ℕ) [NeZero p] (K : Type) [Field K] [CharZero K]
    (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' : ℤ × ℤ)
    (ζ : K) (β : (ZMod (p ^ m))ˣ → ℕ), p.Prime → 0 < N → Nat.Coprime p N → 1 ≤ m → IsPrimitiveRoot ζ (N * p ^ m) →
    (∀ b, ((β b : ℕ) : ZMod (p ^ m)) = b ∧ ((β b : ℕ) : ZMod N) = 1) →
    ∀ r : ℕ, ∑ b : (ZMod (p ^ m))ˣ, ψ b * pieceT N p m m k (1 : DirichletCharacter K (p ^ m)) c d w w' (ζ ^ β b)
        ((unitSet p m).filter (fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))).det = 1)) r =
      pieceT N p m m k ψ c d w w' ζ (unitSet p m) r := by
  intro N p m k _ K _ _ ψ c d w w' ζ β _ hN _ _ hζ hβ r
  unfold pieceT
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun x => x.2 * diagOneUnit x.1)
    (fun γ => (Matrix.GeneralLinearGroup.det γ, γ * diagOneUnit (Matrix.GeneralLinearGroup.det γ)⁻¹))
  · rintro ⟨b, γ⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, unitSet, Finset.mem_univ, true_and] at h ⊢
    simp only [(coe_mul_diagOneUnit γ b 0).1, (coe_mul_diagOneUnit γ b 1).1]
    exact h.1
  · intro γ h
    simp only [Finset.mem_product, Finset.mem_filter, unitSet, Finset.mem_univ, true_and] at h ⊢
    simp only [(coe_mul_diagOneUnit γ _ 0).1, (coe_mul_diagOneUnit γ _ 1).1]
    refine ⟨h, ?_⟩
    rw [det_mul_diagOneUnit, ← Matrix.GeneralLinearGroup.val_det_apply, Units.mul_inv]
  · rintro ⟨b, γ⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h
    have hd : Matrix.GeneralLinearGroup.det (γ * diagOneUnit b) = b := by
      ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, det_mul_diagOneUnit, h.2, one_mul]
    simp only [hd, mul_assoc, diagOneUnit_mul, mul_inv_cancel, diagOneUnit_one, mul_one]
  · intro γ _
    simp only [mul_assoc, diagOneUnit_mul, inv_mul_cancel, diagOneUnit_one, mul_one]
  · rintro ⟨b, γ⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h
    dsimp only
    rw [smF_rowT_subst N p m c (k - 1) ζ hζ hN γ b (β b) (hβ b) 0 w,
      smF_rowT_subst N p m d 1 ζ hζ hN γ b (β b) (hβ b) 1 w', det_mul_diagOneUnit, h.2, one_mul,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, map_one, one_mul]
    ring

end GlobalTheory.KummerEisensteinGalois
end

section

noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

namespace GlobalTheory.HeckeInt

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem exists_pre_exp [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ∃ ω : Ω, ε ω = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hn : x.den ≠ 0 := x.den_nz
  haveI : NeZero ((x.den : ℕ) : Ω) := ⟨by exact_mod_cast hn⟩
  haveI : NeZero x.den := ⟨hn⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω x.den
  have hζ' := hζ.map_of_injective ε.injective
  have hz : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have hx : (x : ℂ) * (x.den : ℂ) = (x.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num x
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = (x.num : ℂ) * (2 * Real.pi * Complex.I) := by
      linear_combination (2 * Real.pi * Complex.I) * hx
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hz
  exact ⟨ζ ^ i, by rw [map_pow]; exact hi⟩

theorem eps_eOm [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) :=
  Function.invFun_eq (exists_pre_exp ε x)

theorem sub_coeff (ε : Ω →+* ℂ) (q : ℕ) (hq : 0 < q) (j : ℚ) (φ : HahnSeries ℚ Ω) (s : ℚ) :
    (sub ε 1 j (q : ℚ) φ).coeff s = eOm ε (s * j) * φ.coeff ((q : ℚ) * s) := by
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have h : (0 : ℚ) < 1 / (q : ℚ) := by positivity
  unfold sub scale
  rw [dite_eq_left h]
  have e : (OrderIso.mulLeft₀ (1 / (q : ℚ)) h).toOrderEmbedding ((q : ℚ) * s) = s := by
    simp only [RelIso.coe_toRelEmbedding, OrderIso.coe_toOrderEmbedding, OrderIso.mulLeft₀_apply]
    field_simp
  have key := HahnSeries.embDomain_coeff (f := (OrderIso.mulLeft₀ (1 / (q : ℚ)) h).toOrderEmbedding)
    (x := cm (fun r => eOm ε (r * j / (q : ℚ))) φ) (a := (q : ℚ) * s)
  rw [e] at key
  rw [key]
  simp only [cm]
  congr 2
  field_simp

theorem sum_eOm [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ) (hq : 0 < q) (s : ℚ) (hs : ((q : ℚ) * s).den = 1) :
    ∑ j ∈ Finset.range q, eOm ε (s * (j : ℚ)) = if s.den = 1 then (q : Ω) else 0 := by
  apply ε.injective
  have hz : ∀ j : ℕ, ε (eOm ε (s * (j : ℚ))) = (Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))) ^ j := by
    intro j
    rw [eps_eOm, ← Complex.exp_nat_mul]
    congr 1
    push_cast; ring

  rw [map_sum]
  simp only [hz]
  split_ifs with hd
  · have h1 : Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) = 1 := by
      have : (s : ℂ) = ((s.num : ℤ) : ℂ) := by
        have := Rat.coe_int_num_of_den_eq_one hd
        rw [← this]; push_cast; rfl
      rw [this, show 2 * (Real.pi : ℂ) * Complex.I * ((s.num : ℤ) : ℂ) = (s.num : ℂ) * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    simp [h1]
  · have hne : Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) ≠ 1 := by
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have hsn : (s : ℂ) = (n : ℂ) := by
        have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
        apply mul_left_cancel₀ h2
        linear_combination hn
      have : s = (n : ℚ) := by exact_mod_cast hsn
      exact hd (by rw [this]; rfl)
    have hpow : (Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))) ^ q = 1 := by
      rw [← Complex.exp_nat_mul]
      have hx : ((q : ℚ) * s : ℚ) = ((((q : ℚ) * s).num : ℤ) : ℚ) := (Rat.coe_int_num_of_den_eq_one hs).symm
      have hx' : (q : ℂ) * (s : ℂ) = ((((q : ℚ) * s).num : ℤ) : ℂ) := by exact_mod_cast hx
      rw [show (q : ℂ) * (2 * Real.pi * Complex.I * (s : ℂ)) = ((((q : ℚ) * s).num : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
        rw [← hx']; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [geom_sum_eq hne, hpow, sub_self, zero_div, map_zero]

theorem hq_coeff_of_int : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ), 0 < q → ∀ φ : HahnSeries ℚ Ω,
    (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → ∀ s : ℚ,
      (hq ε q φ).coeff s = if s.den = 1 then φ.coeff ((q : ℚ) * s) else 0 := by
  intro Ω _ _ _ ε q hq0 φ hφ s
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  unfold hq
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_sum, smul_eq_mul]
  simp only [GlobalTheory.HeckeInt.sub_coeff ε q hq0]
  rw [← Finset.sum_mul]
  by_cases hc : φ.coeff ((q : ℚ) * s) = 0
  · simp [hc]
  · rw [GlobalTheory.HeckeInt.sum_eOm ε q hq0 s (hφ _ hc)]
    have hqne : (q : Ω) ≠ 0 := by exact_mod_cast hq0.ne'
    split_ifs
    · field_simp
    · simp

end GlobalTheory.HeckeInt
end
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.K5.PDiv

open Polynomial

theorem prod_one_sub_pow_dvd {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (ζ : Ω) (hζ : IsIntegral (O0 p) ζ) (S : Finset Ω) (hS : ∀ μ ∈ S, ∃ i : ℕ, ζ ^ i = μ) :
    ∃ c : Ω, IsIntegral (O0 p) c ∧ ∏ μ ∈ S, (1 - μ) = (ζ - 1) ^ S.card * c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, isIntegral_one, by simp⟩
  | insert a S ha ih =>
    obtain ⟨c, hc, e⟩ := ih (fun μ hμ => hS μ (Finset.mem_insert_of_mem hμ))
    obtain ⟨i, rfl⟩ := hS _ (Finset.mem_insert_self _ _)
    refine ⟨-(∑ k ∈ Finset.range i, ζ ^ k) * c, ?_, ?_⟩
    · refine IsIntegral.mul (IsIntegral.neg ?_) hc
      have : (∑ k ∈ Finset.range i, ζ ^ k) ∈ integralClosure (O0 p) Ω :=
        Subalgebra.sum_mem _ fun k _ => Subalgebra.pow_mem _ hζ k
      exact this
    · rw [Finset.prod_insert ha, e, Finset.card_insert_of_notMem ha, pow_succ]
      have g := geom_sum_mul ζ i
      linear_combination ((ζ - 1) ^ S.card * c) * g

theorem pdiv : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    ∀ (T : Tower p Ω) (j s : ℕ), 1 ≤ j → s ≤ Nat.totient (p ^ j) →
      IsInt (p := p) ((p : Ω) / (T.ζ j - 1) ^ s) := by
  intro p _ Ω _ _ T j s hj hs
  classical
  have hprim := T.prim j
  have hpos : 0 < p ^ j := pow_pos (Fact.out : p.Prime).pos j
  have hζ : IsIntegral (O0 p) (T.ζ j) := ⟨X ^ (p ^ j) - C 1, monic_X_pow_sub_C 1 hpos.ne', by simp [hprim.pow_eq_one]⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hne : T.ζ (j' + 1) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact hprim.ne_one (Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt)
  have hp : (p : Ω) = ∏ μ ∈ primitiveRoots (p ^ (j' + 1)) Ω, (1 - μ) := by
    rw [← eval_one_cyclotomic_prime_pow (R := Ω) j', cyclotomic_eq_prod_X_sub_primitiveRoots hprim,
      eval_prod]
    simp
  obtain ⟨c, hc, e⟩ := prod_one_sub_pow_dvd (T.ζ (j' + 1)) hζ (primitiveRoots (p ^ (j' + 1)) Ω)
    (fun μ hμ => by
      have hμ' := (mem_primitiveRoots hpos).1 hμ
      obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hμ'.pow_eq_one
      exact ⟨i, hi⟩)
  rw [hprim.card_primitiveRoots] at e
  have key : (p : Ω) / (T.ζ (j' + 1) - 1) ^ s =
      (T.ζ (j' + 1) - 1) ^ (Nat.totient (p ^ (j' + 1)) - s) * c := by
    rw [div_eq_iff (pow_ne_zero _ hne), hp, e, mul_right_comm, ← pow_add, Nat.sub_add_cancel hs]
  rw [IsInt, key]
  exact IsIntegral.mul (IsIntegral.pow (IsIntegral.sub hζ isIntegral_one) _) hc

end GlobalTheory.K5.PDiv
end

section

open GlobalTheory.K5

private theorem mem_geoField_of_fixed_local {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω]
    [Algebra (O0 p) Ω] (h : IsClo p Ω) (x : Ω)
    (hx : ∀ g ∈ Ggeo (p := p) Ω, g x = x) :
    x ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {y : Ω | IsAlgZp (p := p) y}) := by
  haveI := h.clo
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  let F : Subfield Ω := Subfield.closure
    (Set.range (algebraMap (O0 p) Ω) ∪ {y : Ω | IsAlgZp (p := p) y})
  have hR : ∀ a : O0 p, algebraMap (O0 p) Ω a ∈ F := fun a =>
    Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  let f : O0 p →+* F := (algebraMap (O0 p) Ω).codRestrict F hR
  have hf : (algebraMap F Ω).comp f = algebraMap (O0 p) Ω := by ext; rfl
  have hfi : Function.Injective f := fun a b hab => h.inj (congrArg Subtype.val hab)
  have hAlg : Algebra.IsAlgebraic F Ω := ⟨fun a => by
    obtain ⟨P, hP0, hP⟩ := h.alg.isAlgebraic a
    refine ⟨P.map f, (Polynomial.map_ne_zero_iff hfi).2 hP0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hf, ← Polynomial.aeval_def, hP]⟩
  letI : Algebra.IsAlgebraic F Ω := hAlg
  haveI : IsAlgClosure F Ω := ⟨h.clo, hAlg⟩
  haveI : CharZero F := ⟨fun m n e => CharZero.cast_injective (congrArg Subtype.val e)⟩
  haveI : IsGalois F Ω := inferInstance
  have hbot : x ∈ (⊥ : IntermediateField F Ω) := by
    refine (InfiniteGalois.mem_bot_iff_fixed x).2 fun σ => ?_
    let τ : Ω ≃ₐ[O0 p] Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv)
      (fun a => σ.commutes ⟨_, hR a⟩)
    have hτ : τ ∈ Ggeo (p := p) Ω := fun y hy =>
      σ.commutes ⟨y, Subfield.subset_closure (Or.inr hy)⟩
    exact hx τ hτ
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hbot
  exact y.2


theorem _root_.GlobalTheory.T.geometric_fixed_mem_closure_finite_algZp : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ x : Ω, (∀ g ∈ Ggeo (p := p) Ω, g x = x) → ∃ S : Finset Ω, (∀ s ∈ S, IsAlgZp (p := p) s) ∧
    x ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)) := by
  intro p hp Ω hΩ hΩalg h x hx
  obtain ⟨S, hS, hxS⟩ := GlobalTheory.K5.GeoFix.exists_finset_of_mem_closure _ _
    (mem_geoField_of_fixed_local h x hx)
  exact ⟨S, fun s hs => hS hs, hxS⟩
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_level_emb_of_mem_adjoin_zeta_qq : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (w : On p n), 1 ≤ n ∧ IsEmb T n ι ∧ ι w = b ∧ ∀ w' : On p n, ι w' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  first | exact @GlobalTheory.K5.exists_level_of_mem_adjoin | exact GlobalTheory.K5.exists_level_of_mem_adjoin | (intros; apply GlobalTheory.K5.exists_level_of_mem_adjoin <;> assumption)
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.exists_basis_On_zeta_pow_mul_q_pow : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), ∃ b : Module.Basis (Fin (Nat.totient (p ^ n)) × Fin (p ^ n)) (O0 p) (On p n),
  ∀ i j, b (i, j) = xn p n ^ (i : ℕ) * yn p n ^ (j : ℕ) := by
  first | exact @GlobalTheory.K5.OnFree.on_free | exact GlobalTheory.K5.OnFree.on_free | (intros; apply GlobalTheory.K5.OnFree.on_free <;> assumption)
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.exists_mul_linearIndependent_algebraicOverPadicIntegers : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ y ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp (p := p) x},
    ∃ (n : ℕ) (a : Fin n → Ω) (f : Fin n → O0 p) (g : O0 p), (∀ i, IsAlgZp (p := p) (a i)) ∧
      LinearIndependent (O0 p) a ∧ g ≠ 0 ∧
      algebraMap (O0 p) Ω g * y = ∑ i, algebraMap (O0 p) Ω (f i) * a i := by
  exact @GlobalTheory.K5.algSpan_reprInd
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.prime_natCast_completed_laurent_ring : ∀ (p : ℕ) [Fact p.Prime], Prime (p : O0 p) := by
  first | exact @GlobalTheory.K5.prime_natCast_completedLaurentRing_of_prime | exact GlobalTheory.K5.prime_natCast_completedLaurentRing_of_prime | (intros; apply GlobalTheory.K5.prime_natCast_completedLaurentRing_of_prime <;> assumption)
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.exists_derivation_extend_padicLaurent_to_closure : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ D : Derivation ℤ (O0 p) (O0 p),
    ∃ E : Derivation ℤ Ω Ω, ∀ x, E (algebraMap (O0 p) Ω x) = algebraMap (O0 p) Ω (D x) := by
  first | exact @GlobalTheory.K5.DerExt.derivation_extend | exact GlobalTheory.K5.DerExt.derivation_extend | (intros; apply GlobalTheory.K5.DerExt.derivation_extend <;> assumption)
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.geometricGalois_dense_tau_pow_mul_fixing_qRoots : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo (p := p) Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ g ∈ Ggeo (p := p) Ω, ∀ S : Finset Ω, ∃ s : ℕ, ∃ h ∈ Ggeo (p := p) Ω ⊓ ⨅ n, Gn T n,
    ∀ x ∈ S, (τ ^ s * h) x = g x := by
  exact @GlobalTheory.K5.Dense.dense_tau_pow_mul
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ B → (∀ v, Fixes W A v → ∀ (ι : Type) [Fintype ι] (f : ι → X), (∀ i, f i ∈ B) → (∀ b ∈ B, ∃! i, b - f i ∈ A) → sumOp W A B v = ∑ i, W (f i) v ∧ idx A B = Fintype.card ι) ∧ (idx A B ≠ 0 → (∃ (n : ℕ) (f : Fin n → X), (∀ i, f i ∈ B) ∧ ∀ b ∈ B, ∃! i, b - f i ∈ A) ∧ (∀ v, Fixes W A v → Fixes W B (sumOp W A B v)) ∧ ∀ (c : ℂ) v, sumOp W A B (c • v) = c • sumOp W A B v) ∧ (B ≤ A → idx A B = 1 ∧ ∀ v, Fixes W A v → sumOp W A B v = v) := by
  first | exact @GlobalTheory.FinWeil.sumOp_transversal | exact GlobalTheory.FinWeil.sumOp_transversal | (intros; apply GlobalTheory.FinWeil.sumOp_transversal <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem cuspForm_cuspAll : ∀ (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (f : CuspForm Γ k), CuspAll k f := by
  intro Γ _ k f
  refine ⟨f.holo', fun c hc => ?_⟩
  rw [← Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (Γ : Subgroup (GL (Fin 2) ℝ))] at hc
  exact f.zero_at_cusps' hc

end GlobalTheory.HeckeFamilyMatrices
end
