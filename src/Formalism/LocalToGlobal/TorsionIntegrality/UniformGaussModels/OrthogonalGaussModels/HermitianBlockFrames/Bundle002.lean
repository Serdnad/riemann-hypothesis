module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Bundle001
public import Mathlib.NumberTheory.Padics.RingHoms
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
public import Mathlib.NumberTheory.Padics.Hensel
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem im_mul_conj_lattice (L : PeriodPair) {z w : ℂ} (hz : z ∈ L.lattice) (hw : w ∈ L.lattice) :
    ∃ k : ℤ, (z * conj w).im = k * (L.ω₁ * conj L.ω₂).im := by
  have hz' : z ∈ Submodule.span ℤ {L.ω₁, L.ω₂} := hz
  have hw' : w ∈ Submodule.span ℤ {L.ω₁, L.ω₂} := hw
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz'
  obtain ⟨c, e, rfl⟩ := Submodule.mem_span_pair.mp hw'
  refine ⟨a * e - b * c, ?_⟩
  simp only [zsmul_eq_mul, map_add (f := _), map_mul, map_intCast, Complex.add_im, Complex.mul_im,
    Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]
  push_cast
  ring

theorem im_div_area (L : PeriodPair) : ∃ e : ℤ, (L.ω₁ * conj L.ω₂).im / area L = e := by
  have h : (L.ω₁ * conj L.ω₂).im = -(conj L.ω₁ * L.ω₂).im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [h]
  unfold area
  rcases lt_trichotomy (conj L.ω₁ * L.ω₂).im 0 with ht | ht | ht
  · refine ⟨1, ?_⟩
    rw [abs_of_neg ht, div_self (neg_ne_zero.mpr ht.ne)]
    simp
  · exact ⟨0, by simp [ht]⟩
  · refine ⟨-1, ?_⟩
    rw [abs_of_pos ht, neg_div, div_self ht.ne']
    simp

theorem stdH_apply (L : PeriodPair) {N : Type*} [Fintype N] [DecidableEq N] (z w : N → ℂ) :
    stdH L N z w = ∑ i, z i * ((area L : ℝ) : ℂ)⁻¹ * conj (w i) := by
  simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem stdLat_int (L : PeriodPair) {N : Type*} [Fintype N] [DecidableEq N] {z w : N → ℂ}
    (hz : z ∈ stdLat L N) (hw : w ∈ stdLat L N) : ∃ k : ℤ, altE (stdH L N) z w = k := by
  have hzi : ∀ i, z i ∈ L.lattice := fun i =>
    (show ∀ i ∈ (Set.univ : Set N), z i ∈ L.lattice.toAddSubgroup from hz) i (Set.mem_univ i)
  have hwi : ∀ i, w i ∈ L.lattice := fun i =>
    (show ∀ i ∈ (Set.univ : Set N), w i ∈ L.lattice.toAddSubgroup from hw) i (Set.mem_univ i)
  choose k hk using fun i => im_mul_conj_lattice L (hzi i) (hwi i)
  obtain ⟨e, he⟩ := im_div_area L
  refine ⟨(∑ i, k i) * e, ?_⟩
  have hterm : ∀ i, (z i * ((area L : ℝ) : ℂ)⁻¹ * conj (w i)).im =
      (k i : ℝ) * ((L.ω₁ * conj L.ω₂).im / area L) := by
    intro i
    rw [show z i * ((area L : ℝ) : ℂ)⁻¹ * conj (w i) = (((area L)⁻¹ : ℝ) : ℂ) * (z i * conj (w i)) by
      push_cast; ring, Complex.im_ofReal_mul, hk i]
    ring
  unfold altE
  rw [stdH_apply, Complex.im_sum, Finset.sum_congr rfl (fun i _ => hterm i), he, ← Finset.sum_mul]
  push_cast
  ring

theorem idx_smul_mem {n : Type} [Fintype n] [DecidableEq n] (L : PeriodPair) (Λ : AddSubgroup (n → ℂ))
    (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) {y : Fin 4 × n → ℂ} (hy : y ∈ pow4 Λ) :
    relIdx (stdLat L (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) • g₁ y
      ∈ stdLat L (Fin 4 × n) := by
  have hmem : g₁ y ∈ imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) :=
    AddSubgroup.mem_map.mpr ⟨y, hy, rfl⟩
  have h1 := AddSubgroup.nsmul_index_mem ((stdLat L (Fin 4 × n)).addSubgroupOf
    (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) ⟨g₁ y, hmem⟩
  rw [AddSubgroup.mem_addSubgroupOf] at h1
  simpa [relIdx, AddSubgroup.relIndex] using h1

def emb {n : Type} (a : Fin 4) (v : n → ℂ) : Fin 4 × n → ℂ := fun x => if x.1 = a then v x.2 else 0

theorem emb_mem {n : Type} {Λ : AddSubgroup (n → ℂ)} (a : Fin 4) {v : n → ℂ} (hv : v ∈ Λ) :
    emb a v ∈ pow4 Λ := by
  intro b
  by_cases h : b = a
  · subst h
    convert hv using 1
    funext i
    simp [slice, emb]
  · convert Λ.zero_mem using 1
    funext i
    simp [slice, emb, h]

theorem matrixForm_diagBlocks_blockEmbed {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (x : Fin 4 × n → ℂ) (a : Fin 4)
    (v : n → ℂ) : matH (blk4 h) x (emb a v) = matH h (slice a x) v := by
  simp only [matH, LinearMap.mk₂'ₛₗ_apply]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · simp [blk4, emb, slice]
    · intro c _ hc
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [emb, hc]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hc : c = a
    · subst hc
      simp [blk4, hb]
    · simp [emb, hc]
  · simp

theorem mem_latticeFourfold_of_mem_dualLattice {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (hΛ : IsSelfDual (matH h) Λ) {x : Fin 4 × n → ℂ} (hx : x ∈ dualLat (matH (blk4 h)) (pow4 Λ)) :
    x ∈ pow4 Λ := by
  have hx' : ∀ y ∈ pow4 Λ, ∃ m : ℤ, altE (matH (blk4 h)) x y = (m : ℝ) := hx
  intro a
  rw [← hΛ]
  show ∀ y ∈ Λ, ∃ m : ℤ, altE (matH h) (slice a x) y = (m : ℝ)
  intro v hv
  obtain ⟨m, hm⟩ := hx' (emb a v) (emb_mem a hv)
  refine ⟨m, ?_⟩
  unfold altE at hm ⊢
  rw [matrixForm_diagBlocks_blockEmbed] at hm
  exact hm

theorem idx_smul_symm_mem {n : Type} [Fintype n] [DecidableEq n] (L : PeriodPair) (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (hΛ : IsSelfDual (matH h) Λ) (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hIso : IsIsom (matH (blk4 h)) (stdH L (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
    {z : Fin 4 × n → ℂ} (hz : z ∈ stdLat L (Fin 4 × n)) :
    g₁.symm (relIdx (stdLat L (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) • z)
      ∈ pow4 Λ := by
  apply mem_latticeFourfold_of_mem_dualLattice h Λ hΛ
  show ∀ y ∈ pow4 Λ, ∃ m : ℤ, altE (matH (blk4 h)) (g₁.symm (relIdx (stdLat L (Fin 4 × n))
    (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) • z)) y = (m : ℝ)
  intro y hy
  obtain ⟨k, hk⟩ := stdLat_int L hz (idx_smul_mem L Λ g₁ hy)
  refine ⟨k, ?_⟩
  unfold altE at hk ⊢
  rw [← hIso]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_nsmul, LinearMap.smul_apply] at hk ⊢
  exact hk

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
open Formalism.L2.Th1.Top.FrP

variable (l : ℕ) [Fact l.Prime]

private theorem norm_alg_lemma (x : ℚ_[l]) : ‖algebraMap ℚ_[l] ℂ_[l] x‖ = ‖x‖ := by
  first
  | exact norm_algebraMap' ℂ_[l] x

private theorem cont_alg_lemma_2 : Continuous (algebraMap ℚ_[l] ℂ_[l]) :=
  (AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[l] ℂ_[l]) (norm_alg_lemma l)).continuous

private theorem closed_rat_lemma_3 (S : Set ℚ_[l]) (hS : IsClosed S) (hq : ∀ r : ℚ, (r : ℚ_[l]) ∈ S)
    (x : ℚ_[l]) : x ∈ S := by
  rw [← hS.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r, hr⟩ := Padic.rat_dense l x hε
  exact ⟨r, hq r, by rw [dist_eq_norm]; exact hr⟩

theorem algebraMap_mem_Kur (x : ℚ_[l]) : algebraMap ℚ_[l] ℂ_[l] x ∈ MaximalUnramifiedExtension l := by
  have hK : IsClosed (MaximalUnramifiedExtension l : Set ℂ_[l]) := by
    first
    | exact Subfield.isClosed_topologicalClosure _
  refine closed_rat_lemma_3 l {y | algebraMap ℚ_[l] ℂ_[l] y ∈ MaximalUnramifiedExtension l} (hK.preimage (cont_alg_lemma_2 l)) ?_ x
  intro r
  show algebraMap ℚ_[l] ℂ_[l] (r : ℚ_[l]) ∈ MaximalUnramifiedExtension l
  rw [map_ratCast]
  first
  | exact SubfieldClass.ratCast_mem (MaximalUnramifiedExtension l) r

def φ : ℚ_[l] →+* MaximalUnramifiedExtension l := (algebraMap ℚ_[l] ℂ_[l]).codRestrict (MaximalUnramifiedExtension l) (algebraMap_mem_Kur l)

def ψ : ℤ_[l] →+* MaximalUnramifiedExtension l := (φ l).comp PadicInt.Coe.ringHom

theorem norm_φ (x : ℚ_[l]) : ‖φ l x‖ = ‖x‖ := by
  exact norm_alg_lemma l x

theorem norm_ψ (x : ℤ_[l]) : ‖ψ l x‖ = ‖x‖ := by
  exact norm_φ l (x : ℚ_[l])

theorem norm_ψ_le (x : ℤ_[l]) : ‖ψ l x‖ ≤ 1 := by
  rw [norm_ψ]
  exact x.norm_le_one

theorem continuous_φ : Continuous (φ l) := by
  exact (AddMonoidHomClass.isometry_of_norm (φ l) (norm_φ l)).continuous

theorem σ_φ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (x : ℚ_[l]) : σ (φ l x) = φ l x := by
  have hσc : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ hσ).continuous
  refine closed_rat_lemma_3 l {y | σ (φ l y) = φ l y}
    (isClosed_eq (hσc.comp (continuous_φ l)) (continuous_φ l)) ?_ x
  intro r
  show σ (φ l (r : ℚ_[l])) = φ l (r : ℚ_[l])
  rw [map_ratCast, map_ratCast]

theorem σ_ψ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (x : ℤ_[l]) : σ (ψ l x) = ψ l x := by
  exact σ_φ l σ hσ (x : ℚ_[l])

theorem norm_natCast_Kur (k : ℕ) : ‖(k : MaximalUnramifiedExtension l)‖ = ‖(k : ℚ_[l])‖ := by
  rw [← map_natCast (φ l) k, norm_φ]

theorem norm_l_Kur : ‖(l : MaximalUnramifiedExtension l)‖ = (l : ℝ)⁻¹ := by
  rw [norm_natCast_Kur, Padic.norm_p]

theorem toZMod_eq_zero_iff (z : ℤ_[l]) : PadicInt.toZMod z = 0 ↔ ‖z‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
  first
  | rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

theorem norm_eq_one_iff (z : ℤ_[l]) : ‖z‖ = 1 ↔ PadicInt.toZMod z ≠ 0 := by
  rw [Ne, toZMod_eq_zero_iff]
  constructor
  · intro h h'
    rw [h] at h'
    exact lt_irrefl _ h'
  · intro h
    exact le_antisymm z.norm_le_one (not_lt.1 h)

theorem toZMod_natCast (k : ℕ) : PadicInt.toZMod (k : ℤ_[l]) = (k : ZMod l) := by
  exact map_natCast PadicInt.toZMod k

theorem odd_l (h5 : 5 ≤ l) : (2 : ZMod l) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (ZMod l) l] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem exists_sqrt (h5 : 5 ≤ l) (t : ℤ_[l]) (s : ZMod l) (hs : s ≠ 0) (ht : PadicInt.toZMod t = s ^ 2) :
    ∃ z : ℤ_[l], z * z = t := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[l], PadicInt.toZMod a = s :=
    ⟨(s.val : ℤ_[l]), by rw [toZMod_natCast, ZMod.natCast_zmod_val]⟩
  set F : Polynomial ℤ_[l] := Polynomial.X ^ 2 - Polynomial.C t with hF
  have h1 : Polynomial.aeval a F = a ^ 2 - t := by simp [hF]
  have h2 : Polynomial.aeval a (Polynomial.derivative F) = 2 * a := by
    first
    | (norm_num [hF]; done)
  have n1 : ‖a ^ 2 - t‖ < 1 := by
    rw [← toZMod_eq_zero_iff l, map_sub, map_pow, ha, ht, sub_self]
  have n2 : ‖(2 : ℤ_[l]) * a‖ = 1 := by
    rw [norm_eq_one_iff l, map_mul, map_ofNat, ha]
    exact mul_ne_zero (odd_l l h5) hs
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := a) (by rw [h1, h2, n2, one_pow]; exact n1)
  have hz2 : z ^ 2 = t := by
    have : z ^ 2 - t = 0 := by simpa [hF] using hz
    exact sub_eq_zero.1 this
  exact ⟨z, by rw [← sq]; exact hz2⟩

theorem exists_norm (h5 : 5 ≤ l) (dK : ℕ) (hld : ¬ l ∣ dK) (a : ℤ_[l]) (ha : ‖a‖ = 1) :
    ∃ x y : ℤ_[l], x * x + dK * (y * y) = a := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hd : ((dK : ℕ) : ZMod l) ≠ 0 := by
    rwa [Ne, CharP.cast_eq_zero_iff (ZMod l) l]
  have hA : PadicInt.toZMod a ≠ 0 := (norm_eq_one_iff l a).1 ha
  obtain ⟨x0, y0, hxy⟩ : ∃ x0 y0 : ZMod l, x0 ^ 2 + (dK : ZMod l) * y0 ^ 2 = PadicInt.toZMod a := by
    have hR : Fintype.card (ZMod l) % 2 = 1 := by
      rw [ZMod.card]
      exact Nat.odd_iff.1 ((Fact.out : l.Prime).odd_of_ne_two (by omega))
    have h2 : (Polynomial.C (dK : ZMod l) * Polynomial.X ^ 2).degree = 2 :=
      Polynomial.degree_C_mul_X_pow 2 hd
    have hg : (Polynomial.C (dK : ZMod l) * Polynomial.X ^ 2
        - Polynomial.C (PadicInt.toZMod a)).degree = 2 := by
      rw [Polynomial.degree_sub_C (by rw [h2]; first | decide | norm_num | exact WithBot.coe_lt_coe.2 (by norm_num)), h2]
    obtain ⟨x0, y0, h⟩ := FiniteField.exists_root_sum_quadratic (f := Polynomial.X ^ 2)
      (g := Polynomial.C (dK : ZMod l) * Polynomial.X ^ 2 - Polynomial.C (PadicInt.toZMod a))
      (Polynomial.degree_X_pow 2) hg hR
    refine ⟨x0, y0, ?_⟩
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C] at h
    linear_combination h
  by_cases hx0 : x0 = 0
  · subst hx0
    have hy0 : y0 ≠ 0 := by
      rintro rfl
      apply hA
      rw [← hxy]
      simp

    obtain ⟨w, hw⟩ := exists_sqrt l h5 ((dK : ℤ_[l]) * a) ((dK : ZMod l) * y0) (mul_ne_zero hd hy0)
      (by
        rw [map_mul, toZMod_natCast]
        linear_combination (-(dK : ZMod l)) * hxy)
    have hdu : IsUnit (dK : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, norm_eq_one_iff l, toZMod_natCast]
      exact hd
    obtain ⟨u, hu⟩ := hdu
    have key : (u : ℤ_[l]) * ↑u⁻¹ = 1 := u.mul_inv
    rw [← hu] at hw
    refine ⟨0, ↑u⁻¹ * w, ?_⟩
    rw [← hu]
    linear_combination ((u : ℤ_[l]) * ↑u⁻¹ * ↑u⁻¹) * hw + ((u : ℤ_[l]) * ↑u⁻¹ + 1) * a * key
  ·
    obtain ⟨x, hx⟩ := exists_sqrt l h5 (a - dK * ((y0.val : ℤ_[l]) * (y0.val : ℤ_[l]))) x0 hx0
      (by
        rw [map_sub, map_mul, map_mul, toZMod_natCast, toZMod_natCast, ZMod.natCast_zmod_val]
        linear_combination -hxy)
    exact ⟨x, y0.val, by rw [hx]; ring⟩

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
end
end
