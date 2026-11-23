module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle095
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Module.StablyFree.Basic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle006
public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012
public import Mathlib.Algebra.MvPolynomial.Eval
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle021
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.Normed.Ring.Basic
import ReciprocityTheory.DualLattices.Bundle001

@[expose] public section

section

open CategoryTheory Polynomial GlobalTheory.NormalDescent

namespace GlobalTheory.CharpolyDvd

theorem matrix_charpoly_dvd_pow {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (G : K[X]) (hG : aeval M G = 0) :
    M.charpoly ∣ G ^ Fintype.card ι := by
  apply GlobalTheory.CharpolyPowIrred.charpoly_dvd_pow_of_aeval <;> assumption

theorem charpoly_dvd_pow_finrank {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (G : K[X]) (hG : aeval f G = 0) :
    f.charpoly ∣ G ^ Module.finrank K V := by
  classical
  let b := Module.finBasis K V
  have hM : aeval (LinearMap.toMatrix b b f) G = 0 := by
    have := aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b).toAlgHom f G
    rw [hG, map_zero] at this
    have e : LinearMap.toMatrixAlgEquiv b f = LinearMap.toMatrix b b f := by
      ext i j
      simp [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
    rw [← e]
    exact this
  have := matrix_charpoly_dvd_pow _ G hM
  rwa [LinearMap.charpoly_toMatrix, Fintype.card_fin] at this

theorem main : ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (G : K[X]), aeval f G = 0 → f.charpoly ∣ G ^ Module.finrank K V :=
  fun f G hG => charpoly_dvd_pow_finrank f G hG

end GlobalTheory.CharpolyDvd
end

section

namespace GlobalTheory.KeyLemmaTwo

lemma key {z : ℂ} (h : ∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) (k : ℕ) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  apply GlobalTheory.IterationConvergence.iter <;> assumption

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := key h k
  have h2 := h (2 ^ k)
  rw [div_lt_iff₀ hpos] at hk
  linarith

end GlobalTheory.KeyLemmaTwo
end

section

open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Mem.PartialZeta

variable {K : Type} [Field K] [NumberField K]

theorem place_unique [_root_.NumberField.IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (v w : InfinitePlace K) : v = w := by
  have hc := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
  rw [IsTotallyComplex.nrRealPlaces_eq_zero, h2] at hr
  rw [IsTotallyComplex.nrRealPlaces_eq_zero] at hc
  have h1 : Fintype.card (InfinitePlace K) = 1 := by omega
  exact Fintype.card_le_one_iff.1 h1.le v w

theorem normSq_eq [_root_.NumberField.IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (x : 𝓞 K) :
    ‖φ (x : K)‖ ^ 2 = (Ideal.absNorm (Ideal.span {x}) : ℝ) := by
  haveI : Subsingleton (InfinitePlace K) := ⟨place_unique h2⟩
  have hprod := InfinitePlace.prod_eq_abs_norm (x : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk φ), InfinitePlace.apply,
    InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2
      (IsTotallyComplex.isComplex _))] at hprod
  rw [hprod, Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs,
    ← Algebra.coe_norm_int]
  norm_cast

theorem abs_im_eq (φ : K →+* ℂ) (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (J : Ideal (𝓞 K))
    (e : Module.Basis (Fin 2) ℤ J) :
    |(starRingEnd ℂ (φ ((e 0 : 𝓞 K) : K)) * φ ((e 1 : 𝓞 K) : K)).im| =
      Ideal.absNorm J * |(starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im| := by
  classical
  set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψdef
  have hψ : ∀ x : 𝓞 K, φ (x : K) = ψ x := fun x => rfl
  have he : ∀ j, ψ (e j : 𝓞 K) = (b.repr (e j : 𝓞 K) 0 : ℂ) * ψ (b 0) +
      (b.repr (e j : 𝓞 K) 1 : ℂ) * ψ (b 1) := by
    intro j
    conv_lhs => rw [← b.sum_repr (e j : 𝓞 K)]

    simp [map_sum, Fin.sum_univ_two, zsmul_eq_mul]
  have hdet := Ideal.natAbs_det_basis_change b J e
  rw [Module.Basis.det_apply, Matrix.det_fin_two] at hdet
  simp only [Module.Basis.toMatrix_apply, Function.comp_apply] at hdet
  simp only [hψ]
  rw [← hdet, Nat.cast_natAbs, Int.cast_abs, ← abs_mul, he 0, he 1]
  congr 1
  simp only [map_add (f := _), map_mul, map_intCast, Complex.mul_im, Complex.add_im, Complex.add_re,
    Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

theorem cls_iff {M : ℕ} (D : RayData K M) (c : D.G) (B I : Ideal (𝓞 K))
    (hB : IsCoprime B (Ideal.span {(M : 𝓞 K)})) (hB0 : B ≠ ⊥) (hc : D.cls B = c⁻¹)
    (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) (hI0 : I ≠ ⊥) :
    D.cls I = c ↔ ∃ x : 𝓞 K, x - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧ Ideal.span {x} = I * B := by
  constructor
  · intro h
    have hIB : D.cls (I * B) = 1 := by
      rw [D.cls_mul I B hI hB hI0 hB0, h, hc, mul_inv_cancel]
    obtain ⟨a, b', ha, hb, ha1, hb1, hab⟩ :=
      (D.cls_eq_one_iff (hI.mul_left hB) (mul_ne_zero hI0 hB0)).1 hIB
    have hmem : b' ∈ Ideal.span {a} := by
      have : b' ∈ Ideal.span {a} * (I * B) := by
        rw [hab]; exact Ideal.mem_span_singleton_self b'
      exact Ideal.mul_le_left this
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨x, ?_, ?_⟩
    · have hax : a * x - 1 ∈ Ideal.span {(M : 𝓞 K)} := by rw [mul_comm, hx]; exact hb1
      have : x - 1 = (a * x - 1) - (a - 1) * x := by ring
      rw [this]
      exact Ideal.sub_mem _ hax (Ideal.mul_mem_right x _ ha1)
    · have hspan : Ideal.span {a} * (I * B) = Ideal.span {a} * Ideal.span {x} := by
        rw [hab, ← hx, ← Ideal.span_singleton_mul_span_singleton, mul_comm]
      have ha' : Ideal.span {a} ≠ 0 := by
        rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact ha
      exact (mul_left_cancel₀ ha' hspan).symm
  · rintro ⟨x, hx1, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at hx
      exact mul_ne_zero hI0 hB0 hx.symm
    have h1 : D.cls (I * B) = 1 := by rw [← hx]; exact D.cls_span hx0 hx1
    rw [D.cls_mul I B hI hB hI0 hB0, hc] at h1
    exact mul_inv_eq_one.1 h1

theorem lattice_bij (N B : Ideal (𝓞 K)) (hB : IsCoprime B N) (e : Module.Basis (Fin 2) ℤ ↥(N * B))
    (x₀ : 𝓞 K) (h0 : x₀ ∈ B) (h1 : x₀ - 1 ∈ N) :
    ∃ f : ℤ × ℤ ≃ {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ N},
      ∀ p, (f p : 𝓞 K) = x₀ + p.1 * (e 0 : 𝓞 K) + p.2 * (e 1 : 𝓞 K) := by
  have hmemNB : ∀ y : ↥(N * B), (y : 𝓞 K) ∈ B ∧ (y : 𝓞 K) ∈ N := fun y =>
    ⟨Ideal.mul_le_right y.2, Ideal.mul_le_left y.2⟩
  let g : ↥(N * B) ≃ {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ N} :=
    { toFun := fun y => ⟨x₀ + y, B.add_mem h0 (hmemNB y).1, by
        rw [add_sub_right_comm]; exact N.add_mem h1 (hmemNB y).2⟩
      invFun := fun x => ⟨x.1 - x₀, by
        rw [Ideal.mul_eq_inf_of_isCoprime hB.symm]
        refine ⟨?_, ?_⟩
        · have : x.1 - x₀ = (x.1 - 1) - (x₀ - 1) := by ring
          rw [this]; exact N.sub_mem x.2.2 h1
        · exact B.sub_mem x.2.1 h0⟩
      left_inv := fun y => by ext; simp
      right_inv := fun x => by ext; simp }
  refine ⟨(finTwoArrowEquiv ℤ).symm.trans (e.equivFun.symm.toEquiv.trans g), fun p => ?_⟩
  simp [g, Fin.sum_univ_two, zsmul_eq_mul, add_assoc]

theorem ne_bot_of_coprime {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) {I : Ideal (𝓞 K)}
    (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) : I ≠ ⊥ := by
  rintro rfl
  rw [Ideal.isCoprime_iff_sup_eq, bot_sup_eq] at hI
  exact hM hI

theorem gen_bij {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) (D : RayData K M) (c : D.G)
    (B : Ideal (𝓞 K))
    (hB : IsCoprime B (Ideal.span {(M : 𝓞 K)})) (hB0 : B ≠ ⊥) (hc : D.cls B = c⁻¹) :
    ∃ f : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} ×
        {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}} ≃
        {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}},
      ∀ p, Ideal.span {(f p : 𝓞 K)} = p.1 * B := by
  classical
  have hgen : ∀ I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c},
      ∃ x : 𝓞 K, x - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧ Ideal.span {x} = I.1 * B := fun I =>
    (cls_iff D c B I.1 hB hB0 hc I.2.1 (ne_bot_of_coprime hM I.2.1)).1 I.2.2
  choose g hg1 hg using hgen
  have hgB : ∀ I, g I ∈ B := fun I => by
    have : g I ∈ Ideal.span {g I} := Ideal.mem_span_singleton_self _
    rw [hg I] at this
    exact Ideal.mul_le_right this
  have hg0 : ∀ I, g I ≠ 0 := fun I h => by
    have := hg I
    rw [h, Ideal.span_singleton_eq_bot.2 rfl] at this
    exact mul_ne_zero (ne_bot_of_coprime hM I.2.1) hB0 this.symm
  let F : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} ×
      {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}} →
      {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}} := fun p =>
    ⟨(p.2.1 : 𝓞 K) * g p.1, Ideal.mul_mem_left _ _ (hgB p.1), by
      have : (p.2.1 : 𝓞 K) * g p.1 - 1 = (p.2.1 : 𝓞 K) * (g p.1 - 1) + ((p.2.1 : 𝓞 K) - 1) := by
        ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hg1 p.1)) p.2.2⟩
  have hspanF : ∀ p, Ideal.span {(F p : 𝓞 K)} = p.1 * B := fun p => by
    show Ideal.span {(p.2.1 : 𝓞 K) * g p.1} = _
    rw [Ideal.span_singleton_mul_left_unit p.2.1.isUnit, hg]
  have hinj : Function.Injective F := by
    rintro ⟨I, u⟩ ⟨I', u'⟩ h
    have h1 := hspanF (I, u)
    rw [h, hspanF (I', u')] at h1
    have hII : I = I' := Subtype.ext (mul_right_cancel₀ (by simpa using hB0) h1.symm)
    subst hII
    have h2 : (u.1 : 𝓞 K) * g I = (u'.1 : 𝓞 K) * g I := congrArg Subtype.val h
    have h3 : (u.1 : 𝓞 K) = (u'.1 : 𝓞 K) := mul_right_cancel₀ (hg0 I) h2
    rw [Subtype.ext (Units.ext h3)]
  have hsurj : Function.Surjective F := by
    rintro ⟨x, hxB, hx1⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply hM
      rw [Ideal.eq_top_iff_one]
      have := (Ideal.neg_mem_iff _).2 hx1
      simpa using this
    have hle : Ideal.span {x} ≤ B := (Ideal.span_singleton_le_iff_mem _).2 hxB
    obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 hle
    have hxc : IsCoprime (Ideal.span {x}) (Ideal.span {(M : 𝓞 K)}) := by
      rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
      have : (1 : 𝓞 K) = x - (x - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self x))
        (Ideal.mem_sup_right hx1)
    have hIc : IsCoprime I (Ideal.span {(M : 𝓞 K)}) := by
      rw [hI] at hxc; exact hxc.of_mul_left_right
    have hIB : Ideal.span {x} = I * B := by rw [hI, mul_comm]
    have hIcls : D.cls I = c :=
      (cls_iff D c B I hB hB0 hc hIc (ne_bot_of_coprime hM hIc)).2 ⟨x, hx1, hIB⟩
    let I' : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} :=
      ⟨I, hIc, hIcls⟩
    have hass : Associated (g I') x := by
      rw [← Ideal.span_singleton_eq_span_singleton, hg I', hIB]
    obtain ⟨u, hu⟩ := hass
    have hu1 : (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
      have hgu : g I' * u - 1 ∈ Ideal.span {(M : 𝓞 K)} := by rw [hu]; exact hx1
      have : (u : 𝓞 K) - 1 = (g I' * u - 1) - (g I' - 1) * u := by ring
      rw [this]
      exact Ideal.sub_mem _ hgu (Ideal.mul_mem_right _ _ (hg1 I'))
    refine ⟨(I', ⟨u, hu1⟩), Subtype.ext ?_⟩
    show (u : 𝓞 K) * g I' = x
    rw [mul_comm, hu]
  exact ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun p => hspanF p⟩

end GlobalTheory.Mem.PartialZeta

end
end

section

namespace GlobalTheory.Mem.An

theorem _root_.GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd :
    ∀ d M p : ℕ, d % 4 = 3 → _root_.GlobalTheory.Mem.An.NormOne d M p →
      p ≡ 1 [MOD M] ∧ ∀ M' : ℕ, M' ∣ M → _root_.GlobalTheory.Mem.An.NormOne d M' p := by
  intro d M p hd h
  obtain ⟨A, B, hAB, hB, hA⟩ := h
  refine ⟨?_, fun M' hM' => ⟨A, B, hAB, (Int.natCast_dvd_natCast.mpr hM').trans hB,
    (mul_dvd_mul_left 2 (Int.natCast_dvd_natCast.mpr hM')).trans hA⟩⟩
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨k, hk⟩ := hA
  have hdq : (d : ℤ) = 4 * (d / 4 : ℕ) + 3 := by omega
  have hA' : A = 2 + M * b + 2 * M * k := by linear_combination hk
  have key : (4 : ℤ) * (p - 1) =
      4 * (M * (b + 2 * k + M * (((d / 4 : ℕ) + 1) * b ^ 2 + b * k + k ^ 2))) := by
    rw [hA', hdq] at hAB
    linear_combination -hAB
  have key' : (p : ℤ) - 1 = M * (b + 2 * k + M * (((d / 4 : ℕ) + 1) * b ^ 2 + b * k + k ^ 2)) := by
    linarith
  exact (Nat.modEq_iff_dvd.mpr ⟨_, key'⟩).symm

end GlobalTheory.Mem.An
end

section

noncomputable section

namespace GlobalTheory.Mem.An.ZeroWindow

open Complex DirichletCharacter

theorem analyticOff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (LFunction χ) ({1}ᶜ : Set ℂ) := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
  intro s hs
  exact (χ.differentiableAt_LFunction s (Or.inl hs)).differentiableWithinAt

theorem exists_entire {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 1 ≠ 0 ∧ ∀ s, s ≠ 1 → LFunction χ s = 0 → F s = 0 := by
  by_cases h : χ = 1
  · subst h
    refine ⟨LFunctionTrivChar₁ q, differentiable_LFunctionTrivChar₁ q,
      LFunctionTrivChar₁_apply_one_ne_zero q, fun s hs h0 => ?_⟩
    rw [LFunctionTrivChar₁, Function.update_of_ne hs, LFunctionTrivChar, h0, mul_zero]
  · exact ⟨LFunction χ, differentiable_LFunction h, LFunction_apply_one_ne_zero h,
      fun _ _ h0 => h0⟩

theorem ne_one_of_mem {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {t T : ℝ} {ρ : ℂ}
    (h : ρ ∈ zerosIn χ t T) : ρ ≠ 1 := by
  rintro rfl
  have h2 := h.2.1
  simp at h2

theorem finite_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) :
    (zerosIn χ t T).Finite := by
  obtain ⟨F, hF, h1, h0⟩ := exists_entire χ
  have hA : AnalyticOnNhd ℂ F Set.univ := hF.differentiableOn.analyticOnNhd isOpen_univ
  by_contra hinf
  have hinf : (zerosIn χ t T).Infinite := hinf
  have hsub : zerosIn χ t T ⊆ Metric.closedBall (0 : ℂ) (1 + |t| + T) := by
    rintro ρ ⟨h0, h1, h2, -⟩
    rw [mem_closedBall_zero_iff]
    have := Complex.norm_le_abs_re_add_abs_im ρ
    have h3 : |ρ.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have h4 : |ρ.im| ≤ |t| + T := by
      have := abs_sub_abs_le_abs_sub ρ.im t
      linarith
    linarith
  obtain ⟨z, -, hz⟩ := hinf.exists_accPt_of_subset_isCompact (isCompact_closedBall _ _) hsub
  have hfr : ∃ᶠ w in nhdsWithin z {z}ᶜ, F w = 0 := by
    rw [accPt_iff_frequently_nhdsNE] at hz
    exact hz.mono fun w hw => h0 w (ne_one_of_mem hw) hw.2.2.2
  have := hA.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z) hfr
  exact h1 (this (Set.mem_univ 1))

theorem order_ne_top {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderAt (LFunction χ) ρ ≠ ⊤ := by
  intro ht
  rw [analyticOrderAt_eq_top] at ht
  have hc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have h2 : (2 : ℂ) ≠ 1 := by norm_num
  have := (analyticOff χ).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hρ ht
  exact χ.LFunction_ne_zero_of_one_le_re (s := 2) (Or.inr h2) (by simp) (this h2)

theorem one_le_zmult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zerosIn χ t T) : 1 ≤ zmult χ ρ := by
  unfold zmult analyticOrderNatAt
  have h1 := order_ne_top χ (ne_one_of_mem hρ)
  have h2 : analyticOrderAt (LFunction χ) ρ ≠ 0 := by
    rw [analyticOrderAt_ne_zero]
    exact ⟨analyticOff χ ρ (ne_one_of_mem hρ), hρ.2.2.2⟩
  rw [Nat.one_le_iff_ne_zero]
  simp [h1, h2]

theorem finite_and_one_le_zmult : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ),
    (zerosIn χ t T).Finite ∧ ∀ ρ ∈ zerosIn χ t T, 1 ≤ zmult χ ρ :=
  fun _ _ χ t T => ⟨finite_zeros χ t T, fun _ hρ => one_le_zmult χ hρ⟩

end GlobalTheory.Mem.An.ZeroWindow
end
end

section

set_option autoImplicit false

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

namespace GlobalTheory.CayleyBlock

theorem coeff_dList_of_nodup {σ : Type} [DecidableEq σ] (l : List σ) (hl : l.Nodup) (m : σ →₀ ℕ)
    (hm : ∀ v ∈ l, m v = 0) (G : MvPolynomial σ ℂ) :
    AddMonoidAlgebra.coeff (dList l G) m = AddMonoidAlgebra.coeff G (m + (l.map fun v => Finsupp.single v 1).sum) := by
  induction l generalizing m with
  | nil => simp [dList]
  | cons v l ih =>
    have hc : dList (v :: l) G = pderiv v (dList l G) := by
      simp [dList]
    rw [List.nodup_cons] at hl
    have h0 : m v = 0 := hm v (List.mem_cons_self ..)
    have h1 : ∀ w ∈ l, (m + Finsupp.single v 1 : σ →₀ ℕ) w = 0 := by
      intro w hw
      have hne : w ≠ v := fun h => hl.1 (h ▸ hw)
      rw [Finsupp.add_apply, hm w (List.mem_cons_of_mem _ hw), Finsupp.single_eq_of_ne hne, add_zero]
    rw [hc, MvPolynomial.coeff_pderiv, ih hl.2 _ h1, h0, List.map_cons, List.sum_cons, add_assoc]
    simp

end GlobalTheory.CayleyBlock
end

section

namespace GlobalTheory.SiegelChain

theorem siegel_chain : ∀ {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ}, GlobalTheory.RedTh.IsSiegel d u →
    ∀ (m : ℕ) (i j : Fin n), (↑j : ℕ) = (↑i : ℕ) + m → d i ≤ (4 : ℝ) ^ m * d j := by
  intro n d u h m
  induction m with
  | zero =>
    intro i j hij
    have : i = j := Fin.ext (by simpa using hij.symm)
    subst this
    simp
  | succ m ih =>
    intro i j hij
    have hk : (i : ℕ) + m < n := by have := j.isLt; omega
    let k : Fin n := ⟨(i : ℕ) + m, hk⟩
    have h1 : d i ≤ 4 ^ m * d k := ih i k rfl
    have h2 : d k ≤ 4 * d j := h.step k j (by simp [k]; omega)
    have h4 : (0 : ℝ) ≤ 4 ^ m := by positivity
    calc d i ≤ 4 ^ m * d k := h1
      _ ≤ 4 ^ m * (4 * d j) := mul_le_mul_of_nonneg_left h2 h4
      _ = 4 ^ (m + 1) * d j := by ring

end GlobalTheory.SiegelChain
end

section


theorem _root_.GlobalTheory.T.mvPolynomial_clear_denominators_eval : ∀ {K : Type} [Field K] {ι τ : Type} (F : MvPolynomial ι K) (P D : ι → MvPolynomial τ K), ∃ G M : MvPolynomial τ K, ∀ y : τ → K, (∀ i, MvPolynomial.eval y (D i) ≠ 0) → MvPolynomial.eval y M ≠ 0 ∧ MvPolynomial.eval y G = MvPolynomial.eval y M * MvPolynomial.eval (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F := by
  first | exact @GlobalTheory.clearDenominators | exact GlobalTheory.clearDenominators | (intros; apply GlobalTheory.clearDenominators <;> assumption)
end
