module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle079
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import GroundTheory.GlobalFields.CyclotomicCharacters.Character
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisCoef
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle324
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle475
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle325
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle396
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
import Mathlib.Tactic.ReduceModChar
public import Mathlib.NumberTheory.Real.Irrational
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.CoefZero

@[expose] public section

section

open UpperTheory.V.Af UpperTheory.GalN.V

private theorem root_of_smul {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (c : K) (hc : c ≠ 0) (α : K)
    (h : (c • M).charpoly.IsRoot α) : M.charpoly.IsRoot (c⁻¹ * α) := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly] at h ⊢
  have key : (Matrix.scalar (Fin n)) α - c • M = c • ((Matrix.scalar (Fin n)) (c⁻¹ * α) - M) := by
    rw [smul_sub, Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
    congr 2
    ext i
    simp [mul_inv_cancel_left₀ hc]
  rw [key, Matrix.det_smul] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd (pow_eq_zero_iff'.mp h1).1 hc
  · exact h1

theorem UpperTheory.V.Z.Sym.Unl.twOk :
    UpperTheory.V.Z.Sym.Unl.TwOk := by
  intro F Ω _ _ _ _ l _ n ι r δ
  have hc : ∀ s, ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l) ≠ 0 := fun s => Units.ne_zero _
  have hroot : ∀ s α, (↑((tw r δ) s) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.IsRoot α →
      (↑(r s) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.IsRoot (((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)⁻¹ * α) := by
    intro s α h
    rw [tw_val] at h
    exact root_of_smul _ _ (hc s) α h
  have hnorm : ∀ s α, ‖ι α‖ = ‖ι ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)‖ *
      ‖ι (((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)⁻¹ * α)‖ := by
    intro s α
    rw [← norm_mul, ← map_mul, mul_inv_cancel_left₀ (hc s)]
  have hpos : ∀ s, 0 < ‖ι ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)‖ := by
    intro s
    exact norm_pos_iff.mpr ((map_ne_zero ι).mpr (hc s))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · intro w hw A hA s hs α β hα hβ heq
    apply h w hw A hA s hs _ _ (hroot s α hα) (hroot s β hβ)
    have hp := hpos s
    rw [hnorm s α, hnorm s β, mul_pow, mul_pow] at heq
    have hp2 : 0 < ‖ι ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)‖ ^ 2 := by positivity
    have := heq
    rw [mul_left_comm] at this
    exact mul_left_cancel₀ hp2.ne' this
  · intro w hw A hA s hs α β hα hβ
    have key := h w hw A hA s hs _ _ (hroot s α hα) (hroot s β hβ)
    have hp := hpos s
    rw [hnorm s α, hnorm s β, mul_left_comm]
    exact mul_lt_mul_of_pos_left key hp
end

section

open scoped ComplexConjugate

namespace UpperTheory.V.Z.Sym.Unl

private theorem sq_of_conj {a x : ℂ} (h : conj a * x = a) :
    a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) * x := by
  have h1 : a * conj a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; push_cast; rfl
  calc a * a = a * (conj a * x) := by rw [h]
    _ = (a * conj a) * x := by ring
    _ = _ := by rw [h1]

private theorem ratio_eq {p s t : ℝ} (hp : 2 ≤ p) (hs0 : 0 < s) (hs : s * s = p) {z : ℂ}
    (hz : z * conj z = (p : ℂ)) (ht : 0 ≤ t) (hzt : z + 2 + z⁻¹ = (t : ℂ)) : z = (s : ℂ) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hn : Complex.normSq z = p := by
    have e := Complex.mul_conj z
    rw [hz] at e
    exact_mod_cast e.symm
  have hre := congrArg Complex.re hzt
  have him := congrArg Complex.im hzt
  simp [Complex.inv_re, Complex.inv_im, hn] at hre him
  have hn2 : z.re * z.re + z.im * z.im = p := by rw [← hn, Complex.normSq_apply]
  have hv : z.im = 0 := by
    have e : z.im * (p - 1) = 0 := by
      have e2 : z.im * (p - 1) = p * (z.im + -z.im / p) := by
        field_simp
        ring
      rw [e2, him, mul_zero]
    rcases mul_eq_zero.mp e with h | h
    · exact h
    · exfalso
      linarith
  have hre' : (z.re + 2) * p + z.re = t * p := by
    rw [← hre]
    field_simp
  have hu : (z.re - s) * (z.re + s) = 0 := by
    rw [hv] at hn2
    linear_combination hn2 - hs
  have hr : z.re = s := by
    rcases mul_eq_zero.mp hu with h | h
    · linarith
    · exfalso
      have hm : z.re = -s := by linarith
      rw [hm, ← hs] at hre'
      have hs1 : 1 < s := by nlinarith
      nlinarith [mul_nonneg ht (mul_nonneg hs0.le hs0.le), mul_pos hs0 (mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hs1))]
  apply Complex.ext
  · simp [hr]
  · simp [hv]

private theorem abs_ratio_ne_of_sqrt_flip (p m : ℕ) (a x α β : ℂ) (σ : ℂ ≃+* ℂ) (hp : 2 ≤ p) (hx : ‖x‖ = 1)
    (hσx : ‖σ x‖ = 1) (hσ : σ ((Real.sqrt p : ℝ) : ℂ) = -((Real.sqrt p : ℝ) : ℂ))
    (ha : conj a * x = a) (hσa : conj (σ a) * σ x = σ a) (hsum : α + β = a)
    (hprod : α * β = x * (p : ℂ) ^ m) : ‖α‖ ^ 2 ≠ (p : ℝ) * ‖β‖ ^ 2 := by
  intro hab
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hx
    exact zero_ne_one hx
  have hσx0 : σ x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hσx
    exact zero_ne_one hσx
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hprod0 : α * β ≠ 0 := by
    rw [hprod]
    exact mul_ne_zero hx0 (pow_ne_zero _ hpC)
  have hβ : β ≠ 0 := right_ne_zero_of_mul hprod0
  have hα : α ≠ 0 := left_ne_zero_of_mul hprod0
  set s := Real.sqrt p with hs_def
  have hs0 : 0 < s := Real.sqrt_pos.mpr hp0
  have hss : s * s = p := Real.mul_self_sqrt hp0.le
  have hn : Complex.normSq α = p * Complex.normSq β := by
    rw [← Complex.sq_norm, ← Complex.sq_norm]
    exact hab
  have hnβ : (Complex.normSq β : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr hβ).ne'
  have hz : (α / β) * conj (α / β) = ((p : ℝ) : ℂ) := by
    rw [map_div₀, div_mul_div_comm, Complex.mul_conj, Complex.mul_conj, hn]
    push_cast
    field_simp
  have key : α / β + 2 + (α / β)⁻¹ = (a * a) / (α * β) := by
    rw [← hsum, inv_div]
    field_simp
    ring
  have hzt : α / β + 2 + (α / β)⁻¹ = ((‖a‖ ^ 2 / (p : ℝ) ^ m : ℝ) : ℂ) := by
    rw [key, sq_of_conj ha, hprod]
    push_cast
    field_simp
  have ht : (0 : ℝ) ≤ ‖a‖ ^ 2 / (p : ℝ) ^ m := by positivity
  have hz' := ratio_eq hpR hs0 hss hz ht hzt
  have hαs : α = (s : ℂ) * β := (div_eq_iff hβ).mp hz'
  have k2 : (s : ℂ) * (a * a) = (1 + (s : ℂ)) ^ 2 * (x * (p : ℂ) ^ m) := by
    rw [← hprod, ← hsum, hαs]
    ring
  have k3 := congrArg σ k2
  simp only [map_mul, map_add (f := _), map_pow, map_natCast, map_one, hσ] at k3
  rw [sq_of_conj hσa] at k3
  push_cast at k3
  have k4 : (-(s * ‖σ a‖ ^ 2 : ℝ) : ℂ) * σ x = ((1 - s) ^ 2 * (p : ℝ) ^ m : ℝ) * σ x := by
    push_cast
    linear_combination k3
  have k5 := mul_right_cancel₀ hσx0 k4
  have k6 : -(s * ‖σ a‖ ^ 2) = (1 - s) ^ 2 * (p : ℝ) ^ m := by exact_mod_cast k5
  have hs1 : 1 < s := by nlinarith
  have hpm : 0 < (p : ℝ) ^ m := pow_pos hp0 m
  nlinarith [mul_nonneg hs0.le (sq_nonneg ‖σ a‖), mul_pos (pow_pos (sub_pos.mpr hs1) 2) hpm]

end UpperTheory.V.Z.Sym.Unl

theorem UpperTheory.V.Z.Sym.Unl.halfAlg :
    UpperTheory.V.Z.Sym.Unl.HalfAlg := by
  intro p m a x α β σ hp hx hσx hσ ha hσa hsum hprod
  exact UpperTheory.V.Z.Sym.Unl.abs_ratio_ne_of_sqrt_flip p m a x α β σ hp hx hσx hσ ha hσa hsum hprod
end

section

open UpperTheory.V.Af UpperTheory.V.Sd

namespace UpperTheory.V.Z.Sym.Unl

theorem conjEig : ConjEig := by
  intro k N χ g hg σ
  obtain ⟨f', h1, h2⟩ := hg σ
  refine ⟨⟨f', h1, ?_, ?_⟩, fun n hn => h2 n hn⟩
  · rw [h2 1 le_rfl, g.one, map_one]
  · intro p hp n hn
    have e := congrArg σ (g.eig p hp n hn)
    have hc : (cj σ χ) (p : ZMod N) = σ (χ p) := rfl
    show coef f' (p * n) + (cj σ χ) p * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then coef f' (n / p) else 0) = coef f' p * coef f' n
    rw [h2 _ (Nat.mul_pos hp.pos hn), h2 _ hp.pos, h2 _ hn, hc]
    by_cases hd : p ∣ n
    · have hm : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn hd) hp.pos
      simp only [hd, if_true] at e ⊢
      rw [h2 _ hm]
      simpa [map_add (f := _), map_mul, map_pow, map_natCast] using e
    · simp only [hd, if_false] at e ⊢
      simpa [map_add (f := _), map_mul, map_pow, map_natCast] using e

end UpperTheory.V.Z.Sym.Unl
end

section

namespace UpperTheory.V.Z.Sym.Unl

private theorem ker_cj {N : ℕ} (σ : ℂ ≃+* ℂ) (χ : DirichletCharacter ℂ N) :
    (cj σ χ).toUnitHom.ker = χ.toUnitHom.ker := by
  ext x
  simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, cj, MulChar.ringHomComp_apply]
  exact map_eq_one_iff σ σ.injective

theorem primCj : PrimCj := by
  intro N _ χ σ hχ
  have key : ∀ d : ℕ, (cj σ χ).FactorsThrough d ↔ χ.FactorsThrough d := by
    intro d
    constructor
    · intro h
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd, ← ker_cj σ χ]
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
    · intro h
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd, ker_cj σ χ]
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
  have hc : (cj σ χ).conductor = χ.conductor := by
    unfold DirichletCharacter.conductor DirichletCharacter.conductorSet
    congr 1
    ext d
    exact key d
  unfold DirichletCharacter.IsPrimitive at hχ ⊢
  rw [hc]
  exact hχ

end UpperTheory.V.Z.Sym.Unl
end

section

private theorem UpperTheory.V.Z.Sym.Unl.exists_ring_equiv_flip_sqrt (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsAlgClosed Ω]
    (ε : Ω →+* ℂ) (p : ℕ) (hp : p.Prime) :
    ∃ σ : ℂ ≃+* ℂ, σ ((Real.sqrt p : ℝ) : ℂ) = -((Real.sqrt p : ℝ) : ℂ) := by
  have hne : ∀ b : ℚ, b ^ 2 ≠ (p : ℚ) := by
    intro b hb
    apply hp.irrational_sqrt
    refine ⟨|b|, ?_⟩
    have h2 : ((b : ℝ)) ^ 2 = (p : ℝ) := by exact_mod_cast hb
    rw [← h2, Real.sqrt_sq_eq_abs]
    push_cast
    rfl
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (p : Ω) (by norm_num : 0 < 2)
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (p : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two hne
  have hev : ∀ x : Ω, x ^ 2 = (p : Ω) → Polynomial.aeval x (Polynomial.X ^ 2 - Polynomial.C (p : ℚ)) = 0 := by
    intro x hx
    simp [hx]
  have hmon : (Polynomial.X ^ 2 - Polynomial.C (p : ℚ)).Monic := Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hmin : minpoly ℚ (-a) = minpoly ℚ a := by
    rw [← minpoly.eq_of_irreducible_of_monic hirr (hev a ha) hmon,
      ← minpoly.eq_of_irreducible_of_monic hirr (hev (-a) (by rw [neg_sq, ha])) hmon]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := Ω)).mp hmin
  let s : Ω ≃+* Ω := σ.toRingEquiv
  have hsa : s a = -a := hσ
  obtain ⟨g, hg⟩ := GlobalTheory.FN.exists_ringEquiv_extend_of_embedding Ω ε s
  refine ⟨g, ?_⟩
  have hea : (ε a) ^ 2 = ((Real.sqrt p : ℝ) : ℂ) ^ 2 := by
    rw [← map_pow, ha, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hga : g (ε a) = -(ε a) := by rw [hg, hsa, map_neg]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hea with h | h
  · rw [← h, hga]
  · have : ((Real.sqrt p : ℝ) : ℂ) = -(ε a) := by rw [h, neg_neg]
    rw [this, map_neg, hga, neg_neg]

theorem UpperTheory.V.Z.Sym.Unl.sqrtFlip :
    UpperTheory.V.Z.Sym.Unl.SqrtFlip := fun p hp =>
  UpperTheory.V.Z.Sym.Unl.exists_ring_equiv_flip_sqrt (AlgebraicClosure ℚ)
    (IsAlgClosed.lift (R := ℚ) (S := AlgebraicClosure ℚ) (M := ℂ)).toRingHom p hp
end

section

open UpperTheory.V.Af UpperTheory.V.Sd

namespace UpperTheory.V.Z.Sym.Unl

private lemma map_Lk (σ : ℂ ≃+* ℂ) (k : ℕ) (x : ℂ) : σ (Lk k x) = Lk k (σ x) := by
  unfold Lk
  rw [map_div₀, map_pow, map_sub, map_one]
  congr 1
  exact (Polynomial.aeval_algHom_apply (σ.toRingHom.toIntAlgHom) x (numL k)).symm

private lemma exists_unit (N : ℕ) [NeZero N] (σ : ℂ ≃+* ℂ) :
    ∃ s : (ZMod N)ˣ, ∀ b : ZMod N, σ (ZMod.stdAddChar b : ℂ) = (ZMod.stdAddChar ((s : ZMod N) * b) : ℂ) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hpow : ∀ (m : ℕ) (c : ZMod N), (ZMod.stdAddChar ((m : ZMod N) * c) : ℂ) = (ZMod.stdAddChar c : ℂ) ^ m := by
    intro m c
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hone : (ZMod.stdAddChar (1 : ZMod N) : ℂ) ^ N = 1 := by
    rw [← hpow, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
  have hz : IsPrimitiveRoot (ZMod.stdAddChar (1 : ZMod N) : ℂ) N := by
    refine IsPrimitiveRoot.mk_of_lt _ hN hone fun l hl hlN h => ?_
    have h1 : (ZMod.stdAddChar ((l : ZMod N) * 1) : ℂ) = ZMod.stdAddChar (0 : ZMod N) := by
      rw [hpow, h, AddChar.map_zero_eq_one]
    have h2 := ZMod.injective_stdAddChar h1
    rw [mul_one, ZMod.natCast_eq_zero_iff] at h2
    exact absurd (Nat.le_of_dvd hl h2) (by omega)
  have hz' := hz.map_of_injective (f := σ) σ.injective
  obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one hz'.pow_eq_one
  have hc : i.Coprime N := by
    rw [← hz.pow_iff_coprime hN, hi]
    exact hz'
  refine ⟨ZMod.unitOfCoprime i hc, fun b => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ZMod N) = b := ⟨b.val, ZMod.natCast_zmod_val b⟩
  have e1 : (ZMod.stdAddChar (m : ZMod N) : ℂ) = (ZMod.stdAddChar (1 : ZMod N) : ℂ) ^ m := by
    rw [← hpow, mul_one]
  have e2 : (ZMod.stdAddChar ((i : ZMod N) * (m : ZMod N)) : ℂ) = (ZMod.stdAddChar (1 : ZMod N) : ℂ) ^ (i * m) := by
    rw [← Nat.cast_mul, ← hpow, mul_one]
  rw [ZMod.coe_unitOfCoprime, e1, e2, map_pow, ← hi, pow_mul]

end UpperTheory.V.Z.Sym.Unl

open UpperTheory.V.Af UpperTheory.V.Sd in
theorem UpperTheory.V.Z.Sym.Unl.eisCj : UpperTheory.V.Z.Sym.Unl.EisCj := by
  intro N _ hN σ
  obtain ⟨s, hs⟩ := UpperTheory.V.Z.Sym.Unl.exists_unit N σ
  refine ⟨s, hs, fun k hk a n => ?_⟩
  haveI : Fact (1 < N) := ⟨hN⟩
  have ha : ((a : (ZMod N)ˣ) : ZMod N) ≠ 0 := a.ne_zero
  have hsa : (((s * a : (ZMod N)ˣ)) : ZMod N) ≠ 0 := (s * a).ne_zero
  have hu : (((s * a : (ZMod N)ˣ)) : ZMod N) = (s : ZMod N) * a := Units.val_mul s a
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [(eisCoef N k hk _ hsa).1, (eisCoef N k hk _ ha).1, UpperTheory.V.Z.Sym.Unl.map_Lk, hs, hu]
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [(eisCoef N k hk _ hsa).2 n hn, (eisCoef N k hk _ ha).2 n hn, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_mul σ, map_pow σ, map_natCast σ, map_add σ, map_mul σ, map_pow σ, map_neg σ, map_one σ, hs, hs, hu]
    simp only [mul_assoc, mul_neg]
end

section

private theorem norm_sq_of_scaled (k p : ℕ) (hk : 3 ≤ k) (hp : 2 ≤ p) (x : ℂ)
    (h : ‖x * (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)‖ ^ 2 = (p : ℝ)) : ‖x‖ ^ 2 = (p : ℝ) ^ (k - 1) := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (by omega)
  have hr : (0 : ℝ) < (p : ℝ) ^ (1 - (k : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, mul_pow] at h
  have hr2 : ((p : ℝ) ^ (1 - (k : ℝ) / 2)) ^ 2 = (p : ℝ) ^ (2 - (k : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  have he : (((k - 1 : ℕ) : ℝ)) + (2 - (k : ℝ)) = 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hkey : (p : ℝ) ^ (k - 1) * (p : ℝ) ^ (2 - (k : ℝ)) = p := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hp0, he, Real.rpow_one]
  have hne : (p : ℝ) ^ (2 - (k : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hp0 _).ne'
  rw [hr2] at h
  exact mul_right_cancel₀ hne (h.trans hkey.symm)

theorem UpperTheory.V.Z.Sym.Unl.badAbs :
    UpperTheory.V.Z.Sym.Unl.BadAbs := by
  intro k N _ hk χ hχ g p hp hpN
  have b0 : Ad3.R.B0 := @GlobalTheory.T.global_rankin_selberg_basic_facts
  have c0 : Ad3.R.C0 := @GlobalTheory.T.hecke_coset_representatives
  have c1 : Ad3.R.C1 := @GlobalTheory.T.congruence_subgroup_coset_decomposition
  have u2 : Ad3.R.U2 := @GlobalTheory.T.unramified_whittaker_newform
  have g0 : Ad3.R.G0 := @GlobalTheory.T.fundamental_domain_invariance_of_description (@GlobalTheory.T.fundamental_domain_description)
  have g1 : Ad3.R.G1 := @GlobalTheory.T.central_character_integral_properties (@GlobalTheory.T.fundamental_domain_integral_central_invariance)
  have f0 : Ad3.R.F0 := @GlobalTheory.T.newform_lift_existence b0
  have f0b : Ad3.R.F0b := @GlobalTheory.T.newform_lift_conductor b0
  have f1 : Ad3.R.F1 := @GlobalTheory.T.newform_lift_level b0
  have f1b : Ad3.R.AutomorphicLevelEquivariance := @GlobalTheory.T.newform_lift_level_character b0
  have f2 : Ad3.R.F2 := @GlobalTheory.T.newform_lift_whittaker_expansion
  have f3a : Ad3.R.HeckeSumLocalTranslates := @GlobalTheory.T.newform_lift_local_type b0
  have f3 : Ad3.R.F3 := @GlobalTheory.T.newform_lift_hecke_eigenvalues b0 c0 c1 f0b f1 f1b f3a
  have f5 : Ad3.R.F5 := @GlobalTheory.T.newform_lift_rapid_decay b0
  have f4 : Ad3.R.F4 := @GlobalTheory.T.newform_lift_fourier_coefficients b0 c1 u2 g0 g1 f0b f1 f2 f3 f5
  obtain ⟨hform, heig⟩ := Ad3P.sEig k N hk χ g
  obtain ⟨ω, hω⟩ := f0 N χ
  obtain ⟨-, φ, hφ⟩ := f1 k N χ _ _ hform g.one ω hω
  obtain ⟨v, rfl⟩ := b0.2.2.1 p hp
  have h := f4 k N hk χ hχ _ _ hform heig ω φ hω hφ v hpN
  exact norm_sq_of_scaled k _ hk hp.two_le _ h
end
