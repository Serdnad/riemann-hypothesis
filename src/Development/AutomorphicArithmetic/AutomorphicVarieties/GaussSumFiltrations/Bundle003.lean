module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section
namespace GlobalTheory.HilbertThetaSeries.RatSlash

variable {F : Type} [Field F] [NumberField F]

theorem cmp_scalar_mul (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (v : InfinitePlace F) :
    cmp v (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) = Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Units.map (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) v).toMonoidHom t) * cmp v h := by
  rw [map_mul]
  congr 1
  ext i j
  simp [cmp, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem det_scalar_mul (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) t * h : GL (Fin 2) (InfinitePlace F → ℝ)) :
      Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det =
      (t : InfinitePlace F → ℝ) ^ 2 * (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_mul]

theorem unit_ne (t : (InfinitePlace F → ℝ)ˣ) (v : InfinitePlace F) : (t : InfinitePlace F → ℝ) v ≠ 0 := fun h0 => by
  have := congrFun t.mul_inv v
  simp [h0] at this

theorem denom_scalar_mul (u : ℝˣ) (g : GL (Fin 2) ℝ) (z : ℂ) :
    UpperHalfPlane.denom (Matrix.GeneralLinearGroup.scalar (Fin 2) u * g) z = ((u : ℝ) : ℂ) * UpperHalfPlane.denom g z := by
  simp [UpperHalfPlane.denom, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem sl_scalar_mul {k : ℕ} (hk : Even k) (f : Hn F → ℂ) (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    sl k (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) f = sl k h f := by
  obtain ⟨m, rfl⟩ := hk
  funext z
  have hact : act (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) z = act h z := by
    unfold act
    funext v
    rw [cmp_scalar_mul, mul_smul, UpperHalfPlane.glScalar_smul]
  have hdet : ∏ v, |((Matrix.GeneralLinearGroup.scalar (Fin 2) t * h : GL (Fin 2) (InfinitePlace F → ℝ)) :
      Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| =
      (∏ v, (t : InfinitePlace F → ℝ) v) ^ 2 * ∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| := by
    rw [det_scalar_mul, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    simp [abs_mul, sq_abs]
  have hden : ∏ v, UpperHalfPlane.denom (cmp v (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h)) (z v) =
      ((∏ v, (t : InfinitePlace F → ℝ) v : ℝ) : ℂ) * ∏ v, UpperHalfPlane.denom (cmp v h) (z v) := by
    simp_rw [cmp_scalar_mul, denom_scalar_mul]
    rw [Finset.prod_mul_distrib]
    push_cast
    simp
  have hP : (∏ v, (t : InfinitePlace F → ℝ) v) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => unit_ne t v)
  have hQ : 0 ≤ ∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| :=
    Finset.prod_nonneg (fun v _ => abs_nonneg _)
  have hexp : (((m + m : ℕ) : ℝ) / 2) = ((m : ℕ) : ℝ) := by
    push_cast
    ring
  unfold sl sl0
  rw [hact, hdet, hden, Real.mul_rpow (by positivity) hQ, hexp, Real.rpow_natCast, ← pow_mul]
  set P := ∏ v, (t : InfinitePlace F → ℝ) v
  have hPC : (P : ℂ) ≠ 0 := by exact_mod_cast hP
  push_cast
  rw [mul_inv, mul_pow, inv_pow (P : ℂ)]
  field_simp
  ring

variable [IsTotallyReal F]

theorem ofReal_rhom (v : InfinitePlace F) (x : F) : ((rhom x v : ℝ) : ℂ) = v.embedding x :=
  InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x

theorem rhom_apply (v : InfinitePlace F) (x : F) : rhom x v = reAt v x := by
  unfold rhom reAt
  show InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x = (v.embedding x).re
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]

theorem ofReal_reAt (v : InfinitePlace F) (x : F) : ((reAt v x : ℝ) : ℂ) = v.embedding x := by
  rw [← rhom_apply, ofReal_rhom]


variable (F) in
def embEquiv : InfinitePlace F ≃ (F →+* ℂ) where
  toFun v := v.embedding
  invFun φ := InfinitePlace.mk φ
  left_inv v := InfinitePlace.mk_embedding v
  right_inv φ := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))

theorem prod_reAt (x : F) : ∏ v, reAt v x = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [ofReal_reAt]
  have h1 : ∏ v : InfinitePlace F, v.embedding x = ∏ φ : F →+* ℂ, φ x :=
    Equiv.prod_comp (embEquiv F) (fun φ => φ x)
  have h2 : ∏ φ : F →+* ℂ, φ x = ∏ σ : F →ₐ[ℚ] ℂ, σ x :=
    Equiv.prod_comp (RingHom.equivRatAlgHom F ℂ) (fun σ : F →ₐ[ℚ] ℂ => σ x)
  rw [h1, h2, ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast]

theorem sum_reAt (x : F) : ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [ofReal_reAt]
  have h1 : ∑ v : InfinitePlace F, v.embedding x = ∑ φ : F →+* ℂ, φ x :=
    Equiv.sum_comp (embEquiv F) (fun φ => φ x)
  have h2 : ∑ φ : F →+* ℂ, φ x = ∑ σ : F →ₐ[ℚ] ℂ, σ x :=
    Equiv.sum_comp (RingHom.equivRatAlgHom F ℂ) (fun σ : F →ₐ[ℚ] ℂ => σ x)
  rw [h1, h2, ← trace_eq_sum_embeddings ℂ, eq_ratCast]

theorem det_toInf (γ : GL (Fin 2) F) :
    ((toInf γ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det = rhom γ.val.det := by
  rw [RingHom.map_det]; rfl

theorem toInf_scalar (η : Fˣ) : toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (rhom (F := F)).toMonoidHom η) := by
  ext i j v
  simp [toInf, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem rat_slash : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ), (∀ v (x : F), rhom x v = reAt v x) ∧ (∀ γ : GL (Fin 2) F, (Pos (toInf γ) ↔ TP γ.val.det) ∧ sl k (toInf γ) f = ((|((Algebra.norm ℚ γ.val.det : ℚ) : ℝ)| ^ ((k : ℝ) / 2) : ℝ) : ℂ) • sl0 k (toInf γ) f) ∧ (Even k → ∀ (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)), Pos h → Pos (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) ∧ sl k (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) f = sl k h f) ∧ (∀ η : Fˣ, toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (rhom (F := F)).toMonoidHom η)) ∧ ∀ x : F, ∏ v, reAt v x = ((Algebra.norm ℚ x : ℚ) : ℝ) ∧ ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  intro F _ _ _ k f
  refine ⟨rhom_apply, fun γ => ⟨?_, ?_⟩, fun hk t h hh => ⟨?_, sl_scalar_mul hk f t h⟩, toInf_scalar,
    fun x => ⟨prod_reAt x, sum_reAt x⟩⟩
  · unfold Pos TP
    rw [det_toInf]
    simp only [rhom_apply]
  · funext z
    unfold sl
    rw [det_toInf]
    simp only [rhom_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.abs_prod, prod_reAt]
  · unfold Pos at hh ⊢
    intro v
    rw [det_scalar_mul]
    have h1 := unit_ne t v
    have h2 := hh v
    simp only [Pi.mul_apply, Pi.pow_apply]
    positivity

end GlobalTheory.HilbertThetaSeries.RatSlash

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.hilbert_slash_rational_matrix_properties : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ), (∀ v (x : F), rhom x v = reAt v x) ∧ (∀ γ : GL (Fin 2) F, (Pos (toInf γ) ↔ TP γ.val.det) ∧ sl k (toInf γ) f = ((|((Algebra.norm ℚ γ.val.det : ℚ) : ℝ)| ^ ((k : ℝ) / 2) : ℝ) : ℂ) • sl0 k (toInf γ) f) ∧ (Even k → ∀ (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)), Pos h → Pos (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) ∧ sl k (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) f = sl k h f) ∧ (∀ η : Fˣ, toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (rhom (F := F)).toMonoidHom η)) ∧ ∀ x : F, ∏ v, reAt v x = ((Algebra.norm ℚ x : ℚ) : ℝ) ∧ ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  first | exact @GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash | exact GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash | (intros; apply GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash <;> assumption)
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.QAff

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem rhom_eq (v : InfinitePlace F) (x : F) : rhom x v = reAt v x := (rfl)

theorem sum_reAt (x : F) : ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  have hv : ∀ v : InfinitePlace F, ((reAt v x : ℝ) : ℂ) = v.embedding x := fun v =>
    InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x
  rw [Complex.ofReal_sum, Complex.ofReal_ratCast]
  simp_rw [hv]
  rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ)]
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => φ x)
    (fun σ : F →ₐ[ℚ] ℂ => σ x) (fun _ => rfl)]
  symm
  refine Fintype.sum_equiv ((Equiv.subtypeUnivEquiv
    (fun φ : F →+* ℂ => IsTotallyReal.complexEmbedding_isReal φ)).symm.trans
    (InfinitePlace.mkReal.trans
      (Equiv.subtypeUnivEquiv (fun v : InfinitePlace F => IsTotallyReal.isReal v)))) _ _ ?_
  intro φ
  simp [InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)]

theorem reAt_mul (v : InfinitePlace F) (x y : F) : reAt v (x * y) = reAt v x * reAt v y := by
  rw [← rhom_eq, ← rhom_eq, ← rhom_eq, map_mul, Pi.mul_apply]

theorem e00 (ε : Fˣ) (b : F) (v : InfinitePlace F) :
    ((cmp v (toInf (aff ε b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = reAt v (ε : F) :=
  rhom_eq v _

theorem e01 (ε : Fˣ) (b : F) (v : InfinitePlace F) :
    ((cmp v (toInf (aff ε b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = reAt v b :=
  rhom_eq v _

theorem e10 (ε : Fˣ) (b : F) (v : InfinitePlace F) :
    ((cmp v (toInf (aff ε b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  simp [cmp, toInf, aff]

theorem e11 (ε : Fˣ) (b : F) (v : InfinitePlace F) :
    ((cmp v (toInf (aff ε b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := by
  simp [cmp, toInf, aff]

theorem denom_aff (ε : Fˣ) (b : F) (v : InfinitePlace F) (w : ℂ) :
    UpperHalfPlane.denom (cmp v (toInf (aff ε b))) w = 1 := by
  rw [UpperHalfPlane.denom, e10, e11]; simp

theorem act_aff (ε : Fˣ) (b : F) (hε : TP (ε : F)) (z : Hn F) (v : InfinitePlace F) :
    ((act (toInf (aff ε b)) z v : UpperHalfPlane) : ℂ) = (reAt v (ε : F) : ℂ) * (z v : ℂ) + (reAt v b : ℂ) := by
  have hd : 0 < ((Matrix.GeneralLinearGroup.det (cmp v (toInf (aff ε b))) : ℝˣ) : ℝ) := by
    simpa [Matrix.det_fin_two, e00, e01, e10, e11] using hε v
  simp only [act]
  rw [UpperHalfPlane.coe_smul_of_det_pos hd, denom_aff, div_one, UpperHalfPlane.num]
  simp [e00, e01]

theorem ez_aff (ε : Fˣ) (b : F) (hε : TP (ε : F)) (z : Hn F) (η : F) :
    ez η (act (toInf (aff ε b)) z) = ez (η * ε) z * et (η * b) := by
  simp only [ez, et, act_aff ε b hε]
  rw [← Complex.exp_add, ← Complex.ofReal_ratCast, ← sum_reAt]
  congr 1
  simp only [reAt_mul]
  push_cast
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun v _ => ?_)
  ring

theorem weightSlash_hilbertAffine_apply (k : ℕ) (f : Hn F → ℂ) (ε : Fˣ) (b : F) (z : Hn F) :
    sl0 k (toInf (aff ε b)) f z = f (act (toInf (aff ε b)) z) := by
  simp only [sl0, denom_aff, Finset.prod_const_one, inv_one, one_pow, one_mul]

omit [IsTotallyReal F] in
theorem exists_den (x : F) : ∃ E : ℕ, 0 < E ∧ IsIntegral ℤ ((E : F) * x) := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  rw [Algebra.smul_def, algebraMap_int_eq, Int.coe_castRingHom] at hint
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rcases le_total 0 y with h | h
  · have e : ((y.natAbs : ℕ) : F) = (y : F) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg h]
    rw [e]
    exact hint
  · have e : ((y.natAbs : ℕ) : F) = -(y : F) := by
      rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos h, Int.cast_neg]
    rw [e, neg_mul]
    exact hint.neg

theorem hasQ_aff : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ) (a : F → ℂ) (ε : Fˣ) (b : F),
    TP (ε : F) → HasQ f a → HasQ (sl0 k (toInf (aff ε b)) f) (fun ξ => a (ξ / ε) * et (ξ / ε * b)) := by
  intro F _ _ _ k f a ε b hε hf
  obtain ⟨⟨D, hD, hDa⟩, hsum⟩ := hf
  obtain ⟨E, hE, hEint⟩ := exists_den (ε : F)
  have hε0 : (ε : F) ≠ 0 := ε.ne_zero
  refine ⟨⟨D * E, by positivity, ?_⟩, ?_⟩
  · intro ξ hξ
    have ha : a (ξ / ε) ≠ 0 := fun h0 => hξ (by simp [h0])
    obtain ⟨h1, h2⟩ := hDa _ ha
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | h1
      · left
        rwa [div_eq_zero_iff, or_iff_left hε0] at h1
      · right
        intro v
        have hp := mul_pos (h1 v) (hε v)
        rwa [← reAt_mul, div_mul_cancel₀ _ hε0] at hp
    · have hm := h2.mul hEint
      have e : ((D * E : ℕ) : F) * ξ = ((D : F) * (ξ / ε)) * ((E : F) * ε) := by
        push_cast
        field_simp
      rw [e]
      exact hm
  · intro z
    have hs := hsum (act (toInf (aff ε b)) z)
    simp only [ez_aff ε b hε z] at hs
    rw [weightSlash_hilbertAffine_apply]
    have hc := (Equiv.hasSum_iff (Units.mulRight ε⁻¹)).mpr hs
    convert hc using 1
    funext ξ
    simp only [Function.comp_apply, Units.mulRight_apply, Units.val_inv_eq_inv_val]
    rw [← div_eq_mul_inv, div_mul_cancel₀ _ hε0]
    ring

end GlobalTheory.HilbertThetaSeries.QAff

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.hasQExpansion_affineTranslate_coeff : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ) (a : F → ℂ) (ε : Fˣ) (b : F), TP (ε : F) → HasQ f a → HasQ (sl0 k (toInf (aff ε b)) f) (fun ξ => a (ξ / ε) * et (ξ / ε * b)) := by
  first | exact @GlobalTheory.HilbertThetaSeries.QAff.hasQ_aff | exact GlobalTheory.HilbertThetaSeries.QAff.hasQ_aff | (intros; apply GlobalTheory.HilbertThetaSeries.QAff.hasQ_aff <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section
namespace GlobalTheory.HilbertThetaSeries.FormLat

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem symm_of_evenPos {G : Matrix κ κ ℤ} (hG : EvenPos G) : Gᵀ = G := by
  have h := hG.1.1
  ext i j
  have := congrFun (congrFun h i) j
  simp [Matrix.conjTranspose_apply, Matrix.map_apply] at this
  simp only [Matrix.transpose_apply]
  exact_mod_cast this

theorem bf_symm {G : Matrix κ κ ℤ} (hG : Gᵀ = G) (x y : κ → F) : BF G x y = BF G y x := by
  unfold BF
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.transpose_map, hG]

theorem bf_add_left (G : Matrix κ κ ℤ) (x y z : κ → F) : BF G (x + y) z = BF G x z + BF G y z := by
  unfold BF; rw [add_dotProduct]

theorem bf_add_right (G : Matrix κ κ ℤ) (x y z : κ → F) : BF G x (y + z) = BF G x y + BF G x z := by
  unfold BF; rw [Matrix.mulVec_add, dotProduct_add]

theorem bf_smul_left (G : Matrix κ κ ℤ) (a : F) (x y : κ → F) : BF G (a • x) y = a * BF G x y := by
  unfold BF; rw [smul_dotProduct, smul_eq_mul]

theorem bf_smul_right (G : Matrix κ κ ℤ) (a : F) (x y : κ → F) : BF G x (a • y) = a * BF G x y := by
  unfold BF; rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem qf_add {G : Matrix κ κ ℤ} (hG : Gᵀ = G) (x y : κ → F) : QF G (x + y) = QF G x + BF G x y + QF G y := by
  unfold QF
  rw [bf_add_left, bf_add_right, bf_add_right, bf_symm hG y x]
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  field_simp
  ring

theorem mem_LL {x : κ → F} : x ∈ LL F κ ↔ ∀ i, IsIntegral ℤ (x i) := by
  simp [LL, AddSubgroup.mem_pi, mem_integralClosure_iff]

theorem intCast_isIntegral (n : ℤ) : IsIntegral ℤ (n : F) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := F) (x := n)

theorem bf_int (G : Matrix κ κ ℤ) {x y : κ → F} (hx : ∀ i, IsIntegral ℤ (x i)) (hy : ∀ i, IsIntegral ℤ (y i)) :
    IsIntegral ℤ (BF G x y) := by
  unfold BF
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply]
  exact IsIntegral.sum _ fun i _ => (hx i).mul (IsIntegral.sum _ fun j _ => (intCast_isIntegral _).mul (hy j))

theorem trace_int {x : F} (hx : IsIntegral ℤ x) : ∃ n : ℤ, Algebra.trace ℚ F x = n := by
  have := Algebra.isIntegral_trace (L := ℚ) hx
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp this
  exact ⟨n, by rw [← hn]; simp⟩

theorem qf_single (G : Matrix κ κ ℤ) (i : κ) (c : F) : QF G (Pi.single i c) = c * ((G i i : F) * c) / 2 := by
  simp [QF, BF, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem qf_int {G : Matrix κ κ ℤ} (hG : EvenPos G) {x : κ → F} (hx : ∀ i, IsIntegral ℤ (x i)) : IsIntegral ℤ (QF G x) := by
  have hs : Gᵀ = G := symm_of_evenPos hG
  have hsingle : ∀ i, IsIntegral ℤ (QF G (Pi.single i (x i))) := by
    intro i
    obtain ⟨m, hm⟩ := hG.2 i
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    have : QF G (Pi.single i (x i)) = (m : F) * x i * x i := by
      rw [qf_single, hm]; push_cast; field_simp; ring
    rw [this]
    exact ((intCast_isIntegral m).mul (hx i)).mul (hx i)
  have hvi : ∀ (s : Finset κ) (j : κ), IsIntegral ℤ ((∑ i ∈ s, Pi.single i (x i) : κ → F) j) := by
    intro s j
    rw [Finset.sum_apply]
    exact IsIntegral.sum _ fun i _ => by
      by_cases h : j = i
      · subst h; simpa using hx j
      · simp [Pi.single_apply, h, isIntegral_zero]
  have key : ∀ s : Finset κ, IsIntegral ℤ (QF G (∑ i ∈ s, Pi.single i (x i))) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa [QF, BF] using (isIntegral_zero : IsIntegral ℤ (0 : F))
    · intro i s hi ih
      rw [Finset.sum_insert hi, qf_add hs]
      refine ((hsingle i).add (bf_int G ?_ (hvi s))).add ih
      intro j
      by_cases h : j = i
      · subst h; simpa using hx j
      · simp [Pi.single_apply, h, isIntegral_zero]
  simpa [Finset.univ_sum_single] using key Finset.univ

theorem et_props (x y : F) : et (x + y) = et x * et y ∧ ‖et x‖ = 1 ∧ (et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n) ∧
    (IsIntegral ℤ x → et x = 1) := by
  have h0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have hiff : et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n := by
    unfold et
    rw [Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
        apply mul_left_cancel₀ h0
        rw [hn]; push_cast; ring
      exact_mod_cast this
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [hn]; push_cast; ring⟩
  refine ⟨?_, ?_, hiff, fun hx => hiff.mpr (trace_int hx)⟩
  · unfold et; rw [map_add (f := _), Rat.cast_add, mul_add, Complex.exp_add]
  · unfold et
    have : 2 * (Real.pi : ℂ) * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ) =
        ((2 * Real.pi * (Algebra.trace ℚ F x : ℚ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]

end GlobalTheory.HilbertThetaSeries.FormLat


open GlobalTheory.HilbertThetaSeries.FormLat in
theorem GlobalTheory.HilbertThetaSeries.formLatticeProps : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → (∀ x y : κ → F, BF G x y = BF G y x ∧ QF G (x + y) = QF G x + BF G x y + QF G y) ∧ (∀ (a : F) (x y : κ → F), BF G (a • x) y = a * BF G x y ∧ QF G (a • x) = a ^ 2 * QF G x ∧ QF G (-x) = QF G x) ∧ (∀ x y z : κ → F, BF G (x + y) z = BF G x z + BF G y z) ∧ (∀ x ∈ LL F κ, IsIntegral ℤ (QF G x) ∧ ∀ y ∈ LL F κ, IsIntegral ℤ (BF G x y)) ∧ (∀ x : κ → F, x ∈ LL F κ ↔ ∀ i, IsIntegral ℤ (x i)) ∧ (∀ (a : F) (x : κ → F), x ∈ aL κ a ↔ ∃ l ∈ LL F κ, x = a • l) ∧ (∀ x y : F, et (x + y) = et x * et y ∧ ‖et x‖ = 1 ∧ (et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n) ∧ (IsIntegral ℤ x → et x = 1)) ∧ LL F κ ≤ dualL F G := by
  intro F _ _ κ _ _ G hG
  have hs : Gᵀ = G := symm_of_evenPos hG
  refine ⟨fun x y => ⟨bf_symm hs x y, qf_add hs x y⟩, fun a x y => ⟨bf_smul_left G a x y, ?_, ?_⟩,
    bf_add_left G, fun x hx => ⟨qf_int hG (mem_LL.mp hx), fun y hy => bf_int G (mem_LL.mp hx) (mem_LL.mp hy)⟩,
    fun x => mem_LL, fun a x => ?_, et_props, ?_⟩
  · unfold QF; rw [bf_smul_left, bf_smul_right]; ring
  · unfold QF BF; rw [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  · unfold aL
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, rfl⟩
  · intro y hy l hl
    exact trace_int (bf_int G (mem_LL.mp hy) (mem_LL.mp hl))

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.evenPos_gramForm_integral_lattice_properties : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → (∀ x y : κ → F, BF G x y = BF G y x ∧ QF G (x + y) = QF G x + BF G x y + QF G y) ∧ (∀ (a : F) (x y : κ → F), BF G (a • x) y = a * BF G x y ∧ QF G (a • x) = a ^ 2 * QF G x ∧ QF G (-x) = QF G x) ∧ (∀ x y z : κ → F, BF G (x + y) z = BF G x z + BF G y z) ∧ (∀ x ∈ LL F κ, IsIntegral ℤ (QF G x) ∧ ∀ y ∈ LL F κ, IsIntegral ℤ (BF G x y)) ∧ (∀ x : κ → F, x ∈ LL F κ ↔ ∀ i, IsIntegral ℤ (x i)) ∧ (∀ (a : F) (x : κ → F), x ∈ aL κ a ↔ ∃ l ∈ LL F κ, x = a • l) ∧ (∀ x y : F, et (x + y) = et x * et y ∧ ‖et x‖ = 1 ∧ (et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n) ∧ (IsIntegral ℤ x → et x = 1)) ∧ LL F κ ≤ dualL F G := by
  first | exact @GlobalTheory.HilbertThetaSeries.formLatticeProps | exact GlobalTheory.HilbertThetaSeries.formLatticeProps | (intros; apply GlobalTheory.HilbertThetaSeries.formLatticeProps <;> assumption)
end
end
