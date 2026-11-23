module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Lean.Meta.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Module Matrix
open scoped ComplexOrder

noncomputable section

section Embedding

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}


end Embedding

end

end GroundTheory.Heights₂.Heights
end

section

namespace GroundTheory.Heights₂.Heights

open Algebra Cardinal MvPolynomial

noncomputable section

theorem trdeg_lt_of_surjective_of_ker_ne_bot {R B C : Type} [CommRing R] [CommRing B] [IsDomain B]
    [CommRing C] [IsDomain C] [Algebra R B] [Algebra R C] (f : B →ₐ[R] C)
    (hf : Function.Surjective f) (hker : RingHom.ker f ≠ ⊥)
    (hinj : Function.Injective (algebraMap R C)) (hfin : trdeg R B < ℵ₀) :
    trdeg R C < trdeg R B := by
  have : Nontrivial R := (algebraMap R C).domain_nontrivial
  have : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).2 hinj
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R C
  have hCle : trdeg R C ≤ trdeg R B := trdeg_le_of_surjective f hf
  have hs_card : #s = trdeg R C := hs.cardinalMk_eq_trdeg
  have : Finite s := Cardinal.lt_aleph0_iff_finite.mp (hs_card ▸ hCle.trans_lt hfin)
  let y : s → B := fun i => Function.surjInv hf (i : C)
  have hfy : ∀ i, f (y i) = i := fun i => Function.surjInv_eq hf _
  have hfy' : (fun i => f (y i)) = ((↑) : s → C) := funext hfy
  have hy : AlgebraicIndependent R y := AlgebraicIndependent.of_comp f (by
    change AlgebraicIndependent R (fun i => f (y i))
    rw [hfy']
    exact hs.1)
  by_contra hlt
  push Not at hlt
  have hyb : IsTranscendenceBasis R y :=
    hy.isTranscendenceBasis_of_trdeg_le_of_finite (hlt.trans hs_card.ge)
  have halg := hyb.isAlgebraic
  obtain ⟨q, hq, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hne := Ideal.under_ne_bot_of_algebraic_mem hq0 hq (halg.isAlgebraic q)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have ha' : f (a : B) = 0 := by
    simpa [Ideal.mem_comap, RingHom.mem_ker] using ha
  obtain ⟨P, hP⟩ : ∃ P : MvPolynomial s R, aeval y P = a := by
    have h : (a : B) ∈ (aeval y : MvPolynomial s R →ₐ[R] B).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact a.2
    exact h
  have hPx : aeval ((↑) : s → C) P = 0 := by
    rw [← hfy', ← comp_aeval_apply, hP, ha']
  have hP0 : P = 0 := hs.1 (hPx.trans (map_zero _).symm)
  apply ha0
  apply Subtype.ext
  rw [← hP, hP0, map_zero]
  rfl

theorem trdeg_zmod_quotient_le {B : Type} [CommRing B] [IsDomain B] [Algebra ℤ B]
    (hinj : Function.Injective (algebraMap ℤ B)) (p : ℕ) [Fact p.Prime] (Q : Ideal B) [Q.IsPrime]
    [CharP (B ⧸ Q) p] :
    (letI := ZMod.algebra (B ⧸ Q) p
     trdeg (ZMod p) (B ⧸ Q) ≤ trdeg ℤ B) := by
  let := ZMod.algebra (B ⧸ Q) p
  have : FaithfulSMul (ZMod p) (B ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap (ZMod p) (B ⧸ Q)).injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (ZMod p) (B ⧸ Q)
  rw [← hs.cardinalMk_eq_trdeg]
  let y : s → B := fun i => Function.surjInv Ideal.Quotient.mk_surjective (i : B ⧸ Q)
  have hy : (fun i => Ideal.Quotient.mkₐ ℤ Q (y i)) = ((↑) : s → B ⧸ Q) :=
    funext fun i => Function.surjInv_eq Ideal.Quotient.mk_surjective _
  have hp0 : (p : B) ≠ 0 := by
    intro h
    have : algebraMap ℤ B (p : ℤ) = algebraMap ℤ B 0 := by simpa using h
    exact (Nat.Prime.ne_zero (Fact.out : p.Prime)) (by exact_mod_cast hinj this)

  have hred : ∀ P : MvPolynomial s ℤ, aeval y P = 0 →
      MvPolynomial.map (algebraMap ℤ (ZMod p)) P = 0 := by
    intro P hP
    apply hs.1
    have hc : (algebraMap (ZMod p) (B ⧸ Q)).comp (algebraMap ℤ (ZMod p)) = algebraMap ℤ (B ⧸ Q) :=
      RingHom.ext_int _ _
    rw [map_zero, aeval_def, eval₂_map, hc, ← aeval_def, ← hy, ← comp_aeval_apply, hP, map_zero]
  have key : ∀ n : ℕ, ∀ P : MvPolynomial s ℤ, aeval y P = 0 →
      ∀ m, P.coeff m ≠ 0 → (P.coeff m).natAbs ≤ n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P hP m hm hn
      have hdvd : C (p : ℤ) ∣ P := by
        rw [C_dvd_iff_dvd_coeff]
        intro i
        have := congrArg (AddMonoidAlgebra.coeff · i) (hred P hP)
        rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, algebraMap_int_eq, eq_intCast,
          ZMod.intCast_zmod_eq_zero_iff_dvd] at this
        exact this
      obtain ⟨P', rfl⟩ := hdvd
      have hP' : aeval y P' = 0 := by
        rw [map_mul, aeval_C] at hP
        rcases mul_eq_zero.mp hP with h | h
        · exact absurd (by simpa using h) hp0
        · exact h
      rw [coeff_C_mul] at hm hn
      have hm' : P'.coeff m ≠ 0 := right_ne_zero_of_mul hm
      have hlt : (P'.coeff m).natAbs < n := by
        rw [Int.natAbs_mul] at hn
        have h2 : 2 ≤ ((p : ℤ)).natAbs := by
          simpa using (Fact.out : p.Prime).two_le
        have h1 : 0 < (P'.coeff m).natAbs := Int.natAbs_pos.mpr hm'
        nlinarith
      exact ih _ hlt P' hP' m hm' le_rfl
  refine AlgebraicIndependent.cardinalMk_le_trdeg (R := ℤ) (x := y) ?_
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hne
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hne
  exact key _ P hP m hm le_rfl

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def FibreCompDimZ.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℤ)), P.IsPrime →
    P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥ → ∀ (d p : ℕ), p.Prime →
      ringKrullDim (MvPolynomial σ ℤ ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞) →
        ∀ W ∈ (P ⊔ Ideal.span {(C (p : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes,
          ringKrullDim (MvPolynomial σ ℤ ⧸ W) = ((d : ℕ) : WithBot ℕ∞)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace HadamardGramBound

theorem det_gram_le_prod_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (w : Fin n → V) (hw : LinearIndependent ℝ w) :
    (Matrix.gram ℝ w).det ≤ ∏ i, ‖w i‖ ^ 2 := by
  set K := Submodule.span ℝ (Set.range w)
  have hK : Module.finrank ℝ K = Fintype.card (Fin n) := finrank_span_eq_card hw
  have : FiniteDimensional ℝ K := FiniteDimensional.span_of_finite ℝ (Set.finite_range w)
  let w' : Fin n → K := fun i => ⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hg : Matrix.gram ℝ w = Matrix.gram ℝ w' := by
    ext i j
    simp [Matrix.gram_apply, w']
  let gb := InnerProductSpace.gramSchmidtOrthonormalBasis hK w'
  have hdet : gb.toBasis.det w' = ∏ i, inner ℝ (gb i) (w' i) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det hK w'
  rw [hg, Matrix.gram_eq_conjTranspose_mul gb, Matrix.det_mul, Matrix.det_conjTranspose]
  have hM : (Matrix.of fun i j => gb.repr (w' j) i) = gb.toBasis.toMatrix w' := by
    ext i j
    simp [Module.Basis.toMatrix_apply]
  rw [hM, ← Module.Basis.det_apply, hdet, star_trivial, ← sq, ← Finset.prod_pow]
  refine Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) (fun i _ => ?_)
  have h1 := abs_real_inner_le_norm (gb i) (w' i)
  rw [gb.orthonormal.1 i, one_mul] at h1
  have h2 : ‖w' i‖ = ‖w i‖ := rfl
  rw [← h2, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

end HadamardGramBound

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField Matrix
open scoped ComplexOrder

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def latticeDual {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) : Submodule (𝓞 K) (Fin m → K) where
  carrier := {φ | ∀ v ∈ L, φ ⬝ᵥ v ∈ Set.range (algebraMap (𝓞 K) K)}
  add_mem' := by
    intro φ ψ hφ hψ v hv
    obtain ⟨a, ha⟩ := hφ v hv
    obtain ⟨b, hb⟩ := hψ v hv
    exact ⟨a + b, by rw [map_add (f := _), ha, hb, add_dotProduct]⟩
  zero_mem' := fun v _ ↦ ⟨0, by rw [map_zero, zero_dotProduct]⟩
  smul_mem' := by
    intro c φ hφ v hv
    obtain ⟨a, ha⟩ := hφ v hv
    exact ⟨c * a, by rw [map_mul, ha, smul_dotProduct, Algebra.smul_def]⟩

structure IsDualBasis {m N : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) (φ : Fin (N + 1) → Fin m → K) : Prop where
  independent : LinearIndependent ℤ φ
  span_eq : Submodule.span ℤ (Set.range φ) = (latticeDual L).restrictScalars ℤ

end

end GroundTheory.Heights₂.Heights
end

section

namespace GroundTheory.Heights₂.Heights

noncomputable section

def IntDomainDim.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℤ A] [IsDomain A] [Algebra.FiniteType ℤ A],
    Function.Injective (algebraMap ℤ A) →
      ringKrullDim A = (((Algebra.trdeg ℤ A).toENat + 1 : ℕ∞) : WithBot ℕ∞)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights
end
