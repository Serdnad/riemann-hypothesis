module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle111
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle016
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle145
public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle675
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle112
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle121
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle124
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open TensorProduct

namespace GlobalTheory.IdemSplit

variable {R : Type*} [CommRing R] {n : ℕ}

def fold (e : R) (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := e • M + (1 - e) • 1

theorem fold_mul_fold {e : R} (he : e * e = e) (X Y : Matrix (Fin n) (Fin n) R) :
    fold e X * fold (1 - e) Y = e • X + (1 - e) • Y := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h0' : (1 - e) * e = 0 := by rw [mul_comm, h0]
  have h1 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, h0, sub_zero]
  simp only [fold, sub_sub_cancel, add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, h0, h0',
    he, h1, zero_smul, zero_add, add_zero]
  exact add_comm _ _

theorem fold_mul_fold' {e : R} (he : e * e = e) (X Y : Matrix (Fin n) (Fin n) R) :
    fold (1 - e) Y * fold e X = e • X + (1 - e) • Y := by
  have he' : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have h := fold_mul_fold he' Y X
  rw [sub_sub_cancel] at h
  rw [h, add_comm]

theorem fold_mul {e : R} (he : e * e = e) (X Y : Matrix (Fin n) (Fin n) R) :
    fold e X * fold e Y = fold e (X * Y) := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h0' : (1 - e) * e = 0 := by rw [mul_comm, h0]
  have h1 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, h0, sub_zero]
  simp only [fold, add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, h0, h0',
    he, h1, zero_smul, zero_add, add_zero]

theorem fold_one (e : R) : fold e (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [fold, ← add_smul, add_sub_cancel, one_smul]

theorem conjT_fold (σ : R →+* R) {e : R} (hσ : σ e = e) (M : Matrix (Fin n) (Fin n) R) :
    conjT σ (fold e M) = fold e (conjT σ M) := by
  ext i j
  simp only [conjT, fold, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hσ, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

def unitsFold {e : R} (he : e * e = e) (g : GL (Fin n) R) : GL (Fin n) R :=
  ⟨fold e g, fold e (g⁻¹ : GL (Fin n) R), by rw [fold_mul he, Units.mul_inv, fold_one],
    by rw [fold_mul he, Units.inv_mul, fold_one]⟩

theorem unitsFold_mem_UGroup (σ : R →+* R) (hσ2 : ∀ x, σ (σ x) = x) {e : R} (he : e * e = e)
    (hσ : σ e = e) (g : GL (Fin n) R) (hg : g ∈ UGroup n σ hσ2) :
    unitsFold he g ∈ UGroup n σ hσ2 := by
  have hg' : (g : Matrix (Fin n) (Fin n) R) * conjT σ g = 1 := hg
  show fold e (g : Matrix (Fin n) (Fin n) R) * conjT σ (fold e (g : Matrix (Fin n) (Fin n) R)) = 1
  rw [conjT_fold σ hσ, fold_mul he, hg', fold_one]

theorem fold_apply (e : R) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    fold e M i j = e * M i j + (1 - e) * (1 : Matrix (Fin n) (Fin n) R) i j := by
  simp [fold]

end GlobalTheory.IdemSplit

namespace GlobalTheory.CongSplit

open GlobalTheory.IdemSplit GlobalTheory.InertUmax

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

def idemAt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AL L :=
  (1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1

theorem compAt_idemAt_self (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    compAt L v (idemAt L v) = 1 := by
  rw [idemAt, compAt_tmul, sgl_same]; rfl

theorem compAt_idemAt_ne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    {w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hw : w ≠ v) :
    compAt L w (idemAt L v) = 0 := by
  rw [idemAt, compAt_tmul, sgl_ne L v 1 hw, tmul_zero]

theorem idemAt_mul_self (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    idemAt L v * idemAt L v = idemAt L v := by
  apply sub_eq_zero.1
  apply eq_zero_of_compAt
  intro w
  rw [map_sub, map_mul]
  rcases eq_or_ne w v with rfl | hw
  · rw [compAt_idemAt_self, mul_one, sub_self]
  · rw [compAt_idemAt_ne L v hw, mul_zero, sub_self]

theorem idemAt_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : idemAt L v ∈ ALint L :=
  one_tmul_sgl_mem L v 1 (one_mem _)

theorem conjAL_idemAt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    conjAL L (idemAt L v) = idemAt L v := by
  simp [conjAL, idemAt, Algebra.TensorProduct.map_tmul]

theorem one_apply_mem {n : ℕ} (i j : Fin n) : (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem compAt_one_apply {n : ℕ} (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (i j : Fin n) :
    compAt L w ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
  simp only [Matrix.one_apply]
  split_ifs <;> simp


variable {L} in
def gaFold {n : ℕ} {f : AL L} (hf : f * f = f) (hσ : conjAL L f = f) (g : GAf L n) : GAf L n :=
  ⟨unitsFold hf g.1, unitsFold_mem_UGroup (conjAL L) (conjAL_conjAL L) hf hσ g.1 g.2⟩

theorem gaFold_val {n : ℕ} {f : AL L} (hf : f * f = f) (hσ : conjAL L f = f) (g : GAf L n) :
    ((gaFold hf hσ g).1 : Matrix (Fin n) (Fin n) (AL L)) = fold f (g.1 : Matrix (Fin n) (Fin n) (AL L)) :=
  rfl

theorem gaFold_mem_Umax {n : ℕ} {f : AL L} (hf : f * f = f) (hσ : conjAL L f = f) (hfi : f ∈ ALint L)
    (g : GAf L n) (hg : g ∈ Umax L n) : gaFold hf hσ g ∈ Umax L n := by
  intro i j
  rw [gaFold_val, fold_apply]
  exact Subring.add_mem _ (Subring.mul_mem _ hfi (hg i j))
    (Subring.mul_mem _ (Subring.sub_mem _ (one_mem _) hfi) (one_apply_mem L i j))

theorem decomp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ) (c : GAf L n), NG.Cong L n N c → ∃ a b : GAf L n, c = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ NG.Cong L n N b ∧ ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x := by
  intro L _ _ _ n v N c hc
  set e := idemAt L v with he_def
  have he : e * e = e := idemAt_mul_self L v
  have he' : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have hσ : conjAL L e = e := conjAL_idemAt L v
  have hσ' : conjAL L (1 - e) = 1 - e := by rw [map_sub, map_one, hσ]
  have hei : e ∈ ALint L := idemAt_mem L v
  have hei' : 1 - e ∈ ALint L := Subring.sub_mem _ (one_mem _) hei
  refine ⟨gaFold he hσ c, gaFold he' hσ' c, ?_, gaFold_mem_Umax L he hσ hei c hc.1, ?_, ?_, ?_⟩
  · apply Subtype.ext; apply Units.ext
    show (c.1 : Matrix (Fin n) (Fin n) (AL L)) = fold e _ * fold (1 - e) _
    rw [fold_mul_fold he, ← add_smul, add_sub_cancel, one_smul]
  · intro w hw
    have hw' : w ≠ v := by simpa using hw
    ext i j
    rw [Matrix.map_apply, gaFold_val, fold_apply, map_add (f := _), map_mul, map_mul, map_sub, map_one,
      compAt_idemAt_ne L v hw', compAt_one_apply]
    simp
  · refine ⟨gaFold_mem_Umax L he' hσ' hei' c hc.1, fun i j => ?_⟩
    obtain ⟨y, hy, hEq⟩ := hc.2 i j
    refine ⟨(1 - e) * y, Subring.mul_mem _ hei' hy, ?_⟩
    rw [gaFold_val, fold_apply, sub_sub_cancel]
    linear_combination (1 - e) * hEq
  · intro x hx
    have hxf : (x.1 : Matrix (Fin n) (Fin n) (AL L)) = fold e (x.1 : Matrix (Fin n) (Fin n) (AL L)) := by
      ext i j
      apply sub_eq_zero.1
      rw [fold_apply]
      apply eq_zero_of_compAt
      intro w
      rcases eq_or_ne w v with rfl | hw
      · rw [map_sub, map_add (f := _), map_mul, map_mul, map_sub, map_one, compAt_idemAt_self]
        ring
      · have h := congrFun (congrFun (hx w (by simpa using hw)) i) j
        rw [Matrix.map_apply] at h
        rw [map_sub, map_add (f := _), map_mul, map_mul, map_sub, map_one, compAt_idemAt_ne L v hw,
          compAt_one_apply, h]
        ring
    apply Subtype.ext; apply Units.ext
    show (x.1 : Matrix (Fin n) (Fin n) (AL L)) * fold (1 - e) _ = fold (1 - e) _ * (x.1 : Matrix (Fin n) (Fin n) (AL L))
    rw [hxf, fold_mul_fold he, fold_mul_fold' he]

end GlobalTheory.CongSplit
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TypeTame

theorem conjSP_w_of_isConjPl : ∀ (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host), IsConjPl D.host w s.w → (GlobalTheory.TypeTame.conjSP s).w = w ∧ ∀ x : D.host.E, (GlobalTheory.TypeTame.conjSP s).i x = s.i (D.host.conj x) := by
  intro D s w hw
  have hc : ∀ z : D.host.E, IsCMField.complexConj D.host.E z = D.host.conj z := by
    intro z
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  refine ⟨?_, fun x => by rw [conjSP_i, hc]⟩
  let c : 𝓞 D.host.E →+* 𝓞 D.host.E :=
    RingOfIntegers.mapRingHom (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E)
  have hce : ∀ e : 𝓞 D.host.E, ((c e : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E (e : D.host.E) :=
    fun e => rfl
  ext x
  have h1 : x ∈ (conjSP s).w.asIdeal ↔ c x ∈ s.w.asIdeal := by
    show Valued.v ((conjSP s).i (x : D.host.E)) < 1 ↔ Valued.v (s.i ((c x : 𝓞 D.host.E) : D.host.E)) < 1
    rw [conjSP_i, hce]
  rw [h1, hw x (c x) (by rw [hce, hc])]

end GlobalTheory.TypeTame
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockConj

open Matrix
open Formalism.UG (bc GLint)

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

section Pure

variable {K : Type} [Field K] {n : ℕ}

theorem inv_val_of_diagonal {d : GL (Fin n) K} {D : Fin n → K} (hd : d.val = Matrix.diagonal D) (hD : ∀ i, D i ≠ 0) :
    (d⁻¹ : GL (Fin n) K).val = Matrix.diagonal fun i => (D i)⁻¹ := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [hd, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one with i
  exact mul_inv_cancel₀ (hD i)

theorem conj_diag_apply {d : GL (Fin n) K} {D : Fin n → K} (hd : d.val = Matrix.diagonal D) (hD : ∀ i, D i ≠ 0)
    (g : GL (Fin n) K) (p q : Fin n) : (d * g * d⁻¹).val p q = D p * g.val p q * (D q)⁻¹ := by
  rw [Units.val_mul, Units.val_mul, inv_val_of_diagonal hd hD, hd, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem mem_GLint_of {O : Subring K} {x : GL (Fin n) K} (h1 : ∀ i j, x.1 i j ∈ O) (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) :
    x ∈ GLint (Fin n) O := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

variable (v : Valuation K (WithZero (Multiplicative ℤ))) {r : ℕ} {ϖ : K}

theorem conj_le_one (hϖ : v ϖ = WithZero.exp (-1)) {M : Matrix (Fin n) (Fin n) K} (h1 : ∀ i j, v (M i j) ≤ 1)
    (h2 : ∀ q p : Fin n, p.val < r → q ≠ p → v (M q p) < 1) (p q : Fin n) :
    v ((if (p : ℕ) < r then 1 else ϖ) * M q p * (if (q : ℕ) < r then 1 else ϖ)⁻¹) ≤ 1 := by
  have hne : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  rw [map_mul, map_mul, map_inv₀]
  by_cases hp : (p : ℕ) < r <;> by_cases hq : (q : ℕ) < r <;>
    simp only [hp, hq, if_true, if_false, map_one, inv_one, one_mul, mul_one, hϖ]
  · exact h1 q p
  · have hqp : q ≠ p := fun e => hq (e ▸ hp)
    calc v (M q p) * (WithZero.exp (-1))⁻¹ ≤ WithZero.exp (-1) * (WithZero.exp (-1))⁻¹ :=
          mul_le_mul' (le_exp_neg_one_of_lt_one (h2 q p hp hqp)) le_rfl
      _ = 1 := mul_inv_cancel₀ hne
  · calc WithZero.exp (-1) * v (M q p) ≤ 1 * 1 := mul_le_mul' exp_neg_one_lt_one.le (h1 q p)
      _ = 1 := one_mul 1
  · rw [mul_comm (WithZero.exp (-1)), mul_assoc, mul_inv_cancel₀ hne, mul_one]; exact h1 q p

theorem conj_lower_lt_one (hϖ : v ϖ = WithZero.exp (-1)) {M : Matrix (Fin n) (Fin n) K} (h1 : ∀ i j, v (M i j) ≤ 1)
    (p q : Fin n) (hp : r ≤ p.val) (hq : q.val < r) :
    v ((if (p : ℕ) < r then 1 else ϖ) * M q p * (if (q : ℕ) < r then 1 else ϖ)⁻¹) < 1 := by
  rw [if_neg (not_lt.2 hp), if_pos hq, inv_one, mul_one, map_mul, hϖ]
  calc WithZero.exp (-1) * v (M q p) ≤ WithZero.exp (-1) * 1 := mul_le_mul' le_rfl (h1 q p)
    _ < 1 := by rw [mul_one]; exact exp_neg_one_lt_one

end Pure

section Place

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem valued_lt_one_iff_w (s : SplitPlace L) (x : s.w.adicCompletion L) :
    ValuativeRel.valuation (s.w.adicCompletion L) x < 1 ↔ Valued.v x < 1 := by
  have : (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (s.w.adicCompletion L))
    (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one

theorem valued_le_one_iff_w (s : SplitPlace L) (x : s.w.adicCompletion L) :
    ValuativeRel.valuation (s.w.adicCompletion L) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  have : (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (s.w.adicCompletion L))
    (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

theorem facts_of_mem (s : SplitPlace L) (r t : ℕ)
    (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (a : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)))
    (ha : Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t) :
    (∀ i j, Valued.v (a.val i j) ≤ 1) ∧
      ∀ q p : Fin (r + t), p.val < r → Valued.v (a.val q p - if q = p then 1 else 0) < 1 := by
  obtain ⟨hK, hcol⟩ := ha
  refine ⟨fun i j => ?_, fun q p hp => ?_⟩
  · have := val_le_one_of_mem_KO hK i j
    rw [valued_le_one_iff_w] at this
    simpa [hc] using this
  · have := hcol q ⟨p, hp⟩
    have e : Fin.castAdd t (⟨p, hp⟩ : Fin r) = p := Fin.ext rfl
    rw [e, valued_lt_one_iff_w] at this
    have e2 : ((Matrix.GeneralLinearGroup.map c.toRingHom a).val - 1) q p =
        c (a.val q p - if q = p then 1 else 0) := by
      by_cases h : q = p <;> simp [Matrix.one_apply, h]
    rw [e2, hc] at this
    exact this

end Place

end GlobalTheory.BlockConj

namespace GlobalTheory.BlockConj

open Formalism.UG (GLint)

theorem conj_transpose_inv_uniRT : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), (∀ x, Valued.v (c x) = Valued.v x) → ∀ (a b : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))), b.val = (a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose → Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t → ∀ ϖ : s.v.adicCompletion (maximalRealSubfield L), Valued.v ϖ = WithZero.exp (-1) → ∀ d : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), d.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) → NG.UniRT s r (d * b * d⁻¹) ∧ Valued.v (NG.supDiag s r (d * b * d⁻¹)) < 1 := by
  intro L _ _ _ s r t c hc a b hb ha ϖ hϖ d hd
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hD : ∀ i : Fin (r + t), (if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) ≠ 0 := by
    intro i; split_ifs
    · exact one_ne_zero
    · exact hϖ0
  obtain ⟨ha1, ha2⟩ := facts_of_mem s r t c hc a ha
  obtain ⟨hi1, hi2⟩ := facts_of_mem s r t c hc a⁻¹ (by rw [map_inv]; exact (blockGrp _ r t).inv_mem ha)
  have ha2' : ∀ q p : Fin (r + t), p.val < r → q ≠ p → Valued.v (a.val q p) < 1 := fun q p hp hqp => by
    simpa [hqp] using ha2 q p hp
  have hi2' : ∀ q p : Fin (r + t), p.val < r → q ≠ p → Valued.v ((a⁻¹).val q p) < 1 := fun q p hp hqp => by
    simpa [hqp] using hi2 q p hp
  have hbinv : (b⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val = a.val.transpose := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hb, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hN : ∀ p q, (d * b * d⁻¹).val p q = (if (p : ℕ) < r then 1 else ϖ) * (a⁻¹).val q p *
      (if (q : ℕ) < r then 1 else ϖ)⁻¹ := by
    intro p q; rw [conj_diag_apply hd hD, hb, Matrix.transpose_apply]
  have hNi : ∀ p q, ((d * b * d⁻¹)⁻¹).val p q = (if (p : ℕ) < r then 1 else ϖ) * a.val q p *
      (if (q : ℕ) < r then 1 else ϖ)⁻¹ := by
    have e : (d * b * d⁻¹)⁻¹ = d * b⁻¹ * d⁻¹ := by group
    intro p q; rw [e, conj_diag_apply hd hD, hbinv, Matrix.transpose_apply]

  have hUL : ∀ p q : Fin (r + t), p.val < r → q.val < r → (d * b * d⁻¹).val p q = (a⁻¹).val q p := by
    intro p q hp hq; rw [hN, if_pos hp, if_pos hq, inv_one, one_mul, mul_one]
  refine ⟨⟨⟨mem_GLint_of (fun i j => ?_) (fun i j => ?_), fun p q hp hq => ?_⟩, fun p q hp hq => ⟨fun hlt => ?_, fun he => ?_⟩⟩, ?_⟩
  · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    rw [hN]
    exact conj_le_one Valued.v hϖ hi1 hi2' i j
  · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    rw [hNi]
    exact conj_le_one Valued.v hϖ ha1 ha2' i j
  · rw [hN]; exact conj_lower_lt_one Valued.v hϖ hi1 p q hp hq
  · rw [hUL p q hp hq]; exact hi2' q p hp (Fin.ne_of_lt hlt)
  · subst he; rw [hUL p p hp hp]; simpa using hi2 p p hp
  · unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q _ => ?_
    split_ifs with h
    · rw [hUL p q (by omega) h.2]
      exact hi2' q p (by omega) (fun e => by rw [e] at h; omega)
    · rw [map_zero]; exact zero_lt_one

end GlobalTheory.BlockConj
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.tameParahoricRep_splits_as_product : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], TameSplit k := by
  first | exact @GlobalTheory.TameIwahori.tameSplit | exact GlobalTheory.TameIwahori.tameSplit | (intros; apply GlobalTheory.TameIwahori.tameSplit <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.InertStdLat.loc_mem_KU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (κ : GAf L n), κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n :=
  GlobalTheory.InertKU.loc_mem_KU
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.EigInert.heckeFunI_umax_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)} (Dv : InertDatum L n v w)
    (h : Formalism.UG.GU Dv.σw n → ℂ) (hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n)) :
    ∃ (C : Finset (GAf L n ⧸ Umax L n)) (a : GAf L n ⧸ Umax L n → ℂ) (x : GAf L n ⧸ Umax L n → GAf L n),
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W),
        heckeFunI L n (Umax L n) Dv h φ = ∑ c ∈ C, a c • NG.rt L n (x c) φ :=
  GlobalTheory.SatIso.heckeFunI_eq_sum Dv _ h (GlobalTheory.T.finite_inertHecke_support_cosets L n v w Dv (GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv.ϖ Dv.σw _ n Dv.unram)
    (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv) _ (fun _ _ => Iff.rfl) h hh)

end
