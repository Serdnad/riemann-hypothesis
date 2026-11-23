module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.AlgebraicWeights.InertDatumExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle107
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle008
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle289
public import Formalism.AlgebraicWeights.IsAlgWeight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle273
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle065
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle643
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle007
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.SatInvAuto

open Formalism.UG GlobalTheory.SatInd

section Local

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

def diagExp (n m : ℕ) (a : Fin m → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < m then a ⟨i.val, h⟩
  else if h' : n - m ≤ i.val ∧ n - 1 - i.val < m then -(a ⟨n - 1 - i.val, h'.2⟩) else 0

theorem tMat_eq_diag (x : K) (n m : ℕ) (a : Fin m → ℤ) :
    tMat x n m a = Matrix.diagonal fun i => x ^ diagExp n m a i := by
  unfold tMat diagExp
  congr 1
  funext i
  split_ifs <;> simp

theorem diagExp_rev {n m : ℕ} (hm : 2 * m ≤ n) (a : Fin m → ℤ) (i : Fin n) :
    diagExp n m a i.rev = -diagExp n m a i := by
  have hi := i.isLt
  have hr : (i.rev : ℕ) = n - 1 - i := by rw [Fin.val_rev]; omega
  unfold diagExp
  by_cases h1 : (i : ℕ) < m
  · have h2 : ¬ (i.rev : ℕ) < m := by omega
    have h3 : n - m ≤ (i.rev : ℕ) ∧ n - 1 - (i.rev : ℕ) < m := by omega
    rw [dite_eq_right h2, dite_eq_left h3, dite_eq_left h1]
    rw [show (⟨n - 1 - (i.rev : ℕ), h3.2⟩ : Fin m) = ⟨i, h1⟩ from
      Fin.ext (show n - 1 - (i.rev : ℕ) = (i : ℕ) by omega)]
  · by_cases h4 : n - m ≤ (i : ℕ) ∧ n - 1 - (i : ℕ) < m
    · have h2 : (i.rev : ℕ) < m := by omega
      rw [dite_eq_left h2, dite_eq_right h1, dite_eq_left h4, neg_neg]
      rw [show (⟨(i.rev : ℕ), h2⟩ : Fin m) = ⟨n - 1 - i, h4.2⟩ from Fin.ext hr]
    · have h2 : ¬ (i.rev : ℕ) < m := by omega
      have h3 : ¬ (n - m ≤ (i.rev : ℕ) ∧ n - 1 - (i.rev : ℕ) < m) := by omega
      rw [dite_eq_right h2, dite_eq_right h3, dite_eq_right h1, dite_eq_right h4, neg_zero]

theorem div_mem_intL {ϖ x : K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (hx : x ∈ intL K) (hx' : x⁻¹ ∉ intL K) : x / ϖ ∈ intL K := by
  unfold intL at *
  rw [Valuation.mem_integer_iff] at *
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hx'
    simp
  have hlt : Valued.v x < 1 := lt_of_le_of_ne hx (fun h => hx' (by rw [map_inv₀, h, inv_one]))
  have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [map_div₀, hϖ, ← WithZero.exp_log hv0, ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem map_mul_mat (g : K ≃+* K) {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) :
    (A * B).map g = A.map g * B.map g := by
  ext i j

  simp [Matrix.mul_apply, map_sum]

end Local

section Cell

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem cell_guMap (g : K ≃+* K) {σ : K →+* K} (hg : ∀ x, g (σ x) = σ (g x))
    (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {ϖ : K} {q n m : ℕ} (hU : IsUnramInv ϖ σ q)
    (hm : 2 * m ≤ n) (a : Fin m → ℤ) (y : GU σ n)
    (hy : ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
      ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨u, hu, k, hk, hyuk⟩ := hy
  obtain ⟨-, hσv, hσϖ, hϖ, -, -, -⟩ := hU
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
  have hϖint : ϖ ∈ intL K := by
    unfold intL
    rw [Valuation.mem_integer_iff, hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  have hϖinv : ϖ⁻¹ ∉ intL K := by
    unfold intL
    rw [Valuation.mem_integer_iff, map_inv₀, hϖ', ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp]; norm_num
  set c : K := g ϖ / ϖ with hc
  have hgϖ : g ϖ = ϖ * c := by rw [hc]; field_simp
  have hc0 : c ≠ 0 := div_ne_zero ((map_ne_zero g).2 h0) h0
  have hcint : c ∈ intL K := div_mem_intL hϖ' ((hint ϖ).1 hϖint)
    (by rw [← map_inv₀]; exact fun h => hϖinv ((hint _).2 h))
  have hcinv : c⁻¹ ∈ intL K := by
    have h1 : g.symm ϖ / ϖ ∈ intL K := div_mem_intL hϖ' (by rw [hint]; simpa using hϖint)
      (by rw [← map_inv₀, hint]; simpa using hϖinv)
    have h2 := (hint _).1 h1
    rw [map_div₀, RingEquiv.apply_symm_apply] at h2
    rw [hc, inv_div]; exact h2
  have hcv : Valued.v c = 1 := by
    unfold intL at hcint hcinv
    rw [Valuation.mem_integer_iff] at hcint hcinv
    refine le_antisymm hcint ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (c * c⁻¹) := by rw [mul_inv_cancel₀ hc0, map_one]
      _ = Valued.v c * Valued.v c⁻¹ := map_mul _ _ _
      _ ≤ Valued.v c * 1 := mul_le_mul' le_rfl hcinv
      _ = Valued.v c := mul_one _
  have hσc : σ c = c := by rw [hc, map_div₀, hσϖ, ← hg, hσϖ]
  set e : Fin n → K := fun i => c ^ diagExp n m a i with he
  have he0 : ∀ i, e i ≠ 0 := fun i => zpow_ne_zero _ hc0
  obtain ⟨d, hd, hd'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ) e (fun i => by
    simp only [he]; rw [map_zpow₀, hσc, diagExp_rev hm, ← zpow_add₀ hc0, add_neg_cancel, zpow_zero])
  have hdK : d ∈ KU σ n := by
    have hI : Formalism.UG.P.fIwasawaInt (((d : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      intro i j
      rw [hd]
      by_cases hij : i = j
      · subst hij; rw [Matrix.diagonal_apply_eq, he]; simp only; rw [map_zpow₀, hcv, one_zpow]
      · rw [Matrix.diagonal_apply_ne _ hij, map_zero]; exact zero_le'
    have := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ d) hI
    have e' : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ d) = d := Subtype.ext (Units.ext rfl)
    rwa [e'] at this
  have hk1 : guMap g hg n k ∈ KU σ n := (mem_KU_iff_guMap g hg hint k).1 hk
  refine ⟨d * guMap g hg n u * d⁻¹, ?_, d * guMap g hg n k, (KU σ n).mul_mem hdK hk1, ?_⟩
  · refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · simp only [Subgroup.coe_mul, Units.val_mul, hd, hd', guMap_val, Matrix.mul_diagonal,
        Matrix.diagonal_mul, Matrix.map_apply]
      rw [hu.1 i j hij, map_zero, mul_zero, zero_mul]
    · simp only [Subgroup.coe_mul, Units.val_mul, hd, hd', guMap_val, Matrix.mul_diagonal,
        Matrix.diagonal_mul, Matrix.map_apply]
      rw [hu.2 i, map_one, mul_one, mul_inv_cancel₀ (he0 i)]
  · rw [guMap_val, hyuk, map_mul_mat, map_mul_mat]
    simp only [Subgroup.coe_mul, Units.val_mul, hd, hd', guMap_val]
    rw [tMat_eq_diag, Matrix.diagonal_map (map_zero _)]
    have hD : (Matrix.diagonal fun i => g (ϖ ^ diagExp n m a i)) =
        Matrix.diagonal (fun i => ϖ ^ diagExp n m a i) * Matrix.diagonal e := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rw [map_zpow₀, hgϖ, mul_zpow]
    have hinv : Matrix.diagonal (fun i => (e i)⁻¹) * Matrix.diagonal e = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact inv_mul_cancel₀ (he0 i)
    rw [hD]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal fun i => (e i)⁻¹) (Matrix.diagonal e), hinv, Matrix.one_mul]

end Cell


open Classical in
theorem satU_guMap_self : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ : K →+* K} (hg : ∀ x, g (σ x) = σ (g x)), (∀ x, x ∈ Formalism.UG.intL K ↔ g x ∈ Formalism.UG.intL K) → ∀ (ϖ : K) (q n m : ℕ), Formalism.UG.IsUnramInv ϖ σ q → 2 * m ≤ n → n ≤ 2 * m + 1 → ∀ h : Formalism.UG.GU σ n → ℂ, Formalism.UG.IsBiInv (Formalism.UG.KU σ n) h → ∀ α : Fin m → ℂ, Formalism.UG.SatU ϖ q (fun y => h (GlobalTheory.SatInd.guMap g hg n y)) α = Formalism.UG.SatU ϖ q h α := by
  intro K _ _ g σ hg hint ϖ q n m hU hm1 _ h hbi α
  have hg' : ∀ x, g.symm (σ x) = σ (g.symm x) := by
    intro x; apply g.injective; rw [hg]; simp
  have hint' : ∀ x, x ∈ intL K ↔ g.symm x ∈ intL K := by
    intro x; rw [hint (g.symm x)]; simp
  refine satU_guMap g hg hint ϖ ϖ q n m h hbi
    (fun a y => ⟨cell_guMap g hg hint hU hm1 a y, fun hy => ?_⟩) α
  have := cell_guMap g.symm hg' hint' hU hm1 a (guMap g hg n y) hy
  rwa [guMap_symm_comp g hg hg' y] at this

end GlobalTheory.SatInvAuto
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix

noncomputable section

namespace GlobalTheory.AlgWtHW

theorem eval_adjugate_mvPolynomialX {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n) :
    MvPolynomial.eval (fun p : Fin n × Fin n => g p.1 p.2)
      ((Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).adjugate x y) = g.adjugate x y := by
  have h := RingHom.map_adjugate (MvPolynomial.eval (fun p : Fin n × Fin n => g p.1 p.2))
    (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ)
  have h2 : (MvPolynomial.eval (fun p : Fin n × Fin n => g p.1 p.2)).mapMatrix
      (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ) = g := by
    ext i j; simp [Matrix.mvPolynomialX]
  rw [h2] at h
  simpa using congrFun (congrFun h x) y

theorem eval_det_mvPolynomialX {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial.eval (fun p : Fin n × Fin n => g p.1 p.2) (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det = g.det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

theorem det_mul_inv_apply {n : ℕ} (B : GL (Fin n) ℂ) (x y : Fin n) :
    B.val.det * (B⁻¹).val x y = B.val.adjugate x y := by
  have h : B.val.adjugate = B.val.det • (B⁻¹).val := by
    calc B.val.adjugate = B.val.adjugate * (B.val * (B⁻¹).val) := by rw [Units.mul_inv, Matrix.mul_one]
      _ = (B.val.adjugate * B.val) * (B⁻¹).val := by rw [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [h, Matrix.smul_apply, smul_eq_mul]

theorem exists_det_pow_mul_eq_poly {n : ℕ} (Q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) :
    ∃ (d : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ), ∀ B : GL (Fin n) ℂ,
      B.val.det ^ d * MvPolynomial.eval (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2)) Q =
        MvPolynomial.eval (fun p => B.val p.1 p.2) P := by
  induction Q using MvPolynomial.induction_on with
  | C a => exact ⟨0, MvPolynomial.C a, fun B => by simp⟩
  | add p q hp hq =>
    obtain ⟨d₁, P₁, h₁⟩ := hp
    obtain ⟨d₂, P₂, h₂⟩ := hq
    refine ⟨d₁ + d₂, P₁ * (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det ^ d₂ +
      P₂ * (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det ^ d₁, fun B => ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, eval_det_mvPolynomialX, ← h₁ B, ← h₂ B]
    ring
  | mul_X p v hp =>
    obtain ⟨d, P, h⟩ := hp
    cases v with
    | inl x =>
      refine ⟨d, P * MvPolynomial.X x, fun B => ?_⟩
      simp only [map_mul, MvPolynomial.eval_X, Sum.elim_inl, ← h B]
      ring
    | inr x =>
      refine ⟨d + 1, P * (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).adjugate x.1 x.2, fun B => ?_⟩
      simp only [map_mul, MvPolynomial.eval_X, Sum.elim_inr, eval_adjugate_mvPolynomialX, ← h B,
        ← det_mul_inv_apply]
      ring

theorem sqRep_intertwines_of_unitary : ∀ (n : ℕ) (lam : DomWeight n) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), GlobalTheory.AlgWtHW.IsPolyRep Φ → ∀ M : nablaSq ℂ n lam →ₗ[ℂ] (ι → ℂ), (∀ (u : Matrix.unitaryGroup (Fin n) ℂ) (v : nablaSq ℂ n lam), M (GlobalTheory.Branching.sqRep ℂ n lam (GlobalTheory.Branching.unitaryIncl n u) v) = Matrix.mulVec (Φ (GlobalTheory.Branching.unitaryIncl n u)) (M v)) → ∀ (B : GL (Fin n) ℂ) (v : nablaSq ℂ n lam), M (GlobalTheory.Branching.sqRep ℂ n lam B v) = Matrix.mulVec (Φ B) (M v) := by
  classical
  intro n lam ι _ _ Φ hΦ M hU B v
  funext k
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (nablaSq ℂ n lam)
  let π := (nablaSq ℂ n lam).linearProjOfIsCompl C hC
  let l : Module.Dual ℂ (MvPolynomial (Fin n × Fin n) ℂ) := LinearMap.proj k ∘ₗ M ∘ₗ π
  have hl : ∀ B' : GL (Fin n) ℂ, M (GlobalTheory.Branching.sqRep ℂ n lam B' v) k =
      detPow ℂ n B' lam.detShift * l (Formalism.GradedWeylDivisibility.rowAct ℂ (B'.val)ᵀ v.1) := by
    intro B'
    calc M (GlobalTheory.Branching.sqRep ℂ n lam B' v) k = l (sqAct ℂ n lam B' v.1) := by
          simp only [l, π, LinearMap.comp_apply, LinearMap.proj_apply]
          have := Submodule.linearProjOfIsCompl_apply_left hC (GlobalTheory.Branching.sqRep ℂ n lam B' v)
          rw [← GlobalTheory.Branching.sqRep_coe]
          exact (congrArg (fun w => M w k) this).symm
      _ = _ := by rw [sqAct, map_smul, smul_eq_mul]
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.Branching.exists_poly_rowAct_coef n n v.1 l
  let R₁ := MvPolynomial.rename Prod.swap P₁
  have hR₁ : ∀ g : Matrix (Fin n) (Fin n) ℂ,
      MvPolynomial.eval (fun x => g x.1 x.2) R₁ = l (Formalism.GradedWeylDivisibility.rowAct ℂ gᵀ v.1) := by
    intro g
    rw [hP₁, MvPolynomial.eval_rename]
    rfl
  choose Q hQ using hΦ.poly
  let Qs := ∑ j, Q k j * MvPolynomial.C ((M v) j)
  have hQs : ∀ B' : GL (Fin n) ℂ,
      MvPolynomial.eval (Sum.elim (fun p => B'.val p.1 p.2) (fun p => (B'⁻¹).val p.1 p.2)) Qs = (Φ B' *ᵥ M v) k := by
    intro B'

    simp only [Qs, map_sum, map_mul, MvPolynomial.eval_C, ← hQ, Matrix.mulVec, dotProduct]
  obtain ⟨d, P₂, hP₂⟩ := exists_det_pow_mul_eq_poly Qs
  set a := lam.detShift
  set m : ℕ := a.natAbs
  have ha : 0 ≤ a + (m : ℤ) := by omega
  have hdet : ∀ B' : GL (Fin n) ℂ, B'.val.det ≠ 0 := fun B' => (Matrix.isUnits_det_units B').ne_zero
  have hdp : ∀ B' : GL (Fin n) ℂ, detPow ℂ n B' a = B'.val.det ^ a := by
    intro B'
    simp [detPow, Units.val_zpow_eq_zpow_val]
  have key : ∀ B' : GL (Fin n) ℂ,
      B'.val.det ^ d * B'.val.det ^ (a + (m : ℤ)).toNat * l (Formalism.GradedWeylDivisibility.rowAct ℂ (B'.val)ᵀ v.1) -
        B'.val.det ^ m * MvPolynomial.eval (fun p => B'.val p.1 p.2) P₂ =
      B'.val.det ^ d * B'.val.det ^ m * (M (GlobalTheory.Branching.sqRep ℂ n lam B' v) k - (Φ B' *ᵥ M v) k) := by
    intro B'
    have hx := hdet B'
    rw [hl, ← hQs, ← hP₂, hdp]
    have e1 : B'.val.det ^ (a + (m : ℤ)).toNat = B'.val.det ^ m * B'.val.det ^ a := by
      rw [← zpow_natCast (B'.val.det) (a + (m : ℤ)).toNat, Int.toNat_of_nonneg ha, zpow_add₀ hx, zpow_natCast]
      ring
    rw [e1]
    ring
  let Dp := (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det
  let Qd := Dp ^ d * Dp ^ (a + (m : ℤ)).toNat * R₁ - Dp ^ m * P₂
  have hQd : ∀ g : Matrix (Fin n) (Fin n) ℂ, MvPolynomial.eval (fun x => g x.1 x.2) Qd =
      g.det ^ d * g.det ^ (a + (m : ℤ)).toNat * l (Formalism.GradedWeylDivisibility.rowAct ℂ gᵀ v.1) -
        g.det ^ m * MvPolynomial.eval (fun p => g p.1 p.2) P₂ := by
    intro g
    simp only [Qd, Dp, map_sub, map_mul, map_pow, eval_det_mvPolynomialX, hR₁]
  have Q0 : Qd = 0 := by
    refine GlobalTheory.Branching.eq_zero_of_vanish_unitaryGroup n Qd fun u hu => ?_
    have h1 := key (GlobalTheory.Branching.unitaryIncl n ⟨u, hu⟩)
    have h2 := congrFun (hU ⟨u, hu⟩ v) k
    rw [h2, sub_self, mul_zero] at h1
    rw [hQd]
    exact h1
  have h3 := key B
  rw [← hQd, Q0, map_zero] at h3
  have hx := hdet B
  have h4 : B.val.det ^ d * B.val.det ^ m ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hx)
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3.symm).resolve_left h4)

end GlobalTheory.AlgWtHW
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalUnitary

theorem compAt_conjAL (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (a : AL L) :
    compAt L v (conjAL L a) = Formalism.UG.sigR (↑(IsCMField.complexConj L))
      (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) v) (compAt L v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [compAt, conjAL, Formalism.UG.sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem cT_mul {A : Type} [CommRing A] (σ : A →+* A) {m : Type} [Fintype m]
    (M N : Matrix m m A) : Formalism.UG.cT σ (M * N) = Formalism.UG.cT σ N * Formalism.UG.cT σ M := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one {A : Type} [CommRing A] (σ : A →+* A) {m : Type} [Fintype m] [DecidableEq m] :
    Formalism.UG.cT σ (1 : Matrix m m A) = 1 := by
  unfold Formalism.UG.cT
  simp

theorem cT_conj_form {A : Type} [CommRing A] (σ : A →+* A) {m : Type} [Fintype m] [DecidableEq m]
    (Pm Pi X : Matrix m m A) (h1 : Pm * Pi = 1) (hX : Formalism.UG.cT σ X * X = 1) :
    Formalism.UG.cT σ (Pi * X * Pm) * (Formalism.UG.cT σ Pm * Pm) * (Pi * X * Pm) = Formalism.UG.cT σ Pm * Pm := by
  have h2 : Formalism.UG.cT σ Pi * Formalism.UG.cT σ Pm = 1 := by
    rw [← cT_mul, h1, cT_one]
  rw [cT_mul, cT_mul]
  calc _ = Formalism.UG.cT σ Pm * (Formalism.UG.cT σ X * ((Formalism.UG.cT σ Pi * Formalism.UG.cT σ Pm) * ((Pm * Pi) * X))) * Pm := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ Pm * Pm := by
        rw [h1, h2, Matrix.one_mul, Matrix.one_mul, hX, Matrix.mul_one]

theorem mem_UJ_iff {A : Type} [CommRing A] {m : Type} [Fintype m] [DecidableEq m] (σ : A →+* A)
    (J : Matrix m m A) (g : GL m A) : g ∈ Formalism.UG.UJ σ J ↔ Formalism.UG.cT σ (g : Matrix m m A) * J * g = J := Iff.rfl

theorem loc_mem_GU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n), Dv.loc x ∈ Formalism.UG.GU Dv.σw n := by
  intro L _ _ _ n v w Dv x
  let φ : AL L →+* HeightOneSpectrum.adicCompletion L w :=
    (Dv.e : _ →+* HeightOneSpectrum.adicCompletion L w).comp (compAt L v)
  have hφ : ∀ a : AL L, φ (conjAL L a) = Dv.σw (φ a) := by
    intro a
    simp only [φ, RingHom.comp_apply, RingHom.coe_coe, compAt_conjAL, Dv.comm]
  have hx : ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ReciprocityTheory.Aut.conjT (conjAL L) (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have hconj : φ.mapMatrix (ReciprocityTheory.Aut.conjT (conjAL L)
      ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) =
      Formalism.UG.cT Dv.σw (φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, ReciprocityTheory.Aut.conjT, Formalism.UG.cT,
      Matrix.transpose_apply, hφ]
  have hX : φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      Formalism.UG.cT Dv.σw (φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) = 1 := by
    rw [← hconj, ← map_mul, hx, map_one]
  have hX' := mul_eq_one_comm.mp hX
  have hloc : ((Dv.loc x : GL (Fin n) (HeightOneSpectrum.adicCompletion L w)) :
      Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion L w)) =
      ((Dv.P⁻¹ : GL (Fin n) (HeightOneSpectrum.adicCompletion L w)) :
        Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion L w)) *
      φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((Dv.P : GL (Fin n) (HeightOneSpectrum.adicCompletion L w)) :
        Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion L w)) := by
    rw [Formalism.AUTREP.InertDatum.loc, Units.val_mul, Units.val_mul]
    congr 2
  rw [mem_UJ_iff, hloc, ← Dv.Panti]
  exact cT_conj_form Dv.σw _ _ _ (by simp) hX'

end GlobalTheory.LocalUnitary
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.ClassFinConj

theorem exists_finset_double_cosets_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : GAf L n),
    ∃ T : Finset (GAf L n), ∀ g : GAf L n, ∃ γ ∈ GQ L n, ∃ t ∈ T,
      ∃ κ ∈ (Umax L n ⊓ (Umax L n).map (MulAut.conj h).toMonoidHom), g = γ * t * κ := by
  intro L _ _ _ n h
  classical
  obtain ⟨T, hT⟩ := GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax L n
  obtain ⟨N', hN', hc⟩ := GlobalTheory.CongConjugate.congConj L n h 1 one_pos
  obtain ⟨J, hJ⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hN'
  refine ⟨(T ×ˢ J).image (fun p => p.1 * p.2), fun g => ?_⟩
  obtain ⟨γ, t, u, ht, hu, e⟩ := hT g
  obtain ⟨j, hj, κ, hκ, eu⟩ := hJ u hu
  refine ⟨(γ : GAf L n), γ.2, t * j, Finset.mem_image.2 ⟨(t, j), Finset.mem_product.2 ⟨ht, hj⟩, rfl⟩, κ,
    Subgroup.mem_inf.2 ⟨hκ.1, Subgroup.mem_map.2 ⟨h⁻¹ * κ * h, (hc κ hκ).1, ?_⟩⟩, ?_⟩
  · simp [MulAut.conj_apply, mul_assoc]
  · rw [e, eu]; simp only [mul_assoc]

end GlobalTheory.ClassFinConj
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitian_lattice_invariant_under_level : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (y k : Bridge.Gf V), k ∈ (levEnv V β L).J → Bridge.hLat V (y * k) = Bridge.hLat V y := by
  first | exact @GlobalTheory.HLatLevel.hLat_mul_lev | exact GlobalTheory.HLatLevel.hLat_mul_lev | (intros; apply GlobalTheory.HLatLevel.hLat_mul_lev <;> assumption)
end
