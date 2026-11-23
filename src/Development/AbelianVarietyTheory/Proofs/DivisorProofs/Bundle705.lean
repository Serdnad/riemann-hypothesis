module

public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle669
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

noncomputable section
namespace GlobalTheory.FockEmbExp
open Formalism.BasicNotions.TH Matrix
open scoped Kronecker

section general
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem exp_kron_left (Y : Matrix m m ℂ) :
    NormedSpace.exp (Y ⊗ₖ (1 : Matrix n n ℂ)) = NormedSpace.exp Y ⊗ₖ (1 : Matrix n n ℂ) := by
  let f : Matrix m m ℂ →+* Matrix (m × n) (m × n) ℂ :=
    { toFun Y := Y ⊗ₖ (1 : Matrix n n ℂ)
      map_one' := Matrix.one_kronecker_one
      map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
      map_zero' := Matrix.zero_kronecker _
      map_add' A B := Matrix.add_kronecker _ _ _ }
  have hf : Continuous f := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    show Continuous fun Y : Matrix m m ℂ => Y a.1 b.1 * (1 : Matrix n n ℂ) a.2 b.2
    fun_prop
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp f hf Y).symm

theorem exp_kron_right (Z : Matrix n n ℂ) :
    NormedSpace.exp ((1 : Matrix m m ℂ) ⊗ₖ Z) = (1 : Matrix m m ℂ) ⊗ₖ NormedSpace.exp Z := by
  let f : Matrix n n ℂ →+* Matrix (m × n) (m × n) ℂ :=
    { toFun Z := (1 : Matrix m m ℂ) ⊗ₖ Z
      map_one' := Matrix.one_kronecker_one
      map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
      map_zero' := Matrix.kronecker_zero _
      map_add' A B := Matrix.kronecker_add _ _ _ }
  have hf : Continuous f := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    show Continuous fun Y : Matrix n n ℂ => (1 : Matrix m m ℂ) a.1 b.1 * Y a.2 b.2
    fun_prop
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp f hf Z).symm

theorem exp_reindex' (e : m ≃ n) (X : Matrix m m ℂ) :
    NormedSpace.exp (Matrix.reindex e e X) = Matrix.reindex e e (NormedSpace.exp X) := by
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
    exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) X).symm

end general

variable {p q r s : ℕ}

theorem smul_mem {X : Mat p q} (hX : X ∈ upq p q) (t : ℝ) : t • X ∈ upq p q := by
  have h : Xᴴ * Jm p q + Jm p q * X = 0 := hX
  show (t • X)ᴴ * Jm p q + Jm p q * (t • X) = 0
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h,
    smul_zero]

theorem continuous_expt (T : GrpData p q) {X : Mat p q} (hX : X ∈ upq p q) :
    Continuous fun t : ℝ => T.expt (t • X) :=
  T.expt_cont.comp_continuous (by fun_prop) fun t => smul_mem hX t

theorem lift_unique (T : GrpData p q) {γ δ : ℝ → T.G} (hγ : Continuous γ) (hδ : Continuous δ)
    (hc : ∀ t, T.cov (γ t) = T.cov (δ t)) (h0 : γ 0 = δ 0) (t : ℝ) : γ t = δ t := by
  have hsq : Continuous T.sq := continuous_snd.comp T.emb.continuous
  have h := isPreconnected_univ.eq_of_sq_eq (α := ℝ)
    (f := fun t : ℝ => ((T.sq (γ t) : ℂˣ) : ℂ)) (g := fun t : ℝ => ((T.sq (δ t) : ℂˣ) : ℂ))
    (Units.continuous_val.comp (hsq.comp hγ)).continuousOn
    (Units.continuous_val.comp (hsq.comp hδ)).continuousOn (fun t _ => by
      simp only [Pi.pow_apply]
      rw [T.sq_sq, T.sq_sq, hc]) (fun _ => Units.ne_zero _) (Set.mem_univ 0) (by simp only [h0])
  exact T.emb.injective (Prod.ext (hc t) (Units.ext (h (Set.mem_univ t))))

theorem Jm_diag (p q : ℕ) :
    Jm p q = Matrix.diagonal fun a => if a.isLeft then (1 : ℂ) else -1 := by
  ext (a | a) (b | b) <;> simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem Jm_eq (p q r s : ℕ) : Jm (p * r + q * s) (p * s + q * r) =
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) (Jm p q ⊗ₖ Jm r s) := by
  rw [Jm_diag, Jm_diag, Jm_diag, Matrix.diagonal_kronecker_diagonal, Matrix.reindex_apply,
    Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  obtain ⟨l, rfl⟩ := (lineEquiv p q r s).surjective x
  rw [lineEquiv_isLeft, Function.comp, Equiv.symm_apply_apply]
  rcases l with ⟨a | a, c | c⟩ <;> simp [linePos]

theorem left_mem {Y : Mat p q} (hY : Y ∈ upq p q) (r s : ℕ) :
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) (Y ⊗ₖ (1 : Mat r s)) ∈
      upq (p * r + q * s) (p * s + q * r) := by
  have h : Yᴴ * Jm p q + Jm p q * Y = 0 := hY
  show _ᴴ * _ + _ * _ = 0
  rw [Jm_eq, Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have := congrArg (fun A : Mat p q => (A ⊗ₖ Jm r s).submatrix (lineEquiv p q r s).symm (lineEquiv p q r s).symm) h
  simpa [Matrix.add_kronecker, Matrix.submatrix_add] using this

theorem right_mem {Y : Mat r s} (hY : Y ∈ upq r s) (p q : ℕ) :
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) ((1 : Mat p q) ⊗ₖ Y) ∈
      upq (p * r + q * s) (p * s + q * r) := by
  have h : Yᴴ * Jm r s + Jm r s * Y = 0 := hY
  show _ᴴ * _ + _ * _ = 0
  rw [Jm_eq, Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have := congrArg (fun A : Mat r s => (Jm p q ⊗ₖ A).submatrix (lineEquiv p q r s).symm (lineEquiv p q r s).symm) h
  simpa [Matrix.kronecker_add, Matrix.submatrix_add] using this

variable {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q} {T2 : GrpData r s}

theorem continuous_emb (F : FockData T0 T1 T2) : Continuous F.emb := by
  have h1 : Continuous T1.cov := continuous_fst.comp T1.emb.continuous
  have h2 : Continuous T2.cov := continuous_fst.comp T2.emb.continuous
  have s1 : Continuous T1.sq := continuous_snd.comp T1.emb.continuous
  have s2 : Continuous T2.sq := continuous_snd.comp T2.emb.continuous
  have hv : Continuous fun x : T1.G × T2.G =>
      ((T0.cov (F.emb x) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)) := by
    have c1 := (Units.continuous_val.comp h1).comp (continuous_fst (X := T1.G) (Y := T2.G))
    have c2 := (Units.continuous_val.comp h2).comp (continuous_snd (X := T1.G) (Y := T2.G))
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have := (c1.matrix_elem ((lineEquiv p q r s).symm a).1 ((lineEquiv p q r s).symm b).1).mul
      (c2.matrix_elem ((lineEquiv p q r s).symm a).2 ((lineEquiv p q r s).symm b).2)
    refine this.congr fun x => ?_
    rw [show x = (x.1, x.2) from rfl, F.emb_cov]
    rfl
  rw [T0.emb.isInducing.continuous_iff]
  refine Continuous.prodMk (Units.continuous_iff.2 ⟨hv, ?_⟩) ?_
  · refine (hv.comp continuous_inv).congr fun x => ?_
    simp only [Function.comp, map_inv]
  · refine (((s1.comp continuous_fst).pow (r + s)).mul ((s2.comp continuous_snd).pow (p + q))).congr
      fun x => ?_
    exact (F.emb_sq x.1 x.2).symm

theorem emb_expt_left (F : FockData T0 T1 T2) {Y : Mat p q} (hY : Y ∈ upq p q) (t : ℝ) :
    F.emb (T1.expt (t • Y), 1) = T0.expt (t • Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
      (Y ⊗ₖ (1 : Mat r s))) := by
  refine lift_unique T0 (γ := fun t : ℝ => F.emb (T1.expt (t • Y), 1))
    ((continuous_emb F).comp ((continuous_expt T1 hY).prodMk continuous_const))
    (continuous_expt T0 (left_mem hY r s)) (fun t => Units.ext ?_) ?_ t
  · rw [F.emb_cov, T0.expt_cov _ (smul_mem (left_mem hY r s) t), T1.expt_cov _ (smul_mem hY t),
      map_one, Units.val_one, ← exp_kron_left, ← exp_reindex']
    congr 1
    ext a b
    simp
    ring
  · simp only [zero_smul, T1.expt_zero, T0.expt_zero]
    exact map_one F.emb

theorem emb_expt_right (F : FockData T0 T1 T2) {Y : Mat r s} (hY : Y ∈ upq r s) (t : ℝ) :
    F.emb (1, T2.expt (t • Y)) = T0.expt (t • Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
      ((1 : Mat p q) ⊗ₖ Y)) := by
  refine lift_unique T0 (γ := fun t : ℝ => F.emb (1, T2.expt (t • Y)))
    ((continuous_emb F).comp (continuous_const.prodMk (continuous_expt T2 hY)))
    (continuous_expt T0 (right_mem hY p q)) (fun t => Units.ext ?_) ?_ t
  · rw [F.emb_cov, T0.expt_cov _ (smul_mem (right_mem hY p q) t), T2.expt_cov _ (smul_mem hY t),
      map_one, Units.val_one, ← exp_kron_right, ← exp_reindex']
    congr 1
    ext a b
    simp
    ring
  · simp only [zero_smul, T2.expt_zero, T0.expt_zero]
    exact map_one F.emb

theorem fock_derived : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), Continuous F.emb ∧ (∀ Y ∈ upq p q, ∀ P, HasDerivAt (fun t : ℝ => F.π (T1.expt (t • Y), 1) (F.ι P)) (F.ι (fockAct1 p q r s Y P)) 0) ∧ (∀ Y ∈ upq r s, ∀ P, HasDerivAt (fun t : ℝ => F.π (1, T2.expt (t • Y)) (F.ι P)) (F.ι (fockAct2 p q r s Y P)) 0) := by
  intro p q r s T0 T1 T2 F
  refine ⟨continuous_emb F, fun Y hY P => ?_, fun Y hY P => ?_⟩
  · have h := F.der _ (left_mem hY r s) P
    rw [← Matrix.reindex_symm, Equiv.symm_apply_apply] at h
    simp only [FockData.π, MonoidHom.comp_apply, emb_expt_left F hY]
    exact h
  · have h := F.der _ (right_mem hY p q) P
    rw [← Matrix.reindex_symm, Equiv.symm_apply_apply] at h
    simp only [FockData.π, MonoidHom.comp_apply, emb_expt_right F hY]
    exact h

end GlobalTheory.FockEmbExp
end
end

section

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH

namespace GlobalTheory.CharPair

variable (P Q R S : ℕ)

abbrev Mdl : Type := MvPolynomial (Fin P × Fin Q) ℂ

def mR (a : Fin P) (b : Fin Q) : Pol P Q R 0 :=
  ∑ c : Fin R, X (Sum.inl a, Sum.inl c) * X (Sum.inr b, Sum.inl c)

def mS (a : Fin P) (b : Fin Q) : Pol P Q 0 S :=
  ∑ c : Fin S, X (Sum.inl a, Sum.inr c) * X (Sum.inr b, Sum.inr c)

def detR (h : P ≤ R) : Pol P Q R 0 :=
  (Matrix.of fun a c : Fin P => (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)).det

def detS (h : Q ≤ S) : Pol P Q 0 S :=
  (Matrix.of fun b c : Fin Q => (X (Sum.inr b, Sum.inr (Fin.castLE h c)) : Pol P Q 0 S)).det

def embR (h : P ≤ R) (k : ℕ) : Mdl P Q →ₗ[ℂ] Pol P Q R 0 :=
  LinearMap.mulRight ℂ (detR P Q R h ^ k) ∘ₗ (aeval fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2).toLinearMap

def embS (h : Q ≤ S) (k' : ℕ) : Mdl P Q →ₗ[ℂ] Pol P Q 0 S :=
  LinearMap.mulRight ℂ (detS P Q S h ^ k') ∘ₗ (aeval fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2).toLinearMap

variable {P Q}

abbrev mulM (a : Fin P) (b : Fin Q) : Module.End ℂ (Mdl P Q) := LinearMap.mulLeft ℂ (X (a, b))

abbrev derM (a : Fin P) (b : Fin Q) : Module.End ℂ (Mdl P Q) := (pderiv (a, b)).toLinearMap

variable (P Q)

def opR (k : ℕ) : Ix P Q → Ix P Q → Module.End ℂ (Mdl P Q)
  | .inl a, .inr b => mulM a b
  | .inr b, .inl a => -(∑ a', ∑ b', mulM a' b' * derM a' b * derM a b' + ((R + k : ℕ) : ℂ) • derM a b)
  | .inl a, .inl a' => ∑ b, mulM a b * derM a' b + (if a = a' then (k : ℂ) + (R : ℂ) / 2 else 0) • 1
  | .inr b, .inr b' => -(∑ a, mulM a b' * derM a b) - (if b = b' then (R : ℂ) / 2 else 0) • 1

def opS (k' : ℕ) : Ix P Q → Ix P Q → Module.End ℂ (Mdl P Q)
  | .inl a, .inr b => -mulM a b
  | .inr b, .inl a => ∑ a', ∑ b', mulM a' b' * derM a' b * derM a b' + ((S + k' : ℕ) : ℂ) • derM a b
  | .inl a, .inl a' => -(∑ b, mulM a b * derM a' b) - (if a = a' then (S : ℂ) / 2 else 0) • 1
  | .inr b, .inr b' => ∑ a, mulM a b' * derM a b + (if b = b' then (k' : ℂ) + (S : ℂ) / 2 else 0) • 1

def actR (k : ℕ) : Mat P Q →ₗ[ℂ] Module.End ℂ (Mdl P Q) :=
  ∑ i, ∑ j, (Matrix.entryLinearMap ℂ ℂ i j).smulRight (opR P Q R k i j)

theorem actR_apply (k : ℕ) (Z : Mat P Q) : actR P Q R k Z = ∑ i, ∑ j, Z i j • opR P Q R k i j := by
  simp [actR, LinearMap.sum_apply]

theorem detR_ne_zero (P Q R : ℕ) (h : P ≤ R) : detR P Q R h ≠ 0 := by
  let g : Fin P × Fin P → Ix P Q × Ix R 0 := fun ac => (Sum.inl ac.1, Sum.inl (Fin.castLE h ac.2))
  have hf : Function.Injective g := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ hac
    simp only [g, Prod.mk.injEq, Sum.inl.injEq] at hac
    exact Prod.ext hac.1 (Fin.castLE_injective h hac.2)
  have : detR P Q R h = rename g (Matrix.det (Matrix.mvPolynomialX (Fin P) (Fin P) ℂ)) := by
    rw [detR, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext a c; simp [g, Matrix.mvPolynomialX]
  rw [this]; intro h0
  exact Matrix.det_mvPolynomialX_ne_zero _ _ ((map_eq_zero_iff _ (rename_injective _ hf)).1 h0)

theorem detS_ne_zero (P Q S : ℕ) (h : Q ≤ S) : detS P Q S h ≠ 0 := by
  let g : Fin Q × Fin Q → Ix P Q × Ix 0 S := fun bc => (Sum.inr bc.1, Sum.inr (Fin.castLE h bc.2))
  have hf : Function.Injective g := by
    rintro ⟨b, c⟩ ⟨b', c'⟩ hbc
    simp only [g, Prod.mk.injEq, Sum.inr.injEq] at hbc
    exact Prod.ext hbc.1 (Fin.castLE_injective h hbc.2)
  have : detS P Q S h = rename g (Matrix.det (Matrix.mvPolynomialX (Fin Q) (Fin Q) ℂ)) := by
    rw [detS, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext b c; simp [g, Matrix.mvPolynomialX]
  rw [this]; intro h0
  exact Matrix.det_mvPolynomialX_ne_zero _ _ ((map_eq_zero_iff _ (rename_injective _ hf)).1 h0)

end GlobalTheory.CharPair

end
end

section

open scoped Matrix
open Formalism.BasicNotions.TH

namespace GlobalTheory.UnitaryPolar

open Matrix
open scoped MatrixOrder ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem root {S A : Matrix ι ι ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hA : A.PosSemidef)
    (h : A * S * A = S) : ∃ R : Matrix ι ι ℂ, R.PosSemidef ∧ R * R = A ∧ R * S * R = S := by
  obtain ⟨R, hR, hRR, hu⟩ : ∃ R : Matrix ι ι ℂ, R.PosSemidef ∧ R * R = A ∧
      ∀ T : Matrix ι ι ℂ, T.PosSemidef → T * T = A → R = T :=
    ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).posSemidef, CFC.sqrt_mul_sqrt_self A hA.nonneg,
      fun T hT e => CFC.sqrt_unique e hT.nonneg⟩
  have a1 : R * (R * (S * A * S)) = 1 := by
    rw [← Matrix.mul_assoc, hRR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, h1]
  have a2 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R (Matrix.isUnit_det_of_right_inverse a1)
  have a3 : R⁻¹ * R⁻¹ = S * A * S := by
    calc R⁻¹ * R⁻¹ = R⁻¹ * R⁻¹ * (R * (R * (S * A * S))) := by rw [a1, Matrix.mul_one]
      _ = R⁻¹ * (R⁻¹ * R) * R * (S * A * S) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [a2, Matrix.mul_one, a2, Matrix.one_mul]
  have a4 : R = S * R⁻¹ * S := by
    refine hu _ ?_ ?_
    · have := hR.inv.conjTranspose_mul_mul_same S
      rwa [h2] at this
    · calc S * R⁻¹ * S * (S * R⁻¹ * S) = S * (R⁻¹ * (S * S) * R⁻¹) * S := by simp only [Matrix.mul_assoc]
        _ = (S * S) * A * (S * S) := by rw [h1, Matrix.mul_one, a3, ← h1]; simp only [Matrix.mul_assoc]
        _ = A := by rw [h1, Matrix.mul_one, Matrix.one_mul]
  refine ⟨R, hR, hRR, ?_⟩
  calc R * S * R = S * R⁻¹ * S * S * R := by rw [← a4]
    _ = S * (R⁻¹ * (S * S) * R) := by simp only [Matrix.mul_assoc]
    _ = S := by rw [h1, Matrix.mul_one, a2, Matrix.mul_one]

theorem polar_inv {S U : Matrix ι ι ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hU : Uᴴ * S * U = S) :
    ∃ K Q : Matrix ι ι ℂ, Kᴴ * S * K = S ∧ S * K = K * S ∧ Qᴴ * S * Q = S ∧ S * Q * S * Q = 1 ∧
      U = K * Q * Q := by
  have hS : ∀ X : Matrix ι ι ℂ, S * (S * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have b1 : (S * Uᴴ * S) * U = 1 := by
    rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hU, h1]
  have b2 : U * S * Uᴴ = S := by
    have := congrArg (· * S) (mul_eq_one_comm.1 b1)
    simpa only [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.one_mul] using this
  obtain ⟨P, hP, hPP, hPS⟩ := root h1 h2 (Matrix.posSemidef_conjTranspose_mul_self U) (by
    calc Uᴴ * U * S * (Uᴴ * U) = Uᴴ * (U * S * Uᴴ) * U := by simp only [Matrix.mul_assoc]
      _ = S := by rw [b2, hU])
  obtain ⟨Q, hQ, hQQ, hQS⟩ := root h1 h2 hP hPS
  have hP' : ∀ X : Matrix ι ι ℂ, P * (S * (P * X)) = S * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPS]
  have c0 : (U * (S * P * S))ᴴ = S * P * S * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, h2, hP.isHermitian.eq, Matrix.mul_assoc]
  have c1 : (U * (S * P * S))ᴴ * S * (U * (S * P * S)) = S := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * S * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = S := by rw [hU]; simp only [Matrix.mul_assoc, hS, hP']
  have c2 : (U * (S * P * S))ᴴ * (U * (S * P * S)) = 1 := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hPP]; simp only [Matrix.mul_assoc, hS, hP', h1]
  refine ⟨U * (S * P * S), Q, c1, ?_, by rw [hQ.isHermitian.eq, hQS], ?_, ?_⟩
  · generalize U * (S * P * S) = K at c1 c2
    calc S * K = (K * Kᴴ) * S * K := by rw [mul_eq_one_comm.1 c2, Matrix.one_mul]
      _ = K * (Kᴴ * S * K) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [c1]
  · rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hQS, h1]
  · rw [Matrix.mul_assoc _ Q, hQQ, Matrix.mul_assoc, Matrix.mul_assoc S, Matrix.mul_assoc S, hPS, h1, Matrix.mul_one]

theorem jm_mul_self (R S : ℕ) : Jm R S * Jm R S = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem jm_conjTranspose (R S : ℕ) : (Jm R S)ᴴ = Jm R S := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem polar (R S : ℕ) (u : Mat R S) (hu : uᴴ * Jm R S * u = Jm R S) :
    ∃ k q : Mat R S, kᴴ * Jm R S * k = Jm R S ∧
      Jm R S * k = k * Jm R S ∧ qᴴ * Jm R S * q = Jm R S ∧ Jm R S * q * Jm R S * q = 1 ∧ u = k * q * q :=
  polar_inv (jm_mul_self R S) (jm_conjTranspose R S) hu

end GlobalTheory.UnitaryPolar
end

section

namespace GlobalTheory.KTypeUnderMaps

open Formalism.MainNotions.S

theorem isKTypeOf_map {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H} {Λ : Fin n → ℝ}
    {S : Submodule ℂ H} (hS : Formalism.MainNotions.S.IsKTypeOf ε σ Λ S) (L : H →ₗ[ℂ] H)
    (hL : ∀ k ∈ Formalism.REAL.Kset ε, ∀ (w : H), σ k (L w) = L (σ k w))
    {v : H} (hv : v ∈ S) (hLv : L v ≠ 0) :
    Formalism.MainNotions.S.IsKTypeOf ε σ Λ (Submodule.map L S) := by
  obtain ⟨hfd, hst, hirr, ⟨u, huS, hu0, huw⟩, hdom⟩ := hS
  have hpull : ∀ T : Submodule ℂ H, IsKStableOn ε σ T →
      S ⊓ T.comap L = ⊥ ∨ S ⊓ T.comap L = S := by
    intro T hT
    refine hirr _ inf_le_left ?_
    intro g hg x hx
    refine ⟨hst g hg x hx.1, ?_⟩
    have h2 : L x ∈ T := hx.2
    change L (σ g x) ∈ T
    rw [← hL g hg]
    exact hT g hg _ h2
  have hinj : ∀ x ∈ S, L x = 0 → x = 0 := by
    intro x hx hx0
    have hbot : IsKStableOn ε σ (⊥ : Submodule ℂ H) := by
      intro g _ y hy
      rw [Submodule.mem_bot] at hy ⊢
      rw [hy, map_zero]
    rcases hpull ⊥ hbot with h | h
    · have : x ∈ S ⊓ (⊥ : Submodule ℂ H).comap L := ⟨hx, by simpa using hx0⟩
      rw [h] at this
      simpa using this
    · have : v ∈ S ⊓ (⊥ : Submodule ℂ H).comap L := by rw [h]; exact hv
      exact absurd (by simpa using this.2) hLv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · haveI := hfd
    infer_instance
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ g x, hst g hg x hx, (hL g hg x).symm⟩
  · intro T hTle hT
    rcases hpull T hT with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hTle hy
      have : x ∈ S ⊓ T.comap L := ⟨hx, hy⟩
      rw [h, Submodule.mem_bot] at this
      rw [this, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hTle ?_
      rintro _ ⟨x, hx, rfl⟩
      have : x ∈ S ⊓ T.comap L := by rw [h]; exact hx
      exact this.2
  · refine ⟨L u, ⟨u, huS, rfl⟩, fun h => hu0 (hinj u huS h), ?_⟩
    intro θ hθ
    rw [hL _ hθ, huw θ hθ, map_smul]
  · rintro μ _ ⟨x, hx, rfl⟩ hx0 hw
    refine hdom μ x hx (fun h => hx0 (by rw [h, map_zero])) ?_
    intro θ hθ
    rw [← sub_eq_zero]
    refine hinj _ (S.sub_mem (hst _ hθ x hx) (S.smul_mem _ hx)) ?_
    rw [map_sub, map_smul, ← hL _ hθ, hw θ hθ, sub_self]

end GlobalTheory.KTypeUnderMaps
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.differentIdeal_pow_finrank_eq_span_discr' : ∀ (F : Type) [Field F] [NumberField F] [IsGalois ℚ F], differentIdeal ℤ (𝓞 F) ^ Module.finrank ℚ F = Ideal.span {((discr F : ℤ) : 𝓞 F)} := by
  first | exact @GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr | exact GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr | (intros; apply GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr <;> assumption)
end
