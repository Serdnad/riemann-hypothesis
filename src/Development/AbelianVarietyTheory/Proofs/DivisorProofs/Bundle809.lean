module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle776
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle778
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle779
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
set_option autoImplicit false

namespace GlobalTheory.LogDerProj

def logSub {k A : Type} [CommRing k] [CommRing A] (φ : k →+* A) (J : Ideal A) :
    Submodule A (Derivation ℤ A A) where
  carrier := {D | (∀ a, D (φ a) = 0) ∧ ∀ g ∈ J, D g ∈ J}
  zero_mem' := ⟨fun _ => rfl, fun _ _ => zero_mem _⟩
  add_mem' := fun {D D'} h h' =>
    ⟨fun a => by simp [h.1 a, h'.1 a], fun g hg => add_mem (h.2 g hg) (h'.2 g hg)⟩
  smul_mem' := fun r D h =>
    ⟨fun a => by simp [h.1 a], fun g hg => Ideal.mul_mem_left _ r (h.2 g hg)⟩

theorem mem_logSub {k A : Type} [CommRing k] [CommRing A] (φ : k →+* A) (J : Ideal A) (D : Derivation ℤ A A) :
    D ∈ logSub φ J ↔ (∀ a, D (φ a) = 0) ∧ ∀ g ∈ J, D g ∈ J := Iff.rfl

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S]
include f

def ext (D : Derivation ℤ R R) : Derivation ℤ S S :=
  Classical.choose (GlobalTheory.LogDerLoc.exists_extension (B := S) f D)

theorem ext_algebraMap (D : Derivation ℤ R R) (r : R) :
    ext (S := S) f D (algebraMap R S r) = algebraMap R S (D r) :=
  Classical.choose_spec (GlobalTheory.LogDerLoc.exists_extension (B := S) f D) r

theorem der_ext (D₁ D₂ : Derivation ℤ S S) (h : ∀ r, D₁ (algebraMap R S r) = D₂ (algebraMap R S r)) :
    D₁ = D₂ := by
  ext y
  obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) y
  have hu : IsUnit (algebraMap R S t) := IsLocalization.map_units S t
  have e' : y * algebraMap R S t = algebraMap R S r := e
  have h1 := congrArg D₁ e'
  have h2 := congrArg D₂ e'
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1 h2
  rw [h r, h t] at h1
  have : algebraMap R S t * D₁ y = algebraMap R S t * D₂ y := by linear_combination h1 - h2
  exact hu.mul_left_cancel this

def extL : Derivation ℤ R R →ₗ[R] Derivation ℤ S S where
  toFun := ext f
  map_add' D D' := der_ext f _ _ fun r => by
    rw [ext_algebraMap, Derivation.add_apply, Derivation.add_apply, ext_algebraMap, ext_algebraMap, map_add (f := _)]
  map_smul' c D := der_ext f _ _ fun r => by
    rw [ext_algebraMap, RingHom.id_apply, Derivation.smul_apply, Derivation.smul_apply, ext_algebraMap,
      smul_eq_mul, map_mul, Algebra.smul_def]

theorem extL_algebraMap (D : Derivation ℤ R R) (r : R) :
    extL (S := S) f D (algebraMap R S r) = algebraMap R S (D r) :=
  ext_algebraMap f D r

variable {k : Type} [CommRing k]

def res (φ : k →+* R) (J : Ideal R) :
    logSub φ J →ₗ[R] (logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S))).restrictScalars R where
  toFun D := ⟨extL f D.1, fun a => by
      rw [RingHom.comp_apply, extL_algebraMap, D.2.1 a, map_zero],
    GlobalTheory.LogDerLoc.map_mem_map (algebraMap R S) D.1 (extL f D.1) (extL_algebraMap f D.1) J D.2.2⟩
  map_add' D D' := Subtype.ext (map_add (extL (S := S) f) D.1 D'.1)
  map_smul' c D := Subtype.ext (map_smul (extL (S := S) f) c D.1)

theorem res_apply (φ : k →+* R) (J : Ideal R) (D : logSub φ J) (r : R) :
    (res (S := S) f φ J D).1 (algebraMap R S r) = algebraMap R S (D.1 r) :=
  ext_algebraMap f D.1 r

end GlobalTheory.LogDerProj
end
end

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.ColLie

open GlobalTheory.MinorFrame

variable {ι : Type} [DecidableEq ι]

def colDer {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) : Module.End ℂ (Pol ι d a) :=
  ∑ i : Fin d, ∑ j : Fin a, ∑ k : Fin a,
    S k j • (LinearMap.mulLeft ℂ (X (τ, i, k) : Pol ι d a) ∘ₗ (pderiv (τ, i, j)).toLinearMap)

def atPl {a : ℕ} (τ : ι) (g : Matrix (Fin a) (Fin a) ℂ) : ι → Matrix (Fin a) (Fin a) ℂ :=
  Function.update 1 τ g

theorem colDer_apply {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    colDer τ S P = ∑ i : Fin d, ∑ j : Fin a, ∑ k : Fin a, S k j • (X (τ, i, k) * pderiv (τ, i, j) P) := by
  simp [colDer, LinearMap.sum_apply]

theorem colDer_X {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (v : Var ι d a) :
    colDer (d := d) τ S (X v) = if v.1 = τ then ∑ k, S k v.2.2 • (X (τ, v.2.1, k) : Pol ι d a) else 0 := by
  obtain ⟨σ, i₀, j₀⟩ := v
  rw [colDer_apply]
  simp only [pderiv_X, Pi.single_apply, Prod.ext_iff]
  by_cases h : σ = τ
  · subst h
    simp only [if_true]
    rw [Finset.sum_eq_single i₀, Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · simp
  · simp [h, Ne.symm h]

end GlobalTheory.ColLie

end
end

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame.RowIrr

open GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

def basePt (ι : Type) (d a : ℕ) : Var ι d a → ℂ := fun y => if (y.2.1 : ℕ) = (y.2.2 : ℕ) then 1 else 0

def lowScal (d a : ℕ) (t : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => if (i : ℕ) < a then 1 else t

def topRows {a d : ℕ} (h : a ≤ d) : {s : Fin a → Fin d // StrictMono s} :=
  ⟨Fin.castLE h, Fin.strictMono_castLE h⟩

def topMinors {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) : Pol ι d a :=
  prodMinors (ι := ι) (n := n) (fun _ _ => topRows h)

theorem eval_rowSub {d a : ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) (z : Var ι d a → ℂ) (P : Pol ι d a) :
    eval z (rowSub κ P) = eval (fun y => ∑ i' : Fin d, κ y.1 i' y.2.1 * z (y.1, i', y.2.2)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [rowSub]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p y hp =>
      simp [rowSub, hp] at *
      exact Or.inl hp

theorem eval_colSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (z : Var ι d a → ℂ) (P : Pol ι d a) :
    eval z (colSub g P) = eval (fun y => ∑ j' : Fin a, g y.1 j' y.2.2 * z (y.1, y.2.1, j')) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [colSub]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p y hp =>
      simp [colSub, hp] at *
      exact Or.inl hp

theorem rowSub_rowSub {d a : ℕ} (κ κ' : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) :
    rowSub κ (rowSub κ' P) = rowSub (fun τ => κ τ * κ' τ) P := by
  have : (rowSub κ).comp (rowSub κ') = (rowSub (fun τ => κ τ * κ' τ) : Pol ι d a →ₐ[ℂ] Pol ι d a) := by
    apply MvPolynomial.algHom_ext
    intro y

    simp only [AlgHom.comp_apply, rowSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul, C_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

theorem rowSub_one {d a : ℕ} (P : Pol ι d a) : rowSub (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) P = P := by
  have : (rowSub (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) : Pol ι d a →ₐ[ℂ] Pol ι d a) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [rowSub, aeval_X, Matrix.one_apply, AlgHom.id_apply]
    rw [Finset.sum_eq_single y.2.1]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

theorem eval_basePt_topMinors {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) : eval (basePt ι d a) (topMinors h n) = 1 := by
  simp only [topMinors, prodMinors, minorAt, map_prod, RingHom.map_det]
  refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun j _ => ?_
  have : (RingHom.mapMatrix (eval (basePt ι d a)))
      (Matrix.of fun i i' : Fin a => (X (τ, (topRows h).1 i, i') : Pol ι d a)) = 1 := by
    ext i i'
    simp [basePt, topRows, Matrix.one_apply, Fin.ext_iff]
  rw [this, Matrix.det_one]

theorem topMinors_ne_zero {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) : topMinors (ι := ι) h n ≠ 0 := by
  intro h0
  have := eval_basePt_topMinors (ι := ι) h n
  rw [h0, map_zero] at this
  exact zero_ne_one this

end GlobalTheory.MinorFrame.RowIrr
end
end

section

open Classical

noncomputable section

namespace GlobalTheory.MinorFrame

open MvPolynomial

def smEquivSub (a d : ℕ) : {s : Fin a → Fin d // StrictMono s} ≃ {S : Finset (Fin d) // S.card = a} where
  toFun s := ⟨Finset.univ.map ⟨s.1, s.2.injective⟩, by simp⟩
  invFun S := ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩
  left_inv s := by
    apply Subtype.ext
    symm
    exact Finset.orderEmbOfFin_unique _ (fun x => by simp) s.2
  right_inv S := by
    apply Subtype.ext
    simp only
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨y, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
    · intro hx
      have : x ∈ Set.range (S.1.orderEmbOfFin S.2) := by rw [Finset.range_orderEmbOfFin]; exact hx
      exact this

theorem det_mul_eq_sum_sm {R : Type} [CommRing R] {a d : ℕ} (A : Matrix (Fin a) (Fin d) R)
    (B : Matrix (Fin d) (Fin a) R) :
    (A * B).det = ∑ s : {s : Fin a → Fin d // StrictMono s},
      (A.submatrix id s.1).det * (B.submatrix s.1 id).det := by
  rw [ReciprocityTheory.ChartRestriction.DS.S7.det_mul_eq_sum_submatrix, ← (smEquivSub a d).symm.sum_comp]
  rfl

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial
open scoped Matrix
variable {ι : Type} [Fintype ι]

def xMat (τ : ι) (d a : ℕ) : Matrix (Fin d) (Fin a) (Pol ι d a) := Matrix.of fun i j => X (τ, i, j)

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open scoped Matrix

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial
open scoped Matrix ComplexConjugate

variable {ι : Type} [Fintype ι]

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial

end GlobalTheory.MinorFrame
end
end
end
end
end
end

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame

def rsub {σ σ' : Type} [Fintype σ'] (M : Matrix σ' σ ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ' ℂ :=
  aeval fun v => ∑ w, C (M w v) * X w

theorem rsub_X {σ σ' : Type} [Fintype σ'] (M : Matrix σ' σ ℂ) (v : σ) :
    rsub M (X v) = ∑ w, C (M w v) * X w := aeval_X _ _

variable {ι : Type}

open Classical in
def frameMat {d a : ℕ} (x₀ : Var ι d a → ℂ) : Matrix (ι × Fin a × Fin a) (Var ι d a) ℂ :=
  by
    classical
    exact fun w v => if w.1 = v.1 ∧ w.2.2 = v.2.2 then x₀ (v.1, v.2.1, w.2.1) else 0

def detG [Fintype ι] (a : ℕ) (n : ι → ℕ) : MvPolynomial (ι × Fin a × Fin a) ℂ :=
  ∏ τ, (Matrix.of fun i j : Fin a => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)).det ^ n τ

theorem eval_detG [Fintype ι] (a : ℕ) (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2) (detG a n) = detChar n g := by
  unfold detG detChar
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext i j
  simp

theorem detG_ne_zero [Fintype ι] (a : ℕ) (n : ι → ℕ) : detG (ι := ι) a n ≠ 0 := by
  intro h
  have := eval_detG (ι := ι) a n (fun _ => 1)
  rw [h, map_zero] at this
  simp [detChar] at this

end GlobalTheory.MinorFrame
end
end

section

open Classical

noncomputable section

namespace GlobalTheory.MinorFrame

open MvPolynomial

variable {ι : Type} [Fintype ι]

def genColSub (d a : ℕ) : Pol ι d a →ₐ[ℂ] MvPolynomial (Var ι d a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
  aeval fun y => ∑ j' : Fin a, C (X (y.1, j', y.2.2)) * X (y.1, y.2.1, j')

omit [Fintype ι] in
theorem map_eval_genColSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    map (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) (genColSub d a P) = colSub g P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [genColSub, colSub, algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p y hp =>
    simp only [map_mul, hp]

    simp [genColSub, colSub, map_sum]

def genDetChar (a : ℕ) (n : ι → ℕ) : MvPolynomial (ι × Fin a × Fin a) ℂ :=
  ∏ τ, (Matrix.of fun i j => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)).det ^ n τ

theorem eval_genDetChar {a : ℕ} (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    eval (fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) (genDetChar a n) = detChar n g := by
  rw [genDetChar, map_prod, detChar]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext i j
  simp

theorem colSub_eq_detChar_smul_of_mem_inv {a d : ℕ} (n : ι → ℕ) (P : Pol ι d a) (hP : P ∈ inv a d n)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) : colSub g P = detChar n g • P := by
  set D : MvPolynomial (Var ι d a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
    genColSub d a P - C (genDetChar a n) * map C P with hDdef
  have hD : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ,
      map (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) D = colSub g P - detChar n g • P := by
    intro g
    rw [hDdef, map_sub, map_mul, map_C, map_eval_genColSub, eval_genDetChar, map_map, smul_eq_C_mul]
    congr 2
    have : (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2).comp (C : ℂ →+* MvPolynomial (ι × Fin a × Fin a) ℂ) =
        RingHom.id ℂ := by ext; simp
    rw [this, map_id]
  have hD0 : D = 0 := by
    refine MvPolynomial.ext _ _ fun m => ?_
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    refine Formalism.L2.Col.eq_zero_of_forall_unitary (ι := ι) (n := a) (fun _ => 1) (fun _ => by simp) _ fun u hu => ?_
    simp only [Matrix.one_mul]
    rw [← coeff_map, hD u]
    have hu' : ∀ τ, u τ ∈ Matrix.unitaryGroup (Fin a) ℂ := fun τ =>
      Matrix.mem_unitaryGroup_iff'.mpr (by simpa [Matrix.star_eq_conjTranspose] using hu τ)
    have := hP (fun τ => ⟨u τ, hu' τ⟩)
    simp only at this
    simp only [this, sub_self, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  have := hD g
  rw [hD0, _root_.map_zero] at this
  exact (sub_eq_zero.mp this.symm)

end GlobalTheory.MinorFrame
end
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.normal_local_ring_etale_base_change : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A] [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁]
    [IsIntegrallyClosed A₁] [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    [Algebra.Etale A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∀ a : A, a ≠ 0 →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (P₁ : Ideal (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj)) [P₁.IsPrime], algebraMap A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∉ P₁ →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA) P₁ := by
  first | (exact @GlobalTheory.KeyOriginBCEt.closureEtaleAt_baseChange) | (exact GlobalTheory.KeyOriginBCEt.closureEtaleAt_baseChange) | (intros; apply GlobalTheory.KeyOriginBCEt.closureEtaleAt_baseChange  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.isAffineOpen_preimage_quotientFibre : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), IsPullback ι q p (spMap (Ideal.Quotient.mk m) ≫ chart U) → ∀ W : Z.Opens, IsAffineOpen W → W ≤ p ⁻¹ᵁ U.1 → IsAffineOpen (ι ⁻¹ᵁ W) := by
  first | exact @GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre | exact GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre | (intros; apply GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS

theorem _root_.GlobalTheory.T.exists_spec_vectorField_of_dualNumber_section : ∀ (A : Type) [CommRing A] (σ : A →+* DualNumber A), (∀ a, (σ a).fst = a) → ∃ d : ∀ O : (Sp A).Opens, Γ(Sp A, O) → Γ(Sp A, O), IsField ⊤ d ∧ ∀ a : A, d ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (σ a).snd := by
  first | exact @GlobalTheory.SpecField.exists_isField | exact GlobalTheory.SpecField.exists_isField | (intros; apply GlobalTheory.SpecField.exists_isField <;> assumption)
end
