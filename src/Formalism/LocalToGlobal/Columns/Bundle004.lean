module

public import Aesop.BuiltinRules
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalRingCardinality.DataCoeff
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Formalism.LocalToGlobal.Columns.Bundle003
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.LocalRingCardinality.Params
import Formalism.GL3MeanSquares.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.GlobalTheory.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

section

open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

def bcLat {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] {n : ℕ} (j : K →+* K')
    (M : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K') (Fin n → K') :=
  tauLat (fun _ : Unit => j) () M

def bcPol {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] {σ : Type} (j : K →+* K')
    (T : Submodule (𝓞 K) (MvPolynomial σ K)) : Submodule (𝓞 K') (MvPolynomial σ K') :=
  Submodule.span (𝓞 K') ((fun F : MvPolynomial σ K => MvPolynomial.map j F) '' (T : Set (MvPolynomial σ K)))

def polOfVV {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (T : Submodule (𝓞 K) (VV K lam)) : Submodule (𝓞 K) (Pol K ι n) :=
  T.map ((VV K lam).subtype.restrictScalars (𝓞 K))

def BaseChangeSpace : Prop :=
  ∀ (K K' : Type) [Field K] [Field K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n),
    (∀ F : Pol K ι n, F ∈ VV K lam ↔ MvPolynomial.map j F ∈ VV K' lam) ∧
    Submodule.span K' ((fun F : Pol K ι n => MvPolynomial.map j F) '' (VV K lam : Set (Pol K ι n))) = VV K' lam

def BaseChangeAct : Prop :=
  ∀ (K K' : Type) [Field K] [Field K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (g : ι → GL (Fin n) K) (F : Pol K ι n),
    MvPolynomial.map j (actP lam g F) = actP lam (fun τ => Formalism.UG.bc j (g τ)) (MvPolynomial.map j F)

def BaseChangePair : Prop :=
  ∀ (K K' : Type) [Field K] [StarRing K] [Field K'] [StarRing K'] (j : K →+* K'), (∀ x, j (star x) = star (j x)) →
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (F F' : Pol K ι n),
      pairP lam (fun τ => (G τ).map j) (MvPolynomial.map j F) (MvPolynomial.map j F') = j (pairP lam G F F')

def BaseChangePairV : Prop :=
  ∀ (E K K' : Type) [Field E] [Field K] [StarRing K] [Field K'] [StarRing K'] (j : K →+* K'),
    (∀ x, j (star x) = star (j x)) →
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → DomWeight n) (J : Matrix (Fin n) (Fin n) E)
      (x x' : VV K lam) (y y' : VV K' lam),
      (y : Pol K' ι n) = MvPolynomial.map j (x : Pol K ι n) → (y' : Pol K' ι n) = MvPolynomial.map j (x' : Pol K ι n) →
      pairV (fun τ => j.comp (emb τ)) lam J y y' = j (pairV emb lam J x x') ∧
      pairVr (fun τ => j.comp (emb τ)) lam J y y' = j (pairVr emb lam J x x')

def BaseChangeTauLat : Prop :=
  ∀ (E K K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (ι : Type) (n : ℕ) (emb : ι → E →+* K) (τ : ι) (L : Submodule (𝓞 E) (Fin n → E)),
    tauLat (fun τ => j.comp (emb τ)) τ L = bcLat j (tauLat emb τ L)

def BaseChangeStd : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → DomWeight n), bcPol j (nabStd K lam) = nabStd K' lam ∧ bcPol j (delStd K lam) = delStd K' lam

def NabDelBaseChange : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsFullLattice K (M τ)) →
    bcPol j (nabP lam M) = nabP lam (fun τ => bcLat j (M τ)) ∧
    bcPol j (delP lam M) = delP lam (fun τ => bcLat j (M τ))

def NabDelDescent : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsFullLattice K (M τ)) →
    ∀ F : Pol K ι n,
      (F ∈ nabP lam M ↔ MvPolynomial.map j F ∈ nabP lam (fun τ => bcLat j (M τ))) ∧
      (F ∈ delP lam M ↔ MvPolynomial.map j F ∈ delP lam (fun τ => bcLat j (M τ)))

def BaseChangeDualFr : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (n : ℕ)
    (M : Submodule (𝓞 K) (Fin n → K)), Submodule.IsFullLattice K M → dualFr (bcLat j M) = bcLat j (dualFr M)

def NabDelBaseChangeAt : Prop :=
  ∀ (E K K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsFullLattice E L →
    polOfVV lam (nabAt (fun τ => j.comp (emb τ)) lam L) = bcPol j (polOfVV lam (nabAt emb lam L)) ∧
    polOfVV lam (delAt (fun τ => j.comp (emb τ)) lam L) = bcPol j (polOfVV lam (delAt emb lam L)) ∧
    polOfVV lam (nabAtr (fun τ => j.comp (emb τ)) lam L) = bcPol j (polOfVV lam (nabAtr emb lam L)) ∧
    polOfVV lam (delAtr (fun τ => j.comp (emb τ)) lam L) = bcPol j (polOfVV lam (delAtr emb lam L))

def NabDelDescentAt : Prop :=
  ∀ (E K K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsFullLattice E L → ∀ (x : VV K lam) (y : VV K' lam), (y : Pol K' ι n) = MvPolynomial.map j (x : Pol K ι n) →
    (x ∈ nabAt emb lam L ↔ y ∈ nabAt (fun τ => j.comp (emb τ)) lam L) ∧
    (x ∈ delAt emb lam L ↔ y ∈ delAt (fun τ => j.comp (emb τ)) lam L) ∧
    (x ∈ nabAtr emb lam L ↔ y ∈ nabAtr (fun τ => j.comp (emb τ)) lam L) ∧
    (x ∈ delAtr emb lam L ↔ y ∈ delAtr (fun τ => j.comp (emb τ)) lam L)

end Formalism.L2.DIV
end
end

section

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.HermitianLattices.TraceIntegrality

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

def extQ (lam : DomWeight n) : ℚ := Formalism.GradedWeylDivisibility.fockQ (extremal ℚ n lam) (extremal ℚ n lam)

end Std

section Std2

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

end Std2

section Deg

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

end Deg

end Formalism.L2.Col
end
end

section

open MvPolynomial NumberField
open scoped Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

section Scale

variable {K σ : Type} [Field K] [Fintype σ]

theorem brp_aeval_scale_monomial (m : σ →₀ ℕ) (c t : K) :
    aeval (fun v => C t * X v) (monomial m c) = t ^ (m.sum fun _ e => e) • monomial m c := by
  rw [aeval_monomial, monomial_eq, smul_eq_C_mul, algebraMap_eq]
  simp only [mul_pow, Finsupp.prod_mul]
  have h : (m.prod fun _ e => (C t : MvPolynomial σ K) ^ e) = C (t ^ (m.sum fun _ e => e)) := by
    simp only [Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum, map_pow]
  rw [h, map_pow]
  ring

theorem brp_aeval_scale_whom {r n : ℕ} (ν : Fin n → ℕ) (Q : MvPolynomial (Fin r × Fin n) K)
    (hQ : Q ∈ weightedHomogeneousSubmodule K (Formalism.GradedWeylDivisibility.colW r n) ν) (t : K) :
    aeval (fun v => C t * X v) Q = t ^ (∑ s, ν s) • Q := by
  have hQ' : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) Q ν := by
    simpa [mem_weightedHomogeneousSubmodule] using hQ
  have hdeg : ∀ m ∈ Q.support, (m.sum fun _ e => e) = ∑ s, ν s := by
    intro m hm
    rw [← hQ' (mem_support_iff.mp hm)]
    simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Formalism.GradedWeylDivisibility.colW, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [Pi.single_apply]
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]

  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [brp_aeval_scale_monomial, hdeg m hm]

end Scale

section Scalar

variable (K : Type) [Field K] {n : ℕ}

def brpSc (t : Kˣ) : GL (Fin n) K := Units.map (algebraMap K (Matrix (Fin n) (Fin n) K)).toMonoidHom t

theorem brpSc_coe (t : Kˣ) : ((brpSc K t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (t : K) • 1 := by
  show algebraMap K (Matrix (Fin n) (Fin n) K) (t : K) = _
  exact Algebra.algebraMap_eq_smul_one _

theorem brp_natW_cast (lam : DomWeight n) (i : Fin n) : ((lam.natW i : ℕ) : ℤ) = lam.w i - lam.detShift := by
  have hn : 0 < n := Fin.pos i
  have h : lam.detShift ≤ lam.w i := by
    rw [DomWeight.detShift, dite_eq_left hn]
    exact lam.anti (show i ≤ ⟨n - 1, by omega⟩ from Fin.le_iff_val_le_val.mpr (by simp; omega))
  simp only [DomWeight.natW]
  exact Int.toNat_of_nonneg (by omega)

theorem brp_wsum (lam : DomWeight n) :
    (∑ i, lam.w i) = ((∑ i, lam.natW i : ℕ) : ℤ) + n * lam.detShift := by
  push_cast
  simp only [brp_natW_cast, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

end Scalar

section Chi

variable (K : Type) [Field K] {n : ℕ}

def wsum (lam : DomWeight n) : ℤ := ∑ i, lam.w i

end Chi

section ChiPow

variable (K : Type) [Field K] [CharZero K] {n : ℕ}

def brpGL (M : Matrix (Fin n) (Fin n) K) (h : IsUnit M.det) : GL (Fin n) K := Matrix.nonsingInvUnit M h

theorem brpGL_coe (M : Matrix (Fin n) (Fin n) K) (h : IsUnit M.det) : ((brpGL K M h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = M := rfl

theorem brp_isUnit_transvection (i j : Fin n) (hij : i ≠ j) (c : K) : IsUnit (Matrix.transvection i j c).det := by
  rw [Matrix.det_transvection_of_ne _ _ hij]
  exact isUnit_one

theorem brp_diag_transvection (i j : Fin n) (hij : i ≠ j) (c : K) :
    Matrix.diagonal (Function.update (1 : Fin n → K) i 2) * Matrix.transvection i j c =
      Matrix.transvection i j (2 * c) * Matrix.diagonal (Function.update (1 : Fin n → K) i 2) := by
  have h1 : Matrix.diagonal (Function.update (1 : Fin n → K) i 2) * Matrix.single i j c =
      Matrix.single i j (2 * c) := by
    ext a b
    rw [Matrix.diagonal_mul]
    by_cases ha : a = i
    · subst ha
      by_cases hb : j = b <;> simp [Matrix.single_apply, hb]
    · simp [Matrix.single_apply, ha, Ne.symm ha]
  have h2 : Matrix.single i j (2 * c) * Matrix.diagonal (Function.update (1 : Fin n → K) i 2) =
      Matrix.single i j (2 * c) := by
    ext a b
    rw [Matrix.mul_diagonal]
    by_cases hb : b = j
    · subst hb
      simp [Function.update_apply, Ne.symm hij]
    · simp [Matrix.single_apply, Ne.symm hb]
  rw [Matrix.transvection, Matrix.transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, h1, h2]

def brpDiag : (Fin n → Kˣ) →* GL (Fin n) K :=
  (Units.map (Matrix.diagonalRingHom (Fin n) K).toMonoidHom).comp (MulEquiv.piUnits.symm.toMonoidHom)

theorem brpDiag_coe (d : Fin n → Kˣ) :
    ((brpDiag K d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun a => (d a : K) := by rfl

end ChiPow

section ChiPow2

variable (K : Type) [Field K] [CharZero K] {n : ℕ}

theorem brp_isUnit_perm (σ : Equiv.Perm (Fin n)) : IsUnit (Equiv.Perm.permMatrix K σ).det := by
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem brp_perm_diag (σ : Equiv.Perm (Fin n)) (f : Fin n → K) :
    Equiv.Perm.permMatrix K σ * Matrix.diagonal f = Matrix.diagonal (f ∘ σ) * Equiv.Perm.permMatrix K σ := by
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Function.comp_apply]
  by_cases h : σ a = b
  · subst h
    exact mul_comm _ _
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]

end ChiPow2

section ChiPow3

variable (K : Type) [Field K] [CharZero K] {n : ℕ}

theorem brpDiag_const (t : Kˣ) : brpDiag K (n := n) (fun _ => t) = brpSc K t := by
  apply Units.ext
  rw [brpDiag_coe, brpSc_coe, Matrix.smul_one_eq_diagonal]

theorem brp_coe_list_transvec (L : List (Matrix.TransvectionStruct (Fin n) K)) :
    (((L.map fun t => brpGL K t.toMatrix (by rw [t.det]; exact isUnit_one)).prod : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (L.map Matrix.TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => simp
  | cons t L ih => rw [List.map_cons, List.prod_cons, Units.val_mul, ih, brpGL_coe, List.map_cons, List.prod_cons]

theorem brp_det_list_transvec (L : List (Matrix.TransvectionStruct (Fin n) K)) :
    (L.map Matrix.TransvectionStruct.toMatrix).prod.det = 1 := by
  induction L with
  | nil => simp
  | cons t L ih => rw [List.map_cons, List.prod_cons, Matrix.det_mul, ih, t.det, one_mul]

end ChiPow3

end Formalism.L2.Col
end
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CF

open Formalism.L2.Forms

section XP

variable (D : ColRec)

theorem rankP : letI := D.host.cmStar; D.sp.X'.rank = D.R.N D.R.m - 1 := by
  letI := D.host.cmStar
  have h := D.sp.X'_rank
  have h2 := D.R.m_add_three_le_k
  rw [h]; unfold Ranks.rankX' Ranks.r Ranks.N; rw [Nat.mul_add, Nat.mul_one]; omega

def gramP : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E :=
  letI := D.host.cmStar
  D.sp.X'.gram.reindex (finCongr (rankP D)) (finCongr (rankP D))

def iXc : (Fin (D.R.N D.R.m - 1) → D.host.E) →ₗ[D.host.E] (Fin (D.R.N D.R.m) → D.host.E) :=
  letI := D.host.cmStar
  ((((D.sp.X D.R.m).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D D.R.m le_rfl)).symm) :
      (D.sp.X D.R.m).V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m) → D.host.E)) :
      (D.sp.X D.R.m).V →ₗ[D.host.E] (Fin (D.R.N D.R.m) → D.host.E)).comp D.sp.iX').comp
    ((D.sp.X'.frame.equivFun.trans
      (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm :
      (Fin (D.R.N D.R.m - 1) → D.host.E) →ₗ[D.host.E] D.sp.X'.V)

def zc : Fin (D.R.N D.R.m) → D.host.E :=
  letI := D.host.cmStar
  ((D.sp.X D.R.m).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D D.R.m le_rfl)).symm)) D.sp.z

def iXm : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m - 1)) D.host.E := LinearMap.toMatrix' (iXc D)

def IsExt (z0 : Fin (D.R.N D.R.m) → D.host.E) {R : Type} [CommRing R] (φ : D.host.E →+* R)
    (g' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) R)
    (g : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) R) : Prop :=
  g * (iXm D).map φ = (iXm D).map φ * g' ∧ g *ᵥ (fun a => φ (z0 a)) = fun a => φ (z0 a)

variable {D}



structure ClsPTied (u : D.what₂.Word) where

  lev : StepLevel D.host.F D.host.E (sigD D) (gramP D) 1 D.R.f (badG D)
  y : (D.fm u).clsP → UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls lev))

  lat : (D.fm u).clsP → Submodule (𝓞 D.host.E) (Fin (D.R.N D.R.m - 1) → D.host.E)
  y_lat : ∀ c (x : Fin (D.R.N D.R.m - 1) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (lat c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) lev.Lb
  lat_fin : ∀ c, Module.Finite (𝓞 D.host.E) (lat c)
  stabI : ∀ c, (D.fm u).stabilizer₂ c →* UJ (sigD D : D.host.E →+* D.host.E) (gramP D)
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramP D)),
    γ ∈ (stabI c).range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        lev.U.map (MulAut.conj (y c).1).toMonoidHom

def sgT (u : D.what₂.Word) : D.what₂.Tau → DomWeight (D.R.N D.R.m - 1) :=
  fun τ => shW ((D.fm u).sg τ) ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ)




structure TilTied (u : D.what₂.Word) (A : AtTTied u) (K : ClsPTied u) (P : LvTied u A D.R.m le_rfl) where
  z0 : Fin (D.R.N D.R.m) → D.host.E
  lastCoordinateUniformizerVector_spans_orthogonal_line : ∃ a : D.host.E, z0 = a • zc D
  hermitianForm_lastCoordinateUniformizerVector_self : hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) z0 z0 = ((D.mem u).A.T : D.host.E)
  ga : (D.fm u).clsP → UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
  til_lat : ∀ c, mulLat (ga c).1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) =
    (K.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0}
  til_fv : ∀ v c (x : ↥(Ld D u D.R.m le_rfl ((D.fm u).til c))) (r : 𝓞 D.host.E),
    (r : D.host.E) = hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) z0 ((ga c).1.1 *ᵥ x.1) →
    (D.fm u).fv D.R.m v ((D.fm u).til c) (P.pr v _ x) = A.res v r





structure TilAd {u : D.what₂.Word} {A : AtTTied u} {K : ClsPTied u} {P : LvTied u A D.R.m le_rfl}
    (Tl : TilTied u A K P) (Km : ClsTied u D.R.m le_rfl) where
  ka : (D.fm u).clsP → Km.lev.U
  til_ad : ∀ c (g : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    IsExt D Tl.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (K.y c).1.1 g.1 →
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tl.ga c).1 * (Km.y ((D.fm u).til c)).1 =
      g * (ka c).1


end XP

section All

variable {D : ColRec}



end All

end Formalism.L2.Col.CF

end
end

section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions

namespace Formalism.L2.Col

def rowFrameOf (D : D7) (Occ : Set (NG.FinTyp D.host.E D.R.r)) (e : D.what₂.FT ≃ FinTypCls Occ) : Formalism.L2.RowFrame D where
  rep σ := finTypRep Occ (e σ)
  inj _ _ h := e.injective (finTypRep_inj h)

end Formalism.L2.Col
end
end
