module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointChern

theorem charpolyRev_conj_of_mul_eq_one {R : Type*} [CommRing R] {r : Type*} [Fintype r] [DecidableEq r]
    (M P Q : Matrix r r R) (hQP : Q * P = 1) : (Q * M * P).charpolyRev = M.charpolyRev := by
  have hQP' : Q.map Polynomial.C * P.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  have e : (1 : Matrix r r (Polynomial R)) - (Polynomial.X : Polynomial R) • (Q * M * P).map Polynomial.C =
      Q.map Polynomial.C * (1 - (Polynomial.X : Polynomial R) • M.map Polynomial.C) * P.map Polynomial.C := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hQP',
      Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.charpolyRev, Matrix.charpolyRev, e, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
    ← Matrix.det_mul, hQP', Matrix.det_one, one_mul]

theorem curvPoly_eq_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : curvPoly G v =
      ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) • (curv G v (coordVec a) (coordVec b)).map C := by
  ext i j
  simp [curvPoly, Matrix.sum_apply, mul_comm]

end GlobalTheory.PointChern

namespace GlobalTheory.PointChern

theorem gram_eq_changeFrame {r : Type} [Fintype r] (c : ℝ) (hc : 0 < c) (g K : Matrix r r ℂ) :
    (c : ℂ) • (g * K * gᴴ) = (((Real.sqrt c : ℝ) : ℂ) • gᵀ)ᵀ * K * (((Real.sqrt c : ℝ) : ℂ) • gᵀ)ᴴᵀ := by
  have h1 : ((((Real.sqrt c : ℝ) : ℂ) • gᵀ)ᴴᵀ) = ((Real.sqrt c : ℝ) : ℂ) • gᴴ := by
    ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have h2 : ((Real.sqrt c : ℝ) : ℂ) * ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  rw [h1, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, h2]

theorem chernTop_changeFrame : ∀ {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (G K g : ReciprocityTheory.L2DbarEstimates.V n → Mat m ℂ) (c : ι → ℝ) (v : ReciprocityTheory.L2DbarEstimates.V n), (∀ τ, 0 < c τ) → (∀ τ i j, AnalyticAt ℂ (fun w => g w τ i j) v) → (∀ τ, IsUnit (g v τ).det) → (∀ τ, MContDiffAt 2 (fun w => K w τ) v) → (∀ τ, IsUnit (K v τ).det) → (∀ᶠ w in 𝓝 v, ∀ τ, G w τ = (c τ : ℂ) • (g w τ * K w τ * (g w τ)ᴴ)) → chernTop R G v = chernTop R K v := by
  intro n ι m R G K g c v hc hg hgu hK hKu hG
  have key : ∀ τ, curvPoly (fun u => G u τ) v = ((((Real.sqrt (c τ) : ℝ) : ℂ) • (g v τ)ᵀ)⁻¹).map C *
      curvPoly (fun u => K u τ) v * ((((Real.sqrt (c τ) : ℝ) : ℂ) • (g v τ)ᵀ)).map C := by
    intro τ
    set A : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin (m τ)) ℂ :=
      fun u => ((Real.sqrt (c τ) : ℝ) : ℂ) • (g u τ)ᵀ with hAdef
    have hent : ∀ a b, (fun x => A x a b) = fun x => ((Real.sqrt (c τ) : ℝ) : ℂ) * g x τ b a := fun a b => rfl
    have hA : MContDiffAt 2 A v := fun a b => by
      rw [hent]
      exact contDiffAt_const.mul ((hg τ b a).contDiffAt.restrict_scalars ℝ)
    have hAu : IsUnit (A v).det := by
      simp only [hAdef, Matrix.det_smul, Matrix.det_transpose]
      refine IsUnit.mul (IsUnit.pow _ (Ne.isUnit ?_)) (hgu τ)
      exact_mod_cast (Real.sqrt_pos.2 (hc τ)).ne'
    have hA0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0 := by
      have hev : ∀ᶠ x in 𝓝 v, ∀ a b, AnalyticAt ℂ (fun w => g w τ b a) x :=
        eventually_all.2 fun a => eventually_all.2 fun b => (hg τ b a).eventually_analyticAt
      filter_upwards [hev] with x hx η
      ext a b
      rw [mdbar_apply, hent, GlobalTheory.dbar_eq_zero (((hx a b).differentiableAt).const_mul _)]
      rfl
    have hGe : (fun u => G u τ) =ᶠ[𝓝 v] fun u => (A u)ᵀ * K u τ * (A u)ᴴᵀ :=
      hG.mono fun u hu => by show G u τ = _; rw [hu τ]; exact gram_eq_changeFrame _ (hc τ) _ _
    have hcurv : ∀ ξ η, curv (fun u => G u τ) v ξ η = (A v)⁻¹ * curv (fun u => K u τ) v ξ η * A v :=
      fun ξ η => by rw [curv_congr hGe, curv_changeFrame (hK τ) (hKu τ) hA hAu hA0]
    clear_value A
    rw [curvPoly_eq_sum, curvPoly_eq_sum]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, hcurv]
    subst hAdef
    rfl
  have key2 : ∀ τ k, chernPoly (fun u => G u τ) v k = chernPoly (fun u => K u τ) v k := by
    intro τ k
    have hu : IsUnit (((Real.sqrt (c τ) : ℝ) : ℂ) • (g v τ)ᵀ).det := by
      simp only [Matrix.det_smul, Matrix.det_transpose]
      refine IsUnit.mul (IsUnit.pow _ (Ne.isUnit ?_)) (hgu τ)
      exact_mod_cast (Real.sqrt_pos.2 (hc τ)).ne'
    rw [chernPoly, chernPoly, key, show ∀ (Q M P : Matrix (Fin (m τ)) (Fin (m τ)) (MvPolynomial (Fin n × Fin n) ℂ)), -(Q * M * P) = Q * (-M) * P from fun Q M P => by rw [Matrix.mul_neg, Matrix.neg_mul], charpolyRev_conj_of_mul_eq_one]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  simp only [chernTop, key2]

end GlobalTheory.PointChern
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.ChernConj

theorem charpolyRev_map_hom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R) : M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h]

theorem charpolyRev_conj {R : Type} [CommRing R] {m : ℕ} (P Q M : Matrix (Fin m) (Fin m) R)
    (hPQ : P * Q = 1) : (P * M * Q).charpolyRev = M.charpolyRev := by
  have hPQ' : P.map Polynomial.C * Q.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.charpolyRev, Matrix.charpolyRev]
  have e : (1 : Matrix (Fin m) (Fin m) (Polynomial R)) - (Polynomial.X : Polynomial R) • (P * M * Q).map Polynomial.C
      = P.map Polynomial.C * (1 - (Polynomial.X : Polynomial R) • M.map Polynomial.C) * Q.map Polynomial.C := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ', Matrix.mul_smul, Matrix.smul_mul,
      Matrix.map_mul, Matrix.map_mul]
  rw [e, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, hPQ', Matrix.det_one, one_mul]

theorem chernPoly_conj_subst : ∀ {n r : ℕ} (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin r) ℂ) (v v' : ReciprocityTheory.L2DbarEstimates.V n) (J : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin r) (Fin r) ℂ), IsUnit S.det → (∀ a b, curv F v (coordVec a) (coordVec b) = S⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) • curv F v' (coordVec c) (coordVec d)) * S) → ∀ k, chernPoly F v k = aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) (chernPoly F v' k) := by
  intro n r F v v' J S hS h k
  set φ : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) with hφ
  have hP : (S⁻¹).map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) * S.map C = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hS, Matrix.map_one _ (map_zero _) (map_one _)]
  have hA : curvPoly F v = (S⁻¹).map C * (curvPoly F v').map φ * S.map C := by
    refine Matrix.ext fun i j => ?_

    simp only [curvPoly, h, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, aeval_C, aeval_X, hφ, MvPolynomial.algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
    conv_rhs => enter [2, q, 2, p, 2, c]; rw [Finset.sum_comm]
    conv_rhs => enter [2, q, 2, p]; rw [Finset.sum_comm]
    conv_rhs => enter [2, q]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, q, 2, p, 2, c]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, q, 2, p]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, q]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, b, 2, q]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, b, 2, q, 2, c]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hN : -curvPoly F v = (S⁻¹).map C * (-curvPoly F v').map (φ : MvPolynomial (Fin n × Fin n) ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) * S.map C := by
    rw [hA, Matrix.map_neg, Matrix.mul_neg, Matrix.neg_mul]
    · rfl
    · exact fun a => map_neg φ a
  unfold chernPoly
  rw [hN, charpolyRev_conj _ _ _ hP, ← charpolyRev_map_hom, Polynomial.coeff_map]
  rfl

end GlobalTheory.ChernConj
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.ChernReindex

variable {n a b : ℕ}

theorem mdel_reindex (e : Fin a ≃ Fin b) (H : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (z ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.HermFrame.mdel (fun u => Matrix.reindex e e (H u)) z ξ = Matrix.reindex e e (GlobalTheory.HermFrame.mdel H z ξ) := by
  ext i j; rfl

theorem conn_reindex (e : Fin a ≃ Fin b) (H : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (z ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.HermFrame.conn (fun u => Matrix.reindex e e (H u)) z ξ = Matrix.reindex e e (GlobalTheory.HermFrame.conn H z ξ) := by
  rw [GlobalTheory.HermFrame.conn, GlobalTheory.HermFrame.conn, mdel_reindex, Matrix.transpose_reindex, Matrix.transpose_reindex,
    Matrix.inv_reindex, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv]

theorem curv_reindex (e : Fin a ≃ Fin b) (H : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (z ξ η : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.HermFrame.curv (fun u => Matrix.reindex e e (H u)) z ξ η = Matrix.reindex e e (GlobalTheory.HermFrame.curv H z ξ η) := by
  unfold GlobalTheory.HermFrame.curv
  simp_rw [conn_reindex]
  ext i j; rfl

theorem curvPoly_reindex (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.GoodMetric.curvPoly (fun u => Matrix.reindex e e (F u)) v = Matrix.reindex e e (GlobalTheory.GoodMetric.curvPoly F v) := by
  refine Matrix.ext fun i j => ?_
  simp only [GlobalTheory.GoodMetric.curvPoly, curv_reindex]
  rfl

theorem charpolyRev_reindex {R : Type} [CommRing R] (e : Fin a ≃ Fin b) (M : Matrix (Fin a) (Fin a) R) :
    (Matrix.reindex e e M).charpolyRev = M.charpolyRev := by
  rw [← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly, Matrix.charpoly_reindex]

theorem chernPoly_reindex : ∀ {n a b : ℕ} (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ), chernPoly (fun u => Matrix.reindex e e (F u)) v k = chernPoly F v k := by
  intro n a b e F v k
  rw [GlobalTheory.GoodMetric.chernPoly, GlobalTheory.GoodMetric.chernPoly, curvPoly_reindex,
    show -(Matrix.reindex e e (GlobalTheory.GoodMetric.curvPoly F v)) = Matrix.reindex e e (-GlobalTheory.GoodMetric.curvPoly F v) from by
      ext i j; rfl, charpolyRev_reindex]

end GlobalTheory.ChernReindex
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.ChernDegree

def gradedCoeff (σ : Type) : Subring (Polynomial (MvPolynomial σ ℂ)) where
  carrier := {p | ∀ k, (p.coeff k).IsHomogeneous k}
  mul_mem' := by
    intro p q hp hq k
    rw [Polynomial.coeff_mul]
    refine IsHomogeneous.sum _ _ _ fun x hx => ?_
    have := (hp x.1).mul (hq x.2)
    rwa [Finset.HasAntidiagonal.mem_antidiagonal.1 hx] at this
  one_mem' := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simpa using isHomogeneous_one σ ℂ
    · rw [Polynomial.coeff_one, if_neg (by omega)]; exact isHomogeneous_zero _ _ _
  add_mem' := by
    intro p q hp hq k
    rw [Polynomial.coeff_add]; exact (hp k).add (hq k)
  zero_mem' := by
    intro k
    rw [Polynomial.coeff_zero]; exact isHomogeneous_zero _ _ _
  neg_mem' := by
    intro p hp k
    rw [Polynomial.coeff_neg]; exact (hp k).neg

theorem charpolyRev_coeff_isHomogeneous {σ r : Type} [Fintype r] [DecidableEq r]
    (M : Matrix r r (MvPolynomial σ ℂ)) (hM : ∀ i j, (M i j).IsHomogeneous 1) (k : ℕ) :
    ((Matrix.charpolyRev M).coeff k).IsHomogeneous k := by
  have hent : ∀ i j, (1 - (Polynomial.X : Polynomial (MvPolynomial σ ℂ)) • M.map Polynomial.C) i j ∈ gradedCoeff σ := by
    intro i j
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    refine Subring.sub_mem _ ?_ ?_
    · rw [Matrix.one_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · intro l
      rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs with h
      · subst h; exact hM i j
      · exact isHomogeneous_zero _ _ _
  have hdet : Matrix.charpolyRev M ∈ gradedCoeff σ := by
    rw [Matrix.charpolyRev, Matrix.det_apply']
    refine Subring.sum_mem _ fun s _ => Subring.mul_mem _ (intCast_mem _ _) ?_
    exact Subring.prod_mem _ fun i _ => hent _ _
  exact hdet k

theorem chernPoly_isHomogeneous {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]
    (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) :
    (chernPoly G v k).IsHomogeneous k := by
  refine charpolyRev_coeff_isHomogeneous _ (fun i j => ?_) k
  rw [Matrix.neg_apply, curvPoly, Matrix.of_apply]
  exact (IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ =>
    isHomogeneous_C_mul_X _ _).neg

theorem aeval_isWeightedHomogeneous {σ τ : Type} {w : σ → ℕ} {w' : τ → ℕ}
    {φ : MvPolynomial σ ℝ} {m : ℕ} (hφ : IsWeightedHomogeneous w φ m)
    (g : σ → MvPolynomial τ ℂ) (hg : ∀ i, IsWeightedHomogeneous w' (g i) (w i)) :
    IsWeightedHomogeneous w' (aeval g φ) m := by

  rw [φ.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [aeval_monomial]
  have hdeg : (Finsupp.weight w) d = m := hφ (mem_support_iff.mp hd)
  have h1 : IsWeightedHomogeneous w' (d.prod fun i k => g i ^ k) (∑ i ∈ d.support, d i • w i) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => (hg i).pow (d i)
  have h2 : (∑ i ∈ d.support, d i • w i) = m := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum]
  rw [h2] at h1
  have h3 := (isWeightedHomogeneous_C w' (algebraMap ℝ ℂ (AddMonoidAlgebra.coeff φ d))).mul h1
  rw [zero_add] at h3
  rw [MvPolynomial.algebraMap_apply]
  exact h3

theorem topCoeff_eq_zero {n d : ℕ} {P : MvPolynomial (Fin n × Fin n) ℂ} (hP : P.IsHomogeneous d) (hd : d ≠ n) :
    topCoeff P = 0 := by
  unfold topCoeff
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [hP.coeff_eq_zero, mul_zero]
  intro h
  apply hd

  rw [← h, Finsupp.degree_eq_weight_one, map_sum]
  simp [Finsupp.weight_single]

end GlobalTheory.GoodMetric.ChernDegree


open GlobalTheory.GoodMetric.ChernDegree in
theorem GlobalTheory.GoodMetric.chernTop_eq_zero_of_weightedHomogeneous (n : ℕ) (ι : Type) (m : ι → ℕ)
    (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (Q : MvPolynomial (ι × ℕ) ℝ) (d : ℕ)
    (hQ : MvPolynomial.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) Q d) (hd : d ≠ n) :
    chernTop Q G v = 0 := by
  have h : (aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) Q).IsHomogeneous d :=
    aeval_isWeightedHomogeneous hQ _ fun x => chernPoly_isHomogeneous _ _ _
  rw [chernTop, topCoeff_eq_zero h hd, Complex.zero_re, mul_zero]
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.HermFrame

theorem holo_contDiffOn {n : ℕ} {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U)
    {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} (hg : DifferentiableOn ℂ g U) {m : WithTop ℕ∞} :
    ContDiffOn ℂ m g U := by
  have ha : AnalyticOnNhd ℂ g U := fun z hz =>
    ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.analyticAt_of_diffOn hU hg hz
  exact ha.contDiffOn hU.uniqueDiffOn

theorem holo_fderiv_apply_on {n : ℕ} {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U)
    {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} (hg : DifferentiableOn ℂ g U) (w : ReciprocityTheory.L2DbarEstimates.V n) :
    DifferentiableOn ℂ (fun u => fderiv ℂ g u w) U := by
  have h2 : ContDiffOn ℂ 2 g U := holo_contDiffOn hU hg
  have h1 : ContDiffOn ℂ 1 (fun u => fderiv ℂ g u) U := h2.fderiv_of_isOpen hU (by norm_num)
  exact (h1.clm_apply contDiffOn_const).differentiableOn (by norm_num)

theorem holo_del_eq_on {n : ℕ} {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U)
    {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} (hg : DifferentiableOn ℂ g U) {u : ReciprocityTheory.L2DbarEstimates.V n}
    (hu : u ∈ U) (w : ReciprocityTheory.L2DbarEstimates.V n) : GlobalTheory.del g u w = fderiv ℂ g u w := by
  rw [GlobalTheory.del_eq_fderiv (hg.differentiableAt (hU.mem_nhds hu))]

end GlobalTheory.HermFrame

namespace GlobalTheory.HermFrame

theorem holo_mdel_entry {n : ℕ} {K : Type} {P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ}
    {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U) (hP : ∀ i k, DifferentiableOn ℂ (fun u => P u i k) U)
    {u : ReciprocityTheory.L2DbarEstimates.V n} (hu : u ∈ U) (w : ReciprocityTheory.L2DbarEstimates.V n) (i k : K) :
    mdel P u w i k = fderiv ℂ (fun x => P x i k) u w :=
  holo_del_eq_on hU (hP i k) hu w

theorem holo_mdel_mdel_entry {n : ℕ} {K : Type} {P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ}
    {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U) (hP : ∀ i k, DifferentiableOn ℂ (fun u => P u i k) U)
    {u : ReciprocityTheory.L2DbarEstimates.V n} (hu : u ∈ U) (w w' : ReciprocityTheory.L2DbarEstimates.V n) (i k : K) :
    mdel (fun x => mdel P x w') u w i k =
      fderiv ℂ (fun x => fderiv ℂ (fun y => P y i k) x w') u w := by
  change GlobalTheory.del (fun x => GlobalTheory.del (fun y => P y i k) x w') u w = _
  have hev : (fun x => GlobalTheory.del (fun y => P y i k) x w') =ᶠ[𝓝 u]
      (fun x => fderiv ℂ (fun y => P y i k) x w') := by
    filter_upwards [hU.mem_nhds hu] with x hx
    exact holo_del_eq_on hU (hP i k) hx w'
  rw [GlobalTheory.del_congr hev]
  exact holo_del_eq_on hU (holo_fderiv_apply_on hU (hP i k) w') hu w

theorem holoFrame_local_bounds : ∀ (n : ℕ) (K : Type) [Fintype K] [DecidableEq K] (P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ) (r : ℝ), 0 < r → (∀ i k, DifferentiableOn ℂ (fun u => P u i k) (Metric.ball 0 r)) → IsUnit (P 0).det → ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ ∃ B : ℝ, ∀ v : ReciprocityTheory.L2DbarEstimates.V n, ‖v‖ < r' → IsUnit (P v).det ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => P u i k) v) ∧ (∀ᶠ u in nhds v, ∀ η, GlobalTheory.HermFrame.mdbar P u η = 0) ∧ (∀ i k, ‖P v i k‖ ≤ B) ∧ (∀ i k, ‖(P v)⁻¹ i k‖ ≤ B) ∧ (∀ a i k, ‖GlobalTheory.HermFrame.mdel P v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) ∧ (∀ a b i k, ‖GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.mdel P u (GlobalTheory.GoodMetric.coordVec b)) v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) := by
  intro n K _ _ P r hr hP h0
  set U : Set (ReciprocityTheory.L2DbarEstimates.V n) := Metric.ball 0 r with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hPc : ContinuousOn P U :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => (hP i k).continuousOn
  have hdetc : ContinuousOn (fun u => (P u).det) U :=
    (continuous_id.matrix_det).comp_continuousOn hPc
  have hadjc : ∀ i k, ContinuousOn (fun u => (P u).adjugate i k) U := fun i k =>
    ((continuous_id.matrix_adjugate).matrix_elem i k).comp_continuousOn hPc
  have h0U : (0 : ReciprocityTheory.L2DbarEstimates.V n) ∈ U := Metric.mem_ball_self hr
  have hev : ∀ᶠ u in 𝓝 (0 : ReciprocityTheory.L2DbarEstimates.V n), (P u).det ≠ 0 :=
    (hdetc.continuousAt (hU.mem_nhds h0U)).eventually_ne h0.ne_zero
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hm : 0 < min ε r := lt_min hε hr
  set ρ := min ε r / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  have hρε : ρ < ε := by have := min_le_left ε r; rw [hρ]; linarith
  have hρr : ρ < r := by have := min_le_right ε r; rw [hρ]; linarith
  set S := Metric.closedBall (0 : ReciprocityTheory.L2DbarEstimates.V n) ρ with hSdef
  have hSU : S ⊆ U := Metric.closedBall_subset_ball hρr
  have hSdet : ∀ u ∈ S, (P u).det ≠ 0 := fun u hu =>
    hball u (Metric.closedBall_subset_ball hρε hu)
  have hSc : IsCompact S := isCompact_closedBall 0 ρ

  let G1 : ReciprocityTheory.L2DbarEstimates.V n → (K → K → ℂ) := fun u i k => P u i k
  let G2 : ReciprocityTheory.L2DbarEstimates.V n → (K → K → ℂ) := fun u i k => (P u)⁻¹ i k
  let G3 : ReciprocityTheory.L2DbarEstimates.V n → (Fin n → K → K → ℂ) := fun u a i k =>
    mdel P u (GlobalTheory.GoodMetric.coordVec a) i k
  let G4 : ReciprocityTheory.L2DbarEstimates.V n → (Fin n → Fin n → K → K → ℂ) := fun u a b i k =>
    mdel (fun u => mdel P u (GlobalTheory.GoodMetric.coordVec b)) u (GlobalTheory.GoodMetric.coordVec a) i k
  have hG1 : ContinuousOn G1 S :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => ((hP i k).continuousOn).mono hSU
  have hG2 : ContinuousOn G2 S := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => ?_
    refine (((hdetc.mono hSU).inv₀ hSdet).mul ((hadjc i k).mono hSU)).congr fun u _ => ?_
    simp [G2, Matrix.inv_def, Ring.inverse_eq_inv']
  have hG3 : ContinuousOn G3 S := by
    refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => ?_
    refine ((holo_fderiv_apply_on hU (hP i k) (GlobalTheory.GoodMetric.coordVec a)).continuousOn.mono
      hSU).congr fun u hu => ?_
    exact holo_mdel_entry hU hP (hSU hu) _ i k
  have hG4 : ContinuousOn G4 S := by
    refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => continuousOn_pi.2 fun i =>
      continuousOn_pi.2 fun k => ?_
    refine ((holo_fderiv_apply_on hU (holo_fderiv_apply_on hU (hP i k)
      (GlobalTheory.GoodMetric.coordVec b)) (GlobalTheory.GoodMetric.coordVec a)).continuousOn.mono hSU).congr
      fun u hu => ?_
    exact holo_mdel_mdel_entry hU hP (hSU hu) _ _ i k
  obtain ⟨C1, hC1⟩ := hSc.exists_bound_of_continuousOn hG1
  obtain ⟨C2, hC2⟩ := hSc.exists_bound_of_continuousOn hG2
  obtain ⟨C3, hC3⟩ := hSc.exists_bound_of_continuousOn hG3
  obtain ⟨C4, hC4⟩ := hSc.exists_bound_of_continuousOn hG4
  refine ⟨ρ, hρpos, hρr.le, max (max C1 C2) (max C3 C4), fun v hv => ?_⟩
  have hvS : v ∈ S := by
    rw [hSdef, Metric.mem_closedBall, dist_zero_right]; exact hv.le
  have hvU : v ∈ U := hSU hvS
  refine ⟨isUnit_iff_ne_zero.2 (hSdet v hvS), fun i k => ?_, ?_, fun i k => ?_, fun i k => ?_,
    fun a i k => ?_, fun a b i k => ?_⟩
  · exact ((holo_contDiffOn hU (hP i k)).contDiffAt (hU.mem_nhds hvU)).restrict_scalars ℝ
  · filter_upwards [hU.mem_nhds hvU] with u hu η
    ext i k
    simp [GlobalTheory.dbar_eq_zero ((hP i k).differentiableAt (hU.mem_nhds hu))]
  · have h := (norm_le_pi_norm (G1 v i) k).trans ((norm_le_pi_norm (G1 v) i).trans (hC1 v hvS))
    exact h.trans ((le_max_left _ _).trans (le_max_left _ _))
  · have h := (norm_le_pi_norm (G2 v i) k).trans ((norm_le_pi_norm (G2 v) i).trans (hC2 v hvS))
    exact h.trans ((le_max_right _ _).trans (le_max_left _ _))
  · have h := (norm_le_pi_norm (G3 v a i) k).trans ((norm_le_pi_norm (G3 v a) i).trans
      ((norm_le_pi_norm (G3 v) a).trans (hC3 v hvS)))
    exact h.trans ((le_max_left _ _).trans (le_max_right _ _))
  · have h := (norm_le_pi_norm (G4 v a b i) k).trans ((norm_le_pi_norm (G4 v a b) i).trans
      ((norm_le_pi_norm (G4 v a) b).trans ((norm_le_pi_norm (G4 v) a).trans (hC4 v hvS))))
    exact h.trans ((le_max_right _ _).trans (le_max_right _ _))

end GlobalTheory.HermFrame
end
