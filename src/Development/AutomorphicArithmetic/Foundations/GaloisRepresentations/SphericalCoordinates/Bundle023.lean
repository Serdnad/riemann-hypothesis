module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle009
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.Bundle002
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsFinsetSpanOfIntegralMultiples
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedComplexFibreMarkedLatticeClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.IsCoordA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PerCApply

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.HermitianFrame

variable {F K : Type} [Field F] [Field K] {n : ℕ}

private theorem map_mulVec' (τ : F →+* K) (M : Matrix (Fin n) (Fin n) F) (v : Fin n → F) :
    (fun i => τ ((M *ᵥ v) i)) = M.map τ *ᵥ (fun i => τ (v i)) :=
  funext (τ.map_mulVec M v)

private theorem transpose_conj {R M S : Matrix (Fin n) (Fin n) K} (hS : S.det ≠ 0) (h : R * S = S * M) :
    Rᵀ * (S⁻¹)ᵀ = (S⁻¹)ᵀ * Mᵀ := by
  have hu : IsUnit S.det := isUnit_iff_ne_zero.mpr hS
  have h1 : S⁻¹ * R = M * S⁻¹ := by
    calc S⁻¹ * R = S⁻¹ * R * (S * S⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = S⁻¹ * (R * S) * S⁻¹ := by simp only [Matrix.mul_assoc]
      _ = S⁻¹ * (S * M) * S⁻¹ := by rw [h]
      _ = M * S⁻¹ := by rw [← Matrix.mul_assoc S⁻¹ S M, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, h1]

private theorem pair_eval (τ : F →+* K) (j : F →+* F) (S B : Matrix (Fin n) (Fin n) K) (Q : Matrix (Fin n) (Fin n) F)
    (h : Bᵀ * S = Q.map τ) (y z : Fin n → F) :
    (B *ᵥ (fun i => τ (j (y i)))) ⬝ᵥ (S *ᵥ (fun i => τ (z i))) = τ ((fun i => j (y i)) ⬝ᵥ (Q *ᵥ z)) := by
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h, ← map_mulVec']
  exact (τ.map_dotProduct (fun i => j (y i)) (Q *ᵥ z)).symm

private theorem conj_form (j : F →+* F) (hj : ∀ x, j (j x) = x) (Q : Matrix (Fin n) (Fin n) F) (hQ : (Q.map j)ᵀ = -Q)
    (y z : Fin n → F) :
    j ((fun i => j (y i)) ⬝ᵥ (Q *ᵥ z)) = -((fun i => j (z i)) ⬝ᵥ (Q *ᵥ y)) := by
  have hQ' : ∀ i k, j (Q i k) = - Q k i := fun i k => by
    have := congrFun (congrFun hQ k) i
    simpa using this

  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hj, hQ', Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end UpperTheory.Gal.W2.HermitianFrame

open UpperTheory.Gal.W2.HermitianFrame in
theorem UpperTheory.Gal.W2.pFrameEx_of :
    UpperTheory.Gal.W2.FMat → UpperTheory.Gal.W2.FForm → UpperTheory.Gal.W2.SN → UpperTheory.Gal.W2.FTrace → UpperTheory.Gal.W2.FInt → UpperTheory.Gal.W2.FApprox → UpperTheory.Gal.W2.PFrameEx := by
  intro hMat hForm hSN hTr hInt hApp p _ D G L hm β hβ
  obtain ⟨kp, σ, hkp⟩ := hMat p D G L hm
  obtain ⟨A, hAdet, hAc, hAf, hAsh⟩ := hForm p D G L kp σ hkp
  have hS : ∀ w : Fin G.m, ∃ S : Matrix (Fin G.n) (Fin G.n) (G.Fw w), S.det ≠ 0 ∧
      ∀ c : G.C, G.rho w c * S = S * (σ c).map (G.embW w) := by
    intro w
    obtain ⟨S, hS0, hS1⟩ := hSN G.F (G.Fw w) G.n (G.embW w)
      ((G.rho w).comp σ.symm.toAlgHom.toRingHom) (by
        intro x
        have hx : Matrix.scalar (Fin G.n) x = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) G.F) x := by
          ext i k
          simp [Matrix.scalar_apply, Matrix.algebraMap_matrix_apply, Matrix.diagonal_apply]
        have hσ : σ.symm (algebraMap G.F (Matrix (Fin G.n) (Fin G.n) G.F) x) = algebraMap G.F G.C x :=
          σ.symm.commutes x
        rw [hx]
        exact (congrArg (G.rho w) hσ).trans (G.rho_F w x))
    exact ⟨S, hS0, fun c => by simpa using hS1 (σ c)⟩
  choose S hSdet hSrho using hS
  have hsh : ∀ x y : G.C, sh G (x * y) = sh G y * sh G x := by
    intro x y
    simp [sh, map_mul]
  have hβi : sh G ↑β⁻¹ = ↑β⁻¹ := by
    have h1 : sh G ↑β⁻¹ * ↑β = 1 := by
      rw [← hβ, ← hsh, Units.mul_inv, sh_one_eq]
    calc sh G ↑β⁻¹ = sh G ↑β⁻¹ * (↑β * ↑β⁻¹) := by simp
      _ = ↑β⁻¹ := by rw [← _root_.mul_assoc, h1, _root_.one_mul]
  have hAsh' : ∀ c, Aᵀ * (σ c).map (IsCMField.complexConj G.F) = (σ (sh G c))ᵀ * Aᵀ := by
    intro c
    have := congrArg Matrix.transpose (hAsh c)
    simpa [Matrix.transpose_mul] using this.symm
  have K1 : ∀ w c, (G.rho w c)ᵀ * ((S w)⁻¹)ᵀ = ((S w)⁻¹)ᵀ * ((σ c).map (G.embW w))ᵀ :=
    fun w c => transpose_conj (hSdet w) (hSrho w c)
  have hrinv : ∀ w, (G.rho w ↑β)ᵀ * (G.rho w ↑β⁻¹)ᵀ = 1 := by
    intro w
    rw [← Matrix.transpose_mul, ← map_mul, Units.inv_mul, map_one, Matrix.transpose_one]
  set B : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    fun w => (G.rho w ↑β⁻¹)ᵀ * ((S w)⁻¹)ᵀ * (A.map (G.embW w))ᵀ with hB
  have K2 : ∀ w c, B w * ((σ c).map (IsCMField.complexConj G.F)).map (G.embW w)
      = (G.rho w (↑β * sh G c * ↑β⁻¹))ᵀ * B w := by
    intro w c
    have e1 : (A.map (G.embW w))ᵀ * ((σ c).map (IsCMField.complexConj G.F)).map (G.embW w)
        = ((σ (sh G c)).map (G.embW w))ᵀ * (A.map (G.embW w))ᵀ := by
      rw [← Matrix.transpose_map, ← Matrix.map_mul, hAsh', Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map]
    simp only [hB, map_mul, Matrix.transpose_mul]
    calc (G.rho w ↑β⁻¹)ᵀ * ((S w)⁻¹)ᵀ * (A.map (G.embW w))ᵀ * ((σ c).map (IsCMField.complexConj G.F)).map (G.embW w)
        = (G.rho w ↑β⁻¹)ᵀ * (((S w)⁻¹)ᵀ * ((σ (sh G c)).map (G.embW w))ᵀ) * (A.map (G.embW w))ᵀ := by
          rw [Matrix.mul_assoc _ _ (Matrix.map _ _), e1]; simp only [Matrix.mul_assoc]
      _ = (G.rho w ↑β⁻¹)ᵀ * (G.rho w (sh G c))ᵀ * ((G.rho w ↑β)ᵀ * (G.rho w ↑β⁻¹)ᵀ) * ((S w)⁻¹)ᵀ * (A.map (G.embW w))ᵀ := by
          rw [← K1, hrinv]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hkp' : ∀ c v, kp (L.rep c v) = σ c *ᵥ kp v := hkp
  let j : G.F →+* G.F := (IsCMField.complexConj G.F).toRingEquiv.toRingHom
  have hcm : ∀ w (M : Matrix (Fin G.n) (Fin G.n) G.F) (v : Fin G.n → G.F),
      (fun i => G.embW w (IsCMField.complexConj G.F ((M *ᵥ v) i)))
        = (M.map (IsCMField.complexConj G.F)).map (G.embW w) *ᵥ (fun i => G.embW w (IsCMField.complexConj G.F (v i))) := by
    intro w M v
    rw [Matrix.map_map]
    exact map_mulVec' ((G.embW w).comp j) M v
  have hc1 : ∀ (M : Matrix (Fin G.n) (Fin G.n) G.F) (v : Fin G.n → G.F),
      (fun i => IsCMField.complexConj G.F ((M *ᵥ v) i))
        = M.map (IsCMField.complexConj G.F) *ᵥ (fun i => IsCMField.complexConj G.F (v i)) :=
    map_mulVec' j
  have hdetS : ∀ w, ((S w)⁻¹).det ≠ 0 := by
    intro w
    have : ((S w)⁻¹).det * (S w).det = 1 := by
      rw [← Matrix.det_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hSdet w)), Matrix.det_one]
    exact left_ne_zero_of_mul_eq_one this
  have hBdet : ∀ w, (B w).det ≠ 0 := by
    intro w
    have h1 : (G.rho w ↑β⁻¹).det * (G.rho w ↑β).det = 1 := by
      rw [← Matrix.det_mul, ← map_mul, Units.inv_mul, map_one, Matrix.det_one]
    have h3 : (A.map (G.embW w)).det ≠ 0 := by
      have := (RingHom.map_det (G.embW w) A).symm
      rw [RingHom.mapMatrix_apply] at this
      rw [this]
      exact (_root_.map_ne_zero _).mpr hAdet
    simp only [hB, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero (left_ne_zero_of_mul_eq_one h1) (hdetS w)) h3
  have hBS : ∀ w, (B w)ᵀ * S w = (A * σ ↑β⁻¹).map (G.embW w) := by
    intro w
    simp only [hB, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hSrho, ← Matrix.mul_assoc (S w)⁻¹,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hSdet w)), Matrix.one_mul, Matrix.map_mul]
  have hsw : ∀ v z : Fin G.n → G.F,
      (fun i => IsCMField.complexConj G.F ((σ ↑β⁻¹ *ᵥ v) i)) ⬝ᵥ (A *ᵥ z)
        = (fun i => IsCMField.complexConj G.F (v i)) ⬝ᵥ ((A * σ ↑β⁻¹) *ᵥ z) := by
    intro v z
    rw [hc1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← hAsh, hβi]
  have hjj : ∀ x, j (j x) = x := fun x => by simp [j]
  have hjA : (A.map j)ᵀ = -A := hAc
  let T : VQ D →+ Loc G := AddMonoidHom.mk' (fun x w => S w *ᵥ (fun i => G.embW w (kp x i))) (by
    intro x y
    funext w
    rw [show (fun i => G.embW w (kp (x + y) i)) = (fun i => G.embW w (kp x i)) + (fun i => G.embW w (kp y i)) from by
      funext i; simp, Matrix.mulVec_add]
    rfl)
  let T' : VQ D →+ Loc G := AddMonoidHom.mk'
    (fun x w => B w *ᵥ (fun i => G.embW w (IsCMField.complexConj G.F (kp x i)))) (by
    intro x y
    funext w
    rw [show (fun i => G.embW w (IsCMField.complexConj G.F (kp (x + y) i)))
        = (fun i => G.embW w (IsCMField.complexConj G.F (kp x i)))
          + (fun i => G.embW w (IsCMField.complexConj G.F (kp y i))) from by
      funext i; simp, Matrix.mulVec_add]
    rfl)
  have hT : ∀ x w, T x w = S w *ᵥ (fun i => G.embW w (kp x i)) := fun _ _ => rfl
  have hT' : ∀ x w, T' x w = B w *ᵥ (fun i => G.embW w (IsCMField.complexConj G.F (kp x i))) := fun _ _ => rfl
  refine ⟨⟨T, T', ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro c x w
    rw [hT, hT, hkp', map_mulVec', Matrix.mulVec_mulVec, ← hSrho, ← Matrix.mulVec_mulVec]
  · intro c x w
    rw [hT', hT', hkp', hcm, Matrix.mulVec_mulVec, K2, ← Matrix.mulVec_mulVec]
  · intro u x
    have e0 : formB L β u x = Algebra.trace ℚ G.F
        ((fun i => IsCMField.complexConj G.F (kp x i)) ⬝ᵥ ((A * σ ↑β⁻¹) *ᵥ kp u)) := by
      unfold formB
      rw [hAf, hkp', Matrix.mulVec_mulVec]
    have hpe : ∀ w (y z : Fin G.n → G.F),
        (B w *ᵥ fun i => G.embW w (IsCMField.complexConj G.F (y i))) ⬝ᵥ (S w *ᵥ fun i => G.embW w (z i))
          = G.embW w ((fun i => IsCMField.complexConj G.F (y i)) ⬝ᵥ ((A * σ ↑β⁻¹) *ᵥ z)) :=
      fun w y z => pair_eval (G.embW w) j (S w) (B w) _ (hBS w) y z
    have hneg : IsCMField.complexConj G.F
          ((fun i => IsCMField.complexConj G.F (kp x i)) ⬝ᵥ ((A * σ ↑β⁻¹) *ᵥ kp u))
        = -((fun i => IsCMField.complexConj G.F (kp u i)) ⬝ᵥ ((A * σ ↑β⁻¹) *ᵥ kp x)) := by
      rw [← Matrix.mulVec_mulVec]
      have h4 := conj_form j hjj A hjA (kp x) (σ ↑β⁻¹ *ᵥ kp u)
      have h5 := hsw (kp u) (kp x)
      exact h4.trans (congrArg Neg.neg h5)
    rw [e0, hTr]
    unfold pairL
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [hT', hT, hpe]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [hT', hT, hpe, hneg, map_neg, map_neg]
  · intro a b k
    obtain ⟨y, a', b', ha', hb', h1, h2⟩ := exists_global_approx_of_local_mod_p_pow_conj hApp p G S B hSdet hBdet a b k
    refine ⟨kp.symm y, a', b', ha', hb', ?_, ?_⟩
    · funext w
      rw [hT]
      simp only [AddEquiv.apply_symm_apply]
      rw [h1 w]
      rfl
    · funext w
      rw [hT']
      simp only [AddEquiv.apply_symm_apply]
      rw [h2 w]
      rfl
  · obtain ⟨k, hk⟩ := exists_bounded_denominator_of_local_integrality_conj hInt p G S B hSdet hBdet
    obtain ⟨s, hs, hs'⟩ := exists_finset_span_of_integral_multiples G.F (VQ D) G.n kp
    refine ⟨s, k, hs, fun x h1 h2 => ?_⟩
    obtain ⟨m, c, hm', hc⟩ := hk (kp x) h1 h2
    exact ⟨m, hm', hs' x (m * p ^ k) c hc⟩
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

theorem tateWit_of : TateWit := by
  intro p _ D gb N S s o hX hL ρ D' t P x e hN hNp hU I hI
  classical
  obtain ⟨-, hper, hexp, hker, hact, hweil, heta⟩ := hU
  have hadd : ∀ z w, e (z + w) = e z * e w := hexp.1
  have hsurj : Function.Surjective e := hexp.2.1
  have hlin : ∀ (c : D.O) u, P (c • u) = ρ c *ᵥ P u := hper.1
  have hinj : Function.Injective P := hper.2.1
  haveI : Module.Free ℤ D.toG.La := D.freeLa
  have hlift : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ φ : D.La →+ D'.La, ∀ a, I.ev n a = e ((n : ℂ)⁻¹ • P (φ a)) :=
    fun n hn hnp => unifCls_lift e P hadd hsurj hker (I.ev n) (I.add n) hn
      (fun y => (I.onto n hn _).2 ⟨y, rfl⟩)
  have hroot : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ v : ℤ, IsCoprime v n ∧
      ((I.ζ n : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (v : ℂ) / n) :=
    fun n hn hnp => unifCls_root hn _ (I.ζ_prim n hn)
  let f : ℕ → D.La →+ D'.La := fun n => if hn : 0 < n ∧ n.Coprime p then Classical.choose (hlift n hn.1 hn.2) else 0
  let nu : ℕ → ℤ := fun n => if hn : 0 < n ∧ n.Coprime p then Classical.choose (hroot n hn.1 hn.2) else 0
  have hf : ∀ (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) a, I.ev n a = e ((n : ℂ)⁻¹ • P (f n a)) := by
    intro n hn hnp a
    simp only [f, dif_pos (And.intro hn hnp)]
    exact Classical.choose_spec (hlift n hn hnp) a
  have hnu : ∀ (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p), IsCoprime (nu n) n ∧
      ((I.ζ n : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (nu n : ℂ) / n) := by
    intro n hn hnp
    simp only [nu, dif_pos (And.intro hn hnp)]
    exact Classical.choose_spec (hroot n hn hnp)
  have heq : ∀ {n : ℕ}, 0 < n → ∀ v v' : D'.La,
      e ((n : ℂ)⁻¹ • P v) = e ((n : ℂ)⁻¹ • P v') ↔ ∃ w, v = v' + n • w :=
    fun hn v v' => unifCls_eq_iff e P hadd hker hinj hn v v'
  refine ⟨f, nu, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro n m hn hm hnm
    have hnp : n.Coprime p := (Nat.coprime_mul_iff_left.1 hnm).1
    refine ⟨?_, fun a => ?_⟩
    · have hz := I.ζ_pow n m hn hm
      have hz' := congrArg (fun u : ℂˣ => (u : ℂ)) hz
      simp only [Units.val_pow_eq_pow_val] at hz'
      rw [(hnu _ (Nat.mul_pos hn hm) hnm).2, (hnu n hn hnp).2, ← Complex.exp_nat_mul] at hz'
      have : (m : ℂ) * (-(2 * Real.pi * Complex.I) * (nu (n * m) : ℂ) / ((n * m : ℕ) : ℂ)) =
          -(2 * Real.pi * Complex.I) * (nu (n * m) : ℂ) / n := by
        have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
        have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
        push_cast; field_simp
      rw [this] at hz'
      exact (unifCls_exp_eq_iff hn _ _).1 hz'
    · have ht := I.tower n m hn hm a
      have e1 := hf _ (Nat.mul_pos hn hm) hnm a
      have e2 := hf n hn hnp a
      rw [e1, e2] at ht
      erw [unifCls_tower e P hadd hn hm] at ht
      exact (heq hn _ _).1 ht
  · intro n hn hnp
    refine ⟨(hnu n hn hnp).1, fun c a => ?_, fun a => ?_, fun a' => ?_, fun a a' => ?_⟩
    · have hl := I.lin n c a
      erw [hf n hn hnp (c • a), hf n hn hnp a] at hl
      have h3 := hact c ((n : ℂ)⁻¹ • P (f n a))
      rw [Matrix.mulVec_smul] at h3
      have h4 := hlin c (f n a)
      have h5 : e ((n : ℂ)⁻¹ • P (c • f n a)) = e ((n : ℂ)⁻¹ • P (f n a)) ≫ o.act.act c := by
        rw [h4]; exact h3
      exact (heq hn _ _).1 (hl.trans h5.symm)
    · have h1 := I.ker n hn a
      erw [hf n hn hnp a, unifCls_unit_iff e P hker hinj hn] at h1
      exact h1
    · obtain ⟨y, hy⟩ := (I.onto n hn (e ((n : ℂ)⁻¹ • P a'))).1 (unifCls_pow e P hadd hker hn a')
      rw [hf n hn hnp y] at hy
      obtain ⟨w, hw⟩ := (heq hn _ _).1 hy.symm
      exact ⟨y, w, hw⟩
    · have hiso := I.isom n hn a a'
      rw [hf n hn hnp a, hf n hn hnp a'] at hiso
      have hw := hweil n (f n a) (f n a')
        (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF (f n a) (f n a') : ℂ) / n)) (Complex.exp_ne_zero _))
        hn rfl
      have hu := GlobalTheory.T.weilPairing_complex_value_unique S o.A D.g o.ab hX _ hL x n _ _ _ _ hiso hw
      have hu' := congrArg (fun u : ℂˣ => (u : ℂ)) hu
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hu'
      rw [(hnu n hn hnp).2, ← Complex.exp_int_mul] at hu'
      have : ((2 * D.toG.EF a a' : ℤ) : ℂ) * (-(2 * Real.pi * Complex.I) * (nu n : ℂ) / n) =
          -(2 * Real.pi * Complex.I) * ((nu n * (2 * D.toG.EF a a') : ℤ) : ℂ) / n := by
        push_cast; ring
      rw [this] at hu'
      exact (unifCls_exp_eq_iff hn _ _).1 hu'.symm
  · intro a
    have h3 : I.ev N a = e ((N : ℂ)⁻¹ • P (t a)) := (hI a).symm.trans (heta a)
    rw [hf N hN hNp a] at h3
    obtain ⟨w, hw⟩ := (heq hN _ _).1 h3
    exact ⟨w, hw⟩
  · intro n hn hnp a
    exact hf n hn hnp a

end UpperTheory.Gal.W2
end
end

section

noncomputable section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Wit

variable {p : ℕ} [Fact p.Prime]

theorem actQ_tmul {D : Datum p} (b : D.O) (q : ℚ) (x : D.La) : actQ D b (q ⊗ₜ x) = q ⊗ₜ (b • x) := by
  simp only [actQ, LinearMap.baseChange_tmul]; rfl

theorem actQ_one (D : Datum p) (w : VQ D) : actQ D 1 w = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul q x => rw [actQ_tmul, one_smul]
  | add u v hu hv => rw [map_add (f := _), hu, hv]

theorem actQ_mul (D : Datum p) (a b : D.O) (w : VQ D) : actQ D (a * b) w = actQ D a (actQ D b w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul q x => rw [actQ_tmul, actQ_tmul, actQ_tmul, mul_smul]
  | add u v hu hv => rw [map_add (f := _), hu, hv, map_add (f := _), map_add (f := _)]

theorem actQ_add (D : Datum p) (a b : D.O) (w : VQ D) : actQ D (a + b) w = actQ D a w + actQ D b w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul q x => rw [actQ_tmul, actQ_tmul, actQ_tmul, add_smul, TensorProduct.tmul_add]
  | add u v hu hv => rw [map_add (f := _), hu, hv, map_add (f := _), map_add (f := _)]; abel

theorem actQ_zero (D : Datum p) (w : VQ D) : actQ D 0 w = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul q x => rw [actQ_tmul, zero_smul, TensorProduct.tmul_zero]
  | add u v hu hv => rw [map_add (f := _), hu, hv, add_zero]

structure Sys (D : Datum p) where
  T : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)
  S : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)
  ST : S * T = 1
  comm : ∀ c : D.O, T * (actQ D c).baseChange (AfP p) = (actQ D c).baseChange (AfP p) * T
  B : LinearMap.BilinForm ℚ (VQ D)
  alt : ∀ u, B u u = 0
  nondeg : ∀ u, (∀ w, B u w = 0) → u = 0
  adj : ∀ (c : D.O) u w, B (actQ D c u) w = B u (actQ D (D.inv c) w)
  M : AddSubgroup (VQ D)
  hM : UpperTheory.Gal.W2.IsPLat D M
  s : ℚ
  s_pos : 0 < s
  perf : ∀ w, w ∈ M ↔ ∀ u ∈ M, (s * B w u).den.Coprime p
  ε : (AfP p)ˣ
  ε_int : IsIntAf (ε : AfP p)
  ε_inv : IsIntAf ((ε⁻¹ : (AfP p)ˣ) : AfP p)
  form : ∀ u w, algebraMap ℚ (AfP p) (s * B u w) =
    (ε : AfP p) * (D.EF.baseChange ℚ).baseChange (AfP p) (T ((1 : AfP p) ⊗ₜ u)) (T ((1 : AfP p) ⊗ₜ w))
  dense : ∀ n : ℕ, 0 < n → ∀ z, ∃ w, ∃ e ∈ LaHat D, z = T ((1 : AfP p) ⊗ₜ w) + n • e

namespace Sys

variable {D : Datum p} (X : Sys D)

def r : VQ D →ₗ[ℚ] AfP p ⊗[ℚ] VQ D :=
  (X.T.restrictScalars ℚ) ∘ₗ (TensorProduct.mk ℚ (AfP p) (VQ D) 1)

theorem r_apply (w : VQ D) : X.r w = X.T ((1 : AfP p) ⊗ₜ w) := rfl

theorem r_act (c : D.O) (w : VQ D) : X.r (actQ D c w) = (actQ D c).baseChange (AfP p) (X.r w) := by
  rw [r_apply, r_apply]
  have h := LinearMap.congr_fun (X.comm c) ((1 : AfP p) ⊗ₜ w)
  rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.baseChange_tmul] at h
  exact h

def lat : AddSubgroup (VQ D) where
  carrier := {w | w ∈ X.M ∧ X.r w ∈ LaHat D}
  zero_mem' := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  add_mem' := fun h h' => ⟨add_mem h.1 h'.1, by rw [map_add]; exact add_mem h.2 h'.2⟩
  neg_mem' := fun h => ⟨neg_mem h.1, by rw [map_neg]; exact neg_mem h.2⟩

theorem mem_lat {w : VQ D} : w ∈ X.lat ↔ w ∈ X.M ∧ X.r w ∈ LaHat D := Iff.rfl

theorem act_mem (c : D.O) {w : VQ D} (hw : w ∈ X.lat) : actQ D c w ∈ X.lat :=
  ⟨X.hM.1 c w hw.1, by rw [r_act]; exact GlobalTheory.AdelicSim.bc_mem D c hw.2⟩

instance : Module D.O X.lat where
  smul c w := ⟨actQ D c w.1, X.act_mem c w.2⟩
  one_smul w := Subtype.ext (actQ_one D w.1)
  mul_smul a b w := Subtype.ext (actQ_mul D a b w.1)
  smul_zero c := Subtype.ext (map_zero (actQ D c))
  smul_add c u v := Subtype.ext (map_add (actQ D c) u.1 v.1)
  add_smul a b w := Subtype.ext (actQ_add D a b w.1)
  zero_smul w := Subtype.ext (actQ_zero D w.1)

theorem coe_smul (c : D.O) (w : X.lat) : ((c • w : X.lat) : VQ D) = actQ D c w := rfl

end Sys

end UpperTheory.Gal.W2.Wit
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.regSep_of :
    UpperTheory.Gal.W2.RegSep := by
  intro p _ D G L v hv B a y hfix hreg
  exact GlobalTheory.LKCx.minpoly_of_regAf_of_fixL p G v hv B.β B.sym B.trivR _ _
    B.trivAf.choose_spec.choose_spec y a.1.1 a.2 hfix hreg
end
