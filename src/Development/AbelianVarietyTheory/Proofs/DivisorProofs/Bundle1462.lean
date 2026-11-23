module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentralCircleOneParameterUnitaryRealPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

@[expose] public section

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.CCRFock

open MvPolynomial

def polMapD (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) :
    (⨂[ℂ] w : W, MvPolynomial (Λ w) ℂ) →ₗ[ℂ] MvPolynomial (Σ w, Λ w) ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ W (MvPolynomial (Σ w, Λ w) ℂ)).compLinearMap
    fun w => (MvPolynomial.rename (Sigma.mk w)).toLinearMap)

theorem polMapD_tprod (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) (q : ∀ w, MvPolynomial (Λ w) ℂ) :
    polMapD W Λ (PiTensorProduct.tprod ℂ q) = ∏ v, MvPolynomial.rename (Sigma.mk v) (q v) := by
  simp [polMapD]

theorem polMapD_index_injective (W : Type) [Fintype W] (Λ : W → Type) :
    Function.Injective (fun f : ∀ w, (Λ w →₀ ℕ) => ∑ w, Finsupp.mapDomain (Sigma.mk w) (f w)) := by
  have key : ∀ (f : ∀ w, (Λ w →₀ ℕ)) (w : W) (l : Λ w),
      (∑ w, Finsupp.mapDomain (Sigma.mk w) (f w)) ⟨w, l⟩ = f w l := by
    intro f w l
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single w]
    · exact Finsupp.mapDomain_apply_of_injective sigma_mk_injective _ _
    · intro v _ hv
      apply Finsupp.mapDomain_notin_range
      rintro ⟨x, hx⟩
      exact hv (congrArg Sigma.fst hx)
    · intro h
      exact absurd (Finset.mem_univ w) h
  intro f g h
  funext w
  ext l
  rw [← key f w l, ← key g w l]
  exact congrArg (fun F : (Σ w, Λ w) →₀ ℕ => F ⟨w, l⟩) h

theorem polMapD_tprod_monomial (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) (f : ∀ w, (Λ w →₀ ℕ)) :
    polMapD W Λ (PiTensorProduct.tprod ℂ (fun w => (monomial (f w) (1 : ℂ) : MvPolynomial (Λ w) ℂ))) =
      monomial (∑ w, Finsupp.mapDomain (Sigma.mk w) (f w)) 1 := by
  rw [monomial_sum_one]
  simp only [polMapD, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, rename_monomial]

theorem polMapD_injective (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) :
    Function.Injective (polMapD W Λ) := by
  let B := Basis.piTensorProduct (fun w : W => basisMonomials (Λ w) ℂ)
  have hli : LinearIndependent ℂ (polMapD W Λ ∘ B) := by
    have h := (basisMonomials (Σ w, Λ w) ℂ).linearIndependent.comp _ (polMapD_index_injective W Λ)
    have e : polMapD W Λ ∘ B = (basisMonomials (Σ w, Λ w) ℂ) ∘
        (fun f : ∀ w, (Λ w →₀ ℕ) => ∑ w, Finsupp.mapDomain (Sigma.mk w) (f w)) := by
      funext f
      simp only [Function.comp, B, Basis.piTensorProduct_apply, coe_basisMonomials]
      exact polMapD_tprod_monomial W Λ f
    rw [e]
    exact h
  have h1 : polMapD W Λ ∘ₗ Finsupp.linearCombination ℂ B =
      Finsupp.linearCombination ℂ (polMapD W Λ ∘ B) := by
    ext f
    simp
  intro x y hxy
  apply B.repr.injective
  apply hli
  rw [← h1]
  simp only [LinearMap.comp_apply, Module.Basis.linearCombination_repr, hxy]

theorem atPl_tprod_dep {W : Type} [Fintype W] [DecidableEq W] {Λ : W → Type} (w : W)
    (L : Module.End ℂ (MvPolynomial (Λ w) ℂ)) (p : ∀ v, MvPolynomial (Λ v) ℂ) :
    atPl (V := fun w => MvPolynomial (Λ w) ℂ) w L (PiTensorProduct.tprod ℂ p) =
      PiTensorProduct.tprod ℂ (Function.update p w (L (p w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext v
  by_cases hv : v = w
  · subst hv; simp
  · simp [Function.update_of_ne hv]

theorem polMapD_atPl_mulLeft_X (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) (w : W) (l : Λ w) :
    polMapD W Λ ∘ₗ atPl (V := fun w => MvPolynomial (Λ w) ℂ) w (LinearMap.mulLeft ℂ (MvPolynomial.X l)) =
      LinearMap.mulLeft ℂ (MvPolynomial.X ⟨w, l⟩) ∘ₗ polMapD W Λ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro p
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, atPl_tprod_dep, polMapD_tprod,
    LinearMap.mulLeft_apply]
  rw [Fintype.prod_eq_mul_prod_compl w, Fintype.prod_eq_mul_prod_compl w
    (fun v => MvPolynomial.rename (Sigma.mk v) (p v)), ← mul_assoc]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hv' : v ≠ w := by simpa using hv
    rw [Function.update_of_ne hv']

theorem pderiv_rename_sigmaMk_of_ne {W : Type} {Λ : W → Type} {v w : W} (h : v ≠ w) (l : Λ w)
    (r : MvPolynomial (Λ v) ℂ) :
    MvPolynomial.pderiv (⟨w, l⟩ : Σ w, Λ w) (MvPolynomial.rename (Sigma.mk v) r) = 0 := by
  induction r using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.rename_X, Derivation.leibniz, hp, MvPolynomial.pderiv_X_of_ne]
    · simp
    · intro e; exact h (congrArg Sigma.fst e)

theorem pderiv_prod_rename_sigma_of_notMem {W : Type} {Λ : W → Type} {w : W} (l : Λ w)
    (q : ∀ v, MvPolynomial (Λ v) ℂ) (s : Finset W) (hs : w ∉ s) :
    MvPolynomial.pderiv (⟨w, l⟩ : Σ w, Λ w) (∏ v ∈ s, MvPolynomial.rename (Sigma.mk v) (q v)) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.mem_insert, not_or] at hs
    rw [Finset.prod_insert ha, Derivation.leibniz, ih hs.2,
      pderiv_rename_sigmaMk_of_ne (fun e => hs.1 e.symm)]
    simp

theorem polMapD_atPl_pderiv (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) (w : W) (l : Λ w) :
    polMapD W Λ ∘ₗ atPl (V := fun w => MvPolynomial (Λ w) ℂ) w (MvPolynomial.pderiv l).toLinearMap =
      (MvPolynomial.pderiv (⟨w, l⟩ : Σ w, Λ w)).toLinearMap ∘ₗ polMapD W Λ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro q
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, atPl_tprod_dep, polMapD_tprod]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
  have h1 : ∏ i ∈ Finset.univ.erase w, MvPolynomial.rename (Sigma.mk i)
      (Function.update q w ((MvPolynomial.pderiv l).toLinearMap (q w)) i) =
      ∏ i ∈ Finset.univ.erase w, MvPolynomial.rename (Sigma.mk i) (q i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [h1, Function.update_self, Derivation.coeFn_coe, Derivation.coeFn_coe, Derivation.leibniz,
    pderiv_prod_rename_sigma_of_notMem l q _ (Finset.notMem_erase w _),
    MvPolynomial.pderiv_rename sigma_mk_injective l (q w)]
  simp [mul_comm]

theorem exists_polMapD : ∀ (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type),
    ∃ θ : (⨂[ℂ] w : W, MvPolynomial (Λ w) ℂ) →ₗ[ℂ] MvPolynomial (Σ w, Λ w) ℂ, Function.Injective θ ∧
      ∀ (w : W) (l : Λ w) (T : ⨂[ℂ] w : W, MvPolynomial (Λ w) ℂ),
        θ (atPl (V := fun w => MvPolynomial (Λ w) ℂ) w (LinearMap.mulLeft ℂ (MvPolynomial.X l)) T) =
            MvPolynomial.X ⟨w, l⟩ * θ T ∧
          θ (atPl (V := fun w => MvPolynomial (Λ w) ℂ) w (MvPolynomial.pderiv l).toLinearMap T) =
            MvPolynomial.pderiv ⟨w, l⟩ (θ T) := by
  intro W _ _ Λ
  refine ⟨polMapD W Λ, polMapD_injective W Λ, fun w l T => ⟨?_, ?_⟩⟩
  · exact LinearMap.congr_fun (polMapD_atPl_mulLeft_X W Λ w l) T
  · exact LinearMap.congr_fun (polMapD_atPl_pderiv W Λ w l) T

end GlobalTheory.CCRFock

end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl


theorem _root_.GlobalTheory.T.fockHeisenbergOperatorOfCoords_real_I_smul_signConj_one : ∀ (P Q R S : ℕ) (c : Matrix (Ix P Q) (Ix R S) ℂ) (t : ℝ),
    heisOp (((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) 1 = ((t : ℂ) * Complex.I) • heisOp c 1 := by
  first | exact @GlobalTheory.HeisRot.heisOp_rot_one | exact GlobalTheory.HeisRot.heisOp_rot_one | (intros; apply GlobalTheory.HeisRot.heisOp_rot_one <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.archActionReadings_compatible : GlobalTheory.RealLift.ActsLaws := by
  first | exact @GlobalTheory.RealLift.actsLaws | exact GlobalTheory.RealLift.actsLaws | (intros; apply GlobalTheory.RealLift.actsLaws <;> assumption)
end

section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.fockHeisenbergOperator_I_signatureConj_apply_one : ∀ {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ), heisOp (Complex.I • (Jm P Q * c * Jm R S)) 1 = Complex.I • heisOp c 1 := by
  first | exact @GlobalTheory.RealLift.heisOp_twist_one | exact GlobalTheory.RealLift.heisOp_twist_one | (intros; apply GlobalTheory.RealLift.heisOp_twist_one <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD.FrameCartan

open Matrix GlobalTheory.RealLift.HermitianFrameExistence
open scoped ComplexOrder

theorem frame_of_cartan : ∀ (n : ℕ) (M θ : Matrix (Fin n) (Fin n) ℂ), (∀ i j, star (M j i) = M i j) → M.det ≠ 0 →
    IsCartan M θ → ∃ (r s : ℕ) (A : Matrix (Fin n) (Ix r s) ℂ), IsFrame M A ∧ θ * A = A * Jm r s := by
  intro n M θ hM _ hC
  obtain ⟨hθθ, hiso, hpos⟩ := hC
  set G : Matrix (Fin n) (Fin n) ℂ := M.map star with hGdef
  have hJ : ∀ p q : ℕ, (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map star =
      fromBlocks 1 0 0 (-1) := by
    intro p q; ext (i | i) (j | j) <;> simp [Matrix.one_apply, apply_ite]
  have Gherm : Gᴴ = G := by
    ext i j
    simp only [hGdef, conjTranspose_apply, map_apply, star_star]
    rw [← hM i j, star_star]
  have hiso' : θᴴ * G * θ = G := by rw [← map_star_trip, hiso]
  have hcomm : θᴴ * G = G * θ := by
    calc θᴴ * G = θᴴ * G * θ * θ := by rw [Matrix.mul_assoc (θᴴ * G), hθθ, Matrix.mul_one]
      _ = G * θ := by rw [hiso']
  have hherm : (G * θ).IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_mul, Gherm, hcomm]
  have hPD : (G * θ).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hherm, fun x hx => ?_⟩
    have hval : star x ⬝ᵥ (G * θ) *ᵥ x = star ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x) := by
      rw [← hcomm, star_form, ← hGdef, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
    refine Complex.pos_iff.2 ⟨?_, (hherm.im_star_dotProduct_mulVec_self x).symm⟩
    rw [hval, Complex.star_def, Complex.conj_re]; exact hpos x hx
  obtain ⟨p, q, B, B', h1, _, h3, h4⟩ :=
    GlobalTheory.exists_basis_adapted_to_cartan_involution n G θ hθθ hiso' hPD
  refine ⟨p, q, B, ⟨?_, B', h1⟩, h4⟩
  calc Bᵀ * M * B.map star = ((Bᵀ * M * B.map star).map star).map star := by simp [Matrix.map_map, Function.comp_def]
    _ = _ := by rw [map_star_trip, ← hGdef, h3, hJ]; rfl

end GlobalTheory.HoweD.FrameCartan

end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.cartanEigen_orthonormalFrame_exists : GlobalTheory.RealLift.FrameEx := by
  first | exact @GlobalTheory.RealLift.frameEx_holds | exact GlobalTheory.RealLift.frameEx_holds | (intros; apply GlobalTheory.RealLift.frameEx_holds <;> assumption)
end

section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

theorem _root_.GlobalTheory.T.fockAct2_eq_symmetrised_heisenbergQuadratic : ∀ (P Q R S : ℕ) (Y : Mat R S), Y ∈ upq R S →
    fockAct2 P Q R S Y = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ a : Ix P Q, ∑ b : Ix R S, (lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ))) := by
  first | exact @GlobalTheory.FockHeisQuad.fockAct2_eq_heisOp_quad | exact GlobalTheory.FockHeisQuad.fockAct2_eq_heisOp_quad | (intros; apply GlobalTheory.FockHeisQuad.fockAct2_eq_heisOp_quad <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem polMap_tprod_eq_prod_rename_mulX (W Λ : Type) [Fintype W] [DecidableEq W] (q : W → MvPolynomial Λ ℂ) :
    GlobalTheory.CCRFock.polMap W Λ (PiTensorProduct.tprod ℂ q) =
      ∏ v, MvPolynomial.rename (Prod.mk v) (q v) := by
  simp [GlobalTheory.CCRFock.polMap]

theorem polMap_comp_atPl_mulLeft_X : ∀ (W Λ : Type) [Fintype W] [DecidableEq W] (w : W) (l : Λ),
    GlobalTheory.CCRFock.polMap W Λ ∘ₗ GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
                 (LinearMap.mulLeft ℂ (MvPolynomial.X l)) =
      LinearMap.mulLeft ℂ (MvPolynomial.X (w, l)) ∘ₗ GlobalTheory.CCRFock.polMap W Λ := by
  intro W Λ _ _ w l
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro p
  have h : GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
        (LinearMap.mulLeft ℂ (MvPolynomial.X l)) (PiTensorProduct.tprod ℂ p) =
      PiTensorProduct.tprod ℂ (Function.update p w (MvPolynomial.X l * p w)) := by
    unfold GlobalTheory.RealLift.atPl
    rw [PiTensorProduct.map_tprod]
    congr 1
    funext v
    by_cases hv : v = w
    · subst hv; simp
    · simp [Function.update_of_ne hv]
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, h, polMap_tprod_eq_prod_rename_mulX,
    LinearMap.mulLeft_apply]
  rw [Fintype.prod_eq_mul_prod_compl w, Fintype.prod_eq_mul_prod_compl w
    (fun v => MvPolynomial.rename (Prod.mk v) (p v)), ← mul_assoc]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hv' : v ≠ w := by simpa using hv
    rw [Function.update_of_ne hv']

end GlobalTheory.CCRFock
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
namespace GlobalTheory.CCRFock

theorem pderiv_rename_prodMk_of_ne {W Λ : Type} {v w : W} (h : v ≠ w) (l : Λ) (r : MvPolynomial Λ ℂ) :
    MvPolynomial.pderiv (w, l) (MvPolynomial.rename (Prod.mk v) r) = 0 := by
  induction r using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.rename_X, Derivation.leibniz, hp, MvPolynomial.pderiv_X_of_ne]
    · simp
    · intro e; exact h (congrArg Prod.fst e)

theorem pderiv_prod_rename_of_notMem {W Λ : Type} {w : W} (l : Λ) (q : W → MvPolynomial Λ ℂ) (s : Finset W)
    (hs : w ∉ s) :
    MvPolynomial.pderiv (w, l) (∏ v ∈ s, MvPolynomial.rename (Prod.mk v) (q v)) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.mem_insert, not_or] at hs
    rw [Finset.prod_insert ha, Derivation.leibniz, ih hs.2,
      pderiv_rename_prodMk_of_ne (fun e => hs.1 e.symm)]
    simp

theorem polMap_comp_atPl_pderiv (W Λ : Type) [Fintype W] [DecidableEq W] (w : W) (l : Λ) :
    GlobalTheory.CCRFock.polMap W Λ ∘ₗ GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
                 (MvPolynomial.pderiv l).toLinearMap =
      (MvPolynomial.pderiv (w, l)).toLinearMap ∘ₗ GlobalTheory.CCRFock.polMap W Λ := by
  apply PiTensorProduct.ext
  ext1 q
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, polMap, atPl, PiTensorProduct.map_tprod,
    PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    AlgHom.toLinearMap_apply]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
  have h1 : ∏ i ∈ Finset.univ.erase w, MvPolynomial.rename (Prod.mk i)
      ((Function.update (fun _ : W => (LinearMap.id : MvPolynomial Λ ℂ →ₗ[ℂ] MvPolynomial Λ ℂ)) w
        (MvPolynomial.pderiv l).toLinearMap i) (q i)) =
      ∏ i ∈ Finset.univ.erase w, MvPolynomial.rename (Prod.mk i) (q i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi), LinearMap.id_apply]
  rw [h1, Function.update_self, Derivation.coeFn_coe, Derivation.coeFn_coe, Derivation.leibniz,
    pderiv_prod_rename_of_notMem l q _ (Finset.notMem_erase w _),
    MvPolynomial.pderiv_rename (Prod.mk_right_injective w) l (q w)]
  simp [mul_comm]

end GlobalTheory.CCRFock
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl


theorem _root_.GlobalTheory.T.exists_central_circle_oneParameter_unitary_realPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type)
    [Fintype β] [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (w₀ : InfinitePlace F), IsCMExt F E σ →
    ∃ z : ℝ → (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ, ∃ γ ∈ RLines (σ := σ) J,
      IsGen τ C γ (fun w => if w = w₀ then Complex.I • (1 : Mat R S) else 0) ∧
      (∀ t : ℝ, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = (z t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • (1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) ∧
      (∀ t : ℝ, At (evI F) ((z t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) - 1)) ∧
      ∀ (t : ℝ) (w : InfinitePlace F), piInf (τ w) (z t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = if w = w₀ then Complex.exp (t * Complex.I) else 1 := by
  first | exact @GlobalTheory.CentralLine.exists_central_line | exact GlobalTheory.CentralLine.exists_central_line | (intros; apply GlobalTheory.CentralLine.exists_central_line <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.maximalCompact_oneParameterLines_of_lieLines : GlobalTheory.RealLift.LineEx → GlobalTheory.RealLift.KLine := by
  first | exact @GlobalTheory.RealLift.kLine_of_lineEx | exact GlobalTheory.RealLift.kLine_of_lineEx | (intros; apply GlobalTheory.RealLift.kLine_of_lineEx <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.weakExponential_action_on_fockVectors : ∀ (F : Type) [Field F] [NumberField F] (κ V : Type) [Fintype κ] [AddCommGroup V] [Module ℂ V] (Φ : V →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (L : Module.End ℂ V) (om : Multiplicative ℝ →* Module.End ℂ ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)), GlobalTheory.RealLift.LocFin L → (∀ t, ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, l ∘ₗ om t ∈ (GlobalTheory.WeilM.adeleClass F).adm κ) → (∀ T, GlobalTheory.RealLift.SD (fun t => om (Multiplicative.ofAdd t)) (Φ T) (Φ (L T))) → ∃ U : Module.End ℂ V, GlobalTheory.RealLift.IsExp L U ∧ ∀ T, GlobalTheory.RealLift.SA (om (Multiplicative.ofAdd 1)) (Φ T) (Φ (U T)) := by
  first | exact @GlobalTheory.ExpAct.expAct_fock | exact GlobalTheory.ExpAct.expAct_fock | (intros; apply GlobalTheory.ExpAct.expAct_fock <;> assumption)
end
