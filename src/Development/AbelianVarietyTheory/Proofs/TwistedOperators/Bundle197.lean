module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle009
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle069
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlmostNormEtaProdEqNegOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEverywhereNormDivOfEtaProdEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexTwoOfFiniteReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle182
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenCardOfNotLone
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt.TensorGlob

theorem der_span {E : Type*} [AddCommGroup E] [Module ℂ E] {s : Set E} (hs : Submodule.span ℂ s = ⊤)
    (f : ℝ → E →ₗ[ℂ] ℂ) (g : E →ₗ[ℂ] ℂ) (h : ∀ e ∈ s, HasDerivAt (fun t => f t e) (g e) 0) (e : E) :
    HasDerivAt (fun t => f t e) (g e) 0 := by
  have he : e ∈ Submodule.span ℂ s := hs ▸ Submodule.mem_top
  induction he using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have h0 : (fun t => f t 0) = fun _ => (0 : ℂ) := funext fun t => map_zero (f t)
    rw [h0, map_zero]
    exact hasDerivAt_const _ _
  | add x y _ _ hx hy =>
    have h0 : (fun t => f t (x + y)) = fun t => f t x + f t y := funext fun t => map_add (f t) x y
    rw [h0, map_add (f := _)]
    exact hx.add hy
  | smul a x _ hx =>
    have h0 : (fun t => f t (a • x)) = fun t => a * f t x := funext fun t => map_smul (f t) a x
    rw [h0, map_smul, smul_eq_mul]
    exact hx.const_mul a

theorem der_span₂ {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    {s : Set E} (hs : Submodule.span ℂ s = ⊤) {s' : Set F} (hs' : Submodule.span ℂ s' = ⊤)
    (f : ℝ → E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (g : E →ₗ[ℂ] F →ₗ[ℂ] ℂ)
    (h : ∀ e ∈ s, ∀ x ∈ s', HasDerivAt (fun t => f t e x) (g e x) 0) (e : E) (x : F) :
    HasDerivAt (fun t => f t e x) (g e x) 0 := by
  have h1 : ∀ x ∈ s', ∀ e', HasDerivAt (fun t => f t e' x) (g e' x) 0 := fun x hx e' =>
    der_span hs (fun t => (f t).flip x) (g.flip x) (fun e'' he'' => h e'' he'' x hx) e'
  exact der_span hs' (fun t => f t e) (g e) (fun x hx => h1 x hx e) x

variable {D : D7}

open Classical in
theorem glue_update {a b : ℕ} (P : D.what₂.Tau → LPol b a) (τ : D.what₂.Tau) (p : LPol b a) :
    glue (Function.update P τ p) = MvPolynomial.rename (fun s => (τ, s)) p *
      ∏ ρ ∈ Finset.univ.erase τ, MvPolynomial.rename (fun s => (ρ, s)) (P ρ) := by
  unfold glue
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  congr 1
  · simp
  · exact Finset.prod_congr rfl fun ρ hρ => by simp [Finset.ne_of_mem_erase hρ]

open Classical in
theorem glue_update_add_smul {a b : ℕ} (P : D.what₂.Tau → LPol b a) (τ : D.what₂.Tau) (p : LPol b a) (c : ℂ) :
    glue (Function.update P τ p) + c • glue P = glue (Function.update P τ (p + c • P τ)) := by
  have h0 : glue P = glue (Function.update P τ (P τ)) := by rw [Function.update_eq_self]
  rw [h0, glue_update, glue_update, glue_update, map_add (f := _), map_smul, add_mul, smul_mul_assoc]

variable {V : HSp D} {S : D.what₂.Tau → SPar}

theorem ellT_tprod' (M : DSModel V S) (w v : ∀ τ, M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, ⟪w τ, v τ⟫_ℂ := by
  unfold ellT
  rw [PiTensorProduct.lift.tprod]
  simp

open Classical in
theorem ellT_update (M : DSModel V S) (w v : ∀ τ, M.H τ) (τ : D.what₂.Tau) (u : M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
      ⟪w τ, u⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, v ρ⟫_ℂ := by
  rw [ellT_tprod', ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  congr 1
  · simp
  · exact Finset.prod_congr rfl fun ρ hρ => by simp [Finset.ne_of_mem_erase hρ]

open Classical in
theorem actT_tprod (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : ∀ τ, M.H τ) :
    actT M τ g (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ (M.rep τ g (v τ))) := by
  unfold actT
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases hρ : ρ = τ
  · subst hρ; simp
  · simp [Function.update_of_ne hρ]

theorem der_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {c : ℝ → H} {y : H}
    (h : HasDerivAt c y 0) (w : H) (k : ℂ) : HasDerivAt (fun t => ⟪w, c t⟫_ℂ * k) (⟪w, y⟫_ℂ * k) 0 := by
  have h1 : HasDerivAt (fun t => ⟪w, c t⟫_ℂ) ⟪w, y⟫_ℂ 0 := by
    simpa [Function.comp_def] using ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  exact h1.mul_const k


open Classical in
theorem exists_globIt : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (aS aT : D.what₂.Tau → ℚ) (A : ∀ τ, LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ), GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.ContrTensor → GlueLaw D V.rank W.rank → (∀ τ, LocIt M M' τ (aS τ) (aT τ) (A τ)) → ∃ It I, GlobIt M M' aS aT It I := by
  intro D V W S S' M M' aS aT A hC hG hL
  have hs := hG.1
  have hs' : Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ : (∀ τ, M'.H τ) → ⨂[ℂ] τ, M'.H τ)) = ⊤ :=
    PiTensorProduct.span_tprod_eq_top
  obtain ⟨I, hI, -⟩ := hC D.what₂.Tau (fun _ => Fin W.rank × Fin V.rank) (FVar D W.rank V.rank)
    (Equiv.sigmaEquivProd D.what₂.Tau (Fin W.rank × Fin V.rank) :
      (Σ _ : D.what₂.Tau, Fin W.rank × Fin V.rank) ≃ FVar D W.rank V.rank)
    (fun τ => M'.H τ) (fun τ => M.H τ) A
  have hIg : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (v : ∀ τ, M'.H τ),
      I (glue P) (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun ρ => A ρ (P ρ) (v ρ) :=
    fun P v => hI P v
  let Itl : ∀ τ, LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.sm τ := fun τ =>
    LinearMap.mk₂ ℂ (fun P y => (⟨A τ P (y : M'.H τ), (hL τ).sm P (y : M'.H τ)⟩ : M.sm τ))
      (fun P Q y => Subtype.ext (by simp)) (fun c P y => Subtype.ext (by simp))
      (fun P y z => Subtype.ext (by simp)) (fun c P y => Subtype.ext (by simp))
  have hItl : ∀ τ P y, ((Itl τ P y : M.sm τ) : M.H τ) = A τ P (y : M'.H τ) := fun _ _ _ => rfl
  obtain ⟨It, hIt, hItne⟩ := hC D.what₂.Tau (fun _ => Fin W.rank × Fin V.rank) (FVar D W.rank V.rank)
    (Equiv.sigmaEquivProd D.what₂.Tau (Fin W.rank × Fin V.rank) :
      (Σ _ : D.what₂.Tau, Fin W.rank × Fin V.rank) ≃ FVar D W.rank V.rank)
    (fun τ => ↥(M'.sm τ)) (fun τ => ↥(M.sm τ)) Itl
  have hItg : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (v : ∀ τ, M'.sm τ),
      It (glue P) (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun ρ => Itl ρ (P ρ) (v ρ) :=
    fun P v => hIt P v
  have hupdP : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (τ : D.what₂.Tau) (Q : LPol W.rank V.rank)
      (v : ∀ τ, M'.H τ), (PiTensorProduct.tprod ℂ fun ρ => A ρ (Function.update P τ Q ρ) (v ρ)) =
        PiTensorProduct.tprod ℂ (Function.update (fun ρ => A ρ (P ρ) (v ρ)) τ (A τ Q (v τ))) := by
    intro P τ Q v
    congr 1
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  have hupdV : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (τ : D.what₂.Tau) (v : ∀ τ, M'.H τ) (y : M'.H τ),
      (PiTensorProduct.tprod ℂ fun ρ => A ρ (P ρ) (Function.update v τ y ρ)) =
        PiTensorProduct.tprod ℂ (Function.update (fun ρ => A ρ (P ρ) (v ρ)) τ (A τ (P τ) y)) := by
    intro P τ v y
    congr 1
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  refine ⟨It, I, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro φ v
    have h1 : It.compr₂ (inclT M) = I.compl₂ (inclT M') := by
      refine LinearMap.ext_on hs ?_
      rintro _ ⟨P, rfl⟩
      refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply, hItg]
      unfold inclT
      simp only [PiTensorProduct.map_tprod, Submodule.subtype_apply, hItl, hIg]
    exact DFunLike.congr_fun (DFunLike.congr_fun h1 φ) v
  · apply hItne
    intro τ h0
    obtain ⟨P, y, hy, hne⟩ := (hL τ).ne
    apply hne
    have h2 := congrArg (fun B : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.sm τ =>
      ((B P ⟨y, hy⟩ : M.sm τ) : M.H τ)) h0
    simpa [hItl] using h2
  · intro φ w
    have hφ : φ ∈ Submodule.span ℂ (Set.range (glue : (D.what₂.Tau → LPol W.rank V.rank) → PolF D W.rank V.rank)) :=
      hs ▸ Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨P, rfl⟩ := hx
      choose w' hw' using fun τ => (hL τ).adj (P τ) (w τ)
      refine Submodule.subset_span ⟨w', ?_⟩
      refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, hIg, ellT_tprod', hw']
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _), LinearMap.comp_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [map_smul, LinearMap.comp_smul]
      exact Submodule.smul_mem _ a hx
  · intro τ X hX φ x w
    have key := der_span₂ hs hs' (fun t => I.compr₂ (ellT M w ∘ₗ actT M τ (NormedSpace.exp (t • X))))
      ((I ∘ₗ srcOp M M' τ (aT τ) X).compr₂ (ellT M w)) ?hyp φ x
    · simpa only [LinearMap.compr₂_apply, LinearMap.comp_apply] using key
    case hyp =>
      rintro _ ⟨P, rfl⟩ _ ⟨v, rfl⟩
      simp only [LinearMap.compr₂_apply, LinearMap.comp_apply, srcOp, LinearMap.add_apply,
        LinearMap.smul_apply, Module.End.one_apply, (hG.2 τ (M.ε τ) (M'.ε τ) P).1, glue_update_add_smul,
        hIg, hupdP, actT_tprod, ellT_update]
      rw [neg_smul, ← sub_eq_add_neg]
      exact der_inner ((hL τ).src X hX (P τ) (v τ)) (w τ) _
  · intro τ Y hY φ x w
    have key := der_span₂ hs hs'
      (fun t => (I.compl₂ (actT M' τ (NormedSpace.exp (t • Y)))).compr₂ (ellT M w))
      (-((I ∘ₗ tgtOp M M' τ (aS τ) Y).compr₂ (ellT M w))) ?hyp φ x
    · simpa only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        LinearMap.neg_apply] using key
    case hyp =>
      rintro _ ⟨P, rfl⟩ _ ⟨v, rfl⟩
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.neg_apply,
        tgtOp, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        (hG.2 τ (M.ε τ) (M'.ε τ) P).2, glue_update_add_smul, hIg, hupdP, hupdV, actT_tprod, ellT_update]
      rw [← neg_mul, ← inner_neg_right]
      exact der_inner ((hL τ).tgt Y hY (P τ) (v τ)) (w τ) _

end GlobalTheory.Chain.RealIt.TensorGlob

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealIt.LocalFromCover

theorem trace_conj {p q : ℕ} {Z : Mat p q} (hZ : Z ∈ upq p q) : (starRingEnd ℂ) Z.trace = -Z.trace := by
  have h : Zᴴ * Jm p q + Jm p q * Z = 0 := hZ
  have hJ := GlobalTheory.RealPar.KStabLie.Jm_sq p q
  have h2 := congrArg (fun A => (A * Jm p q).trace) h
  simp only [add_mul, Matrix.trace_add, zero_mul, Matrix.trace_zero] at h2
  rw [mul_assoc, hJ, mul_one, Matrix.trace_mul_comm, ← mul_assoc, hJ, one_mul, Matrix.trace_conjTranspose] at h2
  exact eq_neg_of_add_eq_zero_left h2

theorem trace_reindex' {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) : (Matrix.reindex e e Z).trace = Z.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact e.symm.sum_comp fun a => Z a a

theorem exp_plainMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) (t : ℝ) :
    NormedSpace.exp (t • plainMat e Z) = plainMat e (NormedSpace.exp (t • Z)) := by
  have h : t • plainMat e Z = Matrix.reindex e e (t • Z) := by
    ext a b; simp [plainMat]
  rw [h]
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
    exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) (t • Z)).symm

theorem exp_barMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) (t : ℝ) :
    NormedSpace.exp (t • barMat e Z) = barMat e (NormedSpace.exp (t • Z)) := by
  have h0 : ∀ A : Mat p q, A.map (starRingEnd ℂ) = Aᴴᵀ := fun A => by ext a b; simp
  have h1 := exp_plainMat e (Z.map (starRingEnd ℂ)) t
  have h2 : t • Z.map (starRingEnd ℂ) = (t • Z)ᴴᵀ := by ext a b; simp
  rw [h2, Matrix.exp_transpose, Matrix.exp_conjTranspose, ← h0] at h1
  exact h1

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)

theorem fr_toFrame (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) : M.fr τ * toFrame M τ Y * (M.fr τ)⁻¹ = Y := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  rw [toFrame, ← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul, mul_assoc,
    Matrix.mul_nonsing_inv _ hd, mul_one]

theorem trace_toFrame (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) : (toFrame M τ Y).trace = Y.trace := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  rw [toFrame, Matrix.trace_mul_comm, ← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul]

theorem rep_exp (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) :
    M.rep τ (NormedSpace.exp (t • toFrame M τ Y)) = M.σ τ (NormedSpace.exp (t • Y)) := by
  rw [DSModel.rep, ← Matrix.exp_conj _ _ (M.fr_unit τ), Matrix.mul_smul, Matrix.smul_mul, fr_toFrame]

variable {M τ}

theorem matches_exp {p q : ℕ} {T : GrpData p q} {R : DSRep T}
    {φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ} {m : ℤ} {U : M.H τ → R.U.H} (h : Matches R M τ φ m U)
    (hφ : ∀ (Z : Mat p q) (t : ℝ), NormedSpace.exp (t • φ Z) = φ (NormedSpace.exp (t • Z)))
    {Z : Mat p q} (hZ : Z ∈ upq p q) (t : ℝ) (x : M.H τ) :
    U (M.rep τ (NormedSpace.exp (t • toFrame M τ (φ Z))) x) =
      ((T.sq (T.expt (t • Z)) : ℂˣ) : ℂ) ^ m • R.U.π (T.expt (t • Z)) (U x) := by
  rw [rep_exp, hφ, h.grp, T.expt_cov _ (GlobalTheory.RealPar.KStabLie.smul_mem_upq hZ t), smul_smul,
    ← zpow_add₀ (Units.ne_zero _), add_neg_cancel, zpow_zero, one_smul]

theorem hasDerivAt_sq_zpow {p q : ℕ} (T : GrpData p q) (m : ℤ) {Z : Mat p q} (hZ : Z ∈ upq p q) :
    HasDerivAt (fun t : ℝ => ((T.sq (T.expt (t • Z)) : ℂˣ) : ℂ) ^ m) (m * (Z.trace / 2)) 0 := by
  have h3 := (hasDerivAt_zpow m _ (.inl (Units.ne_zero _))).comp (0 : ℝ)
    (GlobalTheory.RealPar.Cover.hasDerivAt_sq (T := T) hZ)
  refine h3.congr_deriv ?_
  simp [T.expt_zero]

theorem exists_locIt (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ ≃ₗᵢ[ℂ] R₁.U.H)
    (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s)
    (B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H) (hm : (m : ℚ) = 2 * aT) (hm' : (m' : ℚ) = 2 * aS)
    (h₁ : Matches R₁ M τ (barMat e) m U) (h₂ : Matches R₂ M' τ (plainMat e') m' U')
    (hN : Nontrivial R₂.HK.V) (hκ : IsPolyIso (M.ε τ) (M'.ε τ) e e' κ) (hB : IsCoverIt R₁ R₂ B) :
    ∃ A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ, LocIt M M' τ aS aT A := by
  let A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ :=
    LinearMap.mk₂ ℂ (fun P y => U.symm (B (κ P) (U' y)))
      (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp [LinearIsometryEquiv.map_smulₛₗ, LinearMap.map_smulₛₗ])
  have hA : ∀ P y, A P y = U.symm (B (κ P) (U' y)) := fun _ _ => rfl
  have hmC : (m : ℂ) = 2 * (aT : ℂ) := by exact_mod_cast hm
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  refine ⟨A, fun P y => ?_, ?_, fun P w => ?_, ?_, ?_⟩
  · refine Submodule.subset_span (h₁.smooth _ ?_)
    rw [hA, U.apply_symm_apply]
    exact hB.kfin _ _
  · obtain ⟨v, hv⟩ := exists_ne (0 : R₂.HK.V)
    obtain ⟨P, hP⟩ := hB.ne (R₂.ι v) fun h0 => hv (R₂.ι_inj (by rw [h0, map_zero]))
    refine ⟨κ.symm P, U'.symm (R₂.ι v), Submodule.subset_span (h₂.smooth _ ?_), ?_⟩
    · rw [U'.apply_symm_apply]; exact ⟨v, rfl⟩
    · rw [hA, U'.apply_symm_apply, κ.apply_symm_apply]
      intro h0
      exact hP (U.symm.injective (by rw [h0, map_zero]))
  · haveI : CompleteSpace (M'.H τ) := U'.toIsometryEquiv.completeSpace
    obtain ⟨c, hc⟩ := hB.bdd (κ P)
    let L : M'.H τ →L[ℂ] M.H τ := (A P).mkContinuous c fun y => by
      rw [hA, U.symm.norm_map, ← U'.norm_map y]; exact hc _
    refine ⟨(InnerProductSpace.toDual ℂ (M'.H τ)).symm ((innerSL ℂ w).comp L), fun y => ?_⟩
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  · intro X hX P y
    rw [← h₁.lie] at hX
    obtain ⟨Z, hZ, rfl⟩ := hX
    have h1 := (hasDerivAt_sq_zpow T₁ m hZ).fun_smul (hB.src Z hZ (κ P) (U' y))
    have h2 := (U.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) h1
    have h3 : (barMat e Z).map (starRingEnd ℂ) = Matrix.reindex e e Z := by ext a b; simp [barMat]
    have h4 : (barMat e Z).trace = -Z.trace := by
      rw [barMat, trace_reindex', ← trace_conj hZ]
      simp [Matrix.trace]
    convert (preTransparency := .reducible) h2 using 1
    · funext t
      apply U.injective
      rw [matches_exp h₁ (exp_barMat e) hZ, hA]
      simp
    · rw [hA, fr_toFrame, trace_toFrame, h3, h4, map_sub, map_smul, hκ.1, hmC,
        show 2 * (aT : ℂ) * (Z.trace / 2) = aT * Z.trace by ring]
      simp [T₁.expt_zero]
  · intro Y hY P y
    rw [← h₂.lie] at hY
    obtain ⟨Z, hZ, rfl⟩ := hY
    have h1 := (hasDerivAt_sq_zpow T₂ m' hZ).star.fun_smul (hB.tgt Z hZ (κ P) (U' y))
    have h2 := (U.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) h1
    have h4 : (plainMat e' Z).trace = Z.trace := trace_reindex' e' Z
    have h5 : star ((m' : ℂ) * (Z.trace / 2)) = -((aS : ℂ) * Z.trace) := by
      rw [Complex.star_def, map_mul, map_intCast, map_div₀, trace_conj hZ, map_ofNat, hmC']
      ring
    convert (preTransparency := .reducible) h2 using 1
    · funext t
      rw [hA, matches_exp h₂ (exp_plainMat e') hZ, LinearMap.map_smulₛₗ]
      rfl
    · rw [h5, hA, fr_toFrame, trace_toFrame, h4, map_add (f := _), map_smul, plainMat, hκ.2]
      simp [T₂.expt_zero]
      abel

end GlobalTheory.Chain.RealIt.LocalFromCover

end
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.baseChange_thetaLiftSatakeParameter_eq_add_segment : ∀ (q : ℂˣ) (n n' : ℕ), n ≤ n' → ∀ α : Fin (n / 2) → ℂˣ, (bcParam n' (liftPar q n n' α)).map (fun x => ((-1 : ℂˣ) ^ n)⁻¹ * x) = (bcParam n α).map (fun x => ((-1 : ℂˣ) ^ n')⁻¹ * x) + str q ((n' : ℤ) - n) := by
  first | exact @GlobalTheory.SphTheta.bcParam_liftPar | exact GlobalTheory.SphTheta.bcParam_liftPar | (intros; apply GlobalTheory.SphTheta.bcParam_liftPar <;> assumption)
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.QuadSymbol

theorem eta_eq_of_div_mem {K L : Type} [Field K] [Field L] [Algebra K L] {A : Type} [CommRing A]
    [Algebra K A] {a b : Aˣ} (h : a / b ∈ normGroup K L A) : eta K L A a = eta K L A b := by
  have hiff : a ∈ normGroup K L A ↔ b ∈ normGroup K L A := by
    have := (normGroup K L A).mul_mem_cancel_left (x := a / b) (y := b) h
    rwa [div_mul_cancel] at this
  by_cases hb : b ∈ normGroup K L A
  · rw [eta_eq_one_iff.2 hb, eta_eq_one_iff.2 (hiff.2 hb)]
  · rw [eta_eq_neg_one_iff.2 hb, eta_eq_neg_one_iff.2 (fun ha => hb (hiff.1 ha))]

theorem etaProd_eq_of_everywhereNorm_div {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    {x x' : FinFam K} {y y' : InfFam K} (h : EverywhereNorm K L (x / x') (y / y')) :
    etaProd K L x y = etaProd K L x' y' := by
  unfold etaProd
  congr 1
  · exact finprod_congr fun v => eta_eq_of_div_mem (h.1 v)
  · exact Finset.prod_congr rfl fun w _ => eta_eq_of_div_mem (h.2 w)

theorem exactSequence (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] : ExactSequence K L := by
  refine ⟨almostNorm_finDiag K L, fun t => (normTheorem K L t).symm, fun x y hx => ⟨?_, ?_⟩,
    exists_almostNorm_etaProd_eq_neg_one K L⟩
  · rintro ⟨t, ht⟩
    rw [etaProd_eq_of_everywhereNorm_div ht]
    exact (productFormula K L t).2
  · exact exists_everywhereNorm_div_of_etaProd_eq_one K L x y hx

end GlobalTheory.QuadSymbol

namespace GlobalTheory.Published

open GlobalTheory.QuadSymbol

theorem quadraticClassFieldTheory_holds : QuadraticClassFieldTheory :=
  ⟨fun K L _ _ _ _ _ _ =>
    ⟨localCharacters K L, normTheorem K L, exactSequence K L, productFormula K L⟩,
   fun F E K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => baseChange F E K L h⟩

end GlobalTheory.Published
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tendsto_finitePlaceTruncation_adeleE : ∀ (D : D7) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F), (∀ v, IsPlaceIdem D v (ε v)) → ∀ a : AE D, infPart D a = 0 → Filter.Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 D.host.F)) => algebraMap (AF D.host.F) (AE D) (∑ v ∈ s, ε v) * a) Filter.atTop (nhds a) := by
  first | exact @GlobalTheory.VecInv.tendsto_truncation | exact GlobalTheory.VecInv.tendsto_truncation | (intros; apply GlobalTheory.VecInv.tendsto_truncation <;> assumption)
end
