module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedQuasiLogBasisPDivGroupLieDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev Wsp (lam : InfinitePlace E → DomWeight n) : Type :=
  PiTensorProduct ℂ fun v : InfinitePlace E => nablaSq ℂ n (lam v)

def wAt (lam : InfinitePlace E → DomWeight n) (γ : UE E n) : Wsp lam →ₗ[ℂ] Wsp lam :=
  PiTensorProduct.map fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (GeneralLinearGroup.map v.embedding γ.1)

def vecM (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) :
    Submodule ℂ (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) where
  carrier := {F | (∀ (γ : UE E n) x, F (finPt γ * x) = (wAt lam γ⁻¹).dualMap (F x)) ∧
    ∀ k ∈ globLev S K', ∀ x, F (x * k) = F x}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.add_apply, ha.1 γ x, hb.1 γ x, map_add (f := _)]
    · simp only [Pi.add_apply, ha.2 k hk x, hb.2 k hk x]
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ _ => rfl⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.smul_apply, ha.1 γ x, map_smul]
    · simp only [Pi.smul_apply, ha.2 k hk x]

def hopM (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (f : ∀ w : Pl E, UL n w → ℂ) :
    (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) :=
  levOp (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam))) (globLev S (KL n)) (globLev S K') (globFn S f)
    LinearMap.id

end GlobalTheory.BCT.TrKer

namespace GlobalTheory.BCT.TrKer

theorem trace_piMap {ι : Type} [Fintype ι] {M : ι → Type} [∀ c, AddCommGroup (M c)] [∀ c, Module ℂ (M c)]
    [∀ c, Module.Finite ℂ (M c)] (f : ∀ c, M c →ₗ[ℂ] M c) :
    LinearMap.trace ℂ (PiTensorProduct ℂ M) (PiTensorProduct.map f) =
      ∏ c, LinearMap.trace ℂ (M c) (f c) := by
  classical
  let bc := fun c => Module.Free.chooseBasis ℂ (M c)
  let B := Basis.piTensorProduct bc
  rw [LinearMap.trace_eq_matrix_trace ℂ B]
  have hc : ∀ c, LinearMap.trace ℂ (M c) (f c) = ∑ j, (bc c).repr (f c (bc c j)) j := by
    intro c
    rw [LinearMap.trace_eq_matrix_trace ℂ (bc c), Matrix.trace]
    simp only [Matrix.diag, LinearMap.toMatrix_apply]
  simp only [hc]
  rw [Fintype.prod_sum, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]

theorem finrank_wsp {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (lam : InfinitePlace E → DomWeight n) :
    (Module.finrank ℂ (Wsp lam) : ℂ) = dimW lam := by
  rw [← LinearMap.trace_id, ← PiTensorProduct.map_id, trace_piMap]
  unfold dimW
  simp

end GlobalTheory.BCT.TrKer
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isCompU_of_equiv {π : Submodule ℂ (UA E n → ℂ)} {w : Pl E} {σ σ' : SmIrr (UL n w)}
    (h : IsCompU π w σ) (e : σ.ρ.Equiv σ'.ρ) : IsCompU π w σ' := by
  obtain ⟨p, hp, -, f, hf0, hfπ, hfe⟩ := h
  let g : σ'.V →ₗ[ℂ] σ.V := e.symm.toLinearEquiv.toLinearMap
  have hg : ∀ x v, g (σ'.ρ x v) = σ.ρ x (g v) := fun x v =>
    LinearMap.congr_fun (e.symm.isIntertwining' x) v
  refine ⟨p, hp, σ'.irred, f ∘ₗ g, ?_, fun v => hfπ _, fun x v => ?_⟩
  · intro h0
    apply hf0
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun h0 (e.toLinearEquiv v)
    simpa [g] using this
  · simp only [LinearMap.comp_apply, hg, hfe]

theorem hasLevel_of_fixed {S : Set (Pl E)} (hS : IsSection S) {π : Submodule ℂ (UA E n → ℂ)}
    {K' : ∀ w : Pl E, Subgroup (UL n w)} (h : π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥) : HasLevel S π K' := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine ⟨φ, (Submodule.mem_inf.1 hφ).1, hφ0, fun w hw x hx hk => ?_⟩
  obtain ⟨k, hk, hkx⟩ := hk
  have hxf : x ∈ finU (E := E) (n := n) := hx.1
  have hmem : (⟨x, hxf⟩ : finU (E := E) (n := n)) ∈ globLev S K' := by
    simp only [globLev, Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map]
    intro w' hw'
    by_cases hww : w' = w
    · subst hww
      exact ⟨k, hk, hkx⟩
    · have hu : w'.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) := by
        intro he
        exact hww ((hS w).unique ⟨hw', he⟩ ⟨hw, rfl⟩)
      have hker : x ∈ (cLoc w').ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 w') hu
      refine ⟨1, one_mem _, ?_⟩
      simpa using (MonoidHom.mem_ker.1 hker).symm
  have := (Submodule.mem_inf.1 hφ).2 ⟨_, hmem⟩
  simpa [fixed, eig, RF] using this

theorem dimW_ne_zero (lam : InfinitePlace E → DomWeight n) : dimW lam ≠ 0 := by
  unfold dimW
  rw [Finset.prod_ne_zero_iff]
  intro v _
  rw [map_one, LinearMap.trace_one]
  exact_mod_cast Module.finrank_pos.ne'

end GlobalTheory.BCT
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameCplx

theorem gram_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    FD.gram τ (-Gᵀ) x = -(xᴴ * G.map τ * x)ᵀ := by
  ext a b
  simp only [FD.gram, hermC, FD.col, of_apply, Matrix.neg_apply, transpose_apply, Matrix.mul_apply, map_neg, map_apply,
    conjTranspose_apply, Finset.sum_mul, RCLike.star_def]
  simp_rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hermC_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ)
    (a : Fin r) (v : Fin r → ℂ) :
    hermC τ (-Gᵀ) (FD.col x a) v = -((star v ᵥ* (G.map τ * x)) a) := by
  simp only [hermC, FD.col, Matrix.neg_apply, transpose_apply, Matrix.mul_apply, map_neg, map_apply, vecMul, dotProduct,
    Finset.mul_sum, Pi.star_apply, RCLike.star_def]
  simp_rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

section lin
variable {r : ℕ} {G x S s : Matrix (Fin r) (Fin r) ℂ}

theorem isUnit_det (hS : S * S = 1) (hG : xᴴ * G * x = -S) : IsUnit x.det := by
  have h : (-(S * (xᴴ * G))) * x = 1 := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, hG, Matrix.mul_neg, neg_neg, hS]
  exact Matrix.isUnit_det_of_left_inverse h

theorem inv_mul_inv (hS : S * S = 1) (hG : xᴴ * G * x = -S) (hs : s * x = -(x * S)) : x⁻¹ * s = -(S * x⁻¹) := by
  have hx := isUnit_det hS hG
  have : s = -(x * S) * x⁻¹ := by rw [← hs, Matrix.mul_nonsing_inv_cancel_right _ _ hx]
  rw [this, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hx]

open scoped ComplexOrder in
theorem cartan (hS : S * S = 1) (hH : Sᴴ = S) (hG : xᴴ * G * x = -S) (hs : s * x = -(x * S)) : IsCartanInv G s := by
  have hx := isUnit_det hS hG
  have hxH : IsUnit xᴴ.det := by rw [Matrix.det_conjTranspose]; exact hx.star
  have hs' : s = -(x * S * x⁻¹) := by rw [← Matrix.neg_mul, ← hs, Matrix.mul_nonsing_inv_cancel_right _ _ hx]
  have hG' : G = -((x⁻¹)ᴴ * S * x⁻¹) := by
    rw [← Matrix.neg_mul, ← Matrix.mul_neg, ← hG, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc xᴴ,
      Matrix.nonsing_inv_mul_cancel_left _ _ hxH, Matrix.mul_nonsing_inv_cancel_right _ _ hx]
  have c1 : ∀ M : Matrix (Fin r) (Fin r) ℂ, x⁻¹ * (x * M) = M := fun M => Matrix.nonsing_inv_mul_cancel_left _ _ hx
  have c2 : ∀ M : Matrix (Fin r) (Fin r) ℂ, S * (S * M) = M := fun M => by rw [← Matrix.mul_assoc, hS, Matrix.one_mul]
  have c3 : ∀ M : Matrix (Fin r) (Fin r) ℂ, xᴴ * ((x⁻¹)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hx, conjTranspose_one, Matrix.one_mul]
  have hGs : G * s = (x⁻¹)ᴴ * x⁻¹ := by
    rw [hG', hs']; simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc, c1, c2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hs']; simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc, c1, c2]
    exact Matrix.mul_nonsing_inv _ hx
  · rw [Matrix.mul_assoc, hGs, hG', hs']
    simp only [conjTranspose_neg, conjTranspose_mul, hH, Matrix.neg_mul, Matrix.mul_assoc, c3]
  · rw [hGs]
    have hu : IsUnit x⁻¹ := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hx)
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit hu)

theorem adj_inv (hS : S * S = 1) (hH : Sᴴ = S) (hG : xᴴ * G * x = -S) (hs : s * x = -(x * S)) :
    sᴴ * (G * x) = -(G * x * S) := by
  obtain ⟨h1, h2, -⟩ := cartan hS hH hG hs
  have : x = -(s * (x * S)) := by
    rw [← Matrix.mul_assoc, hs, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, hS, Matrix.mul_one]
  calc sᴴ * (G * x) = -((sᴴ * G * s) * (x * S)) := by
        conv_lhs => rw [this]
        simp only [Matrix.mul_neg, Matrix.mul_assoc]
    _ = _ := by rw [h2, Matrix.mul_assoc]
end lin

theorem sgnM_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) : sgnM X * sgnM X = 1 := by
  rw [sgnM, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext a; unfold FD.sgn; split_ifs <;> simp

theorem sgnM_herm {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) : (sgnM X)ᴴ = sgnM X := by
  rw [sgnM, diagonal_conjTranspose]
  congr 1; funext a; simp

theorem per_cplx {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x s : Matrix (Fin r) (Fin r) ℂ) (hG : xᴴ * G.map τ * x = -sgnM X)
    (hs : s * x = -(x * sgnM X)) (v : Fin r → ℂ) (a : Fin r) :
    (if (a : ℕ) < X.p0 then hermC τ (-Gᵀ) (FD.col x a) (I • (s *ᵥ v)) else (x⁻¹ *ᵥ (I • (s *ᵥ v))) a) =
      I * (if (a : ℕ) < X.p0 then hermC τ (-Gᵀ) (FD.col x a) v else (x⁻¹ *ᵥ v) a) := by
  split_ifs with h
  · rw [hermC_eq, hermC_eq, star_smul, star_mulVec, smul_vecMul, vecMul_vecMul,
      adj_inv (sgnM_sq X) (sgnM_herm X) hG hs, vecMul_neg, ← vecMul_vecMul, sgnM]
    simp only [Pi.smul_apply, Pi.neg_apply, vecMul_diagonal]
    simp [FD.sgn, h]
  · rw [mulVec_smul, mulVec_mulVec, inv_mul_inv (sgnM_sq X) hG hs, neg_mulVec, ← mulVec_mulVec, sgnM]
    simp only [Pi.smul_apply, Pi.neg_apply, mulVec_diagonal]
    simp [FD.sgn, h]


open scoped ComplexOrder in
theorem cplx_of_frame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) ∧ (∀ τ, IsCartanInv (gramAt D V τ) 1) ∧ ∀ (τ : D.what₂.Tau) (u : Matrix (Fin W.rank) (Fin V.rank) ℂ), zOf θ V W hr X idx x (lineAt θ τ (cplxO 1 (s τ) u) 1) = I • zOf θ V W hr X idx x (lineAt θ τ u 1) := by
  intro D ψ θ V W r g hr X bas idx _ hθ hV _ hM _ x s hx hs
  subst hr
  have hGm : X.Gm = -(HSpace.gram W)ᵀ := hM.model.1
  have hG : ∀ τ : X.Ψ, (mat x τ)ᴴ * (HSpace.gram W).map τ.1 * mat x τ = -sgnM X := fun τ => by
    have h := hx τ
    rw [hGm, gram_eq] at h
    have h2 : (sgnM X)ᵀ = sgnM X := by rw [sgnM, diagonal_transpose]
    rw [← h2, ← h, transpose_neg, transpose_transpose, neg_neg]
  have hs' : ∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ → s ρ * mat x τ = -(mat x τ * sgnM X) := hs
  refine ⟨fun ρ => ?_, fun ρ => ?_, fun ρ u => ?_⟩
  · have h := hG ⟨tauE D ρ, (hM.psi _).2 ⟨ρ, rfl⟩⟩
    exact cartan (sgnM_sq X) (sgnM_herm X) h (hs' ρ _ rfl)
  · have : gramAt D V ρ = 1 := by
      rw [gramAt, hV]; exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [this]
    refine ⟨by simp, by simp, ?_⟩
    rw [Matrix.mul_one]; exact Matrix.PosDef.one
  · have hL : ∀ z : Matrix (Fin W.rank) (Fin V.rank) ℂ, IsLineAt θ ρ z (lineAt θ ρ z) := fun z =>
      Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ ρ z)
    funext b j
    simp only [zOf, Pi.smul_apply, smul_eq_mul, perC]
    obtain ⟨τ, a⟩ := idx j
    have hτ : ∃ ρ', τ.1 = tauE D ρ' := (hM.psi _).1 τ.2
    simp only [realM, dif_pos hτ, (hL _).2.2, hGm]
    by_cases e : hτ.choose = ρ
    · simp only [if_pos e]
      have := per_cplx X τ.1 (HSpace.gram W) (mat x τ) (s ρ) (hG τ) (hs' ρ τ (e ▸ hτ.choose_spec)) (fun k => u k b) a
      convert this using 3 <;> (try funext k) <;> simp [cplxO, Matrix.mul_apply, mulVec, dotProduct]
    · simp only [if_neg e]
      simp [hermC, mulVec, dotProduct]

end GlobalTheory.FrameCplx
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GoodConj

theorem eventually_mem_integers {E : Type} [Field E] [NumberField E] (a : E) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite,
      algebraMap E (w.adicCompletion E) a ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) a).2

theorem mem_KGL_of_entries {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E) (g : GLw n w)
    (h1 : ∀ a b, g.val a b ∈ w.adicCompletionIntegers E)
    (h2 : ∀ a b, (g⁻¹).val a b ∈ w.adicCompletionIntegers E) : g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  let O : Subring (w.adicCompletion E) := Ov E w
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => funext fun i => funext fun j => Subtype.ext (congrFun (congrFun h i) j)
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ γ : UE E n,
    γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, ∀ g : UL n w, g⁻¹ * locPt w γ * g ∈ KL n w →
      ∃ t ∈ twCent (MonoidHom.id (UL n w)) (locPt w γ), t⁻¹ * g ∈ KL n w := by
  intro E _ _ _ _ n _ γ hsep
  have hint : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) ((γ.1 : GL (Fin n) E).val i j) ∈ w.adicCompletionIntegers E ∧
      algebraMap E (w.adicCompletion E) (((γ.1 : GL (Fin n) E)⁻¹).val i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j =>
      (eventually_mem_integers _).and (eventually_mem_integers _)
  filter_upwards [hint, GlobalTheory.T.eventually_integral_lift_coprime_derivative E _ hsep] with w hw hP
  obtain ⟨P₀, hP₀, hcop⟩ := hP
  intro g hg
  set y : GLw n w := Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ.1 : GL (Fin n) E) with hy
  by_cases hmem : y ∈ UL n w
  · have hloc : ((locPt w γ : UL n w) : GLw n w) = y := by
      simp only [locPt, toSub]
      rw [dite_eq_left hmem]
    have hyK : y ∈ GlobalTheory.LFun.KGL w (n := n) := by
      apply mem_KGL_of_entries
      · intro a b; exact (hw a b).1
      · intro a b
        rw [hy, ← map_inv]
        exact (hw a b).2
    have hK : locPt w γ ∈ KL n w := by
      rw [KL, Subgroup.mem_subgroupOf, hloc]; exact hyK
    obtain ⟨h1, h2⟩ := GlobalTheory.T.localConjugation_involutive_valuation_preserving E w
    have hcp : (locPt w γ).1.val.charpoly =
        P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
      rw [hloc, hP₀, hy]
      exact Matrix.charpoly_map _ _
    obtain ⟨t, ht, k, hk, he⟩ := GlobalTheory.T.integral_conj_set_localUnitary_eq_doubleCoset E n w h1 h2 P₀ hcop (locPt w γ) hcp 1 g
      (by simpa using hK) hg
    refine ⟨t, ht, ?_⟩
    rw [he, mul_one, inv_mul_cancel_left]
    exact hk
  · have hloc : locPt w γ = 1 := by
      simp only [locPt, toSub]
      rw [dite_eq_right hmem]
    refine ⟨g, ?_, by rw [inv_mul_cancel]; exact one_mem _⟩
    rw [hloc]
    show g * 1 = 1 * (MonoidHom.id _) g
    simp

end GlobalTheory.BCT.GoodConj
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.MuProps

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem atEmb_emb (w : InfinitePlace E) (z : ℂ) : atEmb w.embedding z = Pi.single w z := by
  unfold atEmb; simp [InfinitePlace.mk_embedding]

theorem chiInf_expU_single {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) (z : ℂ) :
    ((chiInf μ (expU (Pi.single v z)) : ℂˣ) : ℂ) =
      Complex.exp ((e v : ℂ) / 2 * z + (-(e v : ℂ) / 2) * starRingEnd ℂ z) := by
  rw [h.2.2.2.2, Finset.prod_eq_single v]
  · change (Complex.exp ((Pi.single v z : Cinf E) v) / ((‖Complex.exp ((Pi.single v z : Cinf E) v)‖ : ℝ) : ℂ)) ^ e v = _
    rw [Pi.single_eq_same, Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_sub, ← Complex.exp_int_mul]
    congr 1
    have := Complex.add_conj z
    push_cast at this
    linear_combination ((e v : ℂ) / 2) * this
  · intro u _ hu
    change (Complex.exp ((Pi.single v z : Cinf E) u) / ((‖Complex.exp ((Pi.single v z : Cinf E) u)‖ : ℝ) : ℂ)) ^ e u = 1
    rw [Pi.single_eq_of_ne hu]
    simp
  · simp

theorem expo_emb {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) :
    expo μ v.embedding = (e v : ℂ) / 2 :=
  expo_eq_of_exp μ v.embedding _ (-(e v : ℂ) / 2) fun z => by
    rw [atEmb_emb]; exact chiInf_expU_single h v z

theorem expo_conj {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) :
    expo μ (ComplexEmbedding.conjugate v.embedding) = -(e v : ℂ) / 2 :=
  expo_eq_of_exp μ _ _ ((e v : ℂ) / 2) fun z => by
    rw [atEmb_conj, atEmb_emb, chiInf_expU_single h v]
    congr 1
    simp only [Complex.conj_conj]
    ring

theorem dchi_single {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) (w : ℂ) :
    dchi μ (Pi.single v w) = (w.im : ℂ) * dchi μ (Pi.single v Complex.I) := by
  have h1 := expo_emb h v
  have h2 := expo_conj h v
  simp only [expo, atEmb_conj, atEmb_emb, map_one, Complex.conj_I, Pi.single_neg, map_neg] at h1 h2
  have hd1 : dchi μ (Pi.single v 1) = 0 := by linear_combination h1 + h2
  rw [← atEmb_emb, atEmb_eq, map_add (f := _), map_smul, map_smul, atEmb_emb, atEmb_emb, hd1]
  rw [smul_zero, zero_add, Complex.real_smul]

theorem dchi_neg_star {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (z : Cinf E) :
    dchi μ (-star z) = dchi μ z := by
  conv_lhs => rw [← Finset.univ_sum_single (-star z)]
  conv_rhs => rw [← Finset.univ_sum_single z]

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [dchi_single h v, dchi_single h v (z v), Pi.neg_apply, Pi.star_apply, Complex.neg_im, Complex.star_def, Complex.conj_im, neg_neg]

theorem finId_conjFin (u : (Af E)ˣ) :
    finId E (Units.map (conjFin (IsCMField.complexConj E).toRingEquiv).toMonoidHom u) =
      Units.map (conjAd E).toMonoidHom (finId E u) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (1 : InfiniteAdeleRing E) - 0 + 0 = (infEq E) (starRingEnd (Cinf E) ((infEq E).symm ((1 : InfiniteAdeleRing E) - 0 + 0)))
    simp
  · change (1 : Af E) - 1 + conjFin (IsCMField.complexConj E).toRingEquiv (u : Af E) =
      conjFin (IsCMField.complexConj E).toRingEquiv ((1 : Af E) - 1 + (u : Af E))
    simp

theorem mu_mul_conj {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (x : Neutral.B1.Ideles E) :
    μ.1 x * μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E x) = 1 := by
  rw [← map_mul, ← GlobalTheory.GalOfCusp.ideleMap_ideleNorm, h.2.1]
  have := congrArg (fun c : HChar E => c.1 x) (GlobalTheory.GalOfCusp.compNorm_quadChar E)
  exact this

theorem thetaInv {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (a : ℕ) : ThetaInv a μ := by
  refine CG.thetaInv_of (fun u => ?_) (dchi_neg_star h)
  rw [map_inv, finId_conjFin, ← GlobalTheory.PolChar.ideleConj_eq, map_inv]
  have := mu_mul_conj h (finId E u)
  exact inv_eq_of_mul_eq_one_left this

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → (∀ a, ThetaInv a μ) ∧ (∀ v : InfinitePlace E, expo μ v.embedding = (e v : ℂ) / 2) ∧ ∀ v : InfinitePlace E, expo μ (ComplexEmbedding.conjugate v.embedding) = -(e v : ℂ) / 2 :=
  fun _ _ _ _ _ _ _ h => ⟨thetaInv h, expo_emb h, expo_conj h⟩

end GlobalTheory.BCT.MuProps
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∃ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), IsBasis c.μ e ∧ IsAdapted (RingHom.id O) c.μ e ∧ (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) ∧ ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := by
  first | exact @GlobalTheory.QLogBasis.adapted_basis | exact GlobalTheory.QLogBasis.adapted_basis | (intros; apply GlobalTheory.QLogBasis.adapted_basis <;> assumption)
end
