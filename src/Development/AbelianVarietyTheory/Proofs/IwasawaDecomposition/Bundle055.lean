module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensor
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
public import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Basic.PEquiv
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace GlobalTheory.AlgWtHW

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem exists_gq (γ₀ : GL (Fin n) L) (h : γ₀ ∈ GQ0 L n) :
    ∃ γ : GQ L n, (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
  set g := Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) γ₀ with hgdef
  have hg : g ∈ GA L n := by
    show g.val * conjT (conjAL L) g.val = 1
    have e : conjT (conjAL L) g.val =
        (conjT (IsCMField.complexConj L : L →+* L) γ₀.val).map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := by
      ext i j
      simp [conjT, g, conjAL, Algebra.TensorProduct.map_tmul]
    rw [e]
    have h' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1 := h
    show γ₀.val.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) * _ = 1
    rw [← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.2 ⟨γ₀, h, rfl⟩⟩, rfl⟩

theorem conj_conj (φ : L →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by
  ext x; simp

theorem conjugate_ne_self (τ : L →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
  IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)

theorem isUPt_ratPt (γ₀ : GL (Fin n) L) (h : γ₀ ∈ GQ0 L n) : IsUPt (ratPt γ₀.val) := by
  intro σ
  have h' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1 := h
  have e : ratPt γ₀.val (ComplexEmbedding.conjugate σ) = (γ₀.val.map (IsCMField.complexConj L : L →+* L)).map σ := by
    ext i j
    simp [ratPt, IsCMField.complexEmbedding_complexConj]
  rw [e]
  have := congrArg (fun M => M.map σ) h'
  simpa [ratPt, conjT, Matrix.map_mul, Matrix.transpose_map] using this

open scoped Classical in
open Classical in
def tauPt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ := fun σ =>
  if σ = τ then B.val else if σ = ComplexEmbedding.conjugate τ then (B⁻¹).valᵀ else 1

theorem evPt_eq_upt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) :
    Formalism.L2.NG.evPt τ B = upt (tauPt τ B) := by
  funext p
  simp only [Formalism.L2.NG.evPt, upt, tauPt]
  split_ifs <;> simp [Matrix.one_apply, *]

theorem isUPt_tauPt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : IsUPt (tauPt τ B) := by
  intro σ
  have hne := conjugate_ne_self τ
  by_cases h1 : σ = τ
  · subst h1
    simp [tauPt, hne, Matrix.transpose_transpose]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      simp only [tauPt, if_neg h1, conj_conj, if_true]
      rw [← Matrix.transpose_transpose (B.val), ← Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
    · have h3 : ComplexEmbedding.conjugate σ ≠ τ := fun e => h2 (by rw [← e, conj_conj])
      have h4 : ComplexEmbedding.conjugate σ ≠ ComplexEmbedding.conjugate τ := fun e => h1 (by
        simpa using congrArg ComplexEmbedding.conjugate e)
      simp [tauPt, h1, h2, h3, h4]

end GlobalTheory.AlgWtHW
end
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem span_ratPt_orbit : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ v : ι → ℂ, v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ x = evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) *ᵥ v} := by
  intro L _ _ _ n a ι _ _ b P hA v hv w
  classical
  set x : a.W := b.equivFun.symm v with hx
  have hxv : b.repr x = v := by
    rw [← Module.Basis.equivFun_apply, hx, LinearEquiv.apply_symm_apply]
  have hx0 : x ≠ 0 := by
    intro h
    apply hv
    rw [← hxv, h, map_zero]
    rfl
  let S0 : Submodule ℂ a.W := Submodule.span ℂ (Set.range fun γ : GQ L n => a.ρ γ x)
  have hinv : ∀ (g : GQ L n) (y : a.W), y ∈ S0 → a.ρ g y ∈ S0 := by
    intro g y hy
    have hle : S0 ≤ S0.comap (a.ρ g) := by
      rw [Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      show a.ρ g (a.ρ γ x) ∈ S0
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨g * γ, rfl⟩
    exact hle hy
  let S : Subrepresentation a.ρ := ⟨S0, hinv⟩
  have hxS : x ∈ S0 := Submodule.subset_span ⟨1, by simp⟩
  have hS0 : S0 = ⊤ := by
    haveI := a.irr
    rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hx0
      have h2 : S.toSubmodule = (⊥ : Subrepresentation a.ρ).toSubmodule := congrArg _ h
      have h3 : x ∈ (⊥ : Subrepresentation a.ρ).toSubmodule := h2 ▸ hxS
      change x ∈ (⊥ : Submodule ℂ a.W) at h3
      exact (Submodule.mem_bot ℂ).1 h3
    · have h2 : S.toSubmodule = (⊤ : Subrepresentation a.ρ).toSubmodule := congrArg _ h
      exact h2
  have hw : w = b.equivFun.toLinearMap (b.equivFun.symm w) := (b.equivFun.apply_symm_apply w).symm
  have hmem : b.equivFun.symm w ∈ S0 := by rw [hS0]; trivial
  rw [hw]
  have hmap : Submodule.map b.equivFun.toLinearMap S0 ≤ Submodule.span ℂ {x | ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ x = evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) *ᵥ v} := by
    rw [Submodule.map_span_le]
    rintro _ ⟨γ, rfl⟩
    apply Submodule.subset_span
    have hγ : (γ : GA L n) ∈ ((GQ0 L n).map (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L))).subgroupOf (GA L n) := γ.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hγ
    obtain ⟨γ₀, hγ₀, he⟩ := hγ
    refine ⟨γ₀, hγ₀, ?_⟩
    have hE : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
      rw [← he]; rfl
    have hM := hA γ γ₀ hE
    show b.equivFun (a.ρ γ x) = _
    rw [Module.Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr b b, hxv, hM]
    rfl
  exact hmap (Submodule.mem_map_of_mem hmem)

end GlobalTheory.AlgWtHW
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW.DomLEOfSle

noncomputable def diagU {n : ℕ} (u : Fin n → ℂˣ) : GL (Fin n) ℂ :=
  ⟨Matrix.diagonal (fun i => (u i : ℂ)), Matrix.diagonal (fun i => ((u i)⁻¹ : ℂˣ)),
    by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩

lemma diag_commute {n : ℕ} (D E : GL (Fin n) ℂ) (hD : D.val.IsDiag) (hE : E.val.IsDiag) :
    D * E = E * D := by
  ext1
  simp only [Units.val_mul]
  rw [← hD.diagonal_diag, ← hE.diagonal_diag, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

lemma two_zpow_inj {a b : ℤ} (h : (2 : ℂ) ^ a = (2 : ℂ) ^ b) : a = b := by
  have h' : ((2 : ℝ) ^ a : ℝ) = (2 : ℝ) ^ b := by
    have := congrArg Complex.re h
    have ha : ((2 : ℂ) ^ a) = (((2 : ℝ) ^ a : ℝ) : ℂ) := by push_cast; rfl
    have hb : ((2 : ℂ) ^ b) = (((2 : ℝ) ^ b : ℝ) : ℂ) := by push_cast; rfl
    rw [ha, hb] at h
    exact_mod_cast h
  exact zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) h'

end GlobalTheory.AlgWtHW.DomLEOfSle

namespace GlobalTheory.AlgWtHW.DomLEOfSle

theorem domLE_of_mem_Sle : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (μ lam : Fin n → ℤ) (w : ι → ℂ),
    IsWtVec Φ μ w → w ≠ 0 → w ∈ Sle Φ lam → DomLE μ lam := by
  intro n ι _ _ Φ hΦ μ lam w hw hw0 hS
  by_contra hnot
  let J := {D : GL (Fin n) ℂ // D.val.IsDiag}
  let T : J → Module.End ℂ (ι → ℂ) := fun D => Matrix.toLin' (Φ D.1)
  have hc : ∀ a b : J, Commute (T a) (T b) := by
    intro a b
    show T a * T b = T b * T a
    have e : ∀ A B : Matrix ι ι ℂ, Matrix.toLin' A * Matrix.toLin' B = Matrix.toLin' (A * B) :=
      fun A B => by rw [Matrix.toLin'_mul]; rfl
    simp only [T]
    rw [e, e, ← hΦ.mul, ← hΦ.mul, diag_commute a.1 b.1 a.2 b.2]
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
  let χ : (Fin n → ℤ) → J → ℂ := fun ν D => ∏ i, (D.1.val i i) ^ (ν i)
  let E : (J → ℂ) → Submodule ℂ (ι → ℂ) := fun c => ⨅ D, (T D).maxGenEigenspace (c D)
  have hmem : ∀ ν v, IsWtVec Φ ν v → v ∈ E (χ ν) := by
    intro ν v hv
    refine Submodule.mem_iInf _ |>.mpr fun D => ?_
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff]
    simp only [T, Matrix.toLin'_apply]
    exact hv D.1 D.2
  have hχinj : ∀ ν ν', χ ν = χ ν' → ν = ν' := by
    intro ν ν' h
    funext i
    let u : Fin n → ℂˣ := Function.update 1 i (Units.mk0 2 two_ne_zero)
    have hD : (diagU u).val.IsDiag := by
      show (Matrix.diagonal _).IsDiag
      exact Matrix.isDiag_diagonal _
    have key := congrFun h ⟨diagU u, hD⟩
    have hprod : ∀ ν'' : Fin n → ℤ, χ ν'' ⟨diagU u, hD⟩ = (2 : ℂ) ^ (ν'' i) := by
      intro ν''
      simp only [χ, diagU, Matrix.diagonal_apply_eq]
      rw [Finset.prod_eq_single i]
      · simp [u]
      · intro j _ hj
        simp [u, Function.update_of_ne hj]
      · simp
    rw [hprod, hprod] at key
    exact two_zpow_inj key
  have hle : Sle Φ lam ≤ ⨆ (c : J → ℂ) (_ : c ≠ χ μ), E c := by
    unfold Sle
    rw [Submodule.span_le]
    rintro v ⟨ν, hν, hv⟩
    have hne : χ ν ≠ χ μ := by
      intro h
      have := hχinj _ _ h
      subst this
      exact hnot hν
    exact (le_iSup₂ (f := fun (c : J → ℂ) (_ : c ≠ χ μ) => E c) (χ ν) hne) (hmem ν v hv)
  have hdis := hind (χ μ)
  have h1 : w ∈ E (χ μ) := hmem μ w hw
  have h2 : w ∈ ⨆ (c : J → ℂ) (_ : c ≠ χ μ), E c := hle hS
  exact hw0 ((Submodule.disjoint_def.mp hdis) w h1 h2)

end GlobalTheory.AlgWtHW.DomLEOfSle
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory

theorem isWt_comp_swap : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ),
    IsPolyRep Φ → ∀ μ : Fin n → ℤ, IsWt Φ μ → ∀ i j : Fin n, IsWt Φ (μ ∘ Equiv.swap i j) := by
  intro n ι _ _ Φ hΦ μ ⟨w, hw0, hw⟩ i j
  set σ : Equiv.Perm (Fin n) := Equiv.swap i j with hσ
  set P : Matrix (Fin n) (Fin n) ℂ := σ.toPEquiv.toMatrix with hP
  have hσσ : ∀ k, σ (σ k) = k := fun k => Equiv.swap_apply_self _ _ _
  have hPP : P * P = 1 := by
    rw [hP, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
    have : σ.trans σ = Equiv.refl _ := by ext k; simp [hσσ]
    rw [this, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  let p : GL (Fin n) ℂ := ⟨P, P, hPP, hPP⟩
  have hpp : p * p = 1 := Units.ext hPP
  refine ⟨Φ p *ᵥ w, ?_, ?_⟩
  · intro h
    apply hw0
    have : Φ p *ᵥ (Φ p *ᵥ w) = 0 := by rw [h]; simp
    rwa [mulVec_mulVec, ← hΦ.mul, hpp, hΦ.one, one_mulVec] at this
  · intro D hD
    have hent : ∀ a b, (p * D * p).val a b = D.val (σ a) (σ b) := by
      intro a b
      show (P * D.val * P) a b = _
      rw [hP, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
      simp [hσ, Equiv.symm_swap]
    have hD' : (p * D * p).val.IsDiag := by
      intro a b hab
      rw [hent]
      exact hD (fun h => hab (σ.injective h))
    have key : Φ D * Φ p = Φ p * Φ (p * D * p) := by
      rw [← hΦ.mul, ← hΦ.mul]
      congr 1
      rw [← mul_assoc, ← mul_assoc, hpp, one_mul]
    have hprod : (∏ k, (p * D * p).val k k ^ μ k) = ∏ k, D.val k k ^ (μ ∘ σ) k := by
      simp only [hent, Function.comp]
      rw [← Equiv.prod_comp σ (fun k => D.val k k ^ μ (σ k))]
      simp [hσσ]
    rw [mulVec_mulVec, key, ← mulVec_mulVec, hw _ hD', hprod, mulVec_smul]
end GlobalTheory
end

section

open Matrix GlobalTheory.AlgWtHW

noncomputable section

namespace GlobalTheory.AlgWtHW

def diagGLOfNeZero {n : ℕ} (d : Fin n → ℂ) (h : ∀ i, d i ≠ 0) : GL (Fin n) ℂ :=
  ⟨diagonal d, diagonal d⁻¹, by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; simp [h i],
   by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; simp [h i]⟩

theorem diagGLOfNeZero_val {n : ℕ} (d : Fin n → ℂ) (h : ∀ i, d i ≠ 0) :
    (diagGLOfNeZero d h).val = diagonal d := rfl

theorem diagGLOfNeZero_inv_val {n : ℕ} (d : Fin n → ℂ) (h : ∀ i, d i ≠ 0) :
    ((diagGLOfNeZero d h)⁻¹).val = diagonal d⁻¹ := rfl

theorem diagGLOfNeZero_mul {n : ℕ} (s t : Fin n → ℂ) (hs : ∀ i, s i ≠ 0) (ht : ∀ i, t i ≠ 0) :
    diagGLOfNeZero (s * t) (fun i => mul_ne_zero (hs i) (ht i)) = diagGLOfNeZero s hs * diagGLOfNeZero t ht := by
  ext1; simp [diagGLOfNeZero_val, diagonal_mul_diagonal]

theorem exists_isWt_of_isPolyRep : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∃ μ : Fin n → ℤ, IsWt Φ μ := by
  intro n ι _ _ _ Φ hΦ
  classical
  let T : {D : GL (Fin n) ℂ // D.val.IsDiag} → (ι → ℂ) →ₗ[ℂ] (ι → ℂ) :=
    fun D => Matrix.toLin' (Φ D.1)
  have hcomm : ∀ D D' : {D : GL (Fin n) ℂ // D.val.IsDiag}, D.1 * D'.1 = D'.1 * D.1 := by
    intro D D'
    ext1
    have h1 := D.2.diagonal_diag
    have h2 := D'.2.diagonal_diag
    rw [Units.val_mul, Units.val_mul, ← h1, ← h2, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext i; ring
  have hT : ∀ i j x, T i (T j x) = T j (T i x) := by
    intro i j x
    simp only [T, Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hΦ.mul, ← hΦ.mul, hcomm]
  obtain ⟨v, -, hv0, hv⟩ := GlobalTheory.exists_common_eigenvector_mem T hT ⊤ top_ne_bot
    (fun _ _ _ => Submodule.mem_top)
  choose c hc using hv
  have hc' : ∀ (D : GL (Fin n) ℂ) (hD : D.val.IsDiag), Φ D *ᵥ v = c ⟨D, hD⟩ • v := by
    intro D hD
    simpa [T] using hc ⟨D, hD⟩
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (funext h)
  have cancel : ∀ x y : ℂ, x • v = y • v → x = y := by
    intro x y h
    have := congrFun h a
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ ha this
  let χ : (Fin n → ℂ) → ℂ := fun d =>
    if h : ∀ i, d i ≠ 0 then (Φ (diagGLOfNeZero d h) *ᵥ v) a / v a else 0
  have hχ : ∀ d (h : ∀ i, d i ≠ 0), Φ (diagGLOfNeZero d h) *ᵥ v = χ d • v := by
    intro d h
    have e := hc' (diagGLOfNeZero d h) (by rw [diagGLOfNeZero_val]; exact isDiag_diagonal d)
    rw [e]
    congr 1
    simp only [χ, dif_pos h, e, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ ha]
  have h1 : χ 1 = 1 := by
    have e : diagGLOfNeZero (1 : Fin n → ℂ) (fun _ => one_ne_zero) = 1 := by
      ext1; simp [diagGLOfNeZero_val]
    refine cancel _ _ ?_
    rw [← hχ 1 (fun _ => one_ne_zero), e, hΦ.one, one_mulVec, one_smul]
  have hmul : ∀ s t : Fin n → ℂ, (∀ i, s i ≠ 0) → (∀ i, t i ≠ 0) → χ (s * t) = χ s * χ t := by
    intro s t hs ht
    refine cancel _ _ ?_
    rw [← hχ (s * t) (fun i => mul_ne_zero (hs i) (ht i)), diagGLOfNeZero_mul s t hs ht, hΦ.mul,
      ← mulVec_mulVec, hχ t ht, mulVec_smul, hχ s hs, smul_smul, mul_comm]
  choose Q hQ using hΦ.poly
  have hline : ∀ i : Fin n, ∃ k : ℤ, ∀ t : ℂ, t ≠ 0 → χ (Pi.mulSingle i t) = t ^ k := by
    intro i
    have nz : ∀ t : ℂ, t ≠ 0 → ∀ j, (Pi.mulSingle i t : Fin n → ℂ) j ≠ 0 := by
      intro t ht j
      by_cases hj : j = i
      · subst hj; simp [ht]
      · simp [Pi.mulSingle_eq_of_ne hj]
    let g : (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ → ℂ :=
      Sum.elim (fun q t => diagonal (Pi.mulSingle i t : Fin n → ℂ) q.1 q.2)
        (fun q t => diagonal (Pi.mulSingle i t⁻¹ : Fin n → ℂ) q.1 q.2)
    have hg : ∀ s, ∃ (N : ℕ) (p : Polynomial ℂ), ∀ t : ℂ, t ≠ 0 → t ^ N * g s t = p.eval t := by
      rintro (⟨q1, q2⟩ | ⟨q1, q2⟩)
      · refine ⟨0, if q1 = q2 then (if q1 = i then Polynomial.X else 1) else 0, fun t ht => ?_⟩
        simp only [g, Sum.elim_inl, diagonal_apply, Pi.mulSingle_apply]
        split_ifs <;> simp
      · refine ⟨1, if q1 = q2 then (if q1 = i then 1 else Polynomial.X) else 0, fun t ht => ?_⟩
        simp only [g, Sum.elim_inr, diagonal_apply, Pi.mulSingle_apply]
        split_ifs <;> simp [ht]
    have hent : ∀ (t : ℂ) (ht : t ≠ 0) (b c : ι),
        Φ (diagGLOfNeZero (Pi.mulSingle i t) (nz t ht)) b c = MvPolynomial.eval (fun s => g s t) (Q b c) := by
      intro t ht b c
      rw [hQ]
      refine congrArg (fun x => MvPolynomial.eval x (Q b c)) ?_
      funext s
      rcases s with ⟨q1, q2⟩ | ⟨q1, q2⟩
      · simp [g, diagGLOfNeZero_val]
      · have hinv : (Pi.mulSingle i t : Fin n → ℂ)⁻¹ = Pi.mulSingle i t⁻¹ := by
          funext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Pi.mulSingle_eq_of_ne hj]
        simp only [g, Sum.elim_inr, diagGLOfNeZero_inv_val, hinv]
    let g2 : ι → ℂ → ℂ := fun c t => MvPolynomial.eval (fun s => g s t) (Q a c)
    obtain ⟨N, p, hp⟩ := GlobalTheory.T.exists_pow_mul_mvEval_eq_eval_of_laurent ι g2 (fun c => GlobalTheory.T.exists_pow_mul_mvEval_eq_eval_of_laurent _ g hg (Q a c))
      (∑ c, MvPolynomial.C (v c) * MvPolynomial.X c)
    refine GlobalTheory.T.exists_zpow_of_multiplicative_of_pow_mul_eq_eval (fun t => χ (Pi.mulSingle i t)) ?_ ?_ N (Polynomial.C (v a)⁻¹ * p) ?_
    · intro s t hs ht
      show χ (Pi.mulSingle i (s * t)) = χ (Pi.mulSingle i s) * χ (Pi.mulSingle i t)
      rw [Pi.mulSingle_mul]
      exact hmul _ _ (nz s hs) (nz t ht)
    · simpa using h1
    · intro t ht
      have e1 := congrFun (hχ _ (nz t ht)) a
      simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, hent t ht] at e1
      have e2 := hp t ht

      simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, g2] at e2
      have e3 : (∑ c, v c * MvPolynomial.eval (fun s => g s t) (Q a c)) =
          χ (Pi.mulSingle i t) * v a := by
        rw [← e1]; exact Finset.sum_congr rfl fun c _ => mul_comm _ _
      rw [e3] at e2
      simp only [Polynomial.eval_mul, Polynomial.eval_C, ← e2]
      field_simp
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.exists_monomial_of_multiplicative_of_single_eq_zpow n χ h1 hmul hline
  refine ⟨μ, v, hv0, fun D hD => ?_⟩
  have hd : ∀ i, D.val i i ≠ 0 := by
    intro i h0
    have hdet : D.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 D.isUnit).ne_zero
    rw [← hD.diagonal_diag, det_diagonal] at hdet
    exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have eD : D = diagGLOfNeZero (fun i => D.val i i) hd := by
    ext1
    rw [diagGLOfNeZero_val]
    exact hD.diagonal_diag.symm
  conv_lhs => rw [eD]
  rw [hχ _ hd, hμ _ hd]

end GlobalTheory.AlgWtHW
end
end

section

open Metric Filter Topology Set

theorem _root_.GlobalTheory.T.exists_differentiableOn_ext_of_bounded_off_hyperplane : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z := by
  first | exact @GlobalTheory.riemann_extension_coordinate_hyperplane | exact GlobalTheory.riemann_extension_coordinate_hyperplane | (intros; apply GlobalTheory.riemann_extension_coordinate_hyperplane <;> assumption)
end
