module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle272
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle032
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle167
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle187
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle200
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle246
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle183
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle129
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle207
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle271
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle212
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle127
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle258
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle273
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.MainNotions.N

namespace GlobalTheory.TraceSemisimple

theorem trace_nondegenerate_of_isSSRep {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ}
    (ρ : Γ →* GL (Fin n) k) (hρ : IsSSRep ρ) (x : Matrix (Fin n) (Fin n) k) (hx : x ∈ spanAlg ρ)
    (htr : ∀ g, (x * ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).trace = 0) : x = 0 := by
  first
  | (rename_i h_2 h_3 h_4; revert Γ k h_2 h_3 h_4 n ρ hρ x hx htr; exact @_root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate)
  | exact @_root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate
  | exact _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate
  | (apply _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate <;> assumption)
  | (intros; apply _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate ..)

theorem isSSRep_mapRep :
    ∀ (Γ k k' : Type) [Group Γ] [Field k] [Field k'] [CharZero k] (ι : k →+* k') (n : ℕ)
      (ρ : Γ →* GL (Fin n) k), IsSSRep ρ → IsSSRep (mapRep ι ρ) := by
  intro Γ k k' _ _ _ _ ι n ρ hρ
  let _ : Algebra k k' := ι.toAlgebra
  have hφι : ∀ (φ : k' →ₗ[k] k) (c : k') (r : k), φ (c * ι r) = φ c * r := by
    intro φ c r
    rw [mul_comm c, mul_comm (φ c), ← smul_eq_mul r, ← map_smul]
    rfl
  have hent : ∀ g i j, ((mapRep ι ρ g : GL (Fin n) k') : Matrix (Fin n) (Fin n) k') i j =
      ι (((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) := fun _ _ _ => rfl
  apply isSSRep_of_trace_nondegenerate
  intro x hx htr
  have hmem : ∀ φ : k' →ₗ[k] k, x.map φ ∈ spanAlg ρ := by
    clear htr
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      intro φ
      have : ((mapRep ι ρ g : GL (Fin n) k') : Matrix (Fin n) (Fin n) k').map φ =
          φ 1 • ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
        ext i j
        rw [Matrix.map_apply, hent, Matrix.smul_apply, smul_eq_mul, ← hφι, one_mul]
      rw [this]
      exact (spanAlg ρ).smul_mem (Submodule.subset_span ⟨g, rfl⟩) _
    | zero =>
      intro φ
      have : (0 : Matrix (Fin n) (Fin n) k').map φ = 0 := by ext i j; simp
      rw [this]; exact zero_mem _
    | add y z _ _ hy hz =>
      intro φ
      have : (y + z).map φ = y.map φ + z.map φ := by ext i j; simp
      rw [this]; exact add_mem (hy φ) (hz φ)
    | smul c y _ hy =>
      intro φ
      exact hy (φ ∘ₗ LinearMap.mulLeft k c)
  have hzero : ∀ φ : k' →ₗ[k] k, x.map φ = 0 := by
    intro φ
    refine trace_nondegenerate_of_isSSRep ρ hρ _ (hmem φ) fun g => ?_
    have := congrArg φ (htr g)
    rw [map_zero] at this
    rw [← this]

    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, hent, hφι, Matrix.map_apply]
  ext i j
  rw [Matrix.zero_apply, ← Module.forall_dual_apply_eq_zero_iff k]
  intro φ
  exact congrFun (congrFun (hzero φ) i) j

end GlobalTheory.TraceSemisimple
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem extPeriodMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → ∀ (Q₁ : GL a (Bst P)) (Q₂ : GL b (Bst P)), (∀ g : ↥(GK K), (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁) → (∀ g : ↥(GK K), (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂) → ∀ v : a × b → Bst P, (∀ g : ↥(GK K), (fun i => ks P (extCoc ρ₂ c g i)) = ((homRep ρ₁ ρ₂ g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (v i)) - v) → ∃ Q : GL (a ⊕ b) (Bst P), ∀ g : ↥(GK K), (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix (a ⊕ b) (a ⊕ b) (Bst P)).map (actSt P (g : GQ l)) = Q := by
  intro l _ P a b _ _ _ _ K ρ ρ₁ ρ₂ c hρ Q₁ Q₂ h₁ h₂ v hv
  let β : Matrix a b (Bst P) := Matrix.of fun i j => v (i, j)
  have hvβ : v = vecM β := rfl
  let Qm : Matrix (a ⊕ b) (a ⊕ b) (Bst P) :=
    Matrix.fromBlocks (Q₁ : Matrix a a (Bst P)) (-(β * (Q₂ : Matrix b b (Bst P)))) 0 (Q₂ : Matrix b b (Bst P))
  let Qi : Matrix (a ⊕ b) (a ⊕ b) (Bst P) :=
    Matrix.fromBlocks ((Q₁⁻¹ : GL a (Bst P)) : Matrix a a (Bst P)) (((Q₁⁻¹ : GL a (Bst P)) : Matrix a a (Bst P)) * β) 0
      ((Q₂⁻¹ : GL b (Bst P)) : Matrix b b (Bst P))
  have hQ : Qm * Qi = 1 := by
    simp only [Qm, Qi, Matrix.fromBlocks_multiply, Units.mul_inv, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      ← Matrix.mul_assoc, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_assoc β, Units.mul_inv, Matrix.mul_one,
      add_neg_cancel, Matrix.fromBlocks_one]
  have hQ' : Qi * Qm = 1 := by
    simp only [Qm, Qi, Matrix.fromBlocks_multiply, Units.inv_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_neg, ← Matrix.mul_assoc, neg_add_cancel, neg_zero, Matrix.fromBlocks_one]
  refine ⟨⟨Qm, Qi, hQ, hQ'⟩, fun g => ?_⟩
  set σ : Bst P →+* Bst P := (actSt P (g : GQ l)).toRingHom with hσ
  have hσc : ⇑(actSt P (g : GQ l)) = ⇑σ := rfl
  have hc : ((c g * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l))).map (ks P)) =
      (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * β.map σ * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) - β := by
    apply vecM_injective
    have h := hv g
    rw [homRep_apply, hvβ] at h
    have e1 : (fun i => actSt P (g : GQ l) (vecM β i)) = vecM (β.map σ) := rfl
    rw [e1, homUnit_mulVec] at h
    exact h
  have hR : (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ2 : (Q₂ : Matrix b b (Bst P)).map σ =
      (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)) := by
    calc (Q₂ : Matrix b b (Bst P)).map σ
        = ((((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P)) *
            (Q₂ : Matrix b b (Bst P)).map σ := by rw [hR, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc]; exact congrArg _ (h₂ g)
  have hC : (c g).map (ks P) * (Q₂ : Matrix b b (Bst P)).map σ =
      ((ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * β.map σ * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) - β) *
        (Q₂ : Matrix b b (Bst P)) := by
    rw [hQ2, ← hc, Matrix.map_mul, Matrix.mul_assoc]
  show (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map (ks P) * Qm.map σ = Qm
  rw [hρ g]
  simp only [Qm, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_zero _ (map_zero _), Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]
  have e1 := h₁ g
  have e2 := h₂ g
  rw [hσc] at e1 e2
  rw [e1, e2]
  congr 1
  rw [Matrix.map_neg _ (map_neg σ), Matrix.map_mul, hC, hQ2]
  simp only [Matrix.sub_mul, Matrix.mul_neg, Matrix.mul_assoc]
  abel

end GlobalTheory.PMon
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem kroneckerMap_mul_map_ringHom {R S : Type*} [CommRing R] [CommRing S] {a b : Type*} (f : R →+* S)
    (A : Matrix a a R) (B : Matrix b b R) :
    (Matrix.kroneckerMap (· * ·) A B).map f = Matrix.kroneckerMap (· * ·) (A.map f) (B.map f) := by
  ext p q
  simp [Matrix.kroneckerMap_apply]

theorem inv_periodMatrix_map_mul_eq_inv {S T : Type*} [CommRing S] [CommRing T] {b : Type*} [Fintype b] [DecidableEq b]
    (k : S →+* T) (σ : T →+* T) (r : GL b S) (Q : GL b T)
    (h : (r : Matrix b b S).map k * (Q : Matrix b b T).map σ = Q) :
    ((Q⁻¹ : GL b T) : Matrix b b T).map σ * ((r⁻¹ : GL b S) : Matrix b b S).map k = ((Q⁻¹ : GL b T) : Matrix b b T) := by
  have hQ : (Q : Matrix b b T) * (((Q⁻¹ : GL b T) : Matrix b b T).map σ * ((r⁻¹ : GL b S) : Matrix b b S).map k) = 1 := by
    rw [← h, Matrix.mul_assoc, ← Matrix.mul_assoc ((Q : Matrix b b T).map σ), ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.one_mul, ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero k) (map_one k)]
  calc ((Q⁻¹ : GL b T) : Matrix b b T).map σ * ((r⁻¹ : GL b S) : Matrix b b S).map k
      = ((Q⁻¹ : GL b T) : Matrix b b T) * (Q : Matrix b b T) *
          (((Q⁻¹ : GL b T) : Matrix b b T).map σ * ((r⁻¹ : GL b S) : Matrix b b S).map k) := by
        rw [Units.inv_mul, Matrix.one_mul]
    _ = ((Q⁻¹ : GL b T) : Matrix b b T) := by rw [Matrix.mul_assoc, hQ, Matrix.mul_one]

theorem homUnit_period : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (Q₁ : GL a (Bst P)) (Q₂ : GL b (Bst P)), (∀ g : ↥(GK K), (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁) → (∀ g : ↥(GK K), (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂) → ∀ g : ↥(GK K), (homRep ρ₁ ρ₂ g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map (ks P) * ((homUnit Q₁ Q₂ : GL (a × b) (Bst P)) : Matrix (a × b) (a × b) (Bst P)).map (actSt P (g : GQ l)) = (homUnit Q₁ Q₂ : GL (a × b) (Bst P)) := by
  intro l _ P a b _ _ _ _ K ρ₁ ρ₂ Q₁ Q₂ h₁ h₂ g
  set σ : Bst P →+* Bst P := (actSt P (g : GQ l)).toRingHom with hσ
  have e : ∀ {n : Type} (M : Matrix n n (Bst P)), M.map (actSt P (g : GQ l)) = M.map σ := fun M => rfl
  have h1 := h₁ g
  have h2 := h₂ g
  rw [e] at h1 h2
  rw [e, homRep_apply, homUnit_val, homUnit_val, kroneckerMap_mul_map_ringHom, kroneckerMap_mul_map_ringHom, ← Matrix.mul_kronecker_mul, h1,
    Matrix.transpose_map, Matrix.transpose_map, ← Matrix.transpose_mul, inv_periodMatrix_map_mul_eq_inv (ks P) σ (ρ₂ g) Q₂ h2]

end GlobalTheory.PMon
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section
open Matrix

namespace GlobalTheory.PMon

theorem matrixHomRepresentationCocycleCoords_cocycle {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {G : Type*} [Group G] (ρ : G →* GL (a ⊕ b) R) (ρ₁ : G →* GL a R) (ρ₂ : G →* GL b R) (c : G → Matrix a b R)
    (hρ : ∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) R) = Matrix.fromBlocks (ρ₁ g : Matrix a a R) (c g) 0 (ρ₂ g : Matrix b b R))
    (g h : G) :
    extCoc ρ₂ c (g * h) = extCoc ρ₂ c g + ((homRep ρ₁ ρ₂ g : GL (a × b) R) : Matrix (a × b) (a × b) R).mulVec (extCoc ρ₂ c h) := by
  have hc : c (g * h) = (ρ₁ g : Matrix a a R) * c h + c g * (ρ₂ h : Matrix b b R) := by
    have := congrArg (fun M : GL (a ⊕ b) R => Matrix.toBlocks₁₂ (M : Matrix (a ⊕ b) (a ⊕ b) R)) (map_mul ρ g h)
    simp only [Units.val_mul, hρ, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂] at this
    simpa using this
  unfold extCoc
  rw [homRep_apply, homUnit_val, kronecker_transpose_mulVec]
  rw [hc, map_mul, _root_.mul_inv_rev, Units.val_mul]
  have h2 : (ρ₂ h : Matrix b b R) * (((ρ₂ h)⁻¹ : GL b R) : Matrix b b R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.add_mul, Matrix.mul_assoc (c g), ← Matrix.mul_assoc (ρ₂ h : Matrix b b R), h2, Matrix.one_mul]
  funext p
  simp only [vecM, Pi.add_apply, Matrix.add_apply, Matrix.mul_assoc]
  ring

theorem extCoc_rat_cont_cocycle : ∀ (l : ℕ) [Fact l.Prime] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r : ℕ) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → (∀ g i, fr l r (extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i) = extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i) ∧ (∀ i, Continuous fun g => ((extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i : ↥(MaximalUnramifiedExtension l)) : Om l)) ∧ (∀ g h, extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) (g * h) = extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g + (homRep (ρ₁.comp (Subgroup.inclusion (GK_le hK))) (ρ₂.comp (Subgroup.inclusion (GK_le hK))) g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).mulVec (extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) h)) := by
  intro l _ a b _ _ _ _ K K' hK r ρ ρ₁ ρ₂ c hrat hρ
  set ι := Subgroup.inclusion (GK_le hK) with hι
  have hent : ∀ g (i : a) (k : b), c g i k = (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i) (Sum.inr k) := by
    intro g i k; rw [hρ]; rfl
  have hinv : ∀ g (k j : b), (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)) k j =
      (ρ g⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr k) (Sum.inr j) := by
    intro g k j; rw [← map_inv, hρ]; rfl
  have hform : ∀ g (i : a × b), extCoc (ρ₂.comp ι) (fun g => c (ι g)) g i =
      ∑ k, (ρ (ι g) : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i.1) (Sum.inr k) *
        (ρ (ι g)⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr k) (Sum.inr i.2) := by
    intro g i
    simp only [extCoc, vecM, MonoidHom.comp_apply, Matrix.mul_apply, hent, hinv]
  have hcι : Continuous ι := Continuous.subtype_mk continuous_subtype_val _
  refine ⟨?_, ?_, ?_⟩
  · intro g i

    rw [hform, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hrat.rat, hrat.rat]
  · intro i
    have : (fun g => ((extCoc (ρ₂.comp ι) (fun g => c (ι g)) g i : ↥(MaximalUnramifiedExtension l)) : Om l)) = fun g =>
        ∑ k, (((ρ (ι g) : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i.1) (Sum.inr k) : ↥(MaximalUnramifiedExtension l)) : Om l) *
          (((ρ (ι g)⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr k) (Sum.inr i.2) : ↥(MaximalUnramifiedExtension l)) : Om l) := by
      funext g
      rw [hform]
      push_cast
      rfl
    rw [this]
    refine continuous_finsetSum _ fun k _ => ?_
    exact ((hrat.cont _ _).comp hcι).mul ((hrat.cont _ _).comp (continuous_inv.comp hcι))
  · intro g h
    exact matrixHomRepresentationCocycleCoords_cocycle (ρ.comp ι) (ρ₁.comp ι) (ρ₂.comp ι) (fun g => c (ι g)) (fun g => hρ (ι g)) g h

end GlobalTheory.PMon
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem isRat_homRep_restrict : ∀ (l : ℕ) [Fact l.Prime] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r : ℕ) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → IsRat r (homRep (ρ₁.comp (Subgroup.inclusion (GK_le hK))) (ρ₂.comp (Subgroup.inclusion (GK_le hK)))) := by
  intro l _ a b _ _ _ _ K K' hK r ρ ρ₁ ρ₂ c hρ hb
  set ι := Subgroup.inclusion (GK_le hK) with hι
  have e1 : ∀ g i j, (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) i j = (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i) (Sum.inl j) := by
    intro g i j; rw [hb]; rfl
  have e2 : ∀ g i j, (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)) i j = (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr i) (Sum.inr j) := by
    intro g i j; rw [hb]; rfl
  have key : ∀ g' p q, ((homRep (ρ₁.comp ι) (ρ₂.comp ι) g' : GL (a × b) ↥(MaximalUnramifiedExtension l)) : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)) p q =
      (ρ (ι g') : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl p.1) (Sum.inl q.1) *
        (ρ (ι g')⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr q.2) (Sum.inr p.2) := by
    intro g' p q
    rw [homRep_apply, homUnit_val, Matrix.kroneckerMap_apply, Matrix.transpose_apply, ← map_inv, MonoidHom.comp_apply,
      MonoidHom.comp_apply, e1, e2, map_inv ι]
  have hιc : Continuous ι := continuous_subtype_val.subtype_mk _
  refine ⟨hρ.pos, fun x hx => hK (hρ.le x hx), ?_, ?_⟩
  · intro g p q
    rw [key, map_mul, hρ.rat, hρ.rat]
  · intro p q
    simp only [key, IntermediateField.coe_mul]
    exact ((hρ.cont _ _).comp hιc).mul ((hρ.cont _ _).comp (hιc.inv))

end GlobalTheory.PMon
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

section Assembly

variable {K K' : UQ}

def prodEquiv (φ : K.E →+* K'.E) (B₁ B₂ : InvAlg K) (ψ : K'.E →+* (B₁.prod B₂).A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E (B₁.prod B₂).A e) (hσ : ∀ e, (B₁.prod B₂).σ (ψ e) = ψ (K'.c e)) :
    ((overExt φ B₁ ((RingHom.fst B₁.A B₂.A).comp ψ) (fun e => congrArg Prod.fst (hψ e))
        (fun e => congrArg Prod.fst (hσ e))).prod
      (overExt φ B₂ ((RingHom.snd B₁.A B₂.A).comp ψ) (fun e => congrArg Prod.snd (hψ e))
        (fun e => congrArg Prod.snd (hσ e)))).A ≃ₐ[K'.E] (overExt φ (B₁.prod B₂) ψ hψ hσ).A :=
  { RingEquiv.refl (B₁.A × B₂.A) with commutes' := fun _ => rfl }

theorem prodEquiv_isIso (φ : K.E →+* K'.E) (B₁ B₂ : InvAlg K) (ψ : K'.E →+* (B₁.prod B₂).A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E (B₁.prod B₂).A e) (hσ : ∀ e, (B₁.prod B₂).σ (ψ e) = ψ (K'.c e)) :
    Orbit.IsIso (prodEquiv φ B₁ B₂ ψ hψ hσ) :=
  ⟨fun _ => rfl, rfl⟩

theorem prod_unitary (B₁ B₂ : InvAlg K) (hu₁ : B₁.g * B₁.σ B₁.g = 1) (hu₂ : B₂.g * B₂.σ B₂.g = 1) :
    (B₁.prod B₂).g * (B₁.prod B₂).σ (B₁.prod B₂).g = 1 :=
  Prod.ext hu₁ hu₂

theorem prod_integral (B₁ B₂ : InvAlg K) (hi₁ : IsIntegral K.O B₁.g) (hi₂ : IsIntegral K.O B₂.g) :
    IsIntegral K.O (B₁.prod B₂).g := by
  obtain ⟨p₁, hp₁, e₁⟩ := hi₁
  obtain ⟨p₂, hp₂, e₂⟩ := hi₂
  refine ⟨p₁ * p₂, hp₁.mul hp₂, ?_⟩
  rw [← aeval_def] at e₁ e₂ ⊢
  have h1 : (aeval (B₁.prod B₂).g (p₁ * p₂)).1 = aeval B₁.g (p₁ * p₂) :=
    (aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) (B₁.prod B₂).g (p₁ * p₂)).symm
  have h2 : (aeval (B₁.prod B₂).g (p₁ * p₂)).2 = aeval B₂.g (p₁ * p₂) :=
    (aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) (B₁.prod B₂).g (p₁ * p₂)).symm
  refine Prod.ext ?_ ?_
  · rw [h1, map_mul, e₁, zero_mul]; rfl
  · rw [h2, map_mul, e₂, mul_zero]; rfl

end Assembly

theorem unitLemma_local_of_lie : UnitLemmaLie → ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → InvAlg.Identity B₁ B₂ := by
  intro hL K hK B₁ B₂ hu₁ hu₂ hsep hi₁ hi₂ hl
  have hsepP : (B₁.prod B₂).P.Separable := by rw [Orbit.prod_P]; exact hsep
  have huP := prod_unitary B₁ B₂ hu₁ hu₂
  have hiP := prod_integral B₁ B₂ hi₁ hi₂
  obtain ⟨d, hd, hcard⟩ := GlobalTheory.T.card_residueField_adjoin_unitary_prod K hK B₁ B₂ hu₁ hu₂ hsep hi₁ hi₂ hl
  obtain ⟨K', φ, hq, hc, hv, hodd, hfin, hz⟩ := GlobalTheory.T.exists_unramified_odd_degree_quadratic_local_ext K d hd
  have hU : IsUnrExt K K' d φ := ⟨hq, hc, hv, hodd, hfin⟩
  obtain ⟨ψ, hψ, hσ, hO, s, hs, hres⟩ := GlobalTheory.T.exists_unramified_involution_field_embedding K hK (B₁.prod B₂) huP hsepP hiP hl d hcard K' φ hU hz
  obtain ⟨Q, hQ1, hQ2⟩ := GlobalTheory.T.charpoly_overExt_integral_reduction_pow K K' d φ hU (B₁.prod B₂) ψ hψ hσ hO hl hsepP hiP s hres
  have hiso := prodEquiv_isIso φ B₁ B₂ ψ hψ hσ
  set ψ₁ := (RingHom.fst B₁.A B₂.A).comp ψ with hψ₁
  set ψ₂ := (RingHom.snd B₁.A B₂.A).comp ψ with hψ₂
  have h₁ : ∀ e, ψ₁ (φ e) = algebraMap K.E B₁.A e := fun e => congrArg Prod.fst (hψ e)
  have h₁' : ∀ e, B₁.σ (ψ₁ e) = ψ₁ (K'.c e) := fun e => congrArg Prod.fst (hσ e)
  have h₂ : ∀ e, ψ₂ (φ e) = algebraMap K.E B₂.A e := fun e => congrArg Prod.snd (hψ e)
  have h₂' : ∀ e, B₂.σ (ψ₂ e) = ψ₂ (K'.c e) := fun e => congrArg Prod.snd (hσ e)
  set C₁ := overExt φ B₁ ψ₁ h₁ h₁' with hC₁
  set C₂ := overExt φ B₂ ψ₂ h₂ h₂' with hC₂
  have hPP : C₁.P * C₂.P = (overExt φ (B₁.prod B₂) ψ hψ hσ).P := by
    rw [← Orbit.prod_P, ← hiso.charpoly_eq_of_isIso]
  have hO₁ : ∀ y : K'.O, ψ₁ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B₁.g} : Set B₁.A) := by
    intro y
    have key : ∀ w ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
        (w : B₁.A × B₂.A).1 ∈ Algebra.adjoin K.O ({B₁.g} : Set B₁.A) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
      | algebraMap a => exact Subalgebra.algebraMap_mem _ a
      | add x z _ _ hx hz => exact add_mem hx hz
      | mul x z _ _ hx hz => exact mul_mem hx hz
    exact key _ (hO y)
  have hO₂ : ∀ y : K'.O, ψ₂ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B₂.g} : Set B₂.A) := by
    intro y
    have key : ∀ w ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
        (w : B₁.A × B₂.A).2 ∈ Algebra.adjoin K.O ({B₂.g} : Set B₂.A) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
      | algebraMap a => exact Subalgebra.algebraMap_mem _ a
      | add x z _ _ hx hz => exact add_mem hx hz
      | mul x z _ _ hx hz => exact mul_mem hx hz
    exact key _ (hO y)
  have hO' : ∀ y : K'.O, (ψ₁.prod ψ₂) (algebraMap K'.O K'.E y) ∈
      Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A) := fun y => hO y
  have hQ : ∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = C₁.P * C₂.P ∧
      Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O (s : K'.O))) ^ Q.natDegree :=
    ⟨Q, hQ1.trans hPP.symm, hQ2⟩

  have hsep' : (C₁.P * C₂.P).Separable := by
    rw [hPP]
    exact GlobalTheory.T.separable_charpoly_invAlgBaseChangeUnramified K K' d φ hU (B₁.prod B₂) ψ hψ hσ hsepP
  have hId := GlobalTheory.T.unitLemma_residually_unipotent_via_cayley hL K' (hodd hK) C₁ C₂ hu₁ hu₂ hsep' s hs hQ

  have hst : ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e)
      (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)),
      (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) →
      (overExt φ B ψ hψ hσ).stSum = B.stSum := by
    intro B ψ hψ hσ hO'
    unfold InvAlg.stSum
    exact finsum_congr fun k => GlobalTheory.T.unramifiedBaseChange_latticeCount_eq K K' d φ hU B ψ hψ hσ hO' _
  have hkap : InvAlg.kapSum C₁ C₂ = InvAlg.kapSum B₁ B₂ := by
    unfold InvAlg.kapSum
    refine finsum_congr fun k => ?_
    have hN : (C₁.prod C₂).N k.rep = (B₁.prod B₂).N k.rep := by
      rw [← hiso.N_eq]
      exact GlobalTheory.T.unramifiedBaseChange_latticeCount_eq K K' d φ hU (B₁.prod B₂) ψ hψ hσ hO _
    rw [hN]
    congr 1
    set x := (Quot.out k).1 with hx
    have hfix : B₁.σ ((x : (C₁.prod C₂).A).1) = (x : (C₁.prod C₂).A).1 := congrArg Prod.fst (Quot.out k).2
    let x₁ : B₁.Aˣ := Units.map (MonoidHom.fst B₁.A B₂.A) x
    have := GlobalTheory.T.eta_gramDet_invAlgBaseChangeUnramified_odd K K' d φ hU hd B₁ ψ₁ h₁ h₁' x₁ hfix
    exact this
  have hres' := GlobalTheory.T.val_resultant_eq_degree_mul_unramifiedExt K K' d φ hU hd B₁ B₂ ψ₁ ψ₂ h₁ h₁' h₂ h₂' hO' hsep s hQ
  unfold InvAlg.Identity at hId ⊢
  rw [hkap, hst B₁ ψ₁ h₁ h₁' hO₁, hst B₂ ψ₂ h₂ h₂' hO₂] at hId
  rw [← hId, hres', hq]
  congr 1
  obtain ⟨m, rfl⟩ := hd
  push_cast
  rw [show -((2 * (m : ℤ) + 1) * val K'.O (resultant C₁.P C₂.P)) =
      (2 * (m : ℤ) + 1) * (-val K'.O (resultant C₁.P C₂.P)) by ring, zpow_mul]
  congr 1
  rw [show (2 * (m : ℤ) + 1) = ((2 * m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, Odd.neg_pow ⟨m, rfl⟩]

end GlobalTheory.UnitLemma.Unr
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages

theorem _root_.GlobalTheory.T.isSubquotient_relativeJacquet_blockLevi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d : Fin s → ℕ) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (V W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (Levi k fun a => Fin (d a)) V)
    (τ : Representation ℂ (Levi k fun a => Fin (d a)) W),
    IsSmooth τ → IsSubquotient σ τ → IsSubquotient (relJacD e' σ) (relJacD e' τ) := by
  first | exact @GlobalTheory.JacStagesExact.isSubquotient_relJacD | exact GlobalTheory.JacStagesExact.isSubquotient_relJacD | (intros; apply GlobalTheory.JacStagesExact.isSubquotient_relJacD <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.blochKato_quotient_of_divisible_image_mem : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ HfD (P.PD K) LA → c ∈ HfQ (P.PD K) LA _ hI := by
  first | exact @GlobalTheory.BKFinLevelKer.hfQ_of_ioL_mem_HfD | exact GlobalTheory.BKFinLevelKer.hfQ_of_ioL_mem_HfD | (intros; apply GlobalTheory.BKFinLevelKer.hfQ_of_ioL_mem_HfD <;> assumption)
end
