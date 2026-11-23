module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle307
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
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

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem hk_comm_of {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    {K : Subgroup G} (hK : IsCommensurated K) {h : G → ℂ} (hh : h ∈ Hecke ℂ K) (A : Module.End ℂ V)
    (hA : ∀ g, Commute A (ρ g)) (x : V) : A (hkOp ρ hK hh x) = hkOp ρ hK hh (A x) :=
  map_heckeVec hK hh (ρ' := ρ) A (fun g y => LinearMap.congr_fun (hA g).eq y) x

theorem UpperTheory.V.Cj.S.opComm :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.OpComm := by
  intro hC E _ _ _ a T i i' φ hφ
  rcases i with ⟨t, u⟩ | ⟨⟨w, hw⟩, h, hh⟩ <;> rcases i' with ⟨t', u'⟩ | ⟨⟨w', hw'⟩, h', hh'⟩
  · exact LinearMap.congr_fun ((hC E a t u).2.2.2 t' u').eq φ
  · exact hk_comm_of (fL a w') (Final.GLintComm E w' a) hh' (cap t u) (fun g => (hC E a t u).1 _) φ
  · exact (hk_comm_of (fL a w) (Final.GLintComm E w a) hh (cap t' u') (fun g => (hC E a t' u').1 _) φ).symm
  · by_cases e : w = w'
    · subst e
      have hK := Final.GLintComm E w a
      change heckeVec (fL a w) (KGL w (n := a)) h (heckeVec (fL a w) (KGL w (n := a)) h' φ) =
        heckeVec (fL a w) (KGL w (n := a)) h' (heckeVec (fL a w) (KGL w (n := a)) h φ)
      rw [← SatCompare.heckeVec_conv hK hh hh' (hφ w hw), ← SatCompare.heckeVec_conv hK hh' hh (hφ w hw),
        Final.HeckeCommGL E w a ℂ h hh h' hh']
    · refine hk_comm_of (fL a w') (Final.GLintComm E w' a) hh' (hkOp (fL a w) (Final.GLintComm E w a) hh)
        (fun g => LinearMap.ext fun y => ?_) φ
      refine (hk_comm_of (fL a w) (Final.GLintComm E w a) hh (fL a w' g) (fun k => ?_) y).symm
      exact Commute.map (LocUniq.comm_locGL w (pLoc_locGL_of_ne e g) k) (finRep E a)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem cast_ne_nat {r s : ℕ} (i : Fin r) (j : Fin s) : Fin.castAdd s i ≠ Fin.natAdd r j := fun h => by
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

private theorem std_eq (r s : ℕ) : GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) = finSumFinEquiv :=
  Equiv.ext fun _ => rfl

open UpperTheory.V.Af.Fin in
private theorem lev_left {R : Type} [CommRing R] {r s : ℕ} (x : GL (Fin r) R) :
    GlobalTheory.CompanionTheory.CTFin.lev R r s (x, 1) = emb (e1 r s) x := by
  refine Units.ext ?_
  rw [GlobalTheory.SmGL.val_emb₂, coe_emb, std_eq]
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have := matrixExtendByZero_apply (e1 r s) (x.val - 1) i j
    simp only [orderedCechToCatCochainsOne_apply_valueAtSubset] at this
    simp [this, Matrix.one_apply]
  · rw [Matrix.add_apply, matrixExtendByZero_apply_of_outside_col _ _ _ fun k => (cast_ne_nat k j).symm]
    simp [Matrix.one_apply, cast_ne_nat]
  · rw [Matrix.add_apply, extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cast_ne_nat k i).symm]
    simp [Matrix.one_apply, (cast_ne_nat _ _).symm]
  · rw [Matrix.add_apply, extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cast_ne_nat k i).symm]
    simp [Matrix.one_apply]

open UpperTheory.V.Af.Fin in
private theorem lev_right {R : Type} [CommRing R] {r s : ℕ} (y : GL (Fin s) R) :
    GlobalTheory.CompanionTheory.CTFin.lev R r s (1, y) = emb (e2 r s) y := by
  refine Units.ext ?_
  rw [GlobalTheory.SmGL.val_emb₂, coe_emb, std_eq]
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Matrix.add_apply, extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => cast_ne_nat i k]
    simp [Matrix.one_apply]
  · rw [Matrix.add_apply, extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => cast_ne_nat i k]
    simp [Matrix.one_apply, cast_ne_nat]
  · rw [Matrix.add_apply, matrixExtendByZero_apply_of_outside_col _ _ _ fun k => cast_ne_nat j k]
    simp [Matrix.one_apply, (cast_ne_nat _ _).symm]
  · have := matrixExtendByZero_apply (e2 r s) (y.val - 1) i j
    simp only [alternatingToOrderedCechDegreeTwo_apply_valueAtSubset] at this
    simp [this, Matrix.one_apply]

private theorem lev_eq_blk {R : Type} [CommRing R] {r s : ℕ} (x : GL (Fin r) R) (y : GL (Fin s) R) :
    GlobalTheory.CompanionTheory.CTFin.lev R r s (x, y) = blk x y := by
  rw [blk, ← lev_left, ← lev_right, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem UpperTheory.V.Cj.S.capBlock :
    UpperTheory.V.Cj.S.CapBlock := by
  intro E _ _ _ r s ψ hψ t u x y
  have h := GlobalTheory.CompanionTheory.CTFin.CapFactor.cap_levi E r s t u ψ (fun X g => by
    have e : unip X = unipGL (fun p : UPos (r + s) r => X ⟨p.1, p.2.1, p.2.2⟩) := Units.ext rfl
    rw [e]
    exact hψ _ g) (x, y)
  rw [lev_eq_blk] at h
  exact h
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.capAct :
    UpperTheory.V.Cj.S.CapAct := by
  intro E _ _ _ a t u
  have h0 : ∀ w : Cm.UC E a, Commute (cap (a := a) t u) (Cm.uC E a w) := fun w => by
    rw [← Cm.uC_capC]
    exact Commute.map (Subalgebra.mem_center_iff.1 (Cm.capC_mem_center t u) w).symm (Cm.uC E a)
  have h1 : ∀ g, Commute (cap (a := a) t u) (rt E a g) := fun g =>
    GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg (Cm.cap_mem_Zalg t u) g
  refine ⟨h1, fun o => ?_, fun z => ?_, fun t' u' => ?_⟩
  · cases o with
    | fin k => exact h1 _
    | cpt k => exact h1 _
    | lie X =>
      have := h0 (Cm.ιC E a X)
      rw [Cm.uC_ιC] at this
      exact this
  · have := h0 (1 ⊗ₜ z)
    rwa [Cm.uC_tmul, one_smul] at this
  · have := h0 (Cm.capC t' u')
    rwa [Cm.uC_capC] at this
end
