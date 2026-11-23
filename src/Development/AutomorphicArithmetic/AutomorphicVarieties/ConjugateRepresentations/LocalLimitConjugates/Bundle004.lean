module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.locInt :
    UpperTheory.V.Cj.H.LocInt := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _
  refine ⟨fun F => ?_, fun C hC => ?_⟩
  · rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    exact (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact G Γ μ F K hK).2
  · have hfin := GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (Γ := Γ) (hC.mul hC.inv)
    refine ⟨hfin.toFinset.card, fun g => ?_⟩
    by_cases hne : {γ : Γ | ↑γ * g ∈ C}.Nonempty
    · obtain ⟨γ0, hγ0⟩ := hne
      calc {γ : Γ | ↑γ * g ∈ C}.encard ≤ {δ : Γ | ↑δ ∈ C * C⁻¹}.encard := by
            apply Set.encard_le_encard_of_injOn (f := fun γ => γ * γ0⁻¹)
            · intro γ hγ
              refine ⟨↑γ * g, hγ, (↑γ0 * g)⁻¹, Set.inv_mem_inv.2 hγ0, ?_⟩
              simp [mul_assoc]
            · intro a _ b _ h
              simpa using h
        _ = hfin.toFinset.card := hfin.encard_eq_coe_toFinset_card
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]
      simp
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

namespace UpperTheory.V.Cj.H.CasimirOperatorShift

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem comm_of_zalg {z o : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (ho : ∀ τ u, Commute (cap τ u) o) :
    Commute z o := by
  refine Algebra.adjoin_induction (p := fun x _ => Commute x o) ?_ (fun r => Algebra.commutes r _)
    (fun _ _ _ _ hx hy => hx.add_left hy) (fun _ _ _ _ hx hy => hx.mul_left hy) hz
  rintro _ ⟨τ, u, rfl⟩
  exact ho τ u

private theorem uC_sh (r : ℝ) (X : Lie E a) : Cm.uC E a (shift (Cm.ιC E a) r X) = shift (lie E a) r X := by
  rw [shift_apply, shift_apply, map_add (f := _), Cm.uC_ιC, ← algebraMap_smul ℂ (r * ell E a X) (1 : Cm.UC E a), map_smul,
    map_one, algebraMap_smul]

private theorem cas_mem {n : ℕ} {e : Fin n → Herm E a} (he : IsFrame e) (r : ℝ) :
    cas (shift (lie E a) r) e ∈ Zalg E a := by
  have hL : IsLieHom (shift (Cm.ιC E a) r) := (ellFacts E a).2.2.2 _ _ r Cm.isLieHom_ιC
  have hX : ∀ X, Commute (cas (shift (Cm.ιC E a) r) e) (Cm.ιC E a X) := fun X => by
    have h := casComm E a n e he _ _ hL X
    have h' : Cm.ιC E a X = shift (Cm.ιC E a) r X - (r * ell E a X) • 1 := by rw [shift_apply, add_sub_cancel_right]
    rw [h']
    exact h.sub_right ((Commute.one_right _).smul_right _)
  have hle : Algebra.adjoin ℂ {x : Cm.UC E a | ∃ τ i j, x = Cm.genC τ i j} ≤
      Subalgebra.centralizer ℂ {cas (shift (Cm.ιC E a) r) e} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, i, j, rfl⟩ _ rfl
    exact (((hX _).sub_right ((hX _).smul_right _)).smul_right _).eq
  rw [Cm.adjoin_genC] at hle
  rw [Cm.Zalg_eq_map]
  exact ⟨_, Subalgebra.mem_center_iff.2 fun x => (hle Algebra.mem_top _ rfl).symm,
    by simp only [cas, map_sum, map_sub, map_mul, uC_sh, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]⟩

private theorem cap_rt (τ : E →+* ℂ) (u : ℂ) (g : GA E a) : Commute (cap τ u) (rt E a g) := by
  rw [← infGL_mul_finGL g, map_mul]
  exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _).mul_right (commute_cap_finRep τ u _)

private theorem sh_apply (r : ℝ) (X : Lie E a) (φ : Sm E a) :
    shift (lie E a) r X φ = lie E a X φ + ((r * ell E a X : ℝ) : ℂ) • φ := by
  rw [shift_apply]; rfl

end UpperTheory.V.Cj.H.CasimirOperatorShift

open UpperTheory.V.Cj.H.CasimirOperatorShift in
theorem UpperTheory.V.Cj.H.casOp :
    UpperTheory.V.Cj.H.CasOp := by
  intro E _ _ _ a n e he r c
  have hz := cas_mem he r
  have hc : ∀ o : Module.End ℂ (Sm E a), (∀ τ u, Commute (cap τ u) o) → Commute o (casA r c e) := fun o ho =>
    (comm_of_zalg hz ho).symm.sub_right ((Commute.one_right _).smul_right _)
  refine ⟨fun X => hc _ fun τ u => commute_cap_lie τ u X, fun g => hc _ fun τ u => cap_rt τ u g, fun N hN => ?_⟩
  have hs : ∀ X, ∀ φ ∈ N, shift (lie E a) r X φ ∈ N := fun X φ hφ => by
    rw [sh_apply]
    exact N.add_mem (hN X φ hφ) (N.smul_mem _ hφ)
  refine ⟨fun φ hφ => ?_, fun T hT φ hφ => ?_⟩
  · simp only [casA, cas, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    exact N.sub_mem (N.sum_mem fun j _ => N.sub_mem (hs _ _ (hs _ _ hφ)) (hs _ _ (hs _ _ hφ))) (N.smul_mem _ hφ)
  · have ht : ∀ X, ∀ φ ∈ N, shift (lie E a) r X (T φ) = T (shift (lie E a) r X φ) := fun X φ hφ => by
      rw [sh_apply, sh_apply, hT.lie X φ hφ, map_add (f := _), map_smul]

    simp only [casA, cas, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_sum, map_smul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ht _ _ hφ, ht _ _ (hs _ _ hφ), ht _ _ hφ, ht _ _ (hs _ _ hφ)]
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem sm_sepDer (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) :
    SepDer (smK Ξ) (smLie Ξ) := by
  intro k Z h0 hk m' hm
  have h1 : ∃ j, Bor.cmp j m' ≠ 0 := by
    by_contra h
    push Not at h
    apply hm
    rw [← sum_cmp m']
    simp [h]
  obtain ⟨j, hj⟩ := h1
  have h2 : (Bor.cmp j m').1 ≠ 0 := fun h => hj (Subtype.ext h)
  obtain ⟨g, hg⟩ := Function.ne_iff.1 h2
  let l : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun m => (Bor.cmp j m).1 g
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hl : ∀ (φ : Sm E a) (v : Fin Ξ.d → ℂ), l (φ ⊗ₜ v) = φ.1 g * v j := fun φ v => by
    change (Bor.cmp j (φ ⊗ₜ v)).1 g = _
    rw [cmp_tmul, mul_comm]
    rfl
  have hc0 : (fun t => Unitary.toUnits (k t)) 0 = 1 := by simp only [h0, map_one]
  refine ⟨l, hg, fun m => ?_⟩
  induction m using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add x y hx hy => simpa only [map_add (f := _)] using hx.fun_add hy
  | tmul φ v =>
    have h3 := GlobalTheory.CuspRep.hasDerivAt_curve φ g (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk
    have h4 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (Ξ.hasDerivAt_curve (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk j i).mul_const (v i)
    have h5 := h3.fun_mul h4
    simp only [h0, map_one, mul_one] at h5
    have h7 : smLie Ξ (toL Z) (φ ⊗ₜ v) = lie E a (toL Z) φ ⊗ₜ v + φ ⊗ₜ (Ξ.dmat (toL Z) *ᵥ v) := rfl
    simp only [smK, h7, TensorProduct.map_tmul, map_add (f := _), hl, Matrix.toLin'_apply]
    have h6 : ∑ i, (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) j i * v i = v j := congrFun (Matrix.one_mulVec v) j
    rw [h6] at h5
    exact h5

theorem UpperTheory.V.Cj.H.smAB :
    UpperTheory.V.Cj.H.SmAB := by
  intro E _ _ _ a Ξ
  refine ⟨fun X Y => ?_, fun X Y => ?_, fun X Y => ?_, fun k X => ?_, fun k X => ?_,
    infAbs E a _ _ _ (sm_sepDer E a Ξ)⟩
  · simp only [smA_apply]
    rw [← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul, ← LinearMap.rTensor_sub]
    congr 1
    exact (lie_comm (toL X) (toL Y)).trans (map_sub (lie E a) (toL (X * Y)) (toL (Y * X))).symm
  · simp only [smB_apply]
    rw [← GlobalTheory.AlgInfChar.dmat_bracket, map_sub, LinearMap.lTensor_sub, Matrix.toLin'_mul, Matrix.toLin'_mul,
      LinearMap.lTensor_comp, LinearMap.lTensor_comp]
    rfl
  · rw [smA_apply, smB_apply]
    exact TensorProduct.ext' fun _ _ => rfl
  · refine TensorProduct.ext' fun φ v => ?_
    have h1 : act (.cpt k) (lie E a (toL X) φ) = lie E a (toL (k.1 * X * star k.1)) (act (.cpt k) φ) :=
      LinearMap.congr_fun (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) X) φ
    simp only [Module.End.mul_apply, smK, smA_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul, h1]
  · refine TensorProduct.ext' fun φ v => ?_
    have h2 : Ξ.mat (Unitary.toUnits k) * Ξ.dmat (toL X) =
        Ξ.dmat (toL (k.1 * X * star k.1)) * Ξ.mat (Unitary.toUnits k) :=
      Ξ.mat_mul_dmat (Unitary.toUnits k) X
    simp only [Module.End.mul_apply, smK, smB_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
      Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2]
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem mapQ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by

  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
  Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

private noncomputable def rAlg (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)) :=
  (Module.End.lTensorAlgHom ℂ (Fin d → ℂ) V).comp
    (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toAlgHom

private noncomputable def rOp (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] (Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)))ᵐᵒᵖ where
  toFun N := MulOpposite.op (rAlg V d Nᵀ)
  map_one' := by simp
  map_mul' x y := by simp [Matrix.transpose_mul]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.transpose_add]
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one]

private theorem rOp_apply (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) (N : Matrix (Fin d) (Fin d) ℂ) :
    rOp V d N = MulOpposite.op (rAlg V d Nᵀ) := rfl

private theorem qdet_stab {M : Type} [AddCommGroup M] [Module ℂ M] (N : Submodule ℂ M) {n : ℕ}
    (X : Fin n → Fin n → Module.End ℂ M) (h : ∀ i j, ∀ m ∈ N, X i j m ∈ N) (u : ℂ) :
    ∀ m ∈ N, Formalism.REAL.qdet X u m ∈ N := by
  let S : Subalgebra ℂ (Module.End ℂ M) :=
    { carrier := {z | ∀ m ∈ N, z m ∈ N}
      mul_mem' := fun hx hy m hm => hx _ (hy m hm)
      add_mem' := fun hx hy m hm => N.add_mem (hx m hm) (hy m hm)
      algebraMap_mem' := fun c m hm => N.smul_mem c hm }
  let Z : Fin n → Fin n → S := fun i j => ⟨X i j, h i j⟩
  have e : ((Formalism.REAL.qdet Z u : S) : Module.End ℂ M) = Formalism.REAL.qdet X u := mapQ S.val Z u
  rw [← e]
  exact (Formalism.REAL.qdet Z u).2

theorem UpperTheory.V.Cj.H.capSm :
    UpperTheory.V.Cj.H.CapSm := by
  intro E _ _ _ a Ξ τ u
  have hE : ∀ i j : Fin a, Eop (a := a) τ i j = eL (N := Module.End ℂ (Sm E a)) (lie E a) τ i j := fun _ _ => rfl
  have hc : cap (a := a) τ u = Formalism.REAL.qdet (Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2) := rfl
  refine ⟨?_, fun m hm => ?_, fun X => ?_, fun N hN => ?_⟩
  · let f : Module.End ℂ (Sm E a) →ₐ[ℂ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
      Module.End.rTensorAlgHom ℂ (Sm E a) (Fin Ξ.d → ℂ)
    have hf : ∀ X, smA Ξ X = f (lie E a X) := fun _ => rfl
    have e : eL (smA Ξ) τ = fun i j => f (Eop (a := a) τ i j) := by
      funext i j
      simp only [hE, eL, hf, map_smul, map_sub]
    rw [e, ← mapQ, ← hc]
    rfl
  · have hd := (dualIff E a Ξ τ m).1 hm
    have hB : ∀ X, smB Ξ X = rAlg (Sm E a) Ξ.d (Ξ.dmat X) := fun X => smB_apply Ξ X
    have h := (mapQ (rOp (Sm E a) Ξ.d) (GlobalTheory.WignerGL.dualE Ξ τ) (u + ((a : ℂ) - 1) / 2)).symm.trans
      (congrArg (rOp (Sm E a) Ξ.d) (hd.2 u))
    rw [map_smul, map_one] at h
    have e : ∀ i j, rOp (Sm E a) Ξ.d (GlobalTheory.WignerGL.dualE Ξ τ i j) = -MulOpposite.op (eL (smB Ξ) τ i j) := fun i j => by
      rw [dualE_eq, map_neg, rOp_apply, Matrix.transpose_transpose]
      simp only [eL, hB, map_smul, map_sub]
    simp only [e] at h
    rw [h, MulOpposite.unop_smul, MulOpposite.unop_one]
  · rw [← UpperTheory.V.Cm.uC_capC, ← UpperTheory.V.Cm.uC_ιC]
    exact Commute.map (Subalgebra.mem_center_iff.1 (UpperTheory.V.Cm.capC_mem_center τ u) _) (UpperTheory.V.Cm.uC E a)
  · rw [hc]
    refine qdet_stab N _ (fun i j φ hφ => ?_) _
    rw [hE]
    exact N.smul_mem _ (N.sub_mem (hN _ φ hφ) (N.smul_mem _ (hN _ φ hφ)))
end

section

section SlopeTestRemainingChoices
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible

private def UpperTheory.V.Cj.H.altFlip {A V M : Type} [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup M] [Module ℝ M] {q : ℕ} (φ : A →ₗ[ℝ] (V [⋀^Fin q]→ₗ[ℝ] M)) : V [⋀^Fin q]→ₗ[ℝ] (A →ₗ[ℝ] M) where
  toFun Y :=
    { toFun := fun X => φ X Y
      map_add' := fun X X' => by rw [map_add (f := _), AlternatingMap.add_apply]
      map_smul' := fun c X => by rw [map_smul, AlternatingMap.smul_apply, RingHom.id_apply] }
  map_update_add' Y i x y := LinearMap.ext fun X => (φ X).map_update_add Y i x y
  map_update_smul' Y i c x := LinearMap.ext fun X => (φ X).map_update_smul Y i c x
  map_eq_zero_of_eq' Y _ _ h hij := LinearMap.ext fun X => (φ X).map_eq_zero_of_eq Y h hij

private theorem UpperTheory.V.Cj.H.wigner_homomorphism : UpperTheory.V.Cj.H.WigHom := by
  intro E _ _ _ a M _ _ _ _ L α z hlie hretr
  refine ⟨fun ω h0 h1 Y => ?_, fun q ω h0 h1 => ?_⟩
  · have key : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), L (toL X) (ω Y) = 0 := by
      intro X
      let Z : Matrix (Fin a) (Fin a) (Cinf E) := (1 / 2 : ℝ) • (X - star X)
      have hZ : star Z = -Z := by
        simp only [Z]
        rw [star_smul, star_sub, star_star, star_trivial, ← smul_neg, neg_sub]
      have hX : toL X = toL (hp (toL X)).1 + toL Z := by
        have h : X = (hp (toL X)).1 + Z := by
          rw [hp_val]; simp only [Z]; module
        exact congrArg toL h
      have h3 := DFunLike.congr_fun h1 fun _ => hp (toL X)
      rw [dCo_apply, Fin.sum_univ_one, Subsingleton.elim (Fin.removeNth _ _) Y] at h3
      have h4 : L (toL (hp (toL X)).1) (ω Y) = 0 := by simpa using h3
      rw [congrArg L hX, map_add (f := _), LinearMap.add_apply, h4, h0 Z hZ Y]
      simp
    rw [← hretr (ω Y) 0 fun X => (key (Matrix.of X)).symm, map_zero]
  · let F : Herm E a [⋀^Fin q]→ₗ[ℝ] (Lie E a →ₗ[ℝ] M) := UpperTheory.V.Cj.H.altFlip (ω.curryLeft ∘ₗ hp)
    let ad : Matrix (Fin a) (Fin a) (Cinf E) → Lie E a →ₗ[ℝ] Lie E a := fun Y =>
      { toFun := fun X => toL (Y * Matrix.of X - Matrix.of X * Y)
        map_add' := fun X X' => by
          have h : Y * (Matrix.of X + Matrix.of X') - (Matrix.of X + Matrix.of X') * Y =
              (Y * Matrix.of X - Matrix.of X * Y) + (Y * Matrix.of X' - Matrix.of X' * Y) := by noncomm_ring
          exact congrArg toL h
        map_smul' := fun c X => by
          have h : Y * (c • Matrix.of X) - (c • Matrix.of X) * Y = c • (Y * Matrix.of X - Matrix.of X * Y) := by
            rw [smul_sub, mul_smul_comm, smul_mul_assoc]
          exact congrArg toL h }
    refine ⟨α.compAlternatingMap F, fun Y => ?_⟩
    let G : Fin (q + 1) → Lie E a →ₗ[ℝ] M := fun i =>
      (L (toL (Y i).1)).restrictScalars ℝ ∘ₗ F (i.removeNth Y) - F (i.removeNth Y) ∘ₗ ad (Y i).1
    have h3 : ∀ i, L (toL (Y i).1) (α (F (i.removeNth Y))) = α (G i) := fun i =>
      hlie _ _ _ fun X => (sub_add_cancel _ _).symm

    rw [dCo_apply, ← hretr (ω Y) (∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • G i) fun X => ?_, map_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, ← h3]
      rfl
    · rw [LinearMap.sum_apply]
      exact homId E a M L q ω h1 h0 (Matrix.of X) Y

end SlopeTestRemainingChoices

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.wigHom :
    UpperTheory.V.Cj.H.WigHom :=
  UpperTheory.V.Cj.H.wigner_homomorphism
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {a : ℕ}
  {N : Type} [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]
  {N' : Type} [AddCommGroup N'] [Module ℂ N'] [Module ℝ N'] [IsScalarTower ℝ ℂ N']

omit [NumberField E] [IsScalarTower ℝ ℂ N] [IsScalarTower ℝ ℂ N'] in
private theorem hol_nat (τ : E →+* ℂ) (φ : N →ₗ[ℂ] N') (L : Lie E a →ₗ[ℝ] N) (L' : Lie E a →ₗ[ℝ] N')
    (h : ∀ X, φ (L (toL X)) = L' (toL X)) (x : Matrix (Fin a) (Fin a) ℂ) : φ (hol τ L x) = hol τ L' x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hol_apply, eL, map_sum, map_smul, map_sub, h]

omit [NumberField E] [IsScalarTower ℝ ℂ N] in
private theorem hol_add (τ : E →+* ℂ) (L L' : Lie E a →ₗ[ℝ] N) : hol τ (L + L') = hol τ L + hol τ L' := by
  ext1 x
  simp only [hol_apply, eL, LinearMap.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  module

omit [NumberField E] in
private theorem hol_smul (τ : E →+* ℂ) (r : ℝ) (L : Lie E a →ₗ[ℝ] N) : hol τ (r • L) = (r : ℂ) • hol τ L := by
  ext1 x
  have e : ∀ v : N, r • v = (r : ℂ) • v := fun v => (algebraMap_smul ℂ r v).symm
  simp only [hol_apply, eL, LinearMap.smul_apply, Finset.smul_sum, e]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  module

variable [_root_.NumberField.IsTotallyComplex E]

private theorem hol_der (τ : E →+* ℂ) (φ : N →ₗ[ℂ] N') (L : Lie E a →ₗ[ℝ] N) (L' L'' : Lie E a →ₗ[ℝ] N')
    (Y : Matrix (Fin a) (Fin a) (Cinf E)) (h : ∀ X, φ (L (toL X)) = L' (toL X) + L'' (toL (Y * X - X * Y)))
    (x : Matrix (Fin a) (Fin a) ℂ) :
    φ (hol τ L x) = hol τ L' x + hol τ L'' (Y.map (coord τ) * x - x * Y.map (coord τ)) := by
  rw [hol_nat τ φ L (φ.restrictScalars ℝ ∘ₗ L) (fun _ => rfl),
    ← (holMul E a N' τ L'' (φ.restrictScalars ℝ ∘ₗ L - L')).2 Y (fun X => sub_eq_of_eq_add' (h X)) x,
    ← LinearMap.add_apply, ← hol_add, add_sub_cancel]

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]

private theorem hol_der_end (τ : E →+* ℂ) (u : Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M)
    (Y : Matrix (Fin a) (Fin a) (Cinf E)) (h : ∀ X, u * L (toL X) - L (toL X) * u = L (toL (Y * X - X * Y)))
    (x : Matrix (Fin a) (Fin a) ℂ) :
    u * hol τ L x - hol τ L x * u = hol τ L (Y.map (coord τ) * x - x * Y.map (coord τ)) := by
  have h1 := hol_der τ (LinearMap.mulLeft ℂ u - LinearMap.mulRight ℂ u) L 0 L Y
    (fun X => (h X).trans (zero_add _).symm) x
  have h0 : hol τ (0 : Lie E a →ₗ[ℝ] Module.End ℂ M) x = 0 := by simp [hol_apply, eL]
  rw [h0, zero_add] at h1
  exact h1

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.H.wigAlpha :
    UpperTheory.V.Cj.H.WigAlpha := by
  intro E _ _ _ a M _ _ _ _ LA LB hA hB hc τ x
  have hcomm : ∀ y z, Commute (hol τ LA y) (hol τ LB z) := fun y z => by
    simp only [hol_apply, eL]
    refine Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ =>
      Commute.sum_right _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ => ?_
    exact (((((hc _ _).sub_right ((hc _ _).smul_right _)).sub_left
      (((hc _ _).sub_right ((hc _ _).smul_right _)).smul_left _)).smul_right _).smul_left _
      |>.smul_right _).smul_left _
  have hAlpha := UpperTheory.V.AlgRepEndIrreducible.alphaAbs M a (hol τ LA) (hol τ LB)
    (fun k : Fin a => x - (k.val : ℂ)) hcomm
  obtain ⟨α₀, h1, -, h3⟩ := hAlpha
  set s : ℂ := (a.factorial : ℂ)⁻¹ with hs
  have e : ∀ (r : ℝ) (v : M), r • v = (r : ℂ) • v := fun r v => (algebraMap_smul ℂ r v).symm
  let α : (Lie E a →ₗ[ℝ] M) →ₗ[ℝ] M :=
    { toFun := fun f => s • α₀ (hol τ f)
      map_add' := fun f g => by rw [hol_add, map_add (f := _), smul_add]
      map_smul' := fun r f => by rw [hol_smul, map_smul, RingHom.id_apply, e, smul_comm] }
  have hα : ∀ f, α f = s • α₀ (hol τ f) := fun _ => rfl
  refine ⟨α, fun Y f f' hf => ?_, fun m f hf => ?_⟩
  · rw [hα, hα, map_smul]
    congr 1
    refine h3 _ (Y.map (coord τ)) (hol_der_end τ _ LA Y fun X => ?_) (hol_der_end τ _ LB Y fun X => ?_) _ _
      (hol_der τ _ f f' f Y hf)
    · rw [LinearMap.add_apply, add_mul, mul_add, ← hA Y X, (hc (toL X) (toL Y)).eq]
      abel
    · rw [LinearMap.add_apply, add_mul, mul_add, ← hB Y X, (hc (toL Y) (toL X)).eq]
      abel
  · have hx : ∀ y, hol τ f y = hol τ LA y m + hol τ LB y m := fun y => by
      rw [← hol_nat τ (LinearMap.applyₗ m) (LA + LB) f (fun X => (hf _).symm), hol_add]
      rfl
    rw [hα, h1 m _ hx]
    simp only [hol_single]
    have gA := (eLRel E a _ LA hA).1 τ
    have gB := (glNegOp _ a _ ((eLRel E a _ LB hB).1 τ)).1
    rw [Formalism.HermitianLatticeCounting.P.antisymmetrizedProduct_eq_factorial_smul_qdet _ gB, show (fun i j => eL LA τ i j) = eL LA τ from rfl,
      Formalism.HermitianLatticeCounting.P.antisymmetrizedProduct_eq_factorial_smul_qdet _ gA]
    have hz : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
    simp only [MulOpposite.unop_smul, LinearMap.smul_apply, LinearMap.sub_apply, ← smul_sub, smul_smul]
    rw [hs, inv_mul_cancel₀ hz, one_smul]
end
