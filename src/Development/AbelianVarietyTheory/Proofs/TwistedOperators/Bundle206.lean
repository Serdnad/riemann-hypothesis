module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle928
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle094
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle095
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle116
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealLineKFin

private theorem eq_of_inner_eq_on_dense {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {E : Submodule ℂ H} (hE : Dense (E : Set H)) {v w : H}
    (h : ∀ y : E, ⟪v, (y : H)⟫_ℂ = ⟪w, (y : H)⟫_ℂ) : v = w := by
  have hclosed : IsClosed {x : H | ⟪v - w, x⟫_ℂ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hsub : (E : Set H) ⊆ {x : H | ⟪v - w, x⟫_ℂ = 0} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, inner_sub_left, h ⟨x, hx⟩, sub_self]
  have hall := closure_minimal hsub hclosed
  rw [hE.closure_eq] at hall
  have hz : ⟪v - w, v - w⟫_ℂ = 0 := hall (Set.mem_univ _)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem exists_riesz {H P : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup P] [Module ℂ P] {E : Submodule ℂ H} (hE : Dense (E : Set H)) (F : P →ₗ[ℂ] E →ₗ[ℂ] ℂ)
    (hF : ∀ φ, ∃ c : ℝ, ∀ y : E, ‖F φ y‖ ≤ c * ‖(y : H)‖) :
    ∃ b : P →ₛₗ[starRingEnd ℂ] H, ∀ φ (y : E), F φ y = ⟪b φ, (y : H)⟫_ℂ := by
  have hrep : ∀ φ, ∃ v : H, ∀ y : E, F φ y = ⟪v, (y : H)⟫_ℂ := by
    intro φ
    obtain ⟨c, hc⟩ := hF φ
    have hden : DenseRange (E.subtype : E →ₗ[ℂ] H) := by
      simpa using hE.denseRange_val
    let g : H →L[ℂ] ℂ := (F φ).extendOfNorm E.subtype
    refine ⟨(InnerProductSpace.toDual ℂ H).symm g, fun y => ?_⟩
    rw [InnerProductSpace.toDual_symm_apply]
    have := LinearMap.extendOfNorm_eq (f := F φ) hden ⟨c, fun y => by simpa using hc y⟩ y
    simpa [g] using this.symm
  choose v hv using hrep
  refine ⟨{ toFun := v, map_add' := ?_, map_smul' := ?_ }, hv⟩
  · intro φ ψ
    refine eq_of_inner_eq_on_dense hE fun y => ?_
    rw [← hv, inner_add_left, ← hv, ← hv, map_add (f := _), LinearMap.add_apply]
  · intro c φ
    refine eq_of_inner_eq_on_dense hE fun y => ?_
    rw [← hv, inner_smul_left, ← hv, map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp

theorem finite_map {H P : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup P] [Module ℂ P]
    (b : P →ₛₗ[starRingEnd ℂ] H) (T : Submodule ℂ P) [FiniteDimensional ℂ T] : FiniteDimensional ℂ (T.map b) := by
  have hT : (T : Submodule ℂ P).FG := Module.Finite.iff_fg.mp inferInstance
  exact Module.Finite.iff_fg.mpr (hT.map b)

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem sm_stable (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.MainNotions.S.UJset (M.ε τ)) {y : M.H τ} (hy : y ∈ M.sm τ) : M.σ τ g y ∈ M.sm τ := Submodule.subset_span (GlobalTheory.ConjExt.smooth_translate M τ ⟨y, hy⟩ hg)

theorem dense_sm (M : DSModel V S) (τ : D.what₂.Tau) : Dense (M.sm τ : Set (M.H τ)) := GlobalTheory.LowTypeDetermined.dense_of_irred (M.ds τ).2.2.2.1 (fun _ hg _ hy => sm_stable M τ hg hy) (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)

theorem kset_star {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) :
    star k ∈ Formalism.REAL.Kset ε := by
  obtain ⟨hu, hc⟩ := hk
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact Matrix.mem_unitaryGroup_iff'.mp hu), ?_⟩
  have hJ : star (Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε := by
    rw [Matrix.star_eq_conjTranspose]; exact Formalism.REAL.Jm_conjTranspose ε
  calc star k * Formalism.REAL.Jm ε = star (Formalism.REAL.Jm ε * k) := by rw [star_mul, hJ]
    _ = star (k * Formalism.REAL.Jm ε) := by rw [hc]
    _ = Formalism.REAL.Jm ε * star k := by rw [star_mul, hJ]

private theorem mem_UJset_of_mem_Kset_twisted_operators {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Formalism.REAL.Kset ε) : k ∈ Formalism.MainNotions.S.UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  have hkk : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  simp only [Formalism.MainNotions.S.UJset, Set.mem_ofPred_eq, Formalism.REAL.inUJ]
  rw [← Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hkk, Matrix.one_mul]

private theorem subst_subst_eq_of_subst_eq_X {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) (y : H) : σ k (σ (star k) y) = y := by
  have hks1 : k * star k = 1 := Matrix.mem_unitaryGroup_iff.mp hk.1
  rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 k (mem_UJset_of_mem_Kset_twisted_operators hk) (star k) (mem_UJset_of_mem_Kset_twisted_operators (kset_star hk)),
    hks1, hσ.1.1]
  rfl

private theorem inner_urep_apply_eq_inner_star_of_mem_Kset {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) (x y : H) :
    ⟪σ k x, y⟫_ℂ = ⟪x, σ (star k) y⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := ⟨(σ k).toLinearMap, hσ.2.1 k (mem_UJset_of_mem_Kset_twisted_operators hk)⟩
  conv_lhs => rw [← subst_subst_eq_of_subst_eq_X hσ hk y]
  exact L.inner_map_map x (σ (star k) y)

theorem kfin : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) (aS aT : ℚ) (A : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ), SemiW M M' τ aS aT A → (∀ φ y, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) (A φ y)) ∧ ∀ φ u, ∃ b : M'.H τ, Formalism.MainNotions.S.IsKFin (M'.ε τ) (M'.σ τ) b ∧ ∀ y : M'.sm τ, ⟪u, A φ y⟫_ℂ = ⟪b, (y : M'.H τ)⟫_ℂ := by
  intro D V W S S' M M' τ aS aT A hA
  have : CompleteSpace (M'.H τ) := (M'.ds τ).1
  refine ⟨fun φ y => ?_, fun φ u => ?_⟩
  · refine ⟨(MvPolynomial.restrictTotalDegree _ ℂ φ.totalDegree).map (A.flip y), ?_, ⟨φ, ?_, rfl⟩, ?_⟩
    · exact Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp inferInstance).map _)
    · exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr le_rfl
    · intro g hg v hv
      obtain ⟨ψ, hψ, rfl⟩ := hv
      obtain ⟨ψ', hdeg, heq⟩ := hA.eqK g hg ψ
      refine ⟨ψ', (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
        (hdeg.trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hψ)), ?_⟩
      simp only [LinearMap.flip_apply, heq y]
  · let F : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] ℂ := A.compr₂ (innerSL ℂ u).toLinearMap
    have hFapp : ∀ ψ y, F ψ y = ⟪u, A ψ y⟫_ℂ := fun ψ y => by simp [F]
    obtain ⟨b, hb⟩ := exists_riesz (dense_sm M' τ) F fun ψ => by
      obtain ⟨c, hc⟩ := hA.bdd ψ u
      exact ⟨c, fun y => by rw [hFapp]; exact hc y⟩
    have hσ := (M'.ds τ).2.2.1
    let T : Submodule ℂ (PolF D W.rank V.rank) := MvPolynomial.restrictTotalDegree _ ℂ φ.totalDegree
    refine ⟨b φ, ⟨T.map b, finite_map b T, ⟨φ, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr le_rfl, rfl⟩, ?_⟩,
      fun y => by rw [← hFapp, hb]⟩
    intro k hk v hv
    obtain ⟨ψ, hψ, rfl⟩ := hv
    obtain ⟨ψ', hdeg, heq⟩ := hA.invK k hk ψ
    have key : M'.σ τ k (b ψ) = b ψ' := by
      refine eq_of_inner_eq_on_dense (dense_sm M' τ) fun y => ?_
      have hmem : M'.σ τ (star k) y ∈ M'.sm τ := sm_stable M' τ (mem_UJset_of_mem_Kset_twisted_operators (kset_star hk)) y.2
      rw [inner_urep_apply_eq_inner_star_of_mem_Kset hσ hk]
      have e1 : F ψ ⟨_, hmem⟩ = ⟪b ψ, M'.σ τ (star k) y⟫_ℂ := hb ψ ⟨_, hmem⟩
      rw [← e1, ← hb ψ' y, hFapp, hFapp, heq ⟨_, hmem⟩ y (subst_subst_eq_of_subst_eq_X hσ hk y).symm]
    rw [key]
    exact ⟨ψ', (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
      (hdeg.trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hψ)), rfl⟩

end GlobalTheory.Chain.RealLineKFin

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairingLine

open GlobalTheory.PairingTensor

theorem exists_tensor {V A B H₁ H₂ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] (i₁ : A →ₗ[ℂ] H₁) (i₂ : B →ₗ[ℂ] H₂) (h₁ : Function.Injective i₁)
    (h₂ : Function.Injective i₂) (φ : B → V →ₗ[ℂ] A)
    (hadj : ∀ P x, ∃ b, ∀ y, ⟪i₁ x, i₁ (φ y P)⟫_ℂ = ⟪i₂ y, i₂ b⟫_ℂ)
    (hE : ∀ P, ∃ E : Submodule ℂ A, FiniteDimensional ℂ E ∧ ∀ y, φ y P ∈ E) :
    ∃ f : V →ₗ[ℂ] A ⊗[ℂ] B, (∀ P y, contrR (innerₛₗ ℂ (i₂ y) ∘ₗ i₂) (f P) = φ y P) ∧
      ∀ z w : A ⊗[ℂ] B,
        (∀ y, contrR (innerₛₗ ℂ (i₂ y) ∘ₗ i₂) z = contrR (innerₛₗ ℂ (i₂ y) ∘ₗ i₂) w) → z = w := by
  let m : B → B →ₗ[ℂ] ℂ := fun y => (innerₛₗ ℂ (i₂ y)) ∘ₗ i₂
  have hm : ∀ y b, m y b = inner ℂ (i₂ y) (i₂ b) := fun _ _ => rfl
  have sepm : ∀ b, (∀ y, m y b = 0) → b = 0 := fun b h => by
    apply h₂
    rw [map_zero]
    exact inner_self_eq_zero.mp (h b)
  have sepR : ∀ z w : A ⊗[ℂ] B, (∀ y, contrR (m y) z = contrR (m y) w) → z = w := by
    intro z w h
    rw [← sub_eq_zero]
    exact eq_zero_of_contrR m sepm _ (fun y => by rw [map_sub, h, sub_self])
  choose ψ hψ using hadj
  have ex : ∀ P, ∃ z : A ⊗[ℂ] B, ∀ y, contrR (m y) z = φ y P := by
    intro P
    obtain ⟨E, hfin, hmem⟩ := hE P
    let e := stdOrthonormalBasis ℂ (E.map i₁)
    have ha : ∀ j, ∃ a : A, i₁ a = (e j : H₁) := fun j => by
      obtain ⟨a, -, ha⟩ := (e j).2
      exact ⟨a, ha⟩
    choose a ha using ha
    refine ⟨∑ j, a j ⊗ₜ[ℂ] ψ P (a j), fun y => ?_⟩
    apply h₁
    have := congrArg (fun v : E.map i₁ => (v : H₁))
      (e.sum_repr' ⟨i₁ (φ y P), Submodule.mem_map_of_mem (hmem y)⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at this

    rw [← this, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [contrR_tmul, map_smul, hm, ← hψ, ha]
  choose g hg using ex
  exact ⟨{ toFun := g
           map_add' := fun P Q => sepR _ _ fun y => by rw [map_add (f := _), hg, hg, hg, map_add (f := _)]
           map_smul' := fun s P => sepR _ _ fun y => by
             rw [map_smul, hg, hg, map_smul, RingHom.id_apply] }, hg, sepR⟩

theorem contrR_map_right {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (m : B →ₗ[ℂ] ℂ) (b : Module.End ℂ B) (z : A ⊗[ℂ] B) :
    contrR m (TensorProduct.map LinearMap.id b z) = contrR (m ∘ₗ b) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem contrR_neg {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (m : B →ₗ[ℂ] ℂ) (z : A ⊗[ℂ] B) : contrR (-m) z = -contrR m z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, neg_add]

theorem linear_eq_of_upq {p q : ℕ} {N : Type} [AddCommGroup N] [Module ℂ N] (F G : Mat p q →ₗ[ℂ] N)
    (h : ∀ Z ∈ upq p q, F Z = G Z) (Z : Mat p q) : F Z = G Z := by
  have e1 := h _ (GlobalTheory.AdjDescent.re_mem_upq Z)
  have e2 := h _ (GlobalTheory.AdjDescent.im_mem_upq Z)
  have hd := GlobalTheory.AdjDescent.decomp Z
  generalize Z + conjR Z = X at e1 hd
  generalize Complex.I • (Z - conjR Z) = Y at e2 hd
  subst hd
  simp only [map_add (f := _), map_smul, e1, e2]

theorem skew {p q : ℕ} {T : GrpData p q} (R : DSRep T) {Y : Mat p q} (hY : Y ∈ upq p q) (x y : R.HK.V) :
    ⟪R.ι (R.HK.act Y x), R.ι y⟫_ℂ = -⟪R.ι x, R.ι (R.HK.act Y y)⟫_ℂ := by
  have h1 := (R.der Y hY x).inner ℂ (R.der Y hY y)
  simp only [GlobalTheory.RealPar.DerivedAdjoint.inner_map, zero_smul, T.expt_zero, map_one,
    ContinuousLinearMap.one_apply] at h1
  have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (inner ℂ (R.ι x) (R.ι y)))
  linear_combination h2

theorem exists_intw {p q r s : ℕ} {T₁ : GrpData p q} {T₂ : GrpData r s} (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (hA : Formalism.MainNotions.SchurIrreducible.AdmGK R₁.HK) (B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V)
    (hB : CoverW R₁ R₂ B) :
    ∃ f : Pol p q r s →ₗ[ℂ] R₁.HK.V ⊗[ℂ] R₂.HK.V,
      (∀ Z, f ∘ₗ fockAct1 p q r s Z = TensorProduct.map (R₁.HK.act Z) LinearMap.id ∘ₗ f) ∧
      (∀ Z, f ∘ₗ fockAct2 p q r s Z = TensorProduct.map LinearMap.id (R₂.HK.act Z) ∘ₗ f) ∧
      ∀ P y, contrR (innerₛₗ ℂ (R₂.ι y) ∘ₗ R₂.ι) (f P) = B P y := by
  have hsrc : ∀ Z P y, B (fockAct1 p q r s Z P) y = R₁.HK.act Z (B P y) := fun Z P y =>
    linear_eq_of_upq (B.flip y ∘ₗ (fockAct1 p q r s).flip P) (R₁.HK.act.flip (B P y))
      (fun Z hZ => hB.src Z hZ P y) Z
  have hlie := (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.1
  obtain ⟨f, hf, sep⟩ := exists_tensor R₁.ι R₂.ι R₁.ι_inj R₂.ι_inj (fun y => B.flip y) hB.adj (fun P => by
    obtain ⟨W, hW, hP, hst⟩ := ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).1 P).1
    obtain ⟨E, hE, hE'⟩ := GlobalTheory.T.exists_finiteDimensional_forall_map_mem' p q R₁.HK hA _ (fockAct1 p q r s) (fun Y Z _ _ => hlie Y Z) W hW hst
      (fun v _ => ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).1 v).2)
    exact ⟨E, hE, fun y => hE' (B.flip y) (fun Z _ v => hsrc Z v y) P hP⟩)
  simp only [LinearMap.flip_apply] at hf
  refine ⟨f, fun Z => ?_, fun Z => ?_, hf⟩
  · refine LinearMap.ext fun P => sep _ _ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, contrR_map, hf, hf, hsrc]
  · refine LinearMap.ext fun P => ?_
    refine linear_eq_of_upq (f ∘ₗ (fockAct2 p q r s).flip P)
      (((LinearMap.lTensorHom R₁.HK.V).comp R₂.HK.act).flip (f P)) (fun Z hZ => ?_) Z
    refine sep _ _ fun y => ?_
    change contrR _ (f (fockAct2 p q r s Z P)) = contrR _ (TensorProduct.map LinearMap.id (R₂.HK.act Z) (f P))
    have e : (innerₛₗ ℂ (R₂.ι y) ∘ₗ R₂.ι) ∘ₗ R₂.HK.act Z = -(innerₛₗ ℂ (R₂.ι (R₂.HK.act Z y)) ∘ₗ R₂.ι) := by
      refine LinearMap.ext fun b => ?_
      change ⟪R₂.ι y, R₂.ι (R₂.HK.act Z b)⟫_ℂ = -⟪R₂.ι (R₂.HK.act Z y), R₂.ι b⟫_ℂ
      rw [skew R₂ hZ, neg_neg]
    rw [contrR_map_right, e, contrR_neg, hf, hf]
    exact eq_neg_of_add_eq_zero_left (hB.tgt Z hZ P y)

theorem pairing_line : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds p q lam).HK → Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam lam' → ∃ B₀ : Pol p q r s → (X.ds r s lam').HK.V → (X.ds p q lam).HK.V, ∀ B : Pol p q r s →ₗ[ℂ] (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] (X.ds p q lam).HK.V, CoverW (X.ds p q lam) (X.ds r s lam') B → ∃ c : ℂ, ∀ P y, B P y = c • B₀ P y := by
  intro X p q r s lam lam' hA hL
  obtain ⟨f₀, -, -, hf₀⟩ := hL
  refine ⟨fun P y => contrR (innerₛₗ ℂ ((X.ds r s lam').ι y) ∘ₗ (X.ds r s lam').ι) (f₀ P), fun B hB => ?_⟩
  obtain ⟨f, h1, h2, hf⟩ := exists_intw _ _ hA B hB
  obtain ⟨c, hc⟩ := hf₀ f ⟨h1, h2⟩
  refine ⟨c, fun P y => ?_⟩
  rw [← hf, hc, LinearMap.smul_apply, map_smul]

end GlobalTheory.PairingLine
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {ψ : AddChar L ℂ} {n n' : ℕ}

theorem mem_mixLat_iff {x : Matrix (Fin n') (Fin n) L} : x ∈ mixLat L n' n ↔ ∀ r c,
    (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2 → x r c = 0) ∧ (n' / 2 ≤ r.1 → c.1 < n - n / 2 → x r c ∈ intL L) :=
  Iff.rfl

theorem pairing_mixLat (hσ : ∀ x, σ (σ x) = x) (hv : ∀ x, Valued.v (σ x) = Valued.v x) (hδ : Valued.v δ = 1)
    (hψ0 : ∀ a ∈ intL L, σ a = a → ψ a = 1) {a b : Matrix (Fin n') (Fin n) L} (ha : a ∈ mixLat L n' n)
    (hb : b ∈ mixLat L n' n) : pairing σ δ ψ a b = 1 := by
  have hs : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => mem_intL.2 ((hv x).trans_le hx)
  rw [mem_mixLat_iff] at ha hb
  have hS : ∑ i, ∑ j, a i j * σ (b i.rev j.rev) ∈ intL L := by
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    have hai := ha i j
    have hbi := hb i.rev j.rev
    simp only [Fin.val_rev] at hbi
    have := i.isLt
    have := j.isLt
    by_cases h1 : n' - n' / 2 ≤ i.1 ∨ n' / 2 ≤ i.1 ∧ j.1 < n / 2
    · rw [hai.1 h1, zero_mul]; exact zero_mem _
    by_cases h2 : n' - n' / 2 ≤ n' - (i.1 + 1) ∨ n' / 2 ≤ n' - (i.1 + 1) ∧ n - (j.1 + 1) < n / 2
    · rw [hbi.1 h2, map_zero, mul_zero]; exact zero_mem _
    exact mul_mem (hai.2 (by omega) (by omega)) (hs _ (hbi.2 (by omega) (by omega)))
  have hi : δ * ∑ i, ∑ j, a i j * σ (b i.rev j.rev) ∈ intL L := mul_mem (mem_intL.2 hδ.le) hS
  exact hψ0 _ (add_mem hi (hs _ hi)) (by rw [map_add (f := _), hσ, add_comm])

theorem exists_bad_entry (x : Matrix (Fin n') (Fin n) L)
    (hx : ¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) :
    ∃ r c, x r c ∉ intL L ∧ (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2) := by
  by_contra hc
  refine hx ⟨fun r c => if n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2 then 0 else x r c, fun r c =>
    ⟨fun e => by dsimp only; rw [if_pos (by omega)], fun e e' => by dsimp only; rw [if_pos (by omega)]; exact zero_mem _⟩,
    fun r c => ?_⟩
  show x r c - (if n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2 then 0 else x r c) ∈ intL L
  split_ifs with hb
  · rw [sub_zero]
    by_contra hi
    exact hc ⟨r, c, hi, hb⟩
  · rw [sub_self]; exact zero_mem _

variable {M : Type} [AddCommGroup M] [Module ℂ M]
variable {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M} {ω : GU σ n × GU σ n' →* Module.End ℂ M} {s : M}

theorem IsStd.form_eq_zero (h : IsStd ϖ σ q δ ψ ρ ω s) (ℓ' : M →ₗ[ℂ] ℂ)
    (hℓ' : ∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) (x : Matrix (Fin n') (Fin n) L) (r : Fin n') (c : Fin n)
    (hx : x r c ∉ intL L) (hrc : n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2) : ℓ' (ρ x s) = 0 := by
  obtain ⟨u, hu, hne⟩ := exists_pairing_single_ne h.1.unr h.v_two h.1.delta.1 h.1.psi_ne x hx
  have := r.isLt
  have := c.isLt
  have hyA : Matrix.single r.rev c.rev u ∈ mixLat L n' n := by
    intro r' c'
    rw [Matrix.single_apply]
    split_ifs with he
    · obtain ⟨rfl, rfl⟩ := he
      simp only [Fin.val_rev]
      exact ⟨fun e => by omega, fun _ _ => hu⟩
    · exact ⟨fun _ => rfl, fun _ _ => zero_mem _⟩
  have hyL : Matrix.single r.rev c.rev u ∈ intMat L (Fin n') (Fin n) := by
    intro i j
    rw [Matrix.single_apply]
    split_ifs
    exacts [hu, zero_mem _]
  have e1 := h.isHeis.comm x (Matrix.single r.rev c.rev u) s
  rw [h.fixes _ hyL] at e1
  have e2 := congrArg ℓ' e1
  rw [map_smul, hℓ' _ hyA, smul_eq_mul] at e2
  have e3 : (pairing σ δ ψ x (Matrix.single r.rev c.rev u) - 1) * ℓ' (ρ x s) = 0 := by linear_combination -e2
  rcases mul_eq_zero.1 e3 with h' | h'
  · exact absurd (sub_eq_zero.1 h') hne
  · exact h'

end

theorem exists_mixLat_form : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∃ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 ∧ (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) ∧ (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) ∧ (∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ v, ℓ' v = ℓ' s * ℓ v) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ℓ (ρ (embLow n' n z) s) = if z ∈ intMat L (Fin (n' / 2)) (Fin (n / 2)) then 1 else 0 := by
  intro L _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s h
  obtain ⟨ℓ, h1, h2⟩ := GlobalTheory.T.exists_heisenbergInvariant_linearForm_isotropic_vacuum h.isHeis (intMat L (Fin n') (Fin n)) h.selfDual s h.2.1 h.fixes h.2.2.2
    (mixLat L n' n) fun a ha b hb => pairing_mixLat h.1.unr.1 h.1.unr.2.1 h.1.delta.1 h.1.psi_int ha hb
  have hz : ∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ x,
      (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ' (ρ x s) = 0 := fun ℓ' hℓ' x hx => by
    obtain ⟨r, c, hr, hrc⟩ := exists_bad_entry x hx
    exact h.form_eq_zero ℓ' hℓ' x r c hr hrc
  refine ⟨ℓ, h1, h2, hz ℓ h2, fun ℓ' hℓ' => ?_, fun z => ?_⟩
  · have key : ℓ' = ℓ' s • ℓ := LinearMap.ext_on_range h.2.2.2 fun x => ?_
    · exact fun v => LinearMap.congr_fun key v
    show ℓ' (ρ x s) = (ℓ' s • ℓ) (ρ x s)
    by_cases hx : ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)
    · obtain ⟨a, ha, hxa⟩ := hx
      have e := h.isHeis.comp a (x - a) s
      rw [h.fixes _ hxa, show a + (x - a) = x by abel] at e
      have hg := h.isHeis.ne_zero (half h.v_two • a) (x - a)
      have hx' : ρ x s = (pairing σ δ ψ (half h.v_two • a) (x - a))⁻¹ • ρ a s := by
        rw [e, smul_smul, inv_mul_cancel₀ hg, one_smul]
      rw [LinearMap.smul_apply, hx', map_smul, map_smul, hℓ' a ha, h2 a ha, h1, smul_eq_mul, smul_eq_mul, smul_eq_mul,
        mul_one, mul_comm]
    · rw [LinearMap.smul_apply, hz ℓ' hℓ' x hx, hz ℓ h2 x hx, smul_zero]
  · have := (n' / 2).le_refl
    split_ifs with hzi
    · have hm : embLow n' n z ∈ intMat L (Fin n') (Fin n) := fun r c => by
        unfold embLow
        split_ifs
        exacts [hzi _ _, zero_mem _]
      rw [h.fixes _ hm, h1]
    · obtain ⟨i, j, hij⟩ : ∃ i j, z i j ∉ intL L := by
        by_contra hc
        push_neg at hc
        exact hzi hc
      have he : embLow n' n z (hi n' i) (hi n j) = z i j := by
        simp [embLow, hi]
      refine h.form_eq_zero ℓ h2 _ (hi n' i) (hi n j) (by rwa [he]) (Or.inl ?_)
      simp only [hi]
      omega

end GlobalTheory.SphTheta

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.Grid.Vertex

theorem negIdx_of_sig {D : D7} (V : HSp D) (q : ℕ) (h : V.SigOK) (hs : ∀ τ : D.host.E →+* ℂ, V.sig τ = (V.rank - q, q)) :
    NegIdx V q := fun τ => by
  have := h (tauE D τ)
  rw [hs] at this
  exact this

end GlobalTheory.Grid.Vertex

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelPrimes

theorem pb_eq_of_tie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), R.Char F → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → T.pb = R.C.P.pb := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O i hC hW hO
  obtain ⟨w⟩ := hW
  exact GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R w.laws.toLawsM hC.lev (hO.2.tuple ()).half

end GlobalTheory.LevelPrimes
end
