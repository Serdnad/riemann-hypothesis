module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle003
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle145
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle148
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching Formalism.GradedWeylDivisibility Formalism.REAL
open scoped TensorProduct DirectSum Matrix

namespace GlobalTheory.ConjDual

theorem map_rowAct {r n : ℕ} (φ : ℂ →+* ℂ) (A : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    map φ (rowAct ℂ A f) = rowAct ℂ (A.map φ) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [rowAct]

def bil (σ : Type) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun f f' => fockF f (map (starRingEnd ℂ) f'))
    (fun _ _ _ => fischerInner_add_left _ _ _)
    (fun c f f' => by rw [smul_eq_C_mul, LFocks_C_mul_left, smul_eq_mul])
    (fun f a b => by rw [map_add (f := _), fischerInner_add_right])
    (fun c f f' => by
      rw [smul_eq_C_mul, map_mul, map_C, LFocks_C_mul_right, smul_eq_mul]
      simp)

theorem bil_apply {σ : Type} (f f' : MvPolynomial σ ℂ) : bil σ f f' = fockF f (map (starRingEnd ℂ) f') := rfl

theorem bil_rowAct {r n : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (f f' : MvPolynomial (Fin r × Fin n) ℂ) :
    bil _ (rowAct ℂ A f) f' = bil _ f (rowAct ℂ Aᵀ f') := by
  rw [bil_apply, bil_apply, fockRowAdj, map_rowAct]
  rfl

theorem bil_conj {σ : Type} (f : MvPolynomial σ ℂ) : bil σ f (map (starRingEnd ℂ) f) = fockF f f := by
  rw [bil_apply, map_map]
  have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by ext; simp
  rw [this, map_id]

def toDual (n : ℕ) (lam : DomWeight n) : nablaSq ℂ n lam →ₗ[ℂ] Module.Dual ℂ (nablaSq ℂ n lam) :=
  (bil _).compl₁₂ (nablaSq ℂ n lam).subtype (nablaSq ℂ n lam).subtype

theorem toDual_injective (n : ℕ) (lam : DomWeight n) : Function.Injective (toDual n lam) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro f hf
  by_contra h0
  have h1 : f.1 ≠ 0 := fun h => h0 (Subtype.ext h)
  have h2 := LinearMap.congr_fun hf ⟨map (starRingEnd ℂ) f.1, dualWeylMap ℂ ℂ _ n n _ _ f.2⟩
  have h3 : fockF f.1 f.1 = 0 := (bil_conj f.1).symm.trans h2
  have h := fockPos _ f.1 h1
  rw [h3] at h
  simp at h

theorem detPow_conjU (n : ℕ) (g : U n) (c : ℤ) :
    detPow ℂ n (unitaryIncl n (conjU n g)) c = detPow ℂ n (unitaryIncl n g⁻¹) c := by
  unfold detPow
  congr 2
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, unitaryIncl_coe,
    unitaryIncl_coe, conjU_coe, Matrix.det_transpose]
  rfl

theorem iso_conj_dual : ∀ (n : ℕ) (lam : DomWeight n),
    Iso ((irr n lam).comp (conjU n) : Representation ℂ (U n) (nablaSq ℂ n lam)) (irr n lam).dual := by
  intro n lam
  refine ⟨(toDual n lam).linearEquivOfInjective (toDual_injective n lam) Subspace.dual_finrank_eq.symm,
    fun g x => ?_⟩
  ext y
  change bil _ (sqAct ℂ n lam (unitaryIncl n (conjU n g)) x.1) y.1 =
    bil _ x.1 (sqAct ℂ n lam (unitaryIncl n g⁻¹) y.1)
  unfold sqAct
  rw [map_smul, map_smul, LinearMap.smul_apply, detPow_conjU, bil_rowAct, Matrix.transpose_transpose]
  rfl

end GlobalTheory.ConjDual
end
end

section

noncomputable section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem finrank_invFun_eq_of_surjective {Γ V W : Type} [Monoid Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) (P : V →ₗ[ℂ] W) (hP : Function.Surjective P)
    (he : ∀ g v, P (ρ g v) = σ g (P v)) (hk : ∀ l ∈ invFun ρ, ∀ v, P v = 0 → l v = 0) :
    Module.finrank ℂ (invFun ρ) = Module.finrank ℂ (invFun σ) := by
  have hinj : Function.Injective P.dualMap := LinearMap.dualMap_injective_of_surjective hP
  have hmap : (invFun σ).map P.dualMap = invFun ρ := by
    apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩ g v
      change l (P (ρ g v)) = l (P v)
      rw [he, mem_invFun.1 hl]
    · intro l hl
      obtain ⟨s, hs⟩ := P.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hP)
      have hs' : ∀ w, P (s w) = w := fun w => LinearMap.congr_fun hs w
      have key : ∀ v, l (s (P v)) = l v := fun v => by
        rw [← sub_eq_zero, ← map_sub]
        exact hk l hl _ (by rw [map_sub, hs', sub_self])
      refine ⟨l ∘ₗ s, fun g w => ?_, ?_⟩
      · obtain ⟨v, rfl⟩ := hP w
        change l (s _) = l (s _)
        rw [← he, key, key, mem_invFun.1 hl]
      · ext v
        exact key v
  rw [← hmap]
  exact ((invFun σ).equivMapOfInjective _ hinj).finrank_eq.symm

theorem dual_eq_zero_of_map_eq_zero {U W X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (p : U →ₗ[ℂ] X) (q : W →ₗ[ℂ] Y)
    (hp : Function.Surjective p) (hq : Function.Surjective q) (l : Module.Dual ℂ (U ⊗[ℂ] W))
    (h1 : ∀ u w, p u = 0 → l (u ⊗ₜ w) = 0) (h2 : ∀ u w, q w = 0 → l (u ⊗ₜ w) = 0) (z : U ⊗[ℂ] W)
    (hz : TensorProduct.map p q z = 0) : l z = 0 := by
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
  obtain ⟨t, ht⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq)
  have hs' : ∀ w, p (s w) = w := fun w => LinearMap.congr_fun hs w
  have ht' : ∀ w, q (t w) = w := fun w => LinearMap.congr_fun ht w
  have key : ∀ z, l (TensorProduct.map s t (TensorProduct.map p q z)) = l z := by
    intro z
    induction z with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul u w =>
      simp only [TensorProduct.map_tmul]
      have e1 := h1 (s (p u) - u) (t (q w)) (by rw [map_sub, hs', sub_self])
      have e2 := h2 u (t (q w) - w) (by rw [map_sub, ht', sub_self])
      rw [TensorProduct.sub_tmul, map_sub, sub_eq_zero] at e1
      rw [TensorProduct.tmul_sub, map_sub, sub_eq_zero] at e2
      rw [e1, e2]
  rw [← key, hz, map_zero, map_zero]

theorem iso_tprod_shuffle {Γ A B C D : Type} [Monoid Γ] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] (a : Representation ℂ Γ A) (b : Representation ℂ Γ B)
    (c : Representation ℂ Γ C) (d : Representation ℂ Γ D) :
    Iso ((a.tprod c).tprod (b.tprod d)) (a.tprod (b.tprod (c.tprod d))) := by
  refine ⟨(TensorProduct.tensorTensorTensorComm ℂ A C B D).trans (TensorProduct.assoc ℂ A B (C ⊗[ℂ] D)), fun g z => ?_⟩
  induction z with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul u w =>
    induction u with
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add (f := _), ha, hb]
    | tmul u1 u2 =>
      induction w with
      | add a b ha hb => simp only [TensorProduct.tmul_add, map_add (f := _), ha, hb]
      | tmul w1 w2 => simp

theorem finrank_invFun_two_contractions (Γ A B C D X Y : Type) [Monoid Γ] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] [AddCommGroup X]
    [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (a : Representation ℂ Γ A) (b : Representation ℂ Γ B)
    (c : Representation ℂ Γ C) (d : Representation ℂ Γ D) (x : Representation ℂ Γ X) (y : Representation ℂ Γ Y)
    (p : A ⊗[ℂ] C →ₗ[ℂ] X) (q : B ⊗[ℂ] D →ₗ[ℂ] Y) (hp : Function.Surjective p) (hq : Function.Surjective q)
    (ep : ∀ g u w, p (a g u ⊗ₜ[ℂ] c g w) = x g (p (u ⊗ₜ[ℂ] w)))
    (eq : ∀ g u w, q (b g u ⊗ₜ[ℂ] d g w) = y g (q (u ⊗ₜ[ℂ] w)))
    (kp : ∀ l : Module.Dual ℂ (A ⊗[ℂ] C),
      (∀ g, b g = 1 → d g = 1 → ∀ u w, l (a g u ⊗ₜ[ℂ] c g w) = l (u ⊗ₜ[ℂ] w)) → ∀ z, p z = 0 → l z = 0)
    (kq : ∀ l : Module.Dual ℂ (B ⊗[ℂ] D),
      (∀ g, a g = 1 → c g = 1 → ∀ u w, l (b g u ⊗ₜ[ℂ] d g w) = l (u ⊗ₜ[ℂ] w)) → ∀ z, q z = 0 → l z = 0) :
    Module.finrank ℂ (invFun (a.tprod (b.tprod (c.tprod d)))) = Module.finrank ℂ (invFun (x.tprod y)) := by
  rw [← (iso_tprod_shuffle a b c d).finrank_invFun]
  have ep' : ∀ g z, p (a.tprod c g z) = x g (p z) := by
    intro g z
    induction z with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul u w => simp [ep]
  have eq' : ∀ g z, q (b.tprod d g z) = y g (q z) := by
    intro g z
    induction z with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul u w => simp [eq]
  refine finrank_invFun_eq_of_surjective _ _ (TensorProduct.map p q) (TensorProduct.map_surjective hp hq)
    (fun g z => ?_) (fun l hl z hz => dual_eq_zero_of_map_eq_zero p q hp hq l ?_ ?_ z hz)
  · induction z with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul u w =>
      rw [Representation.tprod_apply, Representation.tprod_apply x, TensorProduct.map_tmul, TensorProduct.map_tmul,
        TensorProduct.map_tmul, TensorProduct.map_tmul, ep', eq']
  · intro u w hu
    refine kp (l ∘ₗ (TensorProduct.mk ℂ (A ⊗[ℂ] C) (B ⊗[ℂ] D)).flip w) (fun g hb hd u1 u2 => ?_) u hu
    have := mem_invFun.1 hl g ((u1 ⊗ₜ u2) ⊗ₜ w)
    simpa [hb, hd, Module.End.one_eq_id] using this
  · intro u w hw
    refine kq (l ∘ₗ TensorProduct.mk ℂ (A ⊗[ℂ] C) (B ⊗[ℂ] D) u) (fun g ha hc w1 w2 => ?_) w hw
    have := mem_invFun.1 hl g (u ⊗ₜ (w1 ⊗ₜ w2))
    simpa [ha, hc, Module.End.one_eq_id] using this

end GlobalTheory.OneFunctional
end
end

section

noncomputable section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem exists_piTensor_succ_equiv (m : ℕ) (F : Fin (m + 1) → Type) [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] :
    ∃ e : ((⨂[ℂ] j : Fin m, F j.succ) ⊗[ℂ] F 0) ≃ₗ[ℂ] (⨂[ℂ] j, F j),
      ∀ (f : ∀ j, F j), e (PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ f 0) = PiTensorProduct.tprod ℂ f := by
  let σ : Fin m ⊕ Unit ≃ Fin (m + 1) :=
    { toFun := Sum.elim Fin.succ (fun _ => 0)
      invFun := fun k => Fin.cases (motive := fun _ => Fin m ⊕ Unit) (Sum.inr ()) Sum.inl k
      left_inv := by rintro (j | ⟨⟩) <;> simp
      right_inv := by intro k; cases k using Fin.cases <;> simp }
  refine ⟨(TensorProduct.congr (LinearEquiv.refl ℂ _)
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Unit => F 0) ()).symm).trans
      ((PiTensorProduct.tmulEquivDep ℂ (fun i : Fin m ⊕ Unit => F (σ i))).trans
        (PiTensorProduct.reindex ℂ F σ.symm).symm), fun f => ?_⟩
  have h1 : TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] j : Fin m, F j.succ))
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Unit => F 0) ()).symm
      (PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ f 0) =
      PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ PiTensorProduct.tprod ℂ (fun _ : Unit => f 0) := by
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, PiTensorProduct.subsingletonEquiv_symm_apply']
  have h2 : PiTensorProduct.tmulEquivDep ℂ (fun i : Fin m ⊕ Unit => F (σ i))
      (PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ PiTensorProduct.tprod ℂ (fun _ : Unit => f 0)) =
      PiTensorProduct.tprod ℂ (fun i => f (σ i)) := by
    rw [← LinearEquiv.eq_symm_apply, PiTensorProduct.tmulEquivDep_symm_apply]
    all_goals rfl
  have h3 : (PiTensorProduct.reindex ℂ F σ.symm).symm (PiTensorProduct.tprod ℂ (fun i => f (σ i))) =
      PiTensorProduct.tprod ℂ f := by
    rw [LinearEquiv.symm_apply_eq, PiTensorProduct.reindex_tprod]
    all_goals rfl
  show (PiTensorProduct.reindex ℂ F σ.symm).symm (PiTensorProduct.tmulEquivDep ℂ (fun i : Fin m ⊕ Unit => F (σ i))
    (TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] j : Fin m, F j.succ))
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Unit => F 0) ()).symm
      (PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ f 0))) = PiTensorProduct.tprod ℂ f
  rw [h1]
  exact (congrArg (PiTensorProduct.reindex ℂ F σ.symm).symm h2).trans h3

theorem exists_piTensor_succ_equiv_map (m : ℕ) (F : Fin (m + 1) → Type) [∀ j, AddCommGroup (F j)]
    [∀ j, Module ℂ (F j)] :
    ∃ e : ((⨂[ℂ] j : Fin m, F j.succ) ⊗[ℂ] F 0) ≃ₗ[ℂ] (⨂[ℂ] j, F j),
      ∀ (A : ∀ j, F j →ₗ[ℂ] F j) (t : ⨂[ℂ] j : Fin m, F j.succ) (a : F 0),
        PiTensorProduct.map A (e (t ⊗ₜ a)) = e (PiTensorProduct.map (fun j : Fin m => A j.succ) t ⊗ₜ A 0 a) := by
  obtain ⟨e, he⟩ := exists_piTensor_succ_equiv m F
  refine ⟨e, fun A t a => ?_⟩
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h1 := he (Fin.cons a f : ∀ j, F j)
    have h2 := he (fun j => A j ((Fin.cons a f : ∀ j, F j) j))
    simp only [Fin.cons_succ, Fin.cons_zero] at h1 h2
    simp only [← TensorProduct.smul_tmul', map_smul, PiTensorProduct.map_tprod, h1, h2]
  | add x y hx hy =>
    simp only [TensorProduct.add_tmul, map_add (f := _), hx, hy]

private theorem factor_dual_lemma {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (p : X →ₗ[ℂ] Y) (hp : Function.Surjective p) (l : Module.Dual ℂ X) (hl : ∀ x, p x = 0 → l x = 0) :
    ∃ l' : Module.Dual ℂ Y, ∀ x, l x = l' (p x) := by
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
  refine ⟨l ∘ₗ s, fun x => ?_⟩
  have hps : p (s (p x)) = p x := by rw [← LinearMap.comp_apply p s, hs, LinearMap.id_apply]
  have h0 : p (x - s (p x)) = 0 := by rw [map_sub, hps, sub_self]
  have h1 := hl _ h0
  rw [map_sub, sub_eq_zero] at h1
  rw [LinearMap.comp_apply]
  exact h1

private theorem lTensor_ker_lemma_2 {Q N P : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup N] [Module ℂ N]
    [AddCommGroup P] [Module ℂ P] (g : N →ₗ[ℂ] P) (hg : Function.Surjective g)
    (l : Module.Dual ℂ (Q ⊗[ℂ] N)) (hl : ∀ q n, g n = 0 → l (q ⊗ₜ n) = 0) :
    ∀ z, LinearMap.lTensor Q g z = 0 → l z = 0 := by
  intro z hz
  obtain ⟨y, rfl⟩ := ((lTensor_exact Q (LinearMap.exact_subtype_ker_map g) hg) z).mp hz
  clear hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul q k =>
    rw [LinearMap.lTensor_tmul]
    exact hl q k.1 (LinearMap.mem_ker.mp k.2)
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, add_zero]

theorem contracts_chain : ∀ (m : ℕ) (G : Fin (m + 1) → Type) [∀ j, Monoid (G j)] (F : Fin m → Type) [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] (V : Fin (m + 1) → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (φ : ∀ j : Fin m, Representation ℂ (G j.castSucc × G j.succ) (F j)) (σ : ∀ j, Representation ℂ (G j) (V j)), (∀ j : Fin m, Contracts (φ j) (σ j.castSucc) (σ j.succ)) → ∃ π : ((⨂[ℂ] j, F j) ⊗[ℂ] V 0) →ₗ[ℂ] V (Fin.last m), Function.Surjective π ∧ (∀ (g : ∀ j, G j) (f : ⨂[ℂ] j, F j) (v : V 0), π (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ[ℂ] σ 0 (g 0) v) = σ (Fin.last m) (g (Fin.last m)) (π (f ⊗ₜ[ℂ] v))) ∧ ∀ l : Module.Dual ℂ ((⨂[ℂ] j, F j) ⊗[ℂ] V 0), (∀ g : ∀ j, G j, g (Fin.last m) = 1 → ∀ (f : ⨂[ℂ] j, F j) (v : V 0), l (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ[ℂ] σ 0 (g 0) v) = l (f ⊗ₜ[ℂ] v)) → ∀ x, π x = 0 → l x = 0 := by
  intro m
  induction m with
  | zero =>
    intro G _ F _ _ V _ _ φ σ _
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ((⨂[ℂ] j : Fin 0, F j) ⊗[ℂ] V 0) ≃ₗ[ℂ] V 0,
        ∀ (f : ⨂[ℂ] j : Fin 0, F j) (v : V 0), ψ (f ⊗ₜ v) = PiTensorProduct.isEmptyEquiv (Fin 0) f • v :=
      ⟨(TensorProduct.congr (PiTensorProduct.isEmptyEquiv (Fin 0)) (LinearEquiv.refl ℂ (V 0))).trans
        (TensorProduct.lid ℂ (V 0)), fun f v => by simp⟩
    have hmap : ∀ (A : ∀ j : Fin 0, F j →ₗ[ℂ] F j) (f : ⨂[ℂ] j : Fin 0, F j),
        PiTensorProduct.isEmptyEquiv (Fin 0) (PiTensorProduct.map A f) =
          PiTensorProduct.isEmptyEquiv (Fin 0) f := by
      intro A f
      induction f using PiTensorProduct.induction_on with
      | smul_tprod r x => simp [PiTensorProduct.map_tprod]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    refine ⟨ψ.toLinearMap, ψ.surjective, ?_, ?_⟩
    · intro g f v
      simp only [LinearEquiv.coe_coe]
      rw [hψ, hψ, hmap, map_smul]
      all_goals rfl
    · intro l _ x hx
      have hx' : ψ x = 0 := hx
      rw [ψ.map_eq_zero_iff] at hx'
      rw [hx', map_zero]
  | succ m ih =>
    intro G _ F _ _ V _ _ φ σ hc
    obtain ⟨e, he⟩ := exists_piTensor_succ_equiv_map m F
    have hc0 : Contracts (φ 0) (σ 0) (σ (Fin.succ 0)) := hc 0
    obtain ⟨π₀, hs₀, he₀, hk₀⟩ := hc0
    obtain ⟨π', hs', he', hk'⟩ := ih (fun j => G j.succ) (fun j => F j.succ) (fun j => V j.succ)
      (fun j => φ j.succ) (fun j => σ j.succ) (fun j => hc j.succ)
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ((⨂[ℂ] j, F j) ⊗[ℂ] V 0) ≃ₗ[ℂ]
        ((⨂[ℂ] j : Fin m, F j.succ) ⊗[ℂ] (F 0 ⊗[ℂ] V 0)),
        ∀ t a v, ψ (e (t ⊗ₜ a) ⊗ₜ v) = t ⊗ₜ (a ⊗ₜ v) :=
      ⟨(TensorProduct.congr e.symm (LinearEquiv.refl ℂ _)).trans (TensorProduct.assoc ℂ _ _ _),
        fun t a v => by simp⟩
    refine ⟨π' ∘ₗ LinearMap.lTensor _ π₀ ∘ₗ ψ.toLinearMap,
      hs'.comp ((LinearMap.lTensor_surjective _ hs₀).comp ψ.surjective), ?_, ?_⟩
    · intro g f v
      show π' (LinearMap.lTensor _ π₀ (ψ (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ
        σ 0 (g 0) v))) = σ (Fin.last (m + 1)) (g (Fin.last (m + 1))) (π' (LinearMap.lTensor _ π₀ (ψ (f ⊗ₜ v))))
      obtain ⟨y, rfl⟩ := e.surjective f
      induction y using TensorProduct.induction_on with
      | zero =>
        simp only [map_zero, TensorProduct.zero_tmul]
        all_goals exact (map_zero _).symm
      | tmul t a =>
        rw [he, hψ, hψ, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
        have h0 : π₀ (φ 0 (g (Fin.castSucc 0), g (Fin.succ 0)) a ⊗ₜ σ 0 (g 0) v) =
            σ (Fin.succ 0) (g (Fin.succ 0)) (π₀ (a ⊗ₜ v)) := he₀ _ _ a v
        rw [h0]
        exact he' (fun j => g j.succ) t (π₀ (a ⊗ₜ v))
      | add y₁ y₂ h₁ h₂ =>
        simp only [map_add (f := _), TensorProduct.add_tmul] at h₁ h₂ ⊢
        rw [h₁, h₂]
    · intro l hl x hx
      obtain ⟨L, hL⟩ : ∃ L : Module.Dual ℂ ((⨂[ℂ] j : Fin m, F j.succ) ⊗[ℂ] (F 0 ⊗[ℂ] V 0)),
          ∀ z, L z = l (ψ.symm z) := ⟨l ∘ₗ ψ.symm.toLinearMap, fun z => rfl⟩
      have hLe : ∀ t a v, L (t ⊗ₜ (a ⊗ₜ v)) = l (e (t ⊗ₜ a) ⊗ₜ v) := by
        intro t a v
        rw [hL, ← hψ t a v, LinearEquiv.symm_apply_apply]

      have hA : ∀ t u, π₀ u = 0 → L (t ⊗ₜ u) = 0 := by
        intro t u hu
        refine hk₀ (L.comp (TensorProduct.mk ℂ _ _ t)) ?_ u hu
        intro h a v
        simp only [LinearMap.comp_apply, TensorProduct.mk_apply, hLe]
        obtain ⟨gs, hg0, hg0', hg1, hg2, hg3, hgl⟩ : ∃ gs : ∀ j, G j, gs (Fin.castSucc 0) = h ∧ gs 0 = h ∧
            gs (Fin.succ 0) = 1 ∧ (∀ j : Fin m, gs j.succ.castSucc = 1) ∧ (∀ j : Fin m, gs j.succ.succ = 1) ∧
            gs (Fin.last (m + 1)) = 1 :=
          ⟨Pi.mulSingle (Fin.castSucc 0) h, Pi.mulSingle_eq_same _ _, Pi.mulSingle_eq_same _ _,
            Pi.mulSingle_eq_of_ne (by simp [Fin.ext_iff]) _, fun j => Pi.mulSingle_eq_of_ne (by simp [Fin.ext_iff]) _,
            fun j => Pi.mulSingle_eq_of_ne (by simp [Fin.ext_iff]) _, Pi.mulSingle_eq_of_ne (by simp [Fin.ext_iff]) _⟩
        have hinv := hl gs hgl (e (t ⊗ₜ a)) v
        rw [← hinv, he]
        simp only [hg0, hg0', hg1, hg2, hg3, ← Prod.one_eq_mk, map_one, PiTensorProduct.map_one,
          Module.End.one_apply]
        all_goals rfl
      have hB := lTensor_ker_lemma_2 π₀ hs₀ L (fun q n hn => hA q n hn)
      obtain ⟨L', hL'⟩ := factor_dual_lemma (LinearMap.lTensor _ π₀) (LinearMap.lTensor_surjective _ hs₀) L hB

      have hD : ∀ g' : ∀ j : Fin (m + 1), G j.succ, g' (Fin.last m) = 1 → ∀ t w,
          L' (PiTensorProduct.map (fun j : Fin m => φ j.succ ((g' j.castSucc : G j.succ.castSucc), g' j.succ)) t ⊗ₜ σ (Fin.succ 0) (g' 0) w) =
            L' (t ⊗ₜ w) := by
        intro g' hg' t w
        obtain ⟨u, rfl⟩ := hs₀ w
        induction u using TensorProduct.induction_on with
        | zero => simp only [map_zero, TensorProduct.tmul_zero]
        | tmul a v =>
          rw [← he₀ 1 (g' 0) a v]
          have k1 := hL' (PiTensorProduct.map (fun j : Fin m => φ j.succ ((g' j.castSucc : G j.succ.castSucc), g' j.succ)) t ⊗ₜ
            (φ 0 (1, g' 0) a ⊗ₜ σ 0 1 v))
          have k2 := hL' (t ⊗ₜ (a ⊗ₜ v))
          rw [LinearMap.lTensor_tmul, hLe] at k1 k2
          have hinv := hl (Fin.cons (1 : G 0) g' : ∀ j, G j)
            (by rw [← Fin.succ_last, Fin.cons_succ]; exact hg') (e (t ⊗ₜ a)) v
          rw [he] at hinv
          exact k1.symm.trans (hinv.trans k2)
        | add u₁ u₂ h₁ h₂ => simp only [map_add (f := _), TensorProduct.tmul_add, h₁, h₂]
      have hx' : π' (LinearMap.lTensor _ π₀ (ψ x)) = 0 := hx
      have h1 := hk' L' hD _ hx'
      rw [← hL', hL, LinearEquiv.symm_apply_apply] at h1
      exact h1

end GlobalTheory.OneFunctional
end
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem iso_outer_dual (ι G : Type) [Fintype ι] [Group G] (V : ι → Type) [∀ τ, AddCommGroup (V τ)]
    [∀ τ, Module ℂ (V τ)] [∀ τ, FiniteDimensional ℂ (V τ)] (ρ : ∀ τ, Representation ℂ G (V τ)) :
    Iso (outer ρ).dual (outer fun τ => (ρ τ).dual) := by
  classical
  refine Iso.symm ⟨PiTensorProduct.dualDistribEquiv, fun g t => ?_⟩
  have hD : ∀ s, (PiTensorProduct.dualDistribEquiv (R := ℂ) (M := V)) s = PiTensorProduct.dualDistrib s :=
    fun _ => rfl
  rw [hD, hD]

  suffices h : PiTensorProduct.dualDistrib ∘ₗ (outer fun τ => (ρ τ).dual) g =
      (outer ρ).dual g ∘ₗ (PiTensorProduct.dualDistrib (R := ℂ) (M := V)) by
    exact LinearMap.congr_fun h t
  refine PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)
  refine PiTensorProduct.ext (MultilinearMap.ext fun m => ?_)
  simp [outer_apply, Representation.dual_apply, PiTensorProduct.map_tprod, Pi.inv_apply,
    Module.Dual.transpose_apply, LinearMap.comp_apply]

end GlobalTheory.OneFunctional
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sobolevContinuous_modelRep_of_sobolevBound : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (ℓ : M.H τ →ₗ[ℂ] ℂ)
    (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) →
    (∀ w, SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w → ‖ℓ w‖ ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w) →
    Sobolev₂ (lieAt V τ) (M.rep τ) ℓ := by
  first | exact @GlobalTheory.SobFrame.sobCont_rep_of_bound | exact GlobalTheory.SobFrame.sobCont_rep_of_bound | (intros; apply GlobalTheory.SobFrame.sobCont_rep_of_bound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalFrameStabiliser_normalises_unipotentRadical : ∀ (D : D7) (W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L → (∀ γ ∈ GQ W, ∀ γ₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W γ = γ₀.map (incA D) → γ₀ * L = L → ∀ n ∈ NI W L, γ * n * γ⁻¹ ∈ NI W L) ∧ (∀ n ∈ NI W L, ∀ n₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W n = n₀.map (incA D) → n₀ * L = L) := by
  first | exact @GlobalTheory.FrameStab.stab | exact GlobalTheory.FrameStab.stab | (intros; apply GlobalTheory.FrameStab.stab <;> assumption)
end
