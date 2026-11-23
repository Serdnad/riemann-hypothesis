module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle512
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
private theorem exists_mulBy_pow_eq_comp_resOne' {p : ℕ} {R : Type} [CommRing R]
    (G : _root_.GlobalTheory.PDivGroup p R) (n : ℕ) :
    ∃ M : G.A 1 →ₐc[R] G.A (n + 1),
      ∀ a : G.A (n + 1),
        _root_.GlobalTheory.PDiv.mulBy R (G.A (n + 1)) (p ^ n) a = M (G.resOne n a) := by
  induction n with
  | zero =>
    refine ⟨BialgHom.id R (G.A 1), fun a => ?_⟩
    have h := _root_.GlobalTheory.PDiv.mulBy_comp (BialgHom.id R (G.A 1)) 1
    rw [pow_one, toConv_ofConv] at h
    rw [_root_.GlobalTheory.PDivGroup.resOne_zero]
    simpa using congrArg (fun f : G.A 1 →ₐc[R] G.A 1 => f a) h
  | succ n ih =>
    obtain ⟨M, hM⟩ := ih
    refine ⟨(G.mulP (n + 1)).comp M, fun a => ?_⟩
    rw [pow_succ, ← _root_.GlobalTheory.PDiv.mulBy_mulBy, ← _root_.GlobalTheory.PDivGroup.mulP_res,
      ← _root_.GlobalTheory.PDiv.map_mulBy, hM, _root_.GlobalTheory.PDivGroup.resOne_succ, BialgHom.comp_apply]


set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
theorem _root_.GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R)
    (n : ℕ) (a : G.A (n + 1))
    (ha : G.transl n a = a ⊗ₜ[R] 1) :
    ∃ e : G.A n, G.mulP n e = a := by
  obtain ⟨M, hM⟩ := exists_mulBy_pow_eq_comp_resOne' G n
  have key : ∀ χ φ : _root_.GlobalTheory.CartierDual R (G.A (n + 1)),
      (χ * _root_.GlobalTheory.CartierDual.map
        (_root_.GlobalTheory.PDiv.mulBy R (G.A (n + 1)) (p ^ n)) φ).ofConv a =
        χ.ofConv a * φ.ofConv 1 := by
    intro χ φ
    have h1 : (_root_.GlobalTheory.CartierDual.map
        (_root_.GlobalTheory.PDiv.mulBy R (G.A (n + 1)) (p ^ n)) φ).ofConv =
        (φ.ofConv ∘ₗ (M : G.A 1 →ₗ[R] G.A (n + 1))) ∘ₗ
          (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1) := by
      ext x
      simp [_root_.GlobalTheory.CartierDual.map_apply, hM]
    rw [_root_.GlobalTheory.CartierDual.mul_apply, _root_.GlobalTheory.CartierDual.pair_tmul, h1]
    have h2 : ∀ t, TensorProduct.map χ.ofConv
        ((φ.ofConv ∘ₗ (M : G.A 1 →ₗ[R] G.A (n + 1))) ∘ₗ
          (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1)) t =
        TensorProduct.map χ.ofConv
          (φ.ofConv ∘ₗ (M : G.A 1 →ₗ[R] G.A (n + 1)))
          (LinearMap.lTensor _
            (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1) t) := by
      intro t
      rw [LinearMap.lTensor, ← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id]
    rw [h2, ← _root_.GlobalTheory.PDivGroup.transl_apply, ha]
    simp
  let K : Ideal (_root_.GlobalTheory.CartierDual R (G.A (n + 1))) :=
    { carrier := {ψ | ∀ χ : _root_.GlobalTheory.CartierDual R (G.A (n + 1)), (χ * ψ).ofConv a = 0}
      add_mem' := by
        intro x y hx hy χ
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [mul_add, ofConv_add, LinearMap.add_apply, hx, hy, add_zero]
      zero_mem' := by
        intro χ
        simp
      smul_mem' := by
        intro c x hx χ
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
        rw [← mul_assoc]
        exact hx _ }
  have hK : _root_.GlobalTheory.PDiv.torsionIdeal (R := R) (A := _root_.GlobalTheory.CartierDual R (G.A (n + 1))) (p ^ n) ≤
      RingHom.ker (Ideal.Quotient.mkₐ R K) := by
    change _root_.GlobalTheory.PDiv.kerIdeal (_root_.GlobalTheory.PDiv.mulBy R _ (p ^ n)) ≤ _
    rw [Ideal.map_le_iff_le_comap]
    intro φ hφ
    have hφ₀ : CoalgebraStruct.counit (R := R) φ = 0 := hφ
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change Ideal.Quotient.mkₐ R K (_root_.GlobalTheory.PDiv.mulBy R _ (p ^ n) φ) = 0
    rw [← _root_.GlobalTheory.PDiv.dual_mulBy, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    intro χ
    rw [key, ← _root_.GlobalTheory.CartierDual.counit_apply, hφ₀, mul_zero]
  have hker : ∀ ψ, _root_.GlobalTheory.CartierDual.map (G.mulP n) ψ = 0 →
      ψ.ofConv a = 0 := by
    intro ψ hψ
    have h3 : ψ ∈ RingHom.ker (Ideal.Quotient.mkₐ R K) := by
      apply hK
      rw [← _root_.GlobalTheory.PDivGroup.ker_dual_mulP]
      exact hψ
    rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h3
    simpa using h3 1
  set πL : _root_.GlobalTheory.CartierDual R (G.A (n + 1)) →ₗ[R] _root_.GlobalTheory.CartierDual R (G.A n) :=
    (_root_.GlobalTheory.CartierDual.map (G.mulP n) :
      _root_.GlobalTheory.CartierDual R (G.A (n + 1)) →ₗ[R] _root_.GlobalTheory.CartierDual R (G.A n))
    with hπL
  have hs : Function.Surjective πL := _root_.GlobalTheory.PDivGroup.dual_mulP_surjective G n
  set evL : _root_.GlobalTheory.CartierDual R (G.A (n + 1)) →ₗ[R] R :=
    (_root_.GlobalTheory.CartierDual.cartierDualToBidual R (G.A (n + 1)) a).ofConv with hevL
  have hle : LinearMap.ker πL ≤ LinearMap.ker evL := by
    intro ψ hψ
    exact hker ψ hψ
  let L : _root_.GlobalTheory.CartierDual R (G.A n) →ₗ[R] R :=
    ((LinearMap.ker πL).liftQ evL hle).comp (πL.quotKerEquivOfSurjective hs).symm.toLinearMap
  have hL : ∀ ψ, L (πL ψ) = ψ.ofConv a := by
    intro ψ
    have h4 : (πL.quotKerEquivOfSurjective hs).symm (πL ψ) = Submodule.Quotient.mk ψ := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, h4, Submodule.liftQ_apply]
    rfl
  obtain ⟨e, he⟩ :=
    (_root_.GlobalTheory.CartierDual.toBidual_bijective (R := R) (M := G.A n)).2 (toConv L)
  refine ⟨e, (_root_.GlobalTheory.CartierDual.toBidual_bijective (R := R) (M := G.A (n + 1))).1 ?_⟩
  apply WithConv.ext
  ext ψ
  show ψ.ofConv (G.mulP n e) = ψ.ofConv a
  rw [← _root_.GlobalTheory.CartierDual.map_apply]
  have h5 := congrArg
    (fun x => x.ofConv (_root_.GlobalTheory.CartierDual.map (G.mulP n) ψ)) he
  simp only [ofConv_toConv] at h5
  rw [← hL ψ]
  exact h5

end GlobalTheory.PDivGroup
end
end

section

open scoped TensorProduct

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra GlobalTheory.PDiv

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

open scoped TensorProduct in
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
theorem _root_.GlobalTheory.PDivGroup.ker_resOne (n : ℕ) :
    RingHom.ker (G.resOne n :
      G.A (n + 1) →ₐ[R] G.A 1) =
      _root_.GlobalTheory.PDiv.torsionIdeal (R := R) (A := G.A (n + 1)) p := by
  induction n with
  | zero =>
    have hid : (G.resOne 0 :
        G.A 1 →ₐ[R] G.A 1) = AlgHom.id R _ := by
      ext a; exact G.resOne_zero a
    rw [hid]
    refine le_antisymm ?_ ?_
    · intro a ha
      have : a = 0 := ha
      simp [this]
    · refine (_root_.GlobalTheory.PDiv.torsionIdeal_le_ker_iff p
        (AlgHom.id R (G.A (0 + 1)))).2 ?_
      simpa using G.pts_pow_self 1 (WithConv.toConv (AlgHom.id R (G.A 1)))
  | succ n ih =>
    have hcomp : (G.resOne (n + 1) :
        G.A (n + 2) →ₐ[R] G.A 1) =
        (G.resOne n :
          G.A (n + 1) →ₐ[R] G.A 1).comp
          (G.res (n + 1) :
            G.A (n + 2) →ₐ[R] G.A (n + 1)) := by
      ext a; exact G.resOne_succ n a
    have hsurj : Function.Surjective (G.res (n + 1) :
        G.A (n + 2) →ₐ[R] G.A (n + 1)) :=
      G.res_surjective (n + 1)
    have hker : RingHom.ker ((G.resOne n :
        G.A (n + 1) →ₐ[R] G.A 1).comp
          (G.res (n + 1) :
            G.A (n + 2) →ₐ[R] G.A (n + 1))) =
        Ideal.comap (G.res (n + 1) :
          G.A (n + 2) →ₐ[R] G.A (n + 1))
          (RingHom.ker (G.resOne n :
            G.A (n + 1) →ₐ[R] G.A 1)) := by
      ext a; exact Iff.rfl
    rw [hcomp, hker, ih, ← _root_.GlobalTheory.PDiv.map_torsionIdeal
      (G.res_surjective (n + 1)) p]
    erw [Ideal.comap_map_of_surjective _ hsurj]
    refine sup_eq_left.mpr ?_
    have h0 : Ideal.comap (G.res (n + 1) :
        G.A (n + 2) →ₐ[R] G.A (n + 1)) ⊥ =
        _root_.GlobalTheory.PDiv.torsionIdeal (R := R) (A := G.A (n + 2)) (p ^ (n + 1)) := by
      rw [← G.ker_res (n + 1)]
      ext a; exact Iff.rfl
    rw [h0]
    exact _root_.GlobalTheory.PDiv.torsionIdeal_le_of_dvd (dvd_pow_self p (Nat.succ_ne_zero n))

open scoped TensorProduct in
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
theorem _root_.GlobalTheory.PDivGroup.kerIdeal_mulP (n : ℕ) :
    _root_.GlobalTheory.PDiv.kerIdeal (G.mulP n) =
      _root_.GlobalTheory.PDiv.torsionIdeal (R := R) (A := G.A (n + 1)) p := by
  unfold _root_.GlobalTheory.PDiv.torsionIdeal
  rw [← G.mulP_comp_res n,
    _root_.GlobalTheory.PDiv.kerIdeal_comp_of_surjective _ (G.res_surjective n)]

end PDivGroup

section TensorQuot

variable {R k M : Type} [CommRing R] [CommRing k] [Algebra R k] [AddCommGroup M] [Module R M]

end TensorQuot

namespace PDivGroup

end PDivGroup

open scoped TensorProduct in
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra in
private theorem mem_ker_smul_univ_of_one_tmul_eq_zero {R k M : Type} [CommRing R] [CommRing k]
    [Algebra R k] [AddCommGroup M] [Module R M] (hk : Function.Surjective (algebraMap R k))
    {m : M} (hm : (1 : k) ⊗ₜ[R] m = 0) :
    m ∈ RingHom.ker (algebraMap R k) • (⊤ : Submodule R M) := by
  set f : R →ₐ[R] k := Algebra.ofId R k
  have hf : Function.Surjective f := hk
  let e : (R ⧸ RingHom.ker f) ≃ₐ[R] k := Ideal.quotientKerAlgEquivOfSurjective hf
  have hker : RingHom.ker f = RingHom.ker (algebraMap R k) := rfl
  let g : k ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker f • (⊤ : Submodule R M)) :=
    (LinearEquiv.rTensor M e.symm.toLinearEquiv).trans
      (quotTensorEquivQuotSMul M (RingHom.ker f))
  have h1 : e.symm 1 = Ideal.Quotient.mk (RingHom.ker f) 1 := by simp
  have h2 : g ((1 : k) ⊗ₜ[R] m) = Submodule.Quotient.mk m := by
    simp only [g, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
      AlgEquiv.toLinearEquiv_apply, h1, quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rw [hm, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at h2
  exact hker ▸ h2

open scoped TensorProduct in
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra in
theorem _root_.GlobalTheory.fibre_statement : ∀ (p : ℕ) (R k : Type) [CommRing R] [CommRing k]
    [Algebra R k], Function.Surjective (algebraMap R k) → ∀ (G : _root_.GlobalTheory.PDivGroup p R) (n : ℕ),
      Function.Surjective (fun a : G.A (n + 1) =>
        ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1)) ∧
      ∀ a : G.A (n + 1),
        ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1) = 0 ↔
          a ∈ (RingHom.ker ((algebraMap R k).comp
            (Bialgebra.counitAlgHom R (G.A n) :
              G.A n →+* R))).map
            ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) :
              G.A n →+* G.A (n + 1)) := by
  intro p R k _ _ _ hk G n
  set ρ := G.resOne n
  set μ := G.mulP n
  set J := RingHom.ker ((algebraMap R k).comp
    (Bialgebra.counitAlgHom R (G.A n) : G.A n →+* R))
  set L := J.map ((μ : G.A n →ₐ[R] G.A (n + 1)) :
    G.A n →+* G.A (n + 1))
  have hρ : Function.Surjective ρ := G.resOne_surjective n
  have hJ : ∀ x : G.A n, x ∈ J ↔
      algebraMap R k (Bialgebra.counitAlgHom R (G.A n) x) = 0 :=
    fun x => Iff.rfl
  refine ⟨?_, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c x =>
      obtain ⟨r, rfl⟩ := hk c
      obtain ⟨y, rfl⟩ := hρ x
      refine ⟨r • y, ?_⟩
      show (1 : k) ⊗ₜ[R] ρ (r • y) = _
      rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.algebraMap_eq_smul_one]
    | add s t hs ht =>
      obtain ⟨a, rfl⟩ := hs
      obtain ⟨b, rfl⟩ := ht
      exact ⟨a + b, by simp [TensorProduct.tmul_add]⟩
  · have hmem := mem_ker_smul_univ_of_one_tmul_eq_zero hk ha
    have hle : RingHom.ker (algebraMap R k) • (⊤ : Submodule R (G.A 1)) ≤
        (L.restrictScalars R).map
          (ρ : G.A (n + 1) →ₐ[R] G.A 1).toLinearMap := by
      refine Submodule.smul_le.mpr fun r hr x _ => ?_
      obtain ⟨y, rfl⟩ := hρ x
      refine ⟨r • y, ?_, map_smul _ r y⟩
      show r • y ∈ L
      rw [Algebra.smul_def]
      refine Ideal.mul_mem_right _ _ ?_
      have h1 : algebraMap R (G.A (n + 1)) r =
          (μ : G.A n →ₐ[R] G.A (n + 1))
            (algebraMap R (G.A n) r) := (AlgHom.commutes _ r).symm
      rw [h1]
      refine Ideal.mem_map_of_mem _ ((hJ _).mpr ?_)
      rw [AlgHom.commutes]
      exact hr
    obtain ⟨b, hb, hab⟩ := hle hmem
    have hker : a - b ∈ RingHom.ker
        (ρ : G.A (n + 1) →ₐ[R] G.A 1) := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact hab.symm
    rw [_root_.GlobalTheory.PDivGroup.ker_resOne,
      ← _root_.GlobalTheory.PDivGroup.kerIdeal_mulP] at hker
    have haug : _root_.GlobalTheory.PDiv.kerIdeal μ ≤ L := by
      unfold _root_.GlobalTheory.PDiv.kerIdeal
      refine Ideal.map_mono fun x hx => (hJ x).mpr ?_
      rw [show Bialgebra.counitAlgHom R (G.A n) x = 0 from hx, map_zero]
    have := L.add_mem (haug hker) hb
    rwa [sub_add_cancel] at this
  · let ψ : G.A (n + 1) →+* k ⊗[R] G.A 1 :=
      (Algebra.TensorProduct.includeRight :
        G.A 1 →ₐ[R] k ⊗[R] G.A 1).toRingHom.comp
        (ρ : G.A (n + 1) →ₐ[R] G.A 1).toRingHom
    have hL : L ≤ RingHom.ker ψ := by
      refine Ideal.map_le_iff_le_comap.mpr fun j hj => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      show (1 : k) ⊗ₜ[R] ρ (μ j) = 0
      rw [G.resOne_mulP, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]
      have := (hJ j).mp hj
      rw [Bialgebra.counitAlgHom_apply] at this
      rw [this, TensorProduct.zero_tmul]
    exact hL ha

end GlobalTheory
end
end

section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

variable {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [CommRing R']
  [Algebra R R']

theorem cobOne_baseChange :
    cobOne R' (R' ⊗[R] A) = (AlgebraTensorModule.distribBaseChange R R' A A).toLinearMap ∘ₗ
      (cobOne R A).baseChange R' := by
  refine AlgebraTensorModule.ext fun r a => ?_
  rw [← mul_one r, ← smul_eq_mul, ← smul_tmul', map_smul, map_smul]
  congr 1
  have h : ∀ c : A ⊗[R] A, AlgebraTensorModule.tensorTensorTensorComm R R' R R' R' R' A A
      (comul (R := R') (1 : R') ⊗ₜ[R] c) = AlgebraTensorModule.distribBaseChange R R' A A (1 ⊗ₜ c) := by
    intro c
    induction c with
    | add x y hx hy => simp only [tmul_add, map_add (f := _), hx, hy]
    | tmul x y => simp [Bialgebra.comul_one, Algebra.TensorProduct.one_def]
  simp only [cobOne_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.baseChange_tmul, tmul_sub, map_sub, TensorProduct.comul_tmul, h,
    AlgebraTensorModule.distribBaseChange_tmul, Algebra.TensorProduct.one_def]

end GlobalTheory.PDiv

namespace GlobalTheory.PDiv

theorem liftSemi_prim_baseChange_bijective {R A : Type} (R' : Type) [CommRing R] [CommRing A]
    [Bialgebra R A] [CommRing R'] [Algebra R R'] [Module.Flat R R'] :
    Function.Bijective (liftSemi (toBaseChange R R' A).prim) := by
  set K := LinearMap.ker (cobOne R A)
  have hsub : ∀ y : R' ⊗[R] K,
      (liftSemi (toBaseChange R R' A).prim y).1 = K.subtype.lTensor R' y := by
    intro y
    induction y with
    | add x y hx hy => simp only [map_add (f := _), Submodule.coe_add, hx, hy]
    | tmul r b =>
      rw [liftSemi_tmul, Submodule.coe_smul, SemiBialgHom.prim_val, toBaseChange_apply,
        LinearMap.lTensor_tmul, Submodule.subtype_apply, smul_tmul', smul_eq_mul, mul_one]
  have hex := Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map (cobOne R A))
  refine ⟨fun x y h => ?_, fun z => ?_⟩
  · apply Module.Flat.lTensor_preserves_injective_linearMap (M := R') K.subtype K.injective_subtype
    simpa only [hsub] using congrArg Subtype.val h
  · obtain ⟨x, hx⟩ := z
    have hz : (cobOne R A).lTensor R' x = 0 := by
      have h0 : cobOne R' (R' ⊗[R] A) x = 0 := hx
      rw [cobOne_baseChange, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.map_eq_zero_iff, LinearMap.baseChange_eq_ltensor] at h0
      exact h0
    obtain ⟨y, hy⟩ := (hex x).1 hz
    exact ⟨y, Subtype.ext ((hsub y).trans hy)⟩

end GlobalTheory.PDiv
end

section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDiv

theorem liftSemi_toBaseChange_cot_bijective (R R' A : Type) [CommRing R] [CommRing R'] [Algebra R R']
    [CommRing A] [Bialgebra R A] : Function.Bijective (liftSemi (toBaseChange R R' A).cot) := by
  have heq : (counitAlgHom R' (R' ⊗[R] A)).comp
      ((AlgEquiv.refl : (R' ⊗[R] A) ≃ₐ[R'] (R' ⊗[R] A)) : (R' ⊗[R] A) →ₐ[R'] (R' ⊗[R] A)) =
      AugCot.baseChangeAug R' (counitAlgHom R A) := by
    apply Algebra.TensorProduct.ext'
    intro r a
    simp [AugCot.baseChangeAug_tmul, Algebra.smul_def, mul_comm]
  let E : R' ⊗[R] Cot R A ≃ₗ[R'] Cot R' (R' ⊗[R] A) :=
    (AugCot.baseChangeEquiv R' (counitAlgHom R A)).trans (AugCot.congr AlgEquiv.refl heq)
  have hmap : liftSemi (toBaseChange R R' A).cot = E.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r m
    obtain ⟨a, rfl⟩ := AugCot.d_surjective (counitAlgHom R A) m
    simp only [liftSemi_tmul, LinearEquiv.coe_coe, E, LinearEquiv.trans_apply,
      AugCot.baseChangeEquiv_tmul_d, map_smul, AugCot.congr_d]
    exact congrArg (r • ·) ((toBaseChange R R' A).cot_d a)
  rw [hmap]
  exact E.bijective

end PDiv

namespace PDivGroup

theorem omega_baseChange_bijective {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (R' : Type)
    [CommRing R'] [Algebra R R'] (hp : (p : R) = 0) :
    Function.Bijective (liftSemi (G.toBase R').omega) := by
  have hp' : (p : R') = 0 := by rw [← map_natCast (algebraMap R R'), hp, map_zero]
  have hL := G.omegaLevel_one_bijective hp
  have hL' := (G.baseChange R').omegaLevel_one_bijective hp'
  have hg := liftSemi_toBaseChange_cot_bijective R R' (G.A 1)
  let e : R' ⊗[R] G.omega ≃ₗ[R'] R' ⊗[R] Cot R (G.A 1) :=
    LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofBijective (G.omegaLevel 1) hL)
  have hcomp : ((G.baseChange R').omegaLevel 1).comp (liftSemi (G.toBase R').omega) =
      (liftSemi (toBaseChange R R' (G.A 1)).cot).comp e.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, liftSemi_tmul, map_smul, e,
      LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply]
    rfl
  refine Function.Bijective.of_comp_left ?_ hL'.injective
  change Function.Bijective (((G.baseChange R').omegaLevel 1).comp (liftSemi (G.toBase R').omega))
  rw [hcomp]
  exact hg.comp e.bijective

end PDivGroup

end GlobalTheory
end
