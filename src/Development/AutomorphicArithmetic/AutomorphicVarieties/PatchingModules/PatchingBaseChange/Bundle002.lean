module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle067
public import Mathlib.RingTheory.PowerSeries.Basic
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
public import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
public import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Lift

@[expose] public section

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.star_map :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [CommRing O'] [Algebra ℤ_[l] O'] (R R' : Type) [CommRing R] [Algebra O R] [CommRing R'] [Algebra O' R'] (g : R →+* R'), (∀ a : ℤ_[l], g (algebraMap O R (algebraMap ℤ_[l] O a)) = algebraMap O' R' (algebraMap ℤ_[l] O' a)) → (pushCh g (F.eps O R) = F.eps O' R') ∧ (∀ n y, MonoidAlgebra.mapRingHom F.G₀ g (F.star O R n y) = F.star O' R' n (MonoidAlgebra.mapRingHom F.G₀ g y)) ∧ ∀ (n : ℕ) (v : F.Vl) (ψ : Fin n → F.Gv v →* Rˣ) (γ : Fin n → F.Gv v), MonoidAlgebra.mapRingHom F.G₀ g (F.oEl v ψ γ) = F.oEl v (fun i => pushCh g (ψ i)) γ := by
  intro l _ F O O' _ _ _ _ R R' _ _ _ _ g hg
  have h1 : pushCh g (F.eps O R) = F.eps O' R' := by
    ext x
    simp [GFrame.eps, pushCh, hg]
  have hs : ∀ (S : Type) [CommRing S] [Algebra O S] (n : ℕ) (h : F.G₀) (r : S), F.star O S n (MonoidAlgebra.single h r) = MonoidAlgebra.single (F.conj h)⁻¹ (r * ((F.eps O S h ^ (1 - (n : ℤ)) : Sˣ) : S)) := by
    intro S _ _ n h r
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have hs' : ∀ (S : Type) [CommRing S] [Algebra O' S] (n : ℕ) (h : F.G₀) (r : S), F.star O' S n (MonoidAlgebra.single h r) = MonoidAlgebra.single (F.conj h)⁻¹ (r * ((F.eps O' S h ^ (1 - (n : ℤ)) : Sˣ) : S)) := by
    intro S _ _ n h r
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have hadd : ∀ (n : ℕ) (a b : MonoidAlgebra R F.G₀), F.star O R n (a + b) = F.star O R n a + F.star O R n b := by
    intro n a b
    simp [GFrame.star]
  have hadd' : ∀ (n : ℕ) (a b : MonoidAlgebra R' F.G₀), F.star O' R' n (a + b) = F.star O' R' n a + F.star O' R' n b := by
    intro n a b
    simp [GFrame.star]
  have hz : ∀ (n : ℕ), F.star O R n 0 = 0 := by
    intro n
    simp [GFrame.star]
  have hz' : ∀ (n : ℕ), F.star O' R' n 0 = 0 := by
    intro n
    simp [GFrame.star]
  have he : ∀ (h : F.G₀) (k : ℤ), g ((F.eps O R h ^ k : Rˣ) : R) = ((F.eps O' R' h ^ k : R'ˣ) : R') := by
    intro h k
    rw [← h1, pushCh, MonoidHom.comp_apply, ← map_zpow (Units.map (g : R →* R'))]
    rfl
  refine ⟨h1, ?_, ?_⟩
  · intro n y
    induction y using MonoidAlgebra.induction_linear with
    | zero => rw [hz, map_zero, hz']
    | add a b ha hb => rw [hadd, map_add (f := _), ha, hb, map_add (f := _), hadd']
    | single h r =>
      rw [hs, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single, hs', map_mul, he]
  · intro n v ψ γ
    simp only [GFrame.oEl, map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    simp [Function.comp_def, map_sub, MonoidAlgebra.mapRingHom_single, pushCh]
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.exists_semilinear_equiv_baseChange_tensor :
    ∀ (B P B' P₁ P' : Type) [CommRing B] [CommRing P] [CommRing B'] [CommRing P₁] [CommRing P'] [Algebra B P] [Algebra B B'] [Algebra P P₁] [Algebra B' P'] (τ : P₁ ≃+* P') (M M' : Type) [AddCommGroup M] [Module B M] [AddCommGroup M'] [Module B' M'] (_μ : B' ⊗[B] M ≃ₗ[B'] M'), (∀ b, τ (algebraMap P P₁ (algebraMap B P b)) = algebraMap B' P' (algebraMap B B' b)) → ∃ e : P₁ ⊗[P] (P ⊗[B] M) ≃+ P' ⊗[B'] M', ∀ z w, e (z • w) = τ z • e w := by
  intro B P B' P₁ P' _ _ _ _ _ _ _ _ _ τ M M' _ _ _ _ μ h
  letI : Algebra P₁ P' := τ.toRingHom.toAlgebra
  letI : Algebra P P' := (τ.toRingHom.comp (algebraMap P P₁)).toAlgebra
  letI : Algebra B P' := ((algebraMap B' P').comp (algebraMap B B')).toAlgebra
  haveI : IsScalarTower P P₁ P' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower B B' P' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower B P P' := IsScalarTower.of_algebraMap_eq (fun b => (h b).symm)
  let t : P₁ ≃ₗ[P₁] P' :=
    { τ.toAddEquiv with
      map_smul' := fun a b => by
        show τ (a * b) = τ a * τ b
        exact map_mul τ a b }
  let e1 : P₁ ⊗[P] (P ⊗[B] M) ≃ₗ[P₁] P' ⊗[P] (P ⊗[B] M) :=
    TensorProduct.AlgebraTensorModule.congr t (LinearEquiv.refl P _)
  let e2 : P' ⊗[P] (P ⊗[B] M) ≃ₗ[P'] P' ⊗[B] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B P P' P' M
  let e3 : P' ⊗[B'] (B' ⊗[B] M) ≃ₗ[P'] P' ⊗[B] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B B' P' P' M
  let e4 : P' ⊗[B'] (B' ⊗[B] M) ≃ₗ[P'] P' ⊗[B'] M' :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl P' P') μ
  let f := e2.trans (e3.symm.trans e4)
  refine ⟨e1.toAddEquiv.trans f.toAddEquiv, fun z w => ?_⟩
  show f (e1 (z • w)) = τ z • f (e1 w)
  rw [map_smul, ← map_smul f]
  rfl
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem span_le_ker {R S : Type} [Ring R] [Ring S] (f : R →+* S) (I : Set R) (h : ∀ x ∈ I, f x = 0) :
    (TwoSidedIdeal.span I).ringCon ≤ RingCon.ker f := by
  intro x y hxy
  rw [RingCon.ker_apply, ← sub_eq_zero, ← map_sub]
  rw [TwoSidedIdeal.rel_iff] at hxy
  have hle : TwoSidedIdeal.span I ≤ TwoSidedIdeal.comap f ⊥ := by
    rw [TwoSidedIdeal.span_le]
    intro z hz
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, TwoSidedIdeal.mem_bot]
    exact h z hz
  have h1 := hle hxy
  rwa [TwoSidedIdeal.mem_comap, TwoSidedIdeal.mem_bot] at h1

private theorem mk_eq_zero {R : Type} [Ring R] (I : Set R) {x : R} (hx : x ∈ I) :
    (TwoSidedIdeal.span I).ringCon.mk' x = 0 := by
  rw [← map_zero (TwoSidedIdeal.span I).ringCon.mk']
  exact (RingCon.eq _).2 ((TwoSidedIdeal.rel_iff _ _ _).2 (by simpa using TwoSidedIdeal.subset_span hx))

theorem UpperTheory.V.Pa.BC.grp_quot_bc :
    ∀ (κ κ' G : Type) [Field κ] [Field κ'] [Algebra κ κ'] [Group G] (I : Set (MonoidAlgebra κ G)), Nonempty (κ' ⊗[κ] (TwoSidedIdeal.span I).ringCon.Quotient ≃+* (TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (algebraMap κ κ') '' I)).ringCon.Quotient) := by
  intro κ κ' G _ _ _ _ I
  let φ : MonoidAlgebra κ G →+* MonoidAlgebra κ' G := MonoidAlgebra.mapRingHom G (algebraMap κ κ')
  let J := (TwoSidedIdeal.span I).ringCon
  let J' := (TwoSidedIdeal.span (φ '' I)).ringCon
  let T := κ' ⊗[κ] J.Quotient
  have hφ : ∀ x ∈ I, ((RingCon.mk' J').comp φ) x = 0 := fun x hx =>
    mk_eq_zero _ ⟨x, hx, rfl⟩
  let g0 : J.Quotient →+* J'.Quotient := RingCon.lift J ((RingCon.mk' J').comp φ) (span_le_ker _ _ hφ)
  have hg0 : ∀ x, g0 (RingCon.mk' J x) = RingCon.mk' J' (φ x) := fun x => RingCon.lift_mk' _ x
  let g : J.Quotient →ₐ[κ] J'.Quotient :=
    { g0 with
      commutes' := fun r => by
        change g0 (RingCon.mk' J (algebraMap κ _ r)) = RingCon.mk' J' (algebraMap κ _ r)
        rw [hg0]
        congr 1
        simp [φ, MonoidAlgebra.coe_algebraMap, MonoidAlgebra.mapRingHom_single] }
  let α : T →ₐ[κ'] J'.Quotient :=
    Algebra.TensorProduct.lift (Algebra.ofId κ' J'.Quotient) g (fun x y => Algebra.commutes _ _)
  let β : MonoidAlgebra κ' G →ₐ[κ'] T :=
    MonoidAlgebra.lift κ' T G
      { toFun := fun m => (1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single m 1)
        map_one' := by
          change (1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single 1 1) = 1
          rw [← MonoidAlgebra.one_def, map_one]
          rfl
        map_mul' := fun a b => by
          change (1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single (a * b) 1) =
            ((1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single a 1)) *
              ((1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single b 1))
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← map_mul,
            MonoidAlgebra.single_mul_single, mul_one] }
  have hβs : ∀ (m : G) (c : κ'), β (MonoidAlgebra.single m c) =
      c • ((1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single m 1)) := by
    intro m c
    rw [MonoidAlgebra.lift_single]
    rfl
  have hβφ : ∀ x, β (φ x) = (1 : κ') ⊗ₜ RingCon.mk' J x := by
    intro x
    have key : (β : MonoidAlgebra κ' G →+* T).comp φ =
        ((Algebra.TensorProduct.includeRight : J.Quotient →ₐ[κ] T) : J.Quotient →+* T).comp (RingCon.mk' J) := by
      apply MonoidAlgebra.ringHom_ext
      · intro r
        simp only [RingHom.coe_comp, Function.comp_apply, φ, MonoidAlgebra.mapRingHom_single, RingHom.coe_coe, hβs]
        rw [TensorProduct.smul_tmul', algebraMap_smul, TensorProduct.smul_tmul,
          Algebra.TensorProduct.includeRight_apply]
        congr 1
        change r • ((MonoidAlgebra.single 1 1 : MonoidAlgebra κ G) : J.Quotient) =
          ((MonoidAlgebra.single 1 r : MonoidAlgebra κ G) : J.Quotient)
        rw [← RingCon.coe_smul, MonoidAlgebra.smul_single', mul_one]
      · intro m
        simp only [RingHom.coe_comp, Function.comp_apply, φ, MonoidAlgebra.mapRingHom_single, RingHom.coe_coe, hβs, map_one, one_smul]
        rfl
    exact congrArg (fun h => h x) key
  have hβ0 : ∀ y ∈ φ '' I, (β : MonoidAlgebra κ' G →+* T) y = 0 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [RingHom.coe_coe, hβφ, mk_eq_zero I hx, TensorProduct.tmul_zero]
  let β' : J'.Quotient →+* T := RingCon.lift J' (β : MonoidAlgebra κ' G →+* T) (span_le_ker _ _ hβ0)
  have hβ' : ∀ y, β' (RingCon.mk' J' y) = β y := fun y => RingCon.lift_mk' _ y
  let q' : MonoidAlgebra κ' G →ₐ[κ'] J'.Quotient :=
    { RingCon.mk' J' with commutes' := fun _ => rfl }
  have hα : ∀ (a : κ') (q : J.Quotient), α (a ⊗ₜ q) = algebraMap κ' J'.Quotient a * g0 q :=
    fun a q => Algebra.TensorProduct.lift_tmul _ _ _ a q
  have hαβ : ∀ z : J'.Quotient, α (β' z) = z := by
    intro z
    obtain ⟨y, rfl⟩ := RingCon.mk'_surjective J' z
    rw [hβ']
    have key : α.comp β = q' := by
      apply MonoidAlgebra.algHom_ext
      · intro m
        rw [AlgHom.comp_apply, hβs, one_smul, hα, map_one, one_mul, hg0, MonoidAlgebra.mapRingHom_single, map_one]
        rfl
      · exact Subsingleton.elim _ _
    exact congrArg (fun h => h y) key
  have hβα : ∀ t : T, β' (α t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a q =>
      obtain ⟨x, rfl⟩ := RingCon.mk'_surjective J q
      rw [hα, map_mul, hg0]
      change β' (RingCon.mk' J' (algebraMap κ' _ a)) * β' (RingCon.mk' J' (φ x)) = _
      rw [hβ', hβ', AlgHom.commutes, hβφ, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  exact ⟨{ toFun := α, invFun := β', left_inv := hβα, right_inv := hαβ, map_mul' := map_mul α, map_add' := map_add α }⟩
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.quot_bc :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M] (I : Ideal R) (I' : Ideal R'), I' = I.map (algebraMap R R') → Nonempty (R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[R'] (R' ⊗[R] M) ⧸ (I' • ⊤ : Submodule R' (R' ⊗[R] M))) := by
  intro R R' _ _ _ M _ _ I I' hI
  subst hI
  have hker : ∀ i ∈ I, ∀ y : R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M)), i • y = 0 := by
    intro i hi y
    induction y using TensorProduct.induction_on with
    | zero => exact smul_zero _
    | tmul a q =>
      induction q using Submodule.Quotient.induction_on with
      | H m =>
        rw [← TensorProduct.tmul_smul, ← Submodule.Quotient.mk_smul,
          (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hi Submodule.mem_top),
          TensorProduct.tmul_zero]
    | add y z hy hz => rw [smul_add, hy, hz, add_zero]
  have hann : I.map (algebraMap R R') ≤ Module.annihilator R' (R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M))) :=
    Ideal.map_le_iff_le_comap.2 fun i hi => Module.mem_annihilator.2 fun y => by
      rw [algebraMap_smul]
      exact hker i hi y
  let ψ : M ⧸ (I • ⊤ : Submodule R M) →ₗ[R]
      (R' ⊗[R] M) ⧸ (I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)) :=
    (I • ⊤ : Submodule R M).liftQ
      (((I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)).mkQ.restrictScalars R) ∘ₗ
        TensorProduct.mk R R' M 1) (by
      rw [Submodule.smul_le]
      intro i hi m _
      rw [LinearMap.mem_ker, LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, TensorProduct.tmul_smul,
        ← algebraMap_smul R' i ((1 : R') ⊗ₜ[R] m)]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hi) Submodule.mem_top)
  let φ := ψ.liftBaseChange R'
  let χ := (I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)).liftQ
    (LinearMap.baseChange R' (I • ⊤ : Submodule R M).mkQ) (by
      rw [Submodule.smul_le]
      intro r hr x _
      rw [LinearMap.mem_ker, map_smul]
      exact Module.mem_annihilator.1 (hann hr) _)
  refine ⟨LinearEquiv.ofLinear φ χ ?_ ?_⟩
  · apply Submodule.linearMap_qext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    simp [φ, χ, ψ]
    rw [← Submodule.Quotient.mk_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · apply TensorProduct.AlgebraTensorModule.ext
    intro a q
    induction q using Submodule.Quotient.induction_on with
    | H m => simp [φ, χ, ψ, TensorProduct.smul_tmul']
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem UpperTheory.V.Pa.BC.chain_lift_down (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B']
    [Module.Flat B B'] (P : Ideal B') (q : Ideal B) (hP : P.IsPrime) (hq : q.IsPrime)
    (hle : q ≤ P.comap (algebraMap B B')) :
    ∃ Q : Ideal B', Q.IsPrime ∧ Q.comap (algebraMap B B') = q ∧ Q ≤ P := by
  haveI : (P.comap (algebraMap B B')).IsPrime := Ideal.comap_isPrime _ _
  haveI : P.LiesOver (P.comap (algebraMap B B')) := ⟨rfl⟩
  obtain ⟨Q, h1, h2, h3⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := q)
    (q := P.comap (algebraMap B B')) P hle
  exact ⟨Q, h2, h3.over.symm, h1⟩

private theorem UpperTheory.V.Pa.BC.prime_chain_lift_extension (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B']
    [Algebra.IsIntegral B B'] [Module.Flat B B'] (h : ℕ) :
    ∀ (p : Fin (h + 1) → Ideal B) (e : Fin h → Ideal B), (∀ i, (p i).IsPrime) →
      (∀ i, (e i).IsPrime ∧ e i ≤ p i.castSucc ∧ e i ≤ p i.succ) →
      ∀ P0 : Ideal B', P0.IsPrime → P0.comap (algebraMap B B') = p 0 →
      ∃ (P : Fin (h + 1) → Ideal B') (E : Fin h → Ideal B'), P 0 = P0 ∧
        (∀ i, (P i).IsPrime ∧ (P i).comap (algebraMap B B') = p i) ∧
        ∀ i, (E i).IsPrime ∧ (E i).comap (algebraMap B B') = e i ∧ E i ≤ P i.castSucc ∧
          E i ≤ P i.succ := by
  induction h with
  | zero =>
    intro p e _ _ P0 hP0 hP0c
    refine ⟨fun _ => P0, Fin.elim0, rfl, ?_, fun i => i.elim0⟩
    intro i
    rw [Fin.fin_one_eq_zero i]
    exact ⟨hP0, hP0c⟩
  | succ h ih =>
    intro p e hp he P0 hP0 hP0c
    obtain ⟨he0, he0l, he0r⟩ := he 0
    obtain ⟨E0, hE0, hE0c, hE0le⟩ :=
      UpperTheory.V.Pa.BC.chain_lift_down B B' P0 (e 0) hP0 he0 (by rw [hP0c]; exact he0l)
    haveI := hp (Fin.succ 0)
    haveI := hE0
    obtain ⟨P1, hP1ge, hP1, hP1c⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
      (p (Fin.succ 0)) E0 (by
        change E0.comap (algebraMap B B') ≤ p (Fin.succ 0)
        rw [hE0c]
        exact he0r)
    obtain ⟨P', E', hP'0, hP', hE'⟩ := ih (fun i => p i.succ) (fun i => e i.succ)
      (fun i => hp i.succ)
      (fun i => by
        obtain ⟨a, b, c⟩ := he i.succ
        refine ⟨a, ?_, c⟩
        rw [← Fin.succ_castSucc] at b
        exact b)
      P1 hP1 hP1c
    refine ⟨(Fin.cons P0 P' : Fin (h + 1 + 1) → Ideal B'),
      (Fin.cons E0 E' : Fin (h + 1) → Ideal B'), Fin.cons_zero _ _, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => rw [Fin.cons_zero]; exact ⟨hP0, hP0c⟩
      | succ j => rw [Fin.cons_succ]; exact hP' j
    · intro i
      cases i using Fin.cases with
      | zero =>
        rw [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hP'0]
        exact ⟨hE0, hE0c, hE0le, hP1ge⟩
      | succ j =>
        rw [Fin.cons_succ, ← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
        exact hE' j

theorem UpperTheory.V.Pa.BC.chain_lift :
    ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B'] [Algebra.IsIntegral B B'] [Module.Flat B B'] [FaithfulSMul B B'] (h : ℕ) (p : Fin (h + 1) → Ideal B) (e : Fin h → Ideal B), (∀ i, (p i).IsPrime) → (∀ i, (e i).IsPrime ∧ e i ≤ p i.castSucc ∧ e i ≤ p i.succ) → (∃ (P : Fin (h + 1) → Ideal B') (E : Fin h → Ideal B'), (∀ i, (P i).IsPrime ∧ (P i).comap (algebraMap B B') = p i) ∧ ∀ i, (E i).IsPrime ∧ (E i).comap (algebraMap B B') = e i ∧ E i ≤ P i.castSucc ∧ E i ≤ P i.succ) ∧ ∀ (P : Ideal B') (q : Ideal B), P.IsPrime → q.IsPrime → q ≤ P.comap (algebraMap B B') → ∃ Q : Ideal B', Q.IsPrime ∧ Q.comap (algebraMap B B') = q ∧ Q ≤ P := by
  intro B B' _ _ _ _ _ _ h p e hp he
  refine ⟨?_, fun P q hP hq hle => UpperTheory.V.Pa.BC.chain_lift_down B B' P q hP hq hle⟩
  haveI := hp 0
  obtain ⟨P0, _, hP0, hP0c⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B') (p 0) ⊥ (by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    rw [(FaithfulSMul.algebraMap_injective B B') (hx.trans (map_zero _).symm)]
    exact Ideal.zero_mem _)
  obtain ⟨P, E, _, hPc, hE⟩ := UpperTheory.V.Pa.BC.prime_chain_lift_extension B B' h p e hp he P0 hP0 hP0c
  exact ⟨P, E, hPc, hE⟩
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.common_field :
    ∀ (B κ₁ κ₂ : Type) [CommRing B] [Field κ₁] [Field κ₂] (f₁ : B →+* κ₁) (f₂ : B →+* κ₂), RingHom.ker f₁ = RingHom.ker f₂ → ∃ (κ : Type) (_ : Field κ) (j₁ : κ₁ →+* κ) (j₂ : κ₂ →+* κ), j₁.comp f₁ = j₂.comp f₂ :=
  _root_.UpperTheory.Reformulated.B.Qe15.common_field
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

open scoped PowerSeries.WithPiTopology in
theorem UpperTheory.V.Pa.BC.ps_ev :
    ∀ (R K : Type) [CommRing R] [CommRing K] (x : R →+* PowerSeries K), ∃ f : PowerSeries R →+* PowerSeries K, (∀ a, f (PowerSeries.C a) = x a) ∧ f PowerSeries.X = PowerSeries.X := by
  intro R K _ _ x
  letI : UniformSpace R := ⊥
  letI : UniformSpace K := ⊥
  haveI : DiscreteUniformity R := ⟨rfl⟩
  haveI : DiscreteUniformity K := ⟨rfl⟩
  refine ⟨PowerSeries.eval₂Hom (φ := x) (a := PowerSeries.X) continuous_of_discreteTopology
    PowerSeries.HasEval.X, ?_, ?_⟩
  · intro a
    rw [PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]
  · rw [PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]
end
