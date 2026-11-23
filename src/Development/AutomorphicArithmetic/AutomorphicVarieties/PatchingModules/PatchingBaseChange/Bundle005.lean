module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle004
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Pi

@[expose] public section

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

section
variable {R : Type} [CommRing R] {ι : Type} (N : Type) [AddCommGroup N] [Module R N]

private theorem UpperTheory.V.Pa.BC.ev_nat {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (x : M ⊗[R] (ι → N)) (k : ι) :
    TensorProduct.piRightHom R R M' (fun _ : ι => N) (f.rTensor _ x) k =
      f.rTensor N (TensorProduct.piRightHom R R M (fun _ : ι => N) x k) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

private theorem UpperTheory.V.Pa.BC.ev_free (n : ℕ) :
    Function.Bijective (TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N)) := by
  classical
  let e1 : (Fin n → R) ⊗[R] (ι → N) ≃ₗ[R] (Fin n → ι → N) :=
    TensorProduct.piLeft R (ι → N) (fun _ : Fin n => R) ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R (ι → N))
  let e2 : (ι → (Fin n → R) ⊗[R] N) ≃ₗ[R] (ι → Fin n → N) :=
    LinearEquiv.piCongrRight (fun _ => TensorProduct.piLeft R N (fun _ : Fin n => R) ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R N))
  have key : ∀ x, TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N) x =
      e2.symm (Equiv.piComm _ (e1 x)) := by
    intro x
    apply e2.injective
    rw [LinearEquiv.apply_symm_apply]
    induction x using TensorProduct.induction_on with
    | zero =>
      ext k i
      simp
      rfl
    | tmul v f =>
      ext k i
      simp [e1, e2, TensorProduct.piRightHom_tmul, Function.swap, LinearEquiv.piCongrRight_apply]
    | add a b ha hb =>
      ext k i
      have h1 := congrFun (congrFun ha k) i
      have h2 := congrFun (congrFun hb k) i
      simp only [map_add (f := _), Pi.add_apply, Equiv.piComm_apply] at h1 h2 ⊢
      rw [h1, h2]
      rfl
  have hfun : ⇑(TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N)) =
      e2.symm ∘ (Equiv.piComm _) ∘ e1 := funext key
  rw [hfun]
  exact e2.symm.bijective.comp ((Equiv.piComm _).bijective.comp e1.bijective)

private theorem UpperTheory.V.Pa.BC.ev_surj (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Surjective (TensorProduct.piRightHom R R M (fun _ : ι => N)) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  intro z
  choose w hw using fun k => LinearMap.rTensor_surjective N hp (z k)
  obtain ⟨y, hy⟩ := (UpperTheory.V.Pa.BC.ev_free (R := R) (ι := ι) N n).2 w
  refine ⟨p.rTensor _ y, ?_⟩
  funext k
  rw [UpperTheory.V.Pa.BC.ev_nat, hy, hw]

private theorem UpperTheory.V.Pa.BC.ev_bij [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Bijective (TensorProduct.piRightHom R R M (fun _ : ι => N)) := by
  haveI := Module.finitePresentation_of_finite R M
  refine ⟨?_, UpperTheory.V.Pa.BC.ev_surj N M⟩
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' R M
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective (ι → N) hf x
  have hex := rTensor_exact N hfg hf
  have hk : ∀ k, TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N) y k ∈
      Set.range (g.rTensor N) := by
    intro k
    have h1 := congrFun hx k
    rw [UpperTheory.V.Pa.BC.ev_nat, Pi.zero_apply] at h1
    exact (hex _).1 h1
  choose z hz using hk
  obtain ⟨w, hw⟩ := (UpperTheory.V.Pa.BC.ev_free N m).2 z
  have hy : y = g.rTensor _ w := by
    apply (UpperTheory.V.Pa.BC.ev_free N n).1
    funext k
    rw [UpperTheory.V.Pa.BC.ev_nat, hw, hz]
  rw [hy, ← LinearMap.rTensor_comp_apply, hfg.linearMap_comp_eq_zero, LinearMap.rTensor_zero,
    LinearMap.zero_apply]

end

theorem UpperTheory.V.Pa.BC.til_ev :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module O M] [IsScalarTower O R M] [Module.Finite R M], ∃ e : Til O O' R ⊗[R] M ≃+ (ℕ → O' ⊗[O] M), ∀ a m k, e (a ⊗ₜ m) k = Til.act O' m (Til.coeff O O' R k a) := by
  intro O O' _ _ _ _ R _ _ _ M _ _ _ _ _
  let N := R ⊗[O] O'
  let tc : O' ⊗[O] R ≃ₗ[O] N := TensorProduct.comm O O' R
  have hadd : ∀ (k : ℕ) (a b : Til O O' R),
      Til.coeff O O' R k (a + b) = Til.coeff O O' R k a + Til.coeff O O' R k b := by
    intro k a b
    unfold Til.coeff
    exact map_add (PowerSeries.coeff k) (show PowerSeries (O' ⊗[O] R) from a)
      (show PowerSeries (O' ⊗[O] R) from b)
  have hmulC : ∀ (k : ℕ) (r : R) (a : Til O O' R),
      Til.coeff O O' R k (algebraMap R (Til O O' R) r * a) = ((1 : O') ⊗ₜ[O] r) * Til.coeff O O' R k a := by
    intro k r a
    unfold Til.coeff
    exact PowerSeries.coeff_C_mul k (show PowerSeries (O' ⊗[O] R) from a) ((1 : O') ⊗ₜ[O] r)
  have hsm : ∀ (r : R) (c : O' ⊗[O] R), tc (((1 : O') ⊗ₜ[O] r) * c) = r • tc c := by
    intro r c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul o s =>
      simp only [tc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [TensorProduct.comm_tmul, TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => rw [mul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]
  let cf : Til O O' R →ₗ[R] (ℕ → N) :=
    { toFun := fun a k => tc (Til.coeff O O' R k a)
      map_add' := fun a b => by
        funext k
        simp only [hadd, map_add (f := _), Pi.add_apply]
      map_smul' := fun r a => by
        funext k
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [Algebra.smul_def, hmulC, hsm] }
  have hcf : Function.Bijective cf := by
    constructor
    · intro a b hab
      apply PowerSeries.ext
      intro k
      have h1 := congrFun hab k
      exact tc.injective h1
    · intro f
      refine ⟨PowerSeries.mk (fun k => tc.symm (f k)), ?_⟩
      funext k
      change tc (PowerSeries.coeff k (PowerSeries.mk (fun k => tc.symm (f k)))) = f k
      rw [PowerSeries.coeff_mk, LinearEquiv.apply_symm_apply]
  let cfe : Til O O' R ≃ₗ[R] (ℕ → N) := LinearEquiv.ofBijective cf hcf
  have hev := UpperTheory.V.Pa.BC.ev_bij (R := R) (ι := ℕ) N M
  let eve : M ⊗[R] (ℕ → N) ≃ₗ[R] (ℕ → M ⊗[R] N) :=
    LinearEquiv.ofBijective (TensorProduct.piRightHom R R M (fun _ : ℕ => N)) hev
  let cb : M ⊗[R] N ≃+ O' ⊗[O] M :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange O R R M O').toAddEquiv.trans
      (TensorProduct.comm O M O').toAddEquiv
  have hcb : ∀ (m : M) (c : O' ⊗[O] R), cb (m ⊗ₜ[R] tc c) = Til.act O' m c := by
    intro m c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul o s =>
      simp [cb, tc, Til.act, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      rw [TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.comm_tmul]
    | add x y hx hy => rw [map_add (f := _), TensorProduct.tmul_add, map_add (f := _), hx, hy, map_add (f := _)]
  refine ⟨(TensorProduct.comm R (Til O O' R) M).toAddEquiv.trans
    ((cfe.lTensor M).toAddEquiv.trans (eve.toAddEquiv.trans (AddEquiv.piCongrRight (fun _ => cb)))), ?_⟩
  intro a m k
  simp only [AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv, TensorProduct.comm_tmul,
    LinearEquiv.lTensor_tmul, AddEquiv.piCongrRight_apply]
  rw [← hcb]
  rfl
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

noncomputable section

namespace UpperTheory.V.Pa.BC

section swap
variable (K A σ : Type) [CommRing K] [CommRing A] [Algebra K A]

private def swF (f : PowerSeries (MvPowerSeries σ A)) : MvPowerSeries σ (PowerSeries A) :=
  fun n => PowerSeries.mk fun k => MvPowerSeries.coeff n (PowerSeries.coeff k f)

private theorem coeff_swF (f : PowerSeries (MvPowerSeries σ A)) (n : σ →₀ ℕ) (k : ℕ) :
    PowerSeries.coeff k (MvPowerSeries.coeff n (swF A σ f)) = MvPowerSeries.coeff n (PowerSeries.coeff k f) :=
  PowerSeries.coeff_mk k (fun k => MvPowerSeries.coeff n (PowerSeries.coeff k f))

private def sw : PowerSeries (MvPowerSeries σ A) →ₐ[K] MvPowerSeries σ (PowerSeries A) where
  toFun := swF A σ
  map_one' := by
    classical
    ext n k
    rw [coeff_swF]
    by_cases hn : n = 0 <;> by_cases hk : k = 0 <;>
      simp [PowerSeries.coeff_one, MvPowerSeries.coeff_one, hn, hk]
  map_mul' f g := by
    classical
    ext n k

    simp only [coeff_swF, PowerSeries.coeff_mul, MvPowerSeries.coeff_mul, map_sum]
    exact Finset.sum_comm
  map_zero' := by
    ext n k
    simp [coeff_swF]
  map_add' f g := by
    ext n k
    simp [coeff_swF]
  commutes' r := by
    classical
    ext n k
    rw [coeff_swF, PowerSeries.algebraMap_apply, PowerSeries.coeff_C, MvPowerSeries.algebraMap_apply,
      MvPowerSeries.algebraMap_apply (A := PowerSeries A), PowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
    by_cases hn : n = 0 <;> by_cases hk : k = 0 <;>
      simp [PowerSeries.coeff_C, MvPowerSeries.coeff_C, hn, hk]

private theorem sw_bij : Function.Bijective (sw K A σ) := by
  constructor
  · intro f g h
    ext k n
    have := congrArg (fun x => PowerSeries.coeff k (MvPowerSeries.coeff n x)) h
    simpa only [sw, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, coeff_swF] using this
  · intro g
    refine ⟨PowerSeries.mk fun k => (fun n => PowerSeries.coeff k (MvPowerSeries.coeff n g) : MvPowerSeries σ A), ?_⟩
    ext n k
    refine (coeff_swF A σ (PowerSeries.mk fun k =>
      (fun n => PowerSeries.coeff k (MvPowerSeries.coeff n g) : MvPowerSeries σ A)) n k).trans ?_
    exact congrArg (MvPowerSeries.coeff n) (PowerSeries.coeff_mk (R := MvPowerSeries σ A) k
      (fun k => (fun n => PowerSeries.coeff k (MvPowerSeries.coeff n g) : MvPowerSeries σ A)))

end swap

section tens
variable (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (R : Type) [CommRing R] [Algebra O R] (σ : Type)

private def ph : O' ⊗[O] MvPowerSeries σ R →ₐ[O'] MvPowerSeries σ (O' ⊗[O] R) :=
  Algebra.TensorProduct.lift (Algebra.ofId O' _)
    (MvPowerSeries.mapAlgHom (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R)) (fun _ _ => Commute.all _ _)

private def cf (n : σ →₀ ℕ) : O' ⊗[O] MvPowerSeries σ R →ₗ[O] O' ⊗[O] R :=
  LinearMap.lTensor O' ((MvPowerSeries.coeff n : MvPowerSeries σ R →ₗ[R] R).restrictScalars O)

private theorem cf_tmul (n : σ →₀ ℕ) (o : O') (f : MvPowerSeries σ R) :
    cf O O' R σ n (o ⊗ₜ f) = o ⊗ₜ MvPowerSeries.coeff n f := rfl

private theorem coeff_ph (n : σ →₀ ℕ) (x : O' ⊗[O] MvPowerSeries σ R) :
    MvPowerSeries.coeff n (ph O O' R σ x) = cf O O' R σ n x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul o f =>
    rw [cf_tmul]
    simp [ph, Algebra.ofId_apply, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C_mul, MvPowerSeries.mapAlgHom]

private theorem ph_bij [Module.Finite O O'] [Module.Free O O'] : Function.Bijective (ph O O' R σ) := by
  classical
  let b := Module.Free.chooseBasis O O'
  have key : ∀ (n : σ →₀ ℕ) (x : O' ⊗[O] MvPowerSeries σ R) i,
      TensorProduct.equivFinsuppOfBasisLeft b (cf O O' R σ n x) i =
        MvPowerSeries.coeff n (TensorProduct.equivFinsuppOfBasisLeft b x i) := by
    intro n x i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul o f =>
      rw [cf_tmul]
      simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      rfl
  constructor
  · intro x y h
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext i n
    rw [← key, ← key, ← coeff_ph, ← coeff_ph, h]
  · intro g
    refine ⟨(TensorProduct.equivFinsuppOfBasisLeft b).symm (Finsupp.equivFunOnFinite.symm fun i =>
      (fun n => TensorProduct.equivFinsuppOfBasisLeft b (MvPowerSeries.coeff n g) i : MvPowerSeries σ R)), ?_⟩
    ext n
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext i
    rw [coeff_ph, key, LinearEquiv.apply_symm_apply]
    rfl

private def tau0 : Til O O' (MvPowerSeries σ R) →ₐ[O'] MvPowerSeries σ (Til O O' R) :=
  (sw O' (O' ⊗[O] R) σ).comp (PowerSeries.mapAlgHom (ph O O' R σ))

private theorem coeff_power_series_restriction (a : Til O O' (MvPowerSeries σ R)) (n : σ →₀ ℕ) (k : ℕ) :
    Til.coeff O O' R k (MvPowerSeries.coeff n (tau0 O O' R σ a)) = cf O O' R σ n (Til.coeff O O' _ k a) := by
  rw [← coeff_ph]
  exact coeff_swF (O' ⊗[O] R) σ (PowerSeries.mapAlgHom (ph O O' R σ) a) n k

private theorem til_ext {a b : Til O O' R} (h : ∀ k, Til.coeff O O' R k a = Til.coeff O O' R k b) : a = b :=
  PowerSeries.ext h

private theorem power_series_restriction_bijective [Module.Finite O O'] [Module.Free O O'] : Function.Bijective (tau0 O O' R σ) := by
  refine (sw_bij O' (O' ⊗[O] R) σ).comp (f := PowerSeries.map (ph O O' R σ).toRingHom) ⟨?_, ?_⟩
  · exact PowerSeries.map_injective _ (ph_bij O O' R σ).1
  · exact PowerSeries.map_surjective _ (ph_bij O O' R σ).2

private theorem coeff_ι (a : R) (k : ℕ) :
    Til.coeff O O' R k (Til.ι O O' R a) = if k = 0 then (1 : O') ⊗ₜ[O] a else 0 :=
  PowerSeries.coeff_C _ _

private theorem coeff_alt (k : ℕ) :
    Til.coeff O O' R k (Til.s O O' R) = if k = 1 then 1 else 0 :=
  PowerSeries.coeff_X _

private theorem coeff_zero' (k : ℕ) : Til.coeff O O' R k 0 = 0 :=
  map_zero (PowerSeries.coeff k : PowerSeries (O' ⊗[O] R) →ₗ[O' ⊗[O] R] _)

private theorem coeff_map' {R' : Type} [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') (a : Til O O' R) (k : ℕ) :
    Til.coeff O O' R' k (Til.map O' f a) = Algebra.TensorProduct.map (AlgHom.id O' O') f (Til.coeff O O' R k a) := rfl

end tens

end UpperTheory.V.Pa.BC

open UpperTheory.V.Pa.BC in
theorem UpperTheory.V.Pa.BC.til_mvps :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] (R : Type) [CommRing R] [Algebra O R] (σ : Type) [Finite σ], ∃ τ : Til O O' (MvPowerSeries σ R) ≃ₐ[O'] MvPowerSeries σ (Til O O' R), (∀ a, τ (Til.ι O O' _ a) = MvPowerSeries.map (Til.ι O O' R) a) ∧ τ (Til.s O O' _) = MvPowerSeries.C (Til.s O O' R) ∧ (∀ a, τ (Til.map O' (IsScalarTower.toAlgHom O R (MvPowerSeries σ R)) a) = MvPowerSeries.C a) ∧ ∀ (c : MvPowerSeries σ R →ₐ[O] R), (∀ z, c z = MvPowerSeries.constantCoeff z) → ∀ a, MvPowerSeries.constantCoeff (τ a) = Til.map O' c a := by
  intro O O' _ _ _ _ _ R _ _ σ _
  classical
  refine ⟨AlgEquiv.ofBijective (tau0 O O' R σ) (power_series_restriction_bijective O O' R σ), ?_, ?_, ?_, ?_⟩
  · intro a
    refine MvPowerSeries.ext fun n => til_ext O O' R fun k => ?_
    rw [AlgEquiv.ofBijective_apply, coeff_power_series_restriction, MvPowerSeries.coeff_map, coeff_ι, coeff_ι]
    split_ifs
    · rfl
    · exact map_zero _
  · refine MvPowerSeries.ext fun n => til_ext O O' R fun k => ?_
    rw [AlgEquiv.ofBijective_apply, coeff_power_series_restriction, MvPowerSeries.coeff_C, coeff_alt]
    by_cases hn : n = 0
    · rw [if_pos hn, coeff_alt]
      split_ifs
      · rw [Algebra.TensorProduct.one_def, cf_tmul, hn, MvPowerSeries.coeff_zero_one]; rfl
      · exact map_zero _
    · rw [if_neg hn, coeff_zero']
      split_ifs
      · rw [Algebra.TensorProduct.one_def, cf_tmul, MvPowerSeries.coeff_one, if_neg hn, TensorProduct.tmul_zero]
      · exact map_zero _
  · intro a
    refine MvPowerSeries.ext fun n => til_ext O O' R fun k => ?_
    rw [AlgEquiv.ofBijective_apply, coeff_power_series_restriction, MvPowerSeries.coeff_C, coeff_map']
    have h : ∀ x : O' ⊗[O] R, cf O O' R σ n (Algebra.TensorProduct.map (AlgHom.id O' O')
        (IsScalarTower.toAlgHom O R (MvPowerSeries σ R)) x) = if n = 0 then x else 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]; split_ifs <;> simp
      | tmul o r =>
        rw [Algebra.TensorProduct.map_tmul, cf_tmul]
        split_ifs with hn <;> simp [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, hn]
    rw [h]
    split_ifs
    · rfl
    · exact (coeff_zero' O O' R k).symm
  · intro c hc a
    refine til_ext O O' R fun k => ?_
    rw [AlgEquiv.ofBijective_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_power_series_restriction, coeff_map']
    generalize Til.coeff O O' _ k a = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | tmul o r =>
      rw [Algebra.TensorProduct.map_tmul, cf_tmul, hc]
      rfl
end
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.gen_bc :
    ∀ (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (S : Set B) (S' : Set (Til O O' B)), IsLocalHom (Til.ι O O' B) → Til.s O O' B ∈ maximalIdeal (Til O O' B) → (∀ a ∈ S, Til.ι O O' B a ∈ S') → Til.s O O' B ∈ S' → GenBy O S → GenBy O' S' := by
  intro O O' _ _ _ _ _ _ _ B _ _ _ _ S S' hloc hs hS hsS hgen N
  let P : Til O O' B → Prop := fun x => ∃ a ∈ Algebra.adjoin O' S', x - a ∈ maximalIdeal (Til O O' B) ^ N
  have Pmem : ∀ x ∈ Algebra.adjoin O' S', P x := fun x hx => ⟨x, hx, by simp⟩
  have Padd : ∀ x y, P x → P y → P (x + y) := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a + b, add_mem ha hb, ?_⟩
    have : x + y - (a + b) = (x - a) + (y - b) := by ring
    rw [this]
    exact add_mem hx hy
  have Pmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_mem ha hb, ?_⟩
    have : x * y - a * b = x * (y - b) + (x - a) * b := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hx)
  have hadj : ∀ a ∈ Algebra.adjoin O S, Til.ι O O' B a ∈ Algebra.adjoin O' S' := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (hS x hx)
    | algebraMap r => rw [Til.ι_algebraMap]; exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hmap : Ideal.map (Til.ι O O' B) (maximalIdeal B ^ N) ≤ maximalIdeal (Til O O' B) ^ N := by
    rw [Ideal.map_pow]
    refine Ideal.pow_right_mono ?_ N
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit (Til.ι O O' B) x hx
  have Pι : ∀ b, P (Til.ι O O' B b) := by
    intro b
    obtain ⟨a, ha, hb⟩ := hgen N b
    refine ⟨_, hadj a ha, ?_⟩
    rw [← map_sub]
    exact hmap (Ideal.mem_map_of_mem _ hb)
  have PC : ∀ t, P (Til.C O O' B t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add (f := _)]; exact Padd _ _ hx hy
    | tmul o b =>
      have h : algebraMap O' (Til O O' B) o = Til.C O O' B (algebraMap O' (O' ⊗[O] B) o) :=
        PowerSeries.algebraMap_apply
      have e : Til.C O O' B (o ⊗ₜ[O] b) = algebraMap O' (Til O O' B) o * Til.ι O O' B b := by
        rw [h]
        show _ = Til.C O O' B _ * Til.C O O' B ((1 : O') ⊗ₜ[O] b)
        rw [← map_mul]
        congr 1
        simp
      rw [e]
      exact Pmul _ _ (Pmem _ (Subalgebra.algebraMap_mem _ _)) (Pι b)
  have hsA : Til.s O O' B ∈ Algebra.adjoin O' S' := Algebra.subset_adjoin hsS
  have hdec : ∀ f : Til O O' B, ∃ (g : Til O O' B) (c : O' ⊗[O] B), f = Til.s O O' B * g + Til.C O O' B c :=
    fun f => ⟨_, _, PowerSeries.eq_X_mul_shift_add_const (R := O' ⊗[O] B) f⟩
  have key : ∀ (k : ℕ) (f : Til O O' B), ∃ g h, P g ∧ f = g + Til.s O O' B ^ k * h := by
    intro k f
    induction k with
    | zero => exact ⟨0, f, Pmem _ (zero_mem _), by simp⟩
    | succ k ih =>
      obtain ⟨g, h, hg, e⟩ := ih
      obtain ⟨h', c, e'⟩ := hdec h
      refine ⟨g + Til.s O O' B ^ k * Til.C O O' B c, h',
        Padd _ _ hg (Pmul _ _ (Pmem _ (pow_mem hsA k)) (PC c)), ?_⟩
      rw [e, e']
      ring
  intro f
  obtain ⟨g, h, hg, e⟩ := key N f
  rw [e]
  refine Padd _ _ hg ⟨0, zero_mem _, ?_⟩
  rw [sub_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hs N)
end
