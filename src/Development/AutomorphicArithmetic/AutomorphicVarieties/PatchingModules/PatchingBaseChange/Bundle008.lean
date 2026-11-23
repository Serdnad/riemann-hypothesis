module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle006
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.til_mod :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (S R : Type) [CommRing S] [Algebra O S] [IsNoetherianRing S] [CommRing R] [Algebra O R] [IsNoetherianRing R] (f : S →ₐ[O] R) (M : Type) [AddCommGroup M] [Module R M] [Module S M] [Module.Finite S M], (∀ (a : S) (m : M), a • m = f a • m) → ∃ e : Til O O' S ⊗[S] M ≃+ Til O O' R ⊗[R] M, (∀ a m, e (a ⊗ₜ m) = Til.map O' f a ⊗ₜ m) ∧ ∀ a z, e (a • z) = Til.map O' f a • e z := by
  intro O O' _ _ _ _ S R _ _ _ _ _ _ f M _ _ _ _ h
  letI : Module O M := Module.compHom M (algebraMap O R)
  haveI : IsScalarTower O R M := ⟨fun o r m => by
    show (o • r) • m = (algebraMap O R o) • (r • m)
    rw [Algebra.smul_def, mul_smul]⟩
  haveI : IsScalarTower O S M := ⟨fun o s m => by
    show (o • s) • m = (algebraMap O R o) • (s • m)
    rw [h (o • s) m, h s m, Algebra.smul_def o s, map_mul, f.commutes, mul_smul]⟩
  have hfin : Module.Finite R M := by
    letI : Algebra S R := f.toRingHom.toAlgebra
    haveI : IsScalarTower S R M := ⟨fun s r m => by
      show (f s * r) • m = s • (r • m)
      rw [mul_smul, h]⟩
    exact Module.Finite.of_restrictScalars_finite S R M
  haveI := hfin
  obtain ⟨e1, he1⟩ := BC.til_ev O O' S M
  obtain ⟨e2, he2⟩ := BC.til_ev O O' R M
  have hact : ∀ (m : M) (x : O' ⊗[O] S), Til.act O' m (Algebra.TensorProduct.map (AlgHom.id O' O') f x) = Til.act O' m x := by
    intro m x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o s => simp [Til.act, h]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hcoeff : ∀ k a, Til.coeff O O' R k (Til.map O' f a) = Algebra.TensorProduct.map (AlgHom.id O' O') f (Til.coeff O O' S k a) := by
    intro k a
    rfl
  have key : ∀ a m, e1 (a ⊗ₜ m) = e2 (Til.map O' f a ⊗ₜ m) := by
    intro a m
    funext k
    rw [he1, he2, hcoeff, hact]
  have hform : ∀ a m, (e1.trans e2.symm) (a ⊗ₜ m) = Til.map O' f a ⊗ₜ m := by
    intro a m
    rw [AddEquiv.trans_apply, key, AddEquiv.symm_apply_apply]
  refine ⟨e1.trans e2.symm, hform, ?_⟩
  intro a z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => rw [TensorProduct.smul_tmul', hform, hform, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem UpperTheory.V.Pa.BC.equiv_of_ker {K A B C : Type} [CommRing K] [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C] (f : A →ₐ[K] B) (g : A →ₐ[K] C) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (h : RingHom.ker f = RingHom.ker g) : ∃ τ : B ≃ₐ[K] C, ∀ a, τ (f a) = g a := by
  refine ⟨((Ideal.quotientKerAlgEquivOfSurjective hf).symm.trans (Ideal.quotientEquivAlgOfEq K h)).trans
    (Ideal.quotientKerAlgEquivOfSurjective hg), fun a => ?_⟩
  have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f a) = Ideal.Quotient.mk _ a := by
    rw [AlgEquiv.symm_apply_eq]; rfl
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, this]
  rfl

private theorem UpperTheory.V.Pa.BC.spIdeal_fg {R : Type} [CommRing R] {q n : ℕ} (P : Fin q → Polynomial R)
    (ut : Fin q → Fin n → R) : (spIdeal P ut).FG := by
  refine Submodule.fg_span ?_
  have key : ∀ (S : Type) [CommRing S] (Q : Fin q → Polynomial S), {z | ∃ j k, z = (Q j).coeff k}.Finite := by
    intro S _ Q
    refine ((Set.finite_iUnion fun j => (Q j).coeffs.finite_toSet).insert 0).subset ?_
    rintro z ⟨j, k, rfl⟩
    by_cases h : (Q j).coeff k = 0
    · exact Or.inl h
    · exact Or.inr (Set.mem_iUnion.2 ⟨j, Polynomial.coeff_mem_coeffs h⟩)
  exact key _ _

private theorem UpperTheory.V.Pa.BC.spIdeal_map {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {q n : ℕ}
    (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) :
    (spIdeal P ut).map (MvPowerSeries.map φ) = spIdeal (fun j => (P j).map φ) (fun j i => φ (ut j i)) := by
  have key : ∀ j k, MvPowerSeries.map φ (((∏ i, (Polynomial.X -
      Polynomial.C (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i)))) -
      (P j).map (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R)).coeff k) =
      ((∏ i, (Polynomial.X - Polynomial.C (MvPowerSeries.C (φ (ut j i)) + MvPowerSeries.X (j, i)))) -
      ((P j).map φ).map (MvPowerSeries.C : R' →+* MvPowerSeries (Fin q × Fin n) R')).coeff k := by
    intro j k
    rw [← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, Polynomial.map_map]
    have : (MvPowerSeries.map φ).comp (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) =
        (MvPowerSeries.C : R' →+* MvPowerSeries (Fin q × Fin n) R').comp φ := by
      ext1 a
      simp
    rw [this]
    simp
  unfold spIdeal
  rw [Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨j, k, rfl⟩, rfl⟩
    exact ⟨j, k, key j k⟩
  · rintro ⟨j, k, rfl⟩
    exact ⟨_, ⟨j, k, rfl⟩, key j k⟩

theorem UpperTheory.V.Pa.BC.til_sp :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] (B : Type) [CommRing B] [Algebra O B] (q n : ℕ) (P : Fin q → Polynomial B) (ut : Fin q → Fin n → B), ∃ τ : Til O O' (Sp P ut) ≃ₐ[O'] Sp (fun j => (P j).map (Til.ι O O' B)) (fun j i => Til.ι O O' B (ut j i)), (∀ a, τ (Til.map O' (IsScalarTower.toAlgHom O B (Sp P ut)) a) = algebraMap (Til O O' B) _ a) ∧ ∀ j i, τ (Til.ι O O' _ (Sp.u P ut j i)) = Sp.u _ _ j i := by
  intro O O' _ _ _ _ _ B _ _ q n P ut
  obtain ⟨τ0, h1, -, h3, -⟩ := UpperTheory.V.Pa.BC.til_mvps O O' B (Fin q × Fin n)
  obtain ⟨hs, hk⟩ := UpperTheory.V.Pa.BC.til_quot O O' _ (spIdeal P ut) (UpperTheory.V.Pa.BC.spIdeal_fg P ut)
  let f : Til O O' (MvPowerSeries (Fin q × Fin n) B) →ₐ[O'] Til O O' (Sp P ut) :=
    Til.map O' ((Sp.mk P ut).restrictScalars O)
  let g : Til O O' (MvPowerSeries (Fin q × Fin n) B) →ₐ[O']
      Sp (fun j => (P j).map (Til.ι O O' B)) (fun j i => Til.ι O O' B (ut j i)) :=
    ((Sp.mk _ _).restrictScalars O').comp τ0.toAlgHom
  have hf : Function.Surjective f := hs
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp τ0.surjective
  have hfk : RingHom.ker f = (spIdeal P ut).map (Til.ι O O' _) := hk
  have hI : ((spIdeal P ut).map (Til.ι O O' _)).map τ0.toRingEquiv.toRingHom =
      spIdeal (fun j => (P j).map (Til.ι O O' B)) (fun j i => Til.ι O O' B (ut j i)) := by
    rw [Ideal.map_map, ← UpperTheory.V.Pa.BC.spIdeal_map]
    congr 1
    exact RingHom.ext h1
  have hfg : RingHom.ker f = RingHom.ker g := by
    rw [hfk]
    ext a
    have e1 : a ∈ RingHom.ker g ↔
        τ0 a ∈ spIdeal (fun j => (P j).map (Til.ι O O' B)) (fun j i => Til.ι O O' B (ut j i)) :=
      Ideal.Quotient.eq_zero_iff_mem
    rw [e1, ← hI]
    exact (Ideal.apply_mem_of_equiv_iff (f := τ0.toRingEquiv)).symm
  obtain ⟨τ, hτ⟩ := UpperTheory.V.Pa.BC.equiv_of_ker f g hf hg hfg
  refine ⟨τ, fun a => ?_, fun j i => ?_⟩
  · have e : Til.map O' (IsScalarTower.toAlgHom O B (Sp P ut)) a =
        f (Til.map O' (IsScalarTower.toAlgHom O B (MvPowerSeries (Fin q × Fin n) B)) a) := by
      have hc : IsScalarTower.toAlgHom O B (Sp P ut) = ((Sp.mk P ut).restrictScalars O).comp
          (IsScalarTower.toAlgHom O B (MvPowerSeries (Fin q × Fin n) B)) :=
        AlgHom.ext fun b => ((Sp.mk P ut).commutes b).symm
      rw [hc]
      refine PowerSeries.ext fun k => ?_
      show Algebra.TensorProduct.map _ _ (Til.coeff O O' B k a) =
        Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ (Til.coeff O O' B k a))
      induction Til.coeff O O' B k a using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [e, hτ]
    show Sp.mk _ _ (τ0 _) = _
    rw [h3]
    exact (Sp.mk _ _).commutes a
  · have e : Til.ι O O' _ (Sp.u P ut j i) =
        f (Til.ι O O' _ (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i))) :=
      (Til.map_ι O' ((Sp.mk P ut).restrictScalars O) (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i))).symm
    rw [e, hτ]
    show Sp.mk _ _ (τ0 _) = Sp.mk _ _ _
    rw [h1, map_add (f := _), MvPowerSeries.map_C, MvPowerSeries.map_X]
end
