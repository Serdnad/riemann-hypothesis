module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle008
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle066
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
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem free_fin_transfer {S T N N' : Type} [CommRing S] [CommRing T] [AddCommGroup N] [AddCommGroup N']
    [Module S N] [Module T N'] [Module.Free S N] [Module.Finite S N] (τ : S ≃+* T) (e : N ≃+ N')
    (he : ∀ a z, e (a • z) = τ a • e z) : Module.Free T N' ∧ Module.Finite T N' := by
  letI : Module S N' := Module.compHom N' (τ : S →+* T)
  let e' : N ≃ₗ[S] N' := { e with map_smul' := he }
  haveI : Module.Free S N' := Module.Free.of_equiv e'
  haveI : Module.Finite S N' := Module.Finite.equiv e'
  refine ⟨Module.Free.of_basis ((Module.Free.chooseBasis S N').mapCoeffs τ (fun _ _ => rfl)), ?_⟩
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := S) (M := N')
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span S (s : Set N') := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ (hy trivial) (hz trivial)
  | smul a y _ hy => exact Submodule.smul_mem _ (τ a) (hy trivial)

private theorem fin_of_hom {S R M : Type} [CommRing S] [CommRing R] [AddCommGroup M] [Module S M] [Module R M]
    [Module.Finite S M] (f : S → R) (h : ∀ (a : S) (m : M), a • m = f a • m) : Module.Finite R M :=
  _root_.UpperTheory.Reformulated.B.Qh10.fin_of_hom f h

private theorem lamEmb_X (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (D : ℕ) (k : Fin D) :
    lamEmb O O' D (MvPowerSeries.X (.inr k)) = MvPowerSeries.X (.inr k) := by
  simp [lamEmb]

theorem UpperTheory.V.Pa.BC.base_bc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O O' : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] [Module.Free O O'] (r : Resid G0.frame O n) (r' : Resid G0.frame O' n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (u : Pair r B) (u' : Pair r' (Til O O' B)) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D), RBC r r' → u.Maps (Til.ι O O' B) u'.D u'.ψ → (∀ a, τ (Til.ι O O' _ a) = lamEmb O O' D a) → ∃ b' : TWBase u' (J.map (Til.ι O O' B)) Unit D, Nonempty (BaseRel b b' τ) := by
  intro l _ L G0 n O O' _ _ _ _ _ _ _ _ _ _ _ _ _ r r' B _ _ _ _ u u' J D b τ hr hu hτ
  haveI := b.free
  haveI := b.fin
  haveI : IsNoetherianRing (abelian₂ O Empty D) := inferInstance
  haveI : Module.Finite B b.M := fin_of_hom b.lam b.smul_lam
  obtain ⟨e, -, he⟩ := UpperTheory.V.Pa.BC.til_mod O O' (abelian₂ O Empty D) B b.lam b.M b.smul_lam
  let lam' : abelian₂ O' Unit D →ₐ[O'] Til O O' B := (Til.map O' b.lam).comp (τ.symm : abelian₂ O' Unit D →ₐ[O'] _)
  have hlam : ∀ a, lam' (τ a) = Til.map O' b.lam a := fun a => by simp [lam']
  letI mL : Module (abelian₂ O' Unit D) (Til O O' B ⊗[B] b.M) := Module.compHom _ (lam' : abelian₂ O' Unit D →+* Til O O' B)
  have hff := free_fin_transfer (T := abelian₂ O' Unit D) (N' := Til O O' B ⊗[B] b.M) τ.toRingEquiv e (fun a z => by
    rw [he, ← hlam]; rfl)
  refine ⟨{ wt := ⟨b.wt.v, b.wt.i, b.wt.γ, fun k => algebraMap O O' (b.wt.c k)⟩
            wt_res := ?_
            lam := lam'
            segmentWeightExponent := ?_
            M := Til O O' B ⊗[B] b.M
            smul_lam := fun _ _ => rfl
            free := hff.1
            fin := hff.2
            supp := ?_ }, ⟨⟨rfl, hlam, LinearEquiv.refl _ _⟩⟩⟩
  · intro k
    have h := congrArg (ResidueField.map (algebraMap O O')) (b.wt_res k)
    rw [map_mul, map_one, ResidueField.map_residue] at h
    dsimp only
    rw [hr.2.1]
    exact h
  · intro k
    dsimp only
    rw [← lamEmb_X O O' D k, ← hτ, hlam, Til.map_ι, b.segmentWeightExponent, map_sub, map_mul, map_one, Til.ι_algebraMap, ← hu.2]
    rfl
  · intro p hp
    have h1 := UpperTheory.V.AlgebraTools.mem_support_baseChange B (Til O O' B) b.M ⟨p, hp⟩
    rw [Module.mem_support_iff_of_finite, Module.mem_support_iff_of_finite] at h1
    rw [Ideal.map_le_iff_le_comap, ← b.supp _ (Ideal.comap_isPrime _ _)]
    exact h1
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem free_quotient_base_change (S T S' : Type) [CommRing S] [CommRing T] [Algebra S T] [CommRing S']
    (τ : T ≃+* S') (I : Ideal S) (rk : ℕ) (M : Type) [AddCommGroup M] [Module S M]
    (e : M ≃ₗ[S] (Fin rk → S ⧸ I)) (I' : Ideal S')
    (hI : I' = I.map ((τ : T →+* S').comp (algebraMap S T))) :
    ∃ e' : T ⊗[S] M ≃+ (Fin rk → S' ⧸ I'), ∀ z m, e' (z • m) = τ z • e' m := by
  let J : Ideal T := I.map (algebraMap S T)
  have hJ : I' = J.map (τ : T →+* S') := by
    rw [hI, Ideal.map_map]
  let q : T ⧸ J ≃+* S' ⧸ I' := Ideal.quotientEquiv J I' τ hJ
  let A1 : T ⊗[S] M ≃ₗ[T] T ⊗[S] (Fin rk → S ⧸ I) := LinearEquiv.baseChange S T M _ e
  let A2 : T ⊗[S] (Fin rk → S ⧸ I) ≃ₗ[T] (Fin rk → T ⊗[S] (S ⧸ I)) :=
    (Algebra.TensorProduct.piRight S T T (fun _ : Fin rk => S ⧸ I)).toLinearEquiv
  let A3 : (Fin rk → T ⊗[S] (S ⧸ I)) ≃ₗ[T] (Fin rk → T ⧸ J) :=
    LinearEquiv.piCongrRight (fun _ => (Algebra.TensorProduct.quotIdealMapEquivTensorQuot T I).symm.toLinearEquiv)
  let A := (A1.trans A2).trans A3
  refine ⟨A.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => q.toAddEquiv), ?_⟩
  intro z m
  funext i
  change q ((A (z • m)) i) = τ z • q ((A m) i)
  rw [A.map_smul, Pi.smul_apply]
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (A m i)
  rw [← hx, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, Ideal.quotientEquiv_mk, Ideal.quotientEquiv_mk, ← map_mul, map_mul]

theorem UpperTheory.V.Pa.BC.free_bc :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (S R : Type) [CommRing S] [Algebra O S] [IsNoetherianRing S] [CommRing R] [Algebra O R] [IsNoetherianRing R] (s : S →ₐ[O] R) (M : Type) [AddCommGroup M] [Module R M] (I : Ideal S) (rk : ℕ) (e : M ≃+ (Fin rk → S ⧸ I)), (∀ z m, e (s z • m) = z • e m) → ∀ (S' : Type) [CommRing S'] (τ : Til O O' S ≃+* S') (I' : Ideal S'), I' = I.map ((τ : Til O O' S →+* S').comp (Til.ι O O' S)) → ∃ e' : Til O O' R ⊗[R] M ≃+ (Fin rk → S' ⧸ I'), ∀ z m, e' (Til.map O' s z • m) = τ z • e' m := by
  intro O O' _ _ _ _ S R _ _ _ _ _ _ s M _ _ I rk e he S' _ τ I' hI
  letI : Module S M := Module.compHom M s.toRingHom
  let eL : M ≃ₗ[S] (Fin rk → S ⧸ I) := e.toLinearEquiv (fun c x => he c x)
  haveI : Module.Finite S M := Module.Finite.equiv eL.symm
  obtain ⟨ε, -, hε⟩ := BC.til_mod O O' S R s M (fun a m => rfl)
  obtain ⟨f, hf⟩ := free_quotient_base_change S (Til O O' S) S' τ I rk M eL I' (by rw [Til.algebraMap_eq]; exact hI)
  refine ⟨ε.symm.trans f, ?_⟩
  intro z m
  have hsymm : ε.symm (Til.map O' s z • m) = z • ε.symm m := by
    apply ε.injective
    rw [hε, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rw [AddEquiv.trans_apply, hsymm, hf, AddEquiv.trans_apply]
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.xmaps_bc :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (R P : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] [CommRing P] [Algebra O P] [IsNoetherianRing P] (θ : R →ₐ[O] P) (X X0 : Type) [AddCommGroup X] [Module R X] [AddCommGroup X0] [Module P X0] (f : R) (φ : X0 →+ X) (ψ : X →+ X0), (∃ s : Finset X0, ∀ z, ∃ c : X0 → R, z = ∑ g ∈ s, θ (c g) • g) → (∀ (t : R) z, φ (θ t • z) = t • φ z) → (∀ (t : R) z, ψ (t • z) = θ t • ψ z) → (∀ z, φ (ψ z) = f • z) → (∀ z, ψ (φ z) = θ f • z) → ∃ (φ' : Til O O' P ⊗[P] X0 →+ Til O O' R ⊗[R] X) (ψ' : Til O O' R ⊗[R] X →+ Til O O' P ⊗[P] X0), (∀ t z, φ' (Til.map O' θ t • z) = t • φ' z) ∧ (∀ t z, ψ' (t • z) = Til.map O' θ t • ψ' z) ∧ (∀ z, φ' (ψ' z) = Til.ι O O' R f • z) ∧ ∀ z, ψ' (φ' z) = Til.map O' θ (Til.ι O O' R f) • z := by
  intro O O' _ _ _ _ R P _ _ _ _ _ _ θ X X0 _ _ _ _ f φ ψ hgen hφ hψ hφψ hψφ
  letI : Module R X0 := Module.compHom X0 θ.toRingHom
  haveI : Module.Finite R X0 := by
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hgen
    refine ⟨s, ?_⟩
    rw [eq_top_iff]
    intro z _
    obtain ⟨c, hc⟩ := hs z
    rw [hc]
    refine Submodule.sum_mem _ (fun g hg => ?_)
    exact Submodule.smul_mem _ (c g) (Submodule.subset_span hg)
  obtain ⟨e, he1, he2⟩ := BC.til_mod O O' R P θ X0 (fun a m => rfl)
  let φL : X0 →ₗ[R] X :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun t z => hφ t z }
  let ψL : X →ₗ[R] X0 :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := fun t z => hψ t z }
  let A := Til O O' R
  let Φ := LinearMap.baseChange A φL
  let Ψ := LinearMap.baseChange A ψL
  have hsc : ∀ (M : Type) [AddCommGroup M] [Module R M] (g : M →ₗ[R] M) (r : R), (∀ m, g m = r • m) →
      ∀ w : A ⊗[R] M, LinearMap.baseChange A g w = Til.ι O O' R r • w := by
    intro M _ _ g r hg w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, hg, ← Til.algebraMap_eq, ← TensorProduct.smul_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]
    | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  have heinv : ∀ (t : A) (z : Til O O' P ⊗[P] X0), e.symm (Til.map O' θ t • z) = t • e.symm z := by
    intro t z
    apply e.injective
    rw [he2, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  refine ⟨Φ.toAddMonoidHom.comp e.symm.toAddMonoidHom, e.toAddMonoidHom.comp Ψ.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro t z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    rw [heinv, LinearMap.map_smul]
  · intro t z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    rw [LinearMap.map_smul, he2]
  · intro z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe, AddEquiv.symm_apply_apply]
    have := hsc X (φL ∘ₗ ψL) f (fun m => hφψ m) z
    rw [LinearMap.baseChange_comp] at this
    exact this
  · intro z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    have := hsc X0 (ψL ∘ₗ φL) f (fun m => hψφ m) (e.symm z)
    rw [LinearMap.baseChange_comp] at this
    change e (Ψ (Φ (e.symm z))) = _
    rw [show Ψ (Φ (e.symm z)) = Til.ι O O' R f • e.symm z from this, he2, AddEquiv.apply_symm_apply]
end
