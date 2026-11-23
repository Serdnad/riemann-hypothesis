module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle002
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
public import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W
open scoped TensorProduct

namespace UpperTheory.V.Pa

variable {l : ℕ} [Fact l.Prime]

structure SinfRel (l : ℕ) {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {D q n : ℕ}
    (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D) (τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n) :
    Prop where
  X : ∀ p, τS (Til.ι O O' _ (MvPowerSeries.X p)) = MvPowerSeries.X p
  C : ∀ a : abelian₂ O Empty D, τS (Til.ι O O' _ (MvPowerSeries.C a)) = MvPowerSeries.C (lamEmb O O' D a)
  cc : ∀ c : Sinf O Empty D q n →ₐ[O] abelian₂ O Empty D, (∀ z, c z = MvPowerSeries.constantCoeff z) →
    ∀ z, MvPowerSeries.constantCoeff (τS z) = τ (Til.map O' c z)
  del : ∀ a : Fin q → ℕ, delIdeal l (abelian₂ O' Unit D) n a =
    (delIdeal l (abelian₂ O Empty D) n a).map ((τS.toRingEquiv : _ →+* Sinf O' Unit D q n).comp (Til.ι O O' _))

structure RingRel {L : Loc} {G0 G : Glob l L} {O O' : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [CommRing O']
    [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] {n : ℕ} {r : Resid G0.frame O n} {r' : Resid G0.frame O' n}
    {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {B' : Type} [CommRing B'] [Algebra O' B'] [IsCO O' B']
    {u : Pair r B} {u' : Pair r' B'} {J : Ideal B} {J' : Ideal B'} {D : ℕ} {b : TWBase u J Empty D}
    {b' : TWBase u' J' Unit D} {h : G.Hom G0} {q : ℕ} {ut : Fin q → Fin n → O} {ut' : Fin q → Fin n → O'} {N : ℕ}
    (A : TWRing b h ut N) (A' : TWRing b' h ut' N)
    (τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n) where
  ρ : Til O O' A.R ≃ₐ[O'] A'.R
  maps : A.p.Maps ((ρ.toRingEquiv : _ →+* A'.R).comp (Til.ι O O' A.R)) A'.p.D A'.p.ψ
  s : ∀ z, A'.s (τS z) = ρ (Til.map O' A.s z)
  U : ∀ j i, A'.U j i = ρ (Til.ι O O' A.R (A.U j i))
  ν : Til O O' A.R ⊗[A.R] A.M ≃+ A'.M
  ν_smul : ∀ t m, ν (t • m) = ρ t • ν m

end UpperTheory.V.Pa
end
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem mem_map_C_of_forall_coeff_mem_of_fg {A : Type} [CommRing A] (J : Ideal A) (hJ : J.FG) (f : PowerSeries A)
    (h : ∀ n, PowerSeries.coeff n f ∈ J) : f ∈ J.map PowerSeries.C := by
  obtain ⟨s, rfl⟩ := hJ
  have hc : ∀ n, ∃ c : A → A, Function.support c ⊆ ↑s ∧ ∑ a ∈ s, c a • a = PowerSeries.coeff n f :=
    fun n => Submodule.mem_span_finset.mp (h n)
  choose c _ hc using hc
  have hf : f = ∑ a ∈ s, PowerSeries.C a * PowerSeries.mk (fun n => c n a) := by
    ext n

    rw [map_sum]
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    rw [← hc n]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_eq_mul, mul_comm]
  rw [hf]
  refine Ideal.sum_mem _ fun a ha => Ideal.mul_mem_right _ _ ?_
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ha)

theorem UpperTheory.V.Pa.BC.til_quot :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (R : Type) [CommRing R] [Algebra O R] (I : Ideal R), I.FG → Function.Surjective (Til.map O' (Ideal.Quotient.mkₐ O I)) ∧ RingHom.ker (Til.map O' (Ideal.Quotient.mkₐ O I)) = I.map (Til.ι O O' R) := by
  intro O O' _ _ _ R _ _ I hI
  set φ := Algebra.TensorProduct.map (AlgHom.id O' O') (Ideal.Quotient.mkₐ O I) with hφ
  have hsurj : Function.Surjective φ :=
    Algebra.TensorProduct.map_surjective _ _ (fun x => ⟨x, rfl⟩) (Ideal.Quotient.mkₐ_surjective O I)
  have hker : RingHom.ker φ = I.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) := by
    have e := Algebra.TensorProduct.lTensor_ker (A := O') (Ideal.Quotient.mkₐ O I)
      (Ideal.Quotient.mkₐ_surjective O I)
    have hk : RingHom.ker (Ideal.Quotient.mkₐ O I) = I := by
      ext x
      simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [hk] at e
    rw [← e]
    rfl
  have hcoeff : ∀ (f : Til O O' R) (n : ℕ),
      PowerSeries.coeff n (Til.map O' (Ideal.Quotient.mkₐ O I) f : PowerSeries (O' ⊗[O] (R ⧸ I)))
        = φ (PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] R))) :=
    fun f n => PowerSeries.coeff_map _ _ _
  refine ⟨?_, ?_⟩
  · intro f
    refine ⟨(PowerSeries.mk fun n =>
      (hsurj (PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] (R ⧸ I))))).choose : PowerSeries (O' ⊗[O] R)), ?_⟩
    apply PowerSeries.ext
    intro n
    refine (hcoeff _ n).trans ?_
    erw [PowerSeries.coeff_mk]
    exact (hsurj _).choose_spec
  · have hι : I.map (Til.ι O O' R) = (RingHom.ker φ).map (Til.C O O' R) := by
      rw [hker]
      exact (Ideal.map_map _ _).symm
    rw [hι]
    ext f
    rw [RingHom.mem_ker]
    constructor
    · intro hf
      have h : ∀ n, PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] R)) ∈ RingHom.ker φ := by
        intro n
        rw [RingHom.mem_ker, ← hcoeff, hf]
        exact map_zero _
      have hJ : (RingHom.ker φ).FG := by
        rw [hker]
        exact hI.map _
      exact mem_map_C_of_forall_coeff_mem_of_fg _ hJ f h
    · intro hf
      refine (Ideal.map_le_iff_le_comap.mpr ?_ : (RingHom.ker φ).map (Til.C O O' R)
        ≤ RingHom.ker (Til.map O' (Ideal.Quotient.mkₐ O I))) hf
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker]
      apply PowerSeries.ext
      intro n
      rw [hcoeff]
      change φ (PowerSeries.coeff n (PowerSeries.C x : PowerSeries (O' ⊗[O] R)))
        = PowerSeries.coeff n (0 : PowerSeries (O' ⊗[O] (R ⧸ I)))
      rw [PowerSeries.coeff_C, map_zero]
      split_ifs
      · exact RingHom.mem_ker.mp hx
      · exact map_zero _
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private noncomputable def UpperTheory.V.Pa.BC.tlHom (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (σ : Type) :
    O' ⊗[O] MvPowerSeries σ O →ₐ[O'] MvPowerSeries σ O' :=
  Algebra.TensorProduct.lift (Algebra.ofId O' _) (MvPowerSeries.mapAlgHom (Algebra.ofId O O'))
    (fun _ _ => Commute.all _ _)

private theorem UpperTheory.V.Pa.BC.tlHom_tmul (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (σ : Type)
    (o : O') (f : MvPowerSeries σ O) :
    UpperTheory.V.Pa.BC.tlHom O O' σ (o ⊗ₜ f) = MvPowerSeries.C o * MvPowerSeries.map (algebraMap O O') f := by
  rw [UpperTheory.V.Pa.BC.tlHom, Algebra.TensorProduct.lift_tmul]
  rfl

private theorem UpperTheory.V.Pa.BC.tlHom_bij (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O']
    [Module.Finite O O'] [Module.Free O O'] (σ : Type) :
    Function.Bijective (UpperTheory.V.Pa.BC.tlHom O O' σ) := by
  classical
  let b := Module.Free.chooseBasis O O'
  have hsum : ∀ (c : Module.Free.ChooseBasisIndex O O' → MvPowerSeries σ O) (m : σ →₀ ℕ),
      MvPowerSeries.coeff m (UpperTheory.V.Pa.BC.tlHom O O' σ (∑ i, b i ⊗ₜ c i)) =
        ∑ i, MvPowerSeries.coeff m (c i) • b i := by
    intro c m

    simp only [map_sum, UpperTheory.V.Pa.BC.tlHom_tmul, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map,
    Algebra.smul_def]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b x
    rw [Finsupp.sum_fintype _ _ (by simp)] at hx ⊢
    have hc : ∀ i, c i = 0 := by
      intro i
      ext m
      have hm := congrArg (MvPowerSeries.coeff m) hx
      rw [hsum, map_zero] at hm
      rw [MvPowerSeries.coeff_zero]
      exact Fintype.linearIndependent_iff.1 b.linearIndependent (fun j => MvPowerSeries.coeff m (c j)) hm i
    simp [hc]
  · intro F
    let c : Module.Free.ChooseBasisIndex O O' → MvPowerSeries σ O :=
      fun i m => b.repr (MvPowerSeries.coeff m F) i
    refine ⟨∑ i, b i ⊗ₜ c i, ?_⟩
    ext m
    rw [hsum]
    exact b.sum_repr _

private theorem UpperTheory.V.Pa.BC.tl_option {σ R : Type} [CommRing R] (p : MvPowerSeries σ R) :
    MvPowerSeries.optionEquivLeft σ R (MvPowerSeries.rename (Function.Embedding.some : σ ↪ Option σ) p) =
      PowerSeries.C p := by
  classical
  ext k x
  rw [MvPowerSeries.coeff_coeff_optionEquivLeft, PowerSeries.coeff_C]
  split_ifs with hk
  · subst hk
    have hx : x.optionElim 0 = Finsupp.embDomain Function.Embedding.some x := by
      ext a
      cases a with
      | none =>
        rw [Finsupp.embDomain_notin_range _ _ _ (by simp)]
        simp
      | some v =>
        rw [show (some v : Option σ) = Function.Embedding.some v from rfl, Finsupp.embDomain_apply_self]
        simp
    rw [hx, MvPowerSeries.coeff_embDomain_rename]
  · rw [MvPowerSeries.coeff_zero]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    apply hk
    have hn := congrArg (fun z : Option σ →₀ ℕ => z none) hy
    simpa [Finsupp.mapDomain_notin_range] using hn.symm

private theorem UpperTheory.V.Pa.BC.tl_map_bij {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Function.Bijective (PowerSeries.map (e : A →+* B)) := by
  refine ⟨fun p q h => ?_, fun q => ⟨PowerSeries.map (e.symm : B →+* A) q, ?_⟩⟩
  · ext n
    have hn := congrArg (PowerSeries.coeff n) h
    simpa using hn
  · ext n
    simp

theorem UpperTheory.V.Pa.BC.til_lam :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] (D : ℕ), ∃ τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D, (∀ a, τ (Til.ι O O' _ a) = lamEmb O O' D a) ∧ τ (Til.s O O' _) = MvPowerSeries.X (.inl ()) := by
  intro O O' _ _ _ _ _ D
  let ε : Option (Empty ⊕ Fin D) ≃ Unit ⊕ Fin D :=
    { toFun := fun o => Option.elim o (Sum.inl ()) (Sum.map Empty.elim id)
      invFun := fun s => Sum.elim (fun _ => none) (fun i => some (Sum.inr i)) s
      left_inv := by
        rintro (_ | (e | i))
        · rfl
        · exact e.elim
        · rfl
      right_inv := by
        rintro (⟨⟩ | i) <;> rfl }
  have hb := UpperTheory.V.Pa.BC.tl_map_bij
    (RingEquiv.ofBijective (UpperTheory.V.Pa.BC.tlHom O O' (Empty ⊕ Fin D))
      (UpperTheory.V.Pa.BC.tlHom_bij O O' (Empty ⊕ Fin D)))
  let e1 : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] PowerSeries (MvPowerSeries (Empty ⊕ Fin D) O') :=
    AlgEquiv.ofBijective (PowerSeries.mapAlgHom (UpperTheory.V.Pa.BC.tlHom O O' (Empty ⊕ Fin D))) hb
  let φ : O' ⊗[O] abelian₂ O Empty D →+* MvPowerSeries (Empty ⊕ Fin D) O' :=
    (UpperTheory.V.Pa.BC.tlHom O O' (Empty ⊕ Fin D) : O' ⊗[O] abelian₂ O Empty D →+* MvPowerSeries (Empty ⊕ Fin D) O')
  refine ⟨e1.trans ((MvPowerSeries.optionEquivLeft (Empty ⊕ Fin D) O').symm.trans
    (MvPowerSeries.renameEquiv O' ε)), ?_, ?_⟩
  · intro a
    have h1 : e1 (Til.ι O O' _ a) = PowerSeries.C (MvPowerSeries.map (algebraMap O O') a) := by
      show PowerSeries.map φ (PowerSeries.C ((1 : O') ⊗ₜ[O] a)) = _
      rw [PowerSeries.map_C]
      show PowerSeries.C (UpperTheory.V.Pa.BC.tlHom O O' _ ((1 : O') ⊗ₜ[O] a)) = _
      rw [UpperTheory.V.Pa.BC.tlHom_tmul, map_one, one_mul]
    have h2 : (MvPowerSeries.optionEquivLeft (Empty ⊕ Fin D) O').symm
        (PowerSeries.C (MvPowerSeries.map (algebraMap O O') a)) =
        MvPowerSeries.rename (Function.Embedding.some : (Empty ⊕ Fin D) ↪ _)
          (MvPowerSeries.map (algebraMap O O') a) := by
      rw [AlgEquiv.symm_apply_eq, UpperTheory.V.Pa.BC.tl_option]
    rw [AlgEquiv.trans_apply, h1, AlgEquiv.trans_apply, h2]
    show MvPowerSeries.rename (⇑ε) _ = _
    rw [MvPowerSeries.rename_rename]
    rfl
  · have h1 : e1 (Til.s O O' _) = PowerSeries.X := by
      show PowerSeries.map φ PowerSeries.X = _
      exact PowerSeries.map_X _
    have h2 : (MvPowerSeries.optionEquivLeft (Empty ⊕ Fin D) O').symm PowerSeries.X =
        MvPowerSeries.X none := by
      rw [AlgEquiv.symm_apply_eq, MvPowerSeries.optionEquivLeft_X_none]
    rw [AlgEquiv.trans_apply, h1, AlgEquiv.trans_apply, h2]
    show MvPowerSeries.rename (⇑ε) _ = _
    rw [MvPowerSeries.rename_X]
    rfl
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.til_prime :
    ∀ (O O' B : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [CommRing B] [Algebra O B] [IsNoetherianRing B] (Q : Ideal (O' ⊗[O] B)), Q.IsPrime → (Q.map (Til.C O O' B)).IsPrime ∧ (Q.map (Til.C O O' B)).comap (Til.ι O O' B) = Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) := by
  intro O O' B _ _ _ _ _ _ _ Q hQ
  haveI hN : IsNoetherianRing (O' ⊗[O] B) := by
    letI : Algebra B (O' ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
    haveI : Module.Finite B (O' ⊗[O] B) :=
      Module.Finite.equiv (Algebra.TensorProduct.commRight O B O').toLinearEquiv
    exact Algebra.FiniteType.isNoetherianRing B (O' ⊗[O] B)
  obtain ⟨-, -, h3, h4⟩ := UpperTheory.V.AlgebraTools.powerSeries_ker_map (O' ⊗[O] B) Q (IsNoetherian.noetherian Q)
  refine ⟨h3 hQ, ?_⟩
  have h5 : (Q.map (Til.C O O' B)).comap (Til.C O O' B) = Q := h4
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap]
  conv_rhs => rw [← h5]
  exact Iff.rfl
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem root_const {O K : Type} [CommRing O] [Field K] [Algebra O K] (P : Polynomial O) (hm : P.Monic)
    (hs : (P.map (algebraMap O K)).Splits) (y : PowerSeries K)
    (hy : Polynomial.eval₂ (algebraMap O (PowerSeries K)) y P = 0) : ∃ c : K, y = PowerSeries.C c := by
  have h : algebraMap O (PowerSeries K) = (PowerSeries.C : K →+* PowerSeries K).comp (algebraMap O K) :=
    RingHom.ext fun a => PowerSeries.algebraMap_apply
  rw [h, ← Polynomial.eval₂_map, hs.eq_prod_roots_of_monic (hm.map _), Polynomial.eval₂_multiset_prod,
    Multiset.prod_eq_zero_iff, Multiset.map_map, Multiset.mem_map] at hy
  obtain ⟨c, -, hc⟩ := hy
  simp only [Function.comp_apply, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at hc
  exact ⟨c, sub_eq_zero.1 hc⟩

private theorem surj_of_card {O' K : Type} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field K]
    [Finite K] (φ : O' →+* K) (hc : Nat.card (ResidueField O') = Nat.card K) : Function.Surjective φ := by
  have hne : RingHom.ker φ ≠ ⊥ := by
    intro h
    have hi : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h
    haveI : Finite O' := Finite.of_injective φ hi
    exact IsDiscreteValuationRing.not_isField O' (Finite.isField_of_domain O')
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hmax : RingHom.ker φ = maximalIdeal O' :=
    IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne inferInstance)
  let g : ResidueField O' →+* K := Ideal.Quotient.lift (maximalIdeal O') φ (fun a ha => by
    rw [← hmax] at ha; exact ha)
  have hg : Function.Bijective g := by
    haveI : Finite (ResidueField O') := Finite.of_injective g g.injective
    exact (Nat.bijective_iff_injective_and_card g).2 ⟨g.injective, hc⟩
  intro k
  obtain ⟨a, ha⟩ := hg.2 k
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨b, ha⟩

private theorem exists_pt {O O' B K : Type} [CommRing O] [CommRing O'] [Algebra O O'] [CommRing B] [Algebra O B]
    [Field K] [Algebra O K] (α : O') (P : Polynomial O) (f : B →ₐ[O] PowerSeries K) (Q : Ideal (O' ⊗[O] B))
    (hα : Algebra.adjoin O {α} = ⊤) (hm : P.Monic) (h0 : Polynomial.aeval α P = 0)
    (hs : (P.map (algebraMap O K)).Splits) (hQ : Q.IsPrime)
    (hc : Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = RingHom.ker f) :
    ∃ x : O' ⊗[O] B →+* PowerSeries K, (∀ b, x (1 ⊗ₜ b) = f b) ∧ RingHom.ker x = Q := by
  letI : Algebra B (O' ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
  have hB : ∀ b : B, algebraMap B (O' ⊗[O] B) b = 1 ⊗ₜ b := fun b => rfl
  have hcomp : (algebraMap B (O' ⊗[O] B)).comp (algebraMap O B) =
      (Algebra.TensorProduct.includeLeftRingHom : O' →+* O' ⊗[O] B).comp (algebraMap O O') :=
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm
  obtain ⟨x, hx1, hx2⟩ := UpperTheory.V.AlgebraTools.exists_lift_ker_eq B (O' ⊗[O] B) (PowerSeries K) f.toRingHom Unit
    (fun _ => α ⊗ₜ 1) (fun _ => P.map (algebraMap O B)) (by
      have hl : ∀ o : O', o ⊗ₜ[O] (1 : B) ∈ Algebra.adjoin B (Set.range fun _ : Unit => α ⊗ₜ[O] (1 : B)) := by
        intro o
        have ho : o ∈ Algebra.adjoin O {α} := hα ▸ Algebra.mem_top
        induction ho using Algebra.adjoin_induction with
        | mem y hy =>
          rw [Set.mem_singleton_iff.1 hy]
          exact Algebra.subset_adjoin ⟨(), rfl⟩
        | algebraMap r =>
          have := RingHom.congr_fun hcomp r
          change algebraMap B (O' ⊗[O] B) (algebraMap O B r) = algebraMap O O' r ⊗ₜ 1 at this
          rw [← this]
          exact Subalgebra.algebraMap_mem _ _
        | add y z _ _ hy hz => rw [TensorProduct.add_tmul]; exact add_mem hy hz
        | mul y z _ _ hy hz =>
          have := mul_mem hy hz
          rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one] at this
      rw [eq_top_iff]
      rintro s -
      induction s using TensorProduct.induction_on with
      | zero => exact zero_mem _
      | tmul o b =>
        have := mul_mem (hl o) (Subalgebra.algebraMap_mem _ b)
        rwa [hB, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
      | add y z hy hz => exact add_mem hy hz)
    (fun _ => ⟨hm.map _, by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
      have := Polynomial.hom_eval₂ P (algebraMap O O')
        (Algebra.TensorProduct.includeLeftRingHom : O' →+* O' ⊗[O] B) α
      rw [← Polynomial.aeval_def, h0, map_zero] at this
      exact this.symm, by
      have h : f.toRingHom.comp (algebraMap O B) = (PowerSeries.C : K →+* PowerSeries K).comp (algebraMap O K) :=
        RingHom.ext fun a => (f.commutes a).trans PowerSeries.algebraMap_apply
      rw [Polynomial.map_map, h, ← Polynomial.map_map]
      exact hs.map _⟩) Q hQ hc
  exact ⟨x, fun b => RingHom.congr_fun hx1 b, hx2⟩

theorem UpperTheory.V.Pa.BC.pt_lift :
    ∀ (l : ℕ) [Fact l.Prime] (O O' : Type) [CommRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [IsCoef l O'] [Algebra O O'] (α : O') (P : Polynomial O) (B : Type) [CommRing B] [Algebra O B] (K : Type) [Field K] [Finite K] [Algebra O K] (f : B →ₐ[O] PowerSeries K) (Q : Ideal (O' ⊗[O] B)), Algebra.adjoin O {α} = ⊤ → P.Monic → Polynomial.aeval α P = 0 → (P.map (algebraMap O K)).Splits → Nat.card (ResidueField O') = Nat.card K → Q.IsPrime → Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = RingHom.ker f → ∃ (_ : Algebra O' K) (f' : Til O O' B →ₐ[O'] PowerSeries K), Function.Surjective (algebraMap O' K) ∧ (∀ b, f' (Til.ι O O' B b) = f b) ∧ f' (Til.s O O' B) = PowerSeries.X ∧ (RingHom.ker f').comap (Til.C O O' B) = Q := by
  intro l _ O O' _ _ _ _ _ _ α P B _ _ K _ _ _ f Q hα hm h0 hs hcard hQ hc
  obtain ⟨x, hx1, hx2⟩ := exists_pt α P f Q hα hm h0 hs hQ hc
  let y : O' →+* PowerSeries K := x.comp (Algebra.TensorProduct.includeLeftRingHom : O' →+* O' ⊗[O] B)
  have hyO : y.comp (algebraMap O O') = algebraMap O (PowerSeries K) := by
    refine RingHom.ext fun r => ?_
    have := RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := O) (A := O') (B := B)) r
    change x ((Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap O O')) r) = _
    rw [this]
    exact (hx1 _).trans (f.commutes r)
  have hconst : ∀ o : O', ∃ c : K, y o = PowerSeries.C c := by
    intro o
    have ho : o ∈ Algebra.adjoin O {α} := hα ▸ Algebra.mem_top
    induction ho using Algebra.adjoin_induction with
    | mem z hz =>
      rw [Set.mem_singleton_iff.1 hz]
      refine root_const P hm hs _ ?_
      rw [← hyO, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, h0, map_zero]
    | algebraMap r => exact ⟨algebraMap O K r, (RingHom.congr_fun hyO r).trans PowerSeries.algebraMap_apply⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha⟩ := ha
      obtain ⟨b', hb⟩ := hb
      exact ⟨a' + b', by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨a', ha⟩ := ha
      obtain ⟨b', hb⟩ := hb
      exact ⟨a' * b', by rw [map_mul, map_mul, ha, hb]⟩
  let φ : O' →+* K := (PowerSeries.constantCoeff : PowerSeries K →+* K).comp y
  have hφ : ∀ o, y o = PowerSeries.C (φ o) := by
    intro o
    obtain ⟨c, hc⟩ := hconst o
    change _ = PowerSeries.C (PowerSeries.constantCoeff (y o))
    rw [hc, PowerSeries.constantCoeff_C]
  obtain ⟨g, hg1, hg2⟩ := UpperTheory.V.Pa.BC.ps_ev (O' ⊗[O] B) K x
  letI : Algebra O' K := φ.toAlgebra
  let g' : Til O O' B →+* PowerSeries K := g
  have hg1' : ∀ a, g' (Til.C O O' B a) = x a := hg1
  refine ⟨this, { g' with commutes' := fun o => ?_ }, surj_of_card φ hcard, fun b => ?_, hg2, ?_⟩
  · have h : algebraMap O' (Til O O' B) o = Til.C O O' B (algebraMap O' (O' ⊗[O] B) o) :=
      PowerSeries.algebraMap_apply
    change g' (algebraMap O' (Til O O' B) o) = _
    rw [h, hg1', PowerSeries.algebraMap_apply]
    exact hφ o
  · exact (hg1' _).trans (hx1 b)
  · ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hx2, RingHom.mem_ker, ← hg1']
    rfl
end
