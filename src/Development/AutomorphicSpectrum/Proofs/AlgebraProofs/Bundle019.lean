module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle002
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RingHomProperties
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle015
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterExists
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsIntegralPosDefPerturbation
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.EquationalCriterion
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.EigDim

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.HT.LatBasic

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {E : Type} [Field E] [NumberField E]

theorem trace_eigProj [FiniteDimensional K V] (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) :
    LinearMap.trace K V (eigProj ρ σ) = (finrank K (eigSp ρ σ) : K) :=
  LinearMap.IsProj.trace (p := eigSp ρ σ)
    ⟨fun x => eigProj_mem ρ σ x, fun _ hx => eigProj_of_mem hx⟩

theorem sum_embedding_dualInt [IsAlgClosed K] [CharZero K]
    (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    ∑ σ : E →+* K, σ (dualInt E k) = (((RingOfIntegers.basis E).repr 1 k : ℤ) : K) := by
  have h1 : ∑ σ : E →+* K, σ (dualInt E k) = ∑ σ : E →ₐ[ℚ] K, σ (dualInt E k) :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom E K) _ _ fun _ => rfl
  have h2 := repr_eq_trace (E := E) 1 k
  rw [h1, ← trace_eq_sum_embeddings (E := K) (K := ℚ) (L := E)]
  have h3 : ((1 : 𝓞 E) : E) = 1 := map_one (algebraMap (𝓞 E) E)
  rw [h3, mul_one] at h2
  rw [← h2]
  simp

theorem sum_eigProj [IsAlgClosed K] [CharZero K] (ρ : 𝓞 E →+* Module.End K V) :
    ∑ σ : E →+* K, eigProj ρ σ = 1 := by
  unfold eigProj
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_embedding_dualInt]

  conv_rhs => rw [← map_one ρ, ← (RingOfIntegers.basis E).sum_repr 1, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

theorem finrank_eigSp_mul :
    ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (V : Type) [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V),
      (∀ a : 𝓞 E, ∃ n : ℤ, LinearMap.trace K V (ρ a) = (n : K)) →
      ∀ σ : E →+* K, Module.finrank K (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) * Module.finrank ℚ E =
        Module.finrank K V := by
  intro K _ _ _ V _ _ _ E _ _ ρ htr σ
  choose m hm using fun k => htr (RingOfIntegers.basis E k)
  set l : E := ∑ k, (m k : E) * dualInt E k with hl
  have h1 : ∀ τ : E →+* K, (finrank K (eigSp ρ τ) : K) = τ l := by
    intro τ

    rw [← trace_eigProj, hl, map_sum]
    unfold eigProj

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hm, map_mul, map_intCast, smul_eq_mul, mul_comm]
  have h2 : ∀ τ : E →+* K, (finrank K (eigSp ρ τ) : E) = l := fun τ =>
    τ.injective (by rw [map_natCast, h1])
  have h3 : ∀ τ : E →+* K, finrank K (eigSp ρ τ) = finrank K (eigSp ρ σ) := fun τ =>
    Nat.cast_injective ((h2 τ).trans (h2 σ).symm)
  have h4 : (finrank K V : K) = ∑ τ : E →+* K, (finrank K (eigSp ρ τ) : K) := by

    rw [← LinearMap.trace_one, ← sum_eigProj ρ, map_sum]
    exact Finset.sum_congr rfl fun τ _ => trace_eigProj ρ τ
  simp_rw [h3] at h4
  rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul] at h4
  have h5 : finrank K V = finrank ℚ E * finrank K (eigSp ρ σ) := by exact_mod_cast h4
  rw [h5, mul_comm]

end GlobalTheory.CompanionTheory.Ar.HT.EigDim
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

noncomputable section
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd

theorem finiteFreeHom_algebraMap_iff {A B : Type} [CommRing A] [CommRing B] [Algebra A B] :
    FiniteFreeHom (algebraMap A B) ↔ Module.Free A B ∧ Module.Finite A B := by
  have h : (algebraMap A B).toAlgebra = ‹Algebra A B› := Algebra.algebra_ext _ _ fun _ => rfl
  simp only [GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom]
  rw [h]

theorem finiteFreeHom_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (hf : FiniteFreeHom f) (hg : FiniteFreeHom g) :
    FiniteFreeHom (g.comp f) := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hf₁, hf₂⟩ := hf
  obtain ⟨hg₁, hg₂⟩ := hg
  exact ⟨Module.Free.trans (S := B), Module.Finite.trans B C⟩

theorem finiteFreeHom_ringEquiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) :
    FiniteFreeHom e.toRingHom := by
  letI := e.toRingHom.toAlgebra
  let l : A ≃ₗ[A] B := { e with map_smul' := fun a x => map_mul e a x }
  exact ⟨Module.Free.of_equiv l, Module.Finite.equiv l⟩

theorem finiteFreeHom_stableUnderComposition :
    RingHom.StableUnderComposition (fun {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) =>
      FiniteFreeHom f) := by
  intro A B C _ _ _ f g hf hg
  exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_comp f g hf hg

theorem finiteFreeHom_respectsIso :
    RingHom.RespectsIso (fun {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) =>
      FiniteFreeHom f) :=
  RingHom.StableUnderComposition.respectsIso GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_stableUnderComposition
    fun e => GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_ringEquiv e

theorem finiteFreeHom_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange (fun {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) =>
      FiniteFreeHom f) := by
  refine RingHom.IsStableUnderBaseChange.mk GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_respectsIso ?_
  intro R S T _ _ _ _ _ h
  obtain ⟨h₁, h₂⟩ := GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_algebraMap_iff.1 h
  exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_algebraMap_iff.2 ⟨inferInstance, inferInstance⟩

theorem finiteFreeHom_appTop_of_isPullback :
    ∀ {P Q D W : Scheme.{0}} {u : P ⟶ Q} {v : P ⟶ D} {g : Q ⟶ W} {h : D ⟶ W} [IsAffine P] [IsAffine Q] [IsAffine D] [IsAffine W], IsPullback u v g h → GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom g.appTop.hom → GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom v.appTop.hom := by
  intro P Q D W u v g h _ _ _ _ hpb hg
  have hbc := RingHom.IsStableUnderBaseChange.pullback_fst_appTop @GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom
    GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_isStableUnderBaseChange GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_respectsIso h g hg
  haveI : IsIso hpb.flip.isoPullback.hom.appTop := by
    rw [← Scheme.Γ_map_op]
    exact (Scheme.Γ.mapIso hpb.flip.isoPullback.op).isIso_hom
  rw [← hpb.flip.isoPullback_hom_fst, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  exact (RingHom.RespectsIso.cancel_right_isIso GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_respectsIso _ _).2 hbc

end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
end
end

section

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

open GlobalTheory.CompanionTheory.Ar.Crv

private theorem valuation_natCast_le_one_algebra {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))
    (n : ℕ) : v (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    push_cast
    exact (v.map_add _ _).trans (max_le ih (le_of_eq v.map_one))

theorem v_intCast_le_one {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))
    (n : ℤ) : v (n : K) ≤ 1 := by
  cases n with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    exact valuation_natCast_le_one_algebra v m
  | negSucc m =>
    rw [Int.cast_negSucc, Valuation.map_neg]
    exact_mod_cast valuation_natCast_le_one_algebra v (m + 1)

theorem freeAt_of_basis_lattice (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O ι k : Type) [CommRing O]
    [Fintype ι] [Field k] [Algebra k K] (b : Module.Basis ι ℤ O) (ρ : O →+* Module.End K V)
    (r : ℕ) (i : C.I) (hL : IsBun C L) (hk : ∀ c : k, C.v i (algebraMap k K c) ≤ 1)
    (h : ∃ x : Fin r → V, LinearIndependent K (fun q : Fin r × ι => ρ (b q.2) (x q.1)) ∧
      ∀ y, y ∈ L i ↔ ∃ c : Fin r × ι → K, (∀ q, C.v i (c q) ≤ 1) ∧
        y = ∑ q, c q • ρ (b q.2) (x q.1)) :
    FreeAt C k (act k ρ) L r i := by
  obtain ⟨x, hli, hL'⟩ := h
  set e : Fin r × ι → V := fun q => ρ (b q.2) (x q.1) with he
  obtain ⟨b0, hb0⟩ := hL.1 i
  have hb0 : ∀ z : V, z ∈ L i ↔ ∀ q, C.v i (b0.repr z q) ≤ 1 := hb0
  have hmemL : ∀ y : V, y ∈ L i → y ∈ Submodule.span K (Set.range e) := by
    intro y hy
    obtain ⟨c, -, rfl⟩ := (hL' y).1 hy
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  have hspan : ⊤ ≤ Submodule.span K (Set.range e) := by
    rw [← b0.span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    refine hmemL _ ((hb0 _).2 fun q => ?_)
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact (map_one _).le
    · rw [map_zero]
      exact zero_le_one
  let B : Module.Basis (Fin r × ι) K V := Module.Basis.mk hli hspan
  have hBe : ∀ q, B q = e q := fun q => Module.Basis.mk_apply hli hspan q
  have key : ∀ (c : Fin r × ι → K) (q : Fin r × ι), B.coord q (∑ q', c q' • e q') = c q := by
    intro c q
    have hc : ∑ q', c q' • e q' = B.equivFun.symm c := by
      rw [Module.Basis.equivFun_symm_apply]
      simp only [hBe]
    rw [hc, Module.Basis.coord_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have key' : ∀ (c : Fin r × ι → K) (q : Fin r × ι),
      B.coord q (∑ q', c q' • ρ (b q'.2) (x q'.1)) = c q := key
  have hrep : ∀ (o : O) (s' : Fin r), ρ o (x s') =
      ∑ q : Fin r × ι, (if q.1 = s' then ((b.repr o q.2 : ℤ) : K) else 0) • e q := by
    intro o s'
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s' (fun s _ hs => by simp [hs])
      (fun h => absurd (Finset.mem_univ _) h)]
    conv_lhs => rw [← b.sum_repr o]

    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    rw [if_pos rfl, map_zsmul, Int.cast_smul_eq_zsmul]
    rfl
  refine ⟨x, fun l s => ∑ j, algebraMap k K (l (1 ⊗ₜ[ℤ] b j)) • B.coord (s, j), ?_, ?_, ?_, ?_⟩
  · intro s
    rw [hL']
    refine ⟨fun q => if q.1 = s then ((b.repr 1 q.2 : ℤ) : K) else 0, fun q => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact v_intCast_le_one _ _
      · rw [map_zero]
        exact zero_le_one
    · exact (LinearMap.congr_fun (map_one ρ) (x s)).symm.trans (hrep 1 s)
  · intro l s s' a
    dsimp only
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul c o =>
      rw [act_tmul, LinearMap.smul_apply, map_smul, hrep o s']
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, key, smul_eq_mul]
      split_ifs with hss
      · have h1 : l (c ⊗ₜ[ℤ] o) = c * l ((1 : k) ⊗ₜ[ℤ] o) := by
          rw [← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have h2 : l ((1 : k) ⊗ₜ[ℤ] o) = ∑ j, b.repr o j • l ((1 : k) ⊗ₜ[ℤ] b j) := by
          conv_lhs => rw [← b.sum_repr o]

          rw [TensorProduct.tmul_sum, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [TensorProduct.tmul_smul, map_zsmul]

        rw [h1, h2, map_mul, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_zsmul, zsmul_eq_mul]
        ring
      · simp [hss]
    | add a a' ha ha' =>
      rw [map_add (f := _), LinearMap.add_apply, map_add (f := _), ha, ha']
      split_ifs <;> simp [map_add (f := _)]
  · intro l s y hy
    obtain ⟨c, hc, rfl⟩ := (hL' y).1 hy
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, key', smul_eq_mul]
    refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact mul_le_one' (hk _) (hc _)
  · intro y
    have hy : y ∈ Submodule.span K (Set.range e) := hspan Submodule.mem_top
    refine Submodule.span_mono ?_ hy
    rintro _ ⟨q, rfl⟩
    exact ⟨(1 ⊗ₜ[ℤ] b q.2, q.1), by
      show (act k ρ) ((1 : k) ⊗ₜ[ℤ] b q.2) (x q.1) = e q
      rw [act_tmul, map_one, one_smul]⟩

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
end
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.LfpDescent

lemma affine_case {X Y S : Scheme.{0}} [IsAffine X] [IsAffine Y] [IsAffine S] (q : X ⟶ Y)
    (f : Y ⟶ S) [IsFinite q] [Flat q] [LocallyOfFinitePresentation q] [Surjective q]
    [LocallyOfFinitePresentation (q ≫ f)] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  have h1 : q.appTop.hom.Finite :=
    Scheme.Hom.finite_appTop q
  have h2 : q.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q).1 ⟨inferInstance, inferInstance⟩
  have h3 : q.appTop.hom.FinitePresentation :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).1 inferInstance
  have h4 : (q.appTop.hom.comp f.appTop.hom).FinitePresentation := by
    have := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).1
      (inferInstance : LocallyOfFinitePresentation (q ≫ f))
    rwa [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at this
  letI : Algebra Γ(S, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (q.appTop.hom.comp f.appTop.hom).toAlgebra
  haveI : IsScalarTower Γ(S, ⊤) Γ(Y, ⊤) Γ(X, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := h1
  haveI : Algebra.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) := h3
  haveI : Module.FaithfullyFlat Γ(Y, ⊤) Γ(X, ⊤) := h2
  haveI : Module.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  have hp : Module.Projective Γ(Y, ⊤) Γ(X, ⊤) := Module.Flat.projective_of_finitePresentation
  exact GlobalTheory.T.finitePresentation_of_faithfully_flat _ _ _ inferInstance hp inferInstance h4

theorem descends : ∀ {X Y S : Scheme.{0}} (q : X ⟶ Y) (f : Y ⟶ S), IsFinite q → Flat q →
    LocallyOfFinitePresentation q → Surjective q → LocallyOfFinitePresentation (q ≫ f) →
    LocallyOfFinitePresentation f := by
  intro X Y S q f _ _ _ _ _
  let I := {p : S.affineOpens × Y.affineOpens // (p.2 : Y.Opens) ≤ f ⁻¹ᵁ (p.1 : S.Opens)}
  haveI := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{0})
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFinitePresentation.{0}) (fun i : I ↦ (i.1.2 : Y.Opens)) ?_ ?_
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := f y) (U := ⊤) trivial
    obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := f ⁻¹ᵁ U) hyU
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hVU⟩, hyV⟩
  · rintro ⟨⟨⟨U, hU⟩, ⟨V, hV⟩⟩, e⟩
    dsimp only at e ⊢
    haveI : IsAffine U.toScheme := hU
    haveI : IsAffine V.toScheme := hV
    haveI : IsAffine (q ⁻¹ᵁ V).toScheme := (hV.preimage q)
    have hc : (q ∣_ V) ≫ f.resLE U V e =
        (q ≫ f).resLE U (q ⁻¹ᵁ V) (by simpa using (Scheme.Hom.preimage_mono q e)) := by
      rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]
    haveI : LocallyOfFinitePresentation ((q ∣_ V) ≫ f.resLE U V e) := by
      rw [hc]; delta Scheme.Hom.resLE; infer_instance
    haveI : Surjective (q ∣_ V) := IsZariskiLocalAtTarget.restrict ‹Surjective q› V
    haveI : LocallyOfFinitePresentation (f.resLE U V e) := affine_case (q ∣_ V) _
    rw [← Scheme.Hom.resLE_comp_ι f e]
    infer_instance

end GlobalTheory.CompanionTheory.LfpDescent
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.ultrametric_det_norm_stable : ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I] (M M' : Matrix I I A) (r : ℝ), 0 < r → (∀ a b, ‖M a b‖ ≤ r) → (∀ a b, ‖M' a b - M a b‖ < r) → ‖M.det‖ = r ^ Fintype.card I → ‖M'.det‖ = r ^ Fintype.card I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.norm_det_eq_of_entries_close | exact GlobalTheory.CompanionTheory.Ar.Fl.norm_det_eq_of_entries_close | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.norm_det_eq_of_entries_close <;> assumption)
end

section

open scoped Matrix TensorProduct
open Matrix

theorem _root_.GlobalTheory.T.gauss_sum_valuation_teichmuller : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → Fintype.card F ≠ 2 → ∀ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) → ∀ ψ : AddChar F C, ψ ≠ 1 → v (∑ a, algebraMap R C (σ⁻¹ a) * ψ a) ^ (p - 1) = v (p : C) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.gauss_value | exact GlobalTheory.CompanionTheory.Ar.GR.gauss_value | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.gauss_value <;> assumption)
end

section

open scoped Matrix TensorProduct
open Matrix

theorem _root_.GlobalTheory.T.teichmuller_character_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∃ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.fund_ex_relay | exact GlobalTheory.CompanionTheory.Ar.GR.fund_ex_relay | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.fund_ex_relay <;> assumption)
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.skew_hermitian_diagonalizable : ∀ (R : Type) [CommRing R] [StarRing R] [Finite (MaximalSpectrum R)] (n : ℕ) (G : Matrix (Fin n) (Fin n) R), Gᴴ = -G → IsUnit G.det → (∀ m : Ideal R, m.IsMaximal → ∃ a : R, a - star a ∉ m) → ∃ T : Matrix (Fin n) (Fin n) R, IsUnit T.det ∧ (T * G * Tᴴ).IsDiag := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.skewHermitian_congr_diag | exact GlobalTheory.CompanionTheory.CommAlg.skewHermitian_congr_diag | (intros; apply GlobalTheory.CompanionTheory.CommAlg.skewHermitian_congr_diag <;> assumption)
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem frame_congr_posDef_on_places : ∀ (E : Type) [Field E] [NumberField E] (Ψ : Set (E →+* ℂ)) (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (M : (E →+* ℂ) → Matrix J J ℂ) (C : (E →+* ℂ) → Matrix I J ℂ) (X₀ : Matrix I J (𝓞 E)) (n : ℕ), n ≠ 0 → (∀ τ ∈ Ψ, ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ ∈ Ψ, (M τ).IsHermitian ∧ (C τ * M τ * (C τ)ᴴ).PosDef) → ∃ Y : Matrix I J (𝓞 E), ∀ τ ∈ Ψ, (((X₀ + n • Y).map fun a => τ (a : E)) * M τ * ((X₀ + n • Y).map fun a => τ (a : E))ᴴ).PosDef :=
  @PositivityTheory.Xgf.exists_integral_posDef_perturbation

end GlobalTheory.CompanionTheory.Ar.Fl
end

section


theorem _root_.GlobalTheory.T.adic_complete_algebra_lifting_unique : ∀ (R A B : Type) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Module.Finite R A] (I : Ideal R) [IsAdicComplete I R] (f : ∀ e : ℕ, B →ₐ[R] A ⧸ (I ^ (e + 1)).map (algebraMap R A)), (∀ e (b : B) (a : A), Ideal.Quotient.mk _ a = f (e + 1) b → Ideal.Quotient.mk _ a = f e b) → ∃! g : B →ₐ[R] A, ∀ e b, Ideal.Quotient.mk _ (g b) = f e b := by
  first | exact @GlobalTheory.CompanionTheory.Relay.adic_complete_algebra_lifting_unique | exact GlobalTheory.CompanionTheory.Relay.adic_complete_algebra_lifting_unique | (intros; apply GlobalTheory.CompanionTheory.Relay.adic_complete_algebra_lifting_unique <;> assumption)
end

section

open TensorProduct

theorem _root_.GlobalTheory.T.alg_closed_tensor_isDomain : ∀ (K Ω C : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Field C] [Algebra K C], (∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) → IsDomain (Ω ⊗[K] C) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isDomain_tensor_of_algebraically_closed_constants | exact GlobalTheory.CompanionTheory.Ar.Flat.isDomain_tensor_of_algebraically_closed_constants | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isDomain_tensor_of_algebraically_closed_constants <;> assumption)
end
