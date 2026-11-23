module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle096
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CenterUActionCommuteRightTranslation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle019
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

theorem UpperTheory.weil_deligne_span_crystalline :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsPst P ρ → IsCrys (P.PD K) ρ → Submodule.span ℂ {z : WDSpace P ι ρ | ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : ↥(Dpst P ρ)), x ∈ Dcris (P.PD K) ρ ∧ (y : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x ∧ z = wdMk P ι ρ y} = ⊤ := by
  intro l _ P ι K LL V _ _ _ _ _ ρ hV hc
  have hk := mem_Dst_and_monV_eq_zero_iff l P K LL V ρ
  set S := Submodule.span ℂ {z : WDSpace P ι ρ | ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : ↥(Dpst P ρ)), x ∈ Dcris (P.PD K) ρ ∧ (y : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x ∧ z = wdMk P ι ρ y} with hS
  have key : ∀ (x : V ⊗[ℚ_[l]] Bst P), x ∈ Dpst P ρ → ∃ h : x ∈ Dpst P ρ, wdMk P ι ρ ⟨x, h⟩ ∈ S := by
    intro x hx
    refine AddSubgroup.closure_induction
      (p := fun y _ => ∃ h : y ∈ Dpst P ρ, wdMk P ι ρ ⟨y, h⟩ ∈ S) ?_ ?_ ?_ ?_
      (GlobalTheory.PstLaws.mem_closure_of_isCrys P ρ hV hc x hx)
    · rintro _ ⟨c, s, hs, rfl⟩
      have hsD : s ∈ Dpst P ρ := Dst_resTo_le P ρ le_rfl ((hk s).mpr hs).1
      obtain ⟨x₀, hx₀, e⟩ := hs
      refine ⟨mulV_mem_Dpst P ρ c s hsD, ?_⟩
      have h1 : wdMk P ι ρ ⟨s, hsD⟩ ∈ S := Submodule.subset_span ⟨x₀, ⟨s, hsD⟩, hx₀, e.symm, rfl⟩
      have h2 := S.smul_mem (ι (c : Om l)) h1
      rw [← wdMk_mul] at h2
      exact h2
    · refine ⟨zero_mem _, ?_⟩
      have h1 : wdMk P ι ρ 0 ∈ S := by rw [wdMk_zero]; exact zero_mem _
      exact h1
    · rintro y z _ _ ⟨hy, h1⟩ ⟨hz, h2⟩
      refine ⟨add_mem hy hz, ?_⟩
      have h3 := S.add_mem h1 h2
      rw [← wdMk_add] at h3
      exact h3
    · rintro y _ ⟨hy, h1⟩
      refine ⟨neg_mem hy, ?_⟩
      have heq : wdMk P ι ρ ⟨-y, neg_mem hy⟩ = -wdMk P ι ρ ⟨y, hy⟩ := by
        apply eq_neg_of_add_eq_zero_left
        rw [← wdMk_add]
        have hz : (⟨-y, neg_mem hy⟩ : ↥(Dpst P ρ)) + ⟨y, hy⟩ = 0 := by
          ext
          simp
        rw [hz, wdMk_zero]
      rw [heq]
      exact S.neg_mem h1
  rw [eq_top_iff, ← span_wdMk P ι ρ, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact (key x.1 x.2).2
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem grp1 {G : Type*} [Group G] (g a b u : G) (h : a * u = u * a) :
    g * u * (a * b) = g * (a * b) * (b⁻¹ * u * b) := by
  rw [mul_assoc g u, ← mul_assoc u, ← h]
  group

private theorem grp2 {G : Type*} [Group G] (g a b u : G) (h : u * a * b = b * (u * a)) :
    g * u * (a * b) = g * b * (u * a) := by
  rw [mul_assoc g b, ← h]
  group

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem id1 (g k : AdelicGLn.AdelicGL K n) (u : AdelicGLn.FiniteAdelicGL K n) :
    g * finEmb K n u * k = g * k * finEmb K n ((finPart k)⁻¹ * u * finPart k) := by
  have h := grp1 g _ (finEmb K n (finPart k)) _ (infEmb_mul_finEmb_comm (archPart k) u)
  rw [infEmb_archPart_mul_finEmb_finPart] at h
  rw [map_mul, map_mul, map_inv]
  exact h

private theorem id2 (g k : AdelicGLn.AdelicGL K n) (u : archGroup K n) :
    g * infEmb K n u * k = g * finEmb K n (finPart k) * infEmb K n (u * archPart k) := by
  have h0 := infEmb_mul_finEmb_comm (u * archPart k) (finPart k)
  rw [map_mul] at h0
  have h := grp2 g _ _ _ h0
  rw [infEmb_archPart_mul_finEmb_finPart] at h
  rw [map_mul]
  exact h

private theorem hmul (a b : AdelicGLn.AdelicGL K n) (φ : archSmooth K n) : rt a (rt b φ) = rt (a * b) φ :=
  Subtype.ext (funext fun x => by rw [rt_apply, rt_apply, rt_apply, mul_assoc])

private theorem hone (φ : archSmooth K n) : rt (1 : AdelicGLn.AdelicGL K n) φ = φ :=
  Subtype.ext (funext fun x => by rw [rt_apply, mul_one])

private noncomputable def sat (S : Submodule ℂ (archSmooth K n)) : Submodule ℂ (archSmooth K n) :=
  Submodule.span ℂ {ψ | ∃ k ∈ Reduction.maxCompact (K := K) (n := n), ∃ φ ∈ S, ψ = rt k φ}

private theorem ind (S : Submodule ℂ (archSmooth K n)) (P : archSmooth K n → Prop) (h0 : P 0)
    (ha : ∀ x y, P x → P y → P (x + y)) (hs : ∀ (c : ℂ) x, P x → P (c • x))
    (hg : ∀ k ∈ Reduction.maxCompact (K := K) (n := n), ∀ φ ∈ S, P (rt k φ)) : ∀ ψ ∈ sat S, P ψ := by
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, φ, hφ, rfl⟩ := hx
    exact hg k hk φ hφ
  | zero => exact h0
  | add x y _ _ hx hy => exact ha x y hx hy
  | smul c x _ hx => exact hs c x hx
end

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ} {S : Submodule ℂ (archSmooth K n)}

private theorem sat_left (hS : Bdd S) : ∀ φ ∈ sat S, IsLeftInvariant φ.1 := by
  refine ind S (fun φ => IsLeftInvariant φ.1) isLeftInvariant_zero
      (fun x y hx hy γ g => congrArg₂ (· + ·) (hx γ g) (hy γ g))
      (fun c x hx γ g => congrArg (c • ·) (hx γ g)) ?_
  intro k _ φ hφ γ g
  rw [rt_apply, rt_apply, mul_assoc]
  exact hS.left φ hφ γ _

private theorem sat_growth (hS : Bdd S) : Growth (sat S) := by
  refine ind S (fun φ => HasModerateGrowth φ.1) hasModerateGrowth_zero
      (fun x y hx hy => hx.add hy) (fun c x hx => hx.smul c) ?_
  intro k _ φ hφ
  have h := (hS.growth φ hφ).translate k
  have e : (rt k φ).1 = rightTranslate k φ.1 := funext fun x => rt_apply k φ x
  rw [e]
  exact h

private theorem sat_level (hS : Bdd S) : Level (sat S) := by
  obtain ⟨L, hL, hinv⟩ := hS.level
  obtain ⟨L', hL', hle, hconj, -⟩ := UpperTheory.exists_open_level_normalized_by_integralFiniteGL K n L hL
  refine ⟨L', hL', ?_⟩
  refine ind S (fun φ => ∀ u ∈ L', ∀ g, φ.1 (g * finEmb K n u) = φ.1 g) (fun _ _ _ => rfl)
      (fun x y hx hy u hu g => congrArg₂ (· + ·) (hx u hu g) (hy u hu g))
      (fun c x hx u hu g => congrArg (c • ·) (hx u hu g)) ?_
  intro k hk φ hφ u hu g
  rw [rt_apply, rt_apply, id1]
  exact hinv φ hφ _ (hle (hconj _ (finPart_mem_integralFiniteGL hk) u hu)) (g * k)

private theorem sat_types (hS : Bdd S) : Types (sat S) := by
  obtain ⟨V, hV, hst, hmem⟩ := hS.types
  refine ⟨V, hV, hst, ?_⟩
  refine ind S (fun φ => ∀ g, (fun k : archCompact K n => φ.1 (g * infEmb K n k.1)) ∈ V) (fun _ => V.zero_mem)
      (fun x y hx hy g => V.add_mem (hx g) (hy g))
      (fun c x hx g => V.smul_mem c (hx g)) ?_
  intro k hk φ hφ g
  have h := hst _ (hmem φ hφ (g * finEmb K n (finPart k))) ⟨archPart k, archPart_mem_archCompact hk⟩
  have e : (fun k' : archCompact K n => (rt k φ).1 (g * infEmb K n k'.1)) =
      fun k' : archCompact K n => φ.1 (g * finEmb K n (finPart k) * infEmb K n (k'.1 * archPart k)) :=
    funext fun k' => by rw [rt_apply, id2]
  rw [e]
  exact h

private theorem sat_centre (hS : Bdd S) : Centre (sat S) := by
  intro z hz
  obtain ⟨p, hp, h⟩ := hS.centre z hz
  refine ⟨p, hp, ?_⟩
  refine ind S (fun φ => Polynomial.aeval (uAction z) p φ ∈ (⊥ : Submodule ℂ (archSmooth K n)))
      (by rw [map_zero]; exact Submodule.zero_mem _)
      (fun x y hx hy => by rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy)
      (fun c x hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) ?_
  intro k _ φ hφ
  have hc : Commute (rt (K := K) (n := n) k) (Polynomial.aeval (uAction z) p) :=
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute (Polynomial.aeval_mem_adjoin_singleton ℂ _)
      (by rintro _ rfl; exact (UpperTheory.centerU_action_commute_rightTranslation K n z hz k).symm)
  have e := LinearMap.congr_fun hc.eq φ
  rw [Module.End.mul_apply, Module.End.mul_apply] at e
  rw [← e, (Submodule.mem_bot ℂ).1 (h φ hφ), map_zero]
  exact Submodule.zero_mem _

private theorem sat_sat : Sat (sat S) := by
  intro k hk
  refine ind S (fun φ => rt k φ ∈ sat S)
      (by rw [map_zero]; exact Submodule.zero_mem _)
      (fun x y hx hy => by rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy)
      (fun c x hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) ?_
  intro k' hk' φ hφ
  exact Submodule.subset_span ⟨k * k', mul_mem hk hk', φ, hφ, hmul _ _ _⟩
end

theorem UpperTheory.exists_automorphic_saturation_submodule :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Bdd S → ∃ S' : Submodule ℂ (archSmooth K n), S ≤ S' ∧ Bdd S' ∧ Sat S' := by
  intro K _ _ n S hS
  exact ⟨sat S, fun φ hφ => Submodule.subset_span ⟨1, one_mem _, φ, hφ, (hone φ).symm⟩,
    ⟨sat_left hS, sat_growth hS, sat_level hS, sat_types hS, sat_centre hS⟩, sat_sat⟩
end

section

open GlobalTheory.CuspRep

private theorem iSup_range_of_jointly_injective {R M S N I : Type} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup S] [Module R S] [AddCommGroup N] [Module R N] [IsSimpleModule R S] [Finite I]
    (h : ∀ x : M, x ∈ ⨆ f : S →ₗ[R] M, LinearMap.range f) (j : I → N →ₗ[R] M)
    (hj : ∀ y, (∀ i, j i y = 0) → y = 0) (y : N) : y ∈ ⨆ f : S →ₗ[R] N, LinearMap.range f := by
  have hM : IsSemisimpleModule R M := by
    refine IsSemisimpleModule.of_sSup_simples_eq_top (top_le_iff.1 fun x _ => ?_)
    refine (iSup_le (a := sSup {m : Submodule R M | IsSimpleModule R m}) fun f => ?_) (h x)
    rcases LinearMap.injective_or_eq_zero f with hf | rfl
    · exact le_sSup (IsSimpleModule.congr (LinearEquiv.ofInjective f hf).symm)
    · simp
  have hinj : Function.Injective (LinearMap.pi j) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    exact fun z hz => hj z fun i => congrFun hz i
  have hN : IsSemisimpleModule R N := IsSemisimpleModule.congr (LinearEquiv.ofInjective _ hinj)
  have hy : y ∈ sSup {m : Submodule R N | IsSimpleModule R m} := by
    rw [IsSemisimpleModule.sSup_simples_eq_top]; trivial
  refine (sSup_le (a := ⨆ f : S →ₗ[R] N, LinearMap.range f) fun m hm => ?_) hy
  have hm' : IsSimpleModule R m := hm
  by_cases hz : ∀ i, (j i).comp m.subtype = 0
  · intro z hzm
    have : z = 0 := hj z fun i => LinearMap.congr_fun (hz i) ⟨z, hzm⟩
    rw [this]; exact zero_mem _
  · obtain ⟨i, hi⟩ := not_forall.1 hz
    have hi' := (LinearMap.injective_or_eq_zero ((j i).comp m.subtype)).resolve_right hi
    obtain ⟨e⟩ := LocUniq.equiv_of_iSup_range h _ hi'
    intro z hzm
    exact Submodule.mem_iSup_of_mem (m.subtype.comp e.toLinearMap) ⟨e.symm ⟨z, hzm⟩, by simp⟩

theorem UpperTheory.isotypic_of_jointly_injective_into_isotypic :
    ∀ (Γ X V : Type) [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ Γ X) (τ : Representation ℂ Γ V), σ.IsIrreducible → (⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1) = ⊤ → ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ Γ Y) (I : Type) [Finite I] (j : I → Y →ₗ[ℂ] V), (∀ i g y, j i (ρ g y) = τ g (j i y)) → (∀ y, (∀ i, j i y = 0) → y = 0) → (⨆ f : {f : X →ₗ[ℂ] Y // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) = ⊤ := by
  intro Γ X V _ _ _ _ _ σ τ hσ h Y _ _ ρ I _ j hj hj0
  have key := iSup_range_of_jointly_injective (R := MonoidAlgebra ℂ Γ) (S := σ.asModule) (M := τ.asModule)
    (N := ρ.asModule) (fun x => by
      have hx : τ.asModuleEquiv x ∈ (⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)},
        LinearMap.range f.1) := h ▸ Submodule.mem_top
      have hle : (⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)},
          LinearMap.range f.1) ≤ ((⨆ f : σ.asModule →ₗ[MonoidAlgebra ℂ Γ] τ.asModule,
          LinearMap.range f).restrictScalars ℂ).comap τ.asModuleEquiv.symm.toLinearMap := by
        refine iSup_le fun f => ?_
        rintro _ ⟨v, rfl⟩
        let f' : σ.IntertwiningMap τ := ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
        have : Representation.IntertwiningMap.equivLinearMapAsModule σ τ f' (σ.asModuleEquiv.symm v) ∈
            ⨆ f : σ.asModule →ₗ[MonoidAlgebra ℂ Γ] τ.asModule, LinearMap.range f :=
          Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ τ f') ⟨_, rfl⟩
        exact this
      exact hle hx)
    (fun i => Representation.IntertwiningMap.equivLinearMapAsModule ρ τ ⟨j i, fun g => LinearMap.ext (hj i g)⟩)
    (fun y hy => hj0 y hy)
  refine top_le_iff.1 fun y _ => ?_
  refine Submodule.iSup_induction _ (motive := fun z : ρ.asModule => ρ.asModuleEquiv z ∈
    (⨆ f : {f : X →ₗ[ℂ] Y // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1))
    (key (ρ.asModuleEquiv.symm y)) ?_ ?_ ?_
  · rintro f _ ⟨v, rfl⟩
    let f' := (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ).symm f
    exact Submodule.mem_iSup_of_mem ⟨f'.toLinearMap, fun g v => LinearMap.congr_fun (f'.isIntertwining' g) v⟩
      ⟨σ.asModuleEquiv v, rfl⟩
  · rw [map_zero]; exact zero_mem _
  · intro a b ha hb
    rw [map_add]; exact add_mem ha hb
end
