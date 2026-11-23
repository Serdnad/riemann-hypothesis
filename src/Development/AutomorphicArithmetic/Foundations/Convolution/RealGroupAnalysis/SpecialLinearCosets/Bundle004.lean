module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.CompCoordMem
import GroundTheory.GlobalFields.Bundle001
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section SlopeTestRemainingChoices

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem ind_mem_SB (U : Subgroup G) (ho : IsOpen (U : Set G)) (hc : IsCompact (U : Set G)) :
    ind U ∈ SB G := by
  have hcl : IsClopen (U : Set G) := ⟨U.isClosed_of_isOpen ho, ho⟩
  refine GroundTheory.LocalField.mem_schwartzBruhat.mpr ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ U
    · refine ⟨U, ho, hx, fun y hy => ?_⟩
      simp [ind, Set.indicator, hx, show y ∈ U from hy]
    · refine ⟨(U : Set G)ᶜ, hcl.compl.isOpen, hx, fun y hy => ?_⟩
      simp [ind, Set.indicator, hx, show y ∉ U from hy]
  · refine HasCompactSupport.intro hc fun x hx => ?_
    simp [ind, Set.indicator, show x ∉ U from hx]

private theorem translate_mem_SB (a : SB G) (g : G) : (fun m => a.1 (m * g)) ∈ SB G := by
  obtain ⟨h1, h2⟩ := GroundTheory.LocalField.mem_schwartzBruhat.mp a.2
  exact GroundTheory.LocalField.mem_schwartzBruhat.mpr
    ⟨h1.comp_continuous (continuous_mul_const g), h2.comp_homeomorph (Homeomorph.mulRight g)⟩

private theorem scale (B : SB G →ₗ[ℂ] ℂ) (U U' : Subgroup G) (s : Finset G) (hs : ∀ g ∈ s, g ∈ U)
    (hsum : ∀ x, ind U x = ∑ g ∈ s, ind U' (x * g⁻¹)) (a a' : SB G) (ha : a.1 = ind U)
    (ha' : a'.1 = ind U')
    (hB : ∀ g ∈ U, ∀ b b' : SB G, (∀ m, b'.1 m = b.1 (m * g)) → B b' = B b) :
    B a = (s.card : ℂ) * B a' := by
  let t : G → SB G := fun g => ⟨fun m => a'.1 (m * g⁻¹), translate_mem_SB a' g⁻¹⟩
  have hat : a = ∑ g ∈ s, t g := by
    apply Subtype.ext
    funext x
    rw [ha, hsum x, Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    change ind U' (x * g⁻¹) = a'.1 (x * g⁻¹)
    rw [ha']
  have ht : ∀ g ∈ s, B (t g) = B a' := fun g hg =>
    hB g⁻¹ (U.inv_mem (hs g hg)) a' (t g) fun _ => rfl

  rw [hat, map_sum, Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul]

variable [T2Space G]

private theorem cross_le (B C : SB G →ₗ[ℂ] ℂ) (U U' : Subgroup G) (hle : U' ≤ U)
    (hc : IsCompact (U : Set G)) (ho : IsOpen (U' : Set G)) (a a' : SB G) (ha : a.1 = ind U)
    (ha' : a'.1 = ind U')
    (hB : ∀ g ∈ U, ∀ b b' : SB G, (∀ m, b'.1 m = b.1 (m * g)) → B b' = B b)
    (hC : ∀ g ∈ U, ∀ b b' : SB G, (∀ m, b'.1 m = b.1 (m * g)) → C b' = C b) :
    B a * C a' = B a' * C a := by
  obtain ⟨s, -, hs, hsum⟩ := cosetSum G U U' hle hc ho
  rw [scale B U U' s hs hsum a a' ha ha' hB, scale C U U' s hs hsum a a' ha ha' hC]
  ring

private theorem core {V : Type} [AddCommGroup V] [Module ℂ V] (hL : Lgrp G) (act : G → V →ₗ[ℂ] V)
    (hact : ∀ f, {g | act g f = f} ∈ 𝓝 (1 : G)) (I : SB G →ₗ[ℂ] ℂ)
    (hI : ∀ (g : G) (a a' : SB G), (∀ m, a'.1 m = a.1 (m * g)) → I a' = I a)
    (hne : ∀ (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → a.1 = ind U → I a ≠ 0)
    (β : V →ₗ[ℂ] SB G →ₗ[ℂ] ℂ)
    (hβ : ∀ (g : G) f (a a' : SB G), (∀ m, a'.1 m = a.1 (m * g)) → β (act g f) a' = β f a) :
    ∃ Λ : V →ₗ[ℂ] ℂ, ∀ f (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → a.1 = ind U →
      (∀ g ∈ U, act g f = f) → β f a = I a * Λ f := by

  have hinv : ∀ (f : V) (U : Subgroup G), (∀ g ∈ U, act g f = f) →
      ∀ g ∈ U, ∀ b b' : SB G, (∀ m, b'.1 m = b.1 (m * g)) → β f b' = β f b := by
    intro f U hf g hg b b' hb
    have := hβ g f b b' hb
    rwa [hf g hg] at this

  have hex : ∀ f f' : V, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ IsCompact (U : Set G) ∧
      (∀ g ∈ U, act g f = f) ∧ (∀ g ∈ U, act g f' = f') := by
    intro f f'
    obtain ⟨U, ho, hc, hsub⟩ := hL _ (Filter.inter_mem (hact f) (hact f'))
    exact ⟨U, ho, hc, fun g hg => (hsub hg).1, fun g hg => (hsub hg).2⟩

  have hcpt : ∀ (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → a.1 = ind U →
      IsCompact (U : Set G) := by
    intro U a ho ha
    obtain ⟨-, h2⟩ := GroundTheory.LocalField.mem_schwartzBruhat.mp a.2
    refine IsCompact.of_isClosed_subset h2 (U.isClosed_of_isOpen ho) fun x hx => ?_
    refine subset_tsupport _ ?_
    rw [Function.mem_support, ha]
    simp [ind, Set.indicator, show x ∈ U from hx]

  have hcross : ∀ (f : V) (U₁ U₂ : Subgroup G) (a₁ a₂ : SB G), IsOpen (U₁ : Set G) →
      IsOpen (U₂ : Set G) → a₁.1 = ind U₁ → a₂.1 = ind U₂ → (∀ g ∈ U₁, act g f = f) →
      (∀ g ∈ U₂, act g f = f) → β f a₁ * I a₂ = β f a₂ * I a₁ := by
    intro f U₁ U₂ a₁ a₂ ho₁ ho₂ h₁ h₂ hf₁ hf₂
    have hc₁ := hcpt U₁ a₁ ho₁ h₁
    have hc₂ := hcpt U₂ a₂ ho₂ h₂
    have ho₃ : IsOpen ((U₁ ⊓ U₂ : Subgroup G) : Set G) := by
      rw [Subgroup.coe_inf]
      exact ho₁.inter ho₂
    have hc₃ : IsCompact ((U₁ ⊓ U₂ : Subgroup G) : Set G) :=
      IsCompact.of_isClosed_subset hc₁ ((U₁ ⊓ U₂).isClosed_of_isOpen ho₃) fun x hx => hx.1
    let a₃ : SB G := ⟨ind (U₁ ⊓ U₂), ind_mem_SB _ ho₃ hc₃⟩
    have e₁ := cross_le (β f) I U₁ (U₁ ⊓ U₂) inf_le_left hc₁ ho₃ a₁ a₃ h₁ rfl
      (hinv f U₁ hf₁) fun g _ => hI g
    have e₂ := cross_le (β f) I U₂ (U₁ ⊓ U₂) inf_le_right hc₂ ho₃ a₂ a₃ h₂ rfl
      (hinv f U₂ hf₂) fun g _ => hI g
    have h₃ : I a₃ ≠ 0 := hne _ a₃ ho₃ rfl
    apply mul_right_cancel₀ h₃
    linear_combination I a₂ * e₁ - I a₁ * e₂
  choose W hWo hWc hWf _ using fun f : V => hex f f
  let A : V → SB G := fun f => ⟨ind (W f), ind_mem_SB _ (hWo f) (hWc f)⟩
  let Λ₀ : V → ℂ := fun f => β f (A f) / I (A f)
  have key : ∀ f (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → a.1 = ind U →
      (∀ g ∈ U, act g f = f) → β f a = I a * Λ₀ f := by
    intro f U a ho ha hf
    have h := hcross f U (W f) a (A f) ho (hWo f) ha rfl hf (hWf f)
    have hA : I (A f) ≠ 0 := hne _ (A f) (hWo f) rfl
    change β f a = I a * (β f (A f) / I (A f))
    field_simp
    linear_combination h
  have hadd : ∀ f f', Λ₀ (f + f') = Λ₀ f + Λ₀ f' := by
    intro f f'
    obtain ⟨U, ho, hc, h₁, h₂⟩ := hex f f'
    let a : SB G := ⟨ind U, ind_mem_SB _ ho hc⟩
    have hIa : I a ≠ 0 := hne U a ho rfl
    apply mul_left_cancel₀ hIa
    have hf : ∀ g ∈ U, act g (f + f') = f + f' := fun g hg => by
      rw [map_add (f := _), h₁ g hg, h₂ g hg]
    rw [mul_add, ← key f U a ho rfl h₁, ← key f' U a ho rfl h₂, ← key (f + f') U a ho rfl hf,
      map_add, LinearMap.add_apply]
  have hsmul : ∀ (c : ℂ) f, Λ₀ (c • f) = c * Λ₀ f := by
    intro c f
    obtain ⟨U, ho, hc, h₁, -⟩ := hex f f
    let a : SB G := ⟨ind U, ind_mem_SB _ ho hc⟩
    have hIa : I a ≠ 0 := hne U a ho rfl
    apply mul_left_cancel₀ hIa
    have hf : ∀ g ∈ U, act g (c • f) = c • f := fun g hg => by
      rw [map_smul, h₁ g hg]
    rw [mul_left_comm, ← key f U a ho rfl h₁, ← key (c • f) U a ho rfl hf, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
  exact ⟨⟨⟨Λ₀, hadd⟩, fun c f => by simpa using hsmul c f⟩, key⟩

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.I.lamEx :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLv v) V), (∀ f, IsOpen {g | ρ g f = f}) →
      ∀ (I : SB (SL v) →ₗ[ℂ] ℂ), InvI I → ∀ β : V →ₗ[ℂ] SB (SL v) →ₗ[ℂ] ℂ,
      (∀ (g : SL v) f (a a' : SB (SL v)), (∀ m, a'.1 m = a.1 (m * g)) → β (ρ (Matrix.SpecialLinearGroup.toGL g) f) a' = β f a) →
      ∃ Λ : V →ₗ[ℂ] ℂ, ∀ f (U : Subgroup (SL v)) (a : SB (SL v)), IsOpen (U : Set (SL v)) → a.1 = ind U →
        (∀ g ∈ U, ρ (Matrix.SpecialLinearGroup.toGL g) f = f) → β f a = I a * Λ f := by
  intro F _ _ v V _ _ ρ hρ I hI β hβ
  refine core (lgrp F v).1 (fun g => ρ (Matrix.SpecialLinearGroup.toGL g)) (fun f => ?_) I
    hI.right hI.ne β hβ
  have ho : IsOpen {g : SL v | ρ (Matrix.SpecialLinearGroup.toGL g) f = f} :=
    (hρ f).preimage Matrix.SpecialLinearGroup.continuous_toGL
  exact ho.mem_nhds (by simp)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem trace_compactOpen {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {i : Y → X}
    (hi : IsClosedEmbedding i)
    (hb : ∀ x, ∀ N ∈ 𝓝 x, ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ x ∈ O ∧ O ⊆ N)
    {C : Set Y} (hCo : IsOpen C) (hCc : IsCompact C) :
    ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ i ⁻¹' O = C := by
  have hcl : IsClosed (i '' Cᶜ) := hi.isClosedMap _ hCo.isClosed_compl
  have hloc : ∀ y ∈ C, ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ i y ∈ O ∧ O ⊆ (i '' Cᶜ)ᶜ := by
    intro y hy
    refine hb (i y) _ (hcl.isOpen_compl.mem_nhds ?_)
    rintro ⟨y', hy', e⟩
    exact hy' (hi.injective e ▸ hy)
  choose! O hOo hOc hOy hON using hloc
  obtain ⟨t, ht, hcov⟩ := hCc.elim_nhds_subcover (fun y => i ⁻¹' O y)
    (fun y hy => ((hOo y hy).preimage hi.continuous).mem_nhds (hOy y hy))
  refine ⟨⋃ y ∈ t, O y, isOpen_biUnion fun y hy => hOo y (ht y hy),
    t.isCompact_biUnion fun y hy => hOc y (ht y hy), ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨z, hz, hy⟩
    by_contra hc
    exact hON z (ht z hz) hy ⟨y, hc, rfl⟩
  · intro hy
    simpa using hcov hy

private theorem indicator_mem_SB {X : Type} [TopologicalSpace X] [T2Space X] {O : Set X}
    (hO : IsOpen O) (hc : IsCompact O) : O.indicator (fun _ => (1 : ℂ)) ∈ SB X := by
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ O
  · exact ⟨O, hO, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨Oᶜ, hc.isClosed.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

private theorem extend_SB {X Y : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] {i : Y → X}
    (hi : IsClosedEmbedding i)
    (hb : ∀ x, ∀ N ∈ 𝓝 x, ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ x ∈ O ∧ O ⊆ N)
    (a : Y → ℂ) (ha : a ∈ SB Y) : ∃ b ∈ SB X, ∀ y, b (i y) = a y := by
  obtain ⟨hlc, hcs⟩ := ha
  have hK : IsCompact (tsupport a) := hcs
  haveI : CompactSpace (tsupport a) := isCompact_iff_compactSpace.mp hK
  have hfin : (Set.range ((tsupport a).restrict a)).Finite :=
    (hlc.comp_continuous continuous_subtype_val).range_finite
  have hfib : ∀ c : ℂ, c ≠ 0 → ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ i ⁻¹' O = a ⁻¹' {c} := by
    intro c hc
    refine trace_compactOpen hi hb (hlc.isOpen_fiber c) (hK.of_isClosed_subset (hlc.isClosed_fiber c) ?_)
    intro y hy
    refine subset_tsupport _ ?_
    rw [Function.mem_support, show a y = c from hy]
    exact hc
  choose! O hOo hOc hOt using hfib
  let S : Finset ℂ := hfin.toFinset.erase 0
  refine ⟨fun x => ∑ c ∈ S, c * (O c).indicator (fun _ => (1 : ℂ)) x, ?_, ?_⟩
  · have : (fun x => ∑ c ∈ S, c * (O c).indicator (fun _ => (1 : ℂ)) x) =
        ∑ c ∈ S, c • (O c).indicator (fun _ => (1 : ℂ)) := by
      ext x
      simp [Finset.sum_apply]
    rw [this]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
    exact indicator_mem_SB (hOo c hc0) (hOc c hc0)
  · intro y
    have hterm : ∀ c ∈ S, c * (O c).indicator (fun _ => (1 : ℂ)) (i y) = if c = a y then c else 0 := by
      intro c hc
      have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
      have hm : i y ∈ O c ↔ a y = c := by
        have := Set.ext_iff.mp (hOt c hc0) y
        simpa using this
      by_cases h : c = a y
      · rw [Set.indicator_of_mem (hm.mpr h.symm), if_pos h, mul_one]
      · have : i y ∉ O c := fun h' => h (hm.mp h').symm
        rw [Set.indicator_of_notMem this, if_neg h, mul_zero]
    change ∑ c ∈ S, c * (O c).indicator (fun _ => (1 : ℂ)) (i y) = a y
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S (a y) (fun c => c)]
    split_ifs with h
    · rfl
    · have h0 : a y = 0 := by
        by_contra hne
        exact h (Finset.mem_erase.mpr ⟨hne, hfin.mem_toFinset.mpr ⟨⟨y, subset_tsupport _ hne⟩, rfl⟩⟩)
      exact h0.symm

private theorem closedEmbedding_val (F : Type) [Field F] [NumberField F] (v : P F) :
    IsClosedEmbedding (Subtype.val : SL v → M2 v) := by
  have h : IsClosed {m : M2 v | m.det = 1} :=
    isClosed_singleton.preimage (show Continuous (fun m : M2 v => m.det) from continuous_id.matrix_det)
  exact h.isClosedEmbedding_subtypeVal

private theorem compactOpen_basis (F : Type) [Field F] [NumberField F] (v : P F) (x : M2 v) (N : Set (M2 v))
    (hN : N ∈ 𝓝 x) : ∃ O : Set (M2 v), IsOpen O ∧ IsCompact O ∧ x ∈ O ∧ O ⊆ N := by
  have h0 : (fun y : M2 v => x + y) ⁻¹' N ∈ 𝓝 (0 : M2 v) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hN)
  obtain ⟨U, hUo, hUc, hUN⟩ := (UpperTheory.ConvolutionTheory.R2.I.lgrp F v).2
    ((fun y : Multiplicative (M2 v) => Multiplicative.toAdd y) ⁻¹' ((fun y : M2 v => x + y) ⁻¹' N))
    (by
      have : Tendsto (fun y : Multiplicative (M2 v) => Multiplicative.toAdd y) (𝓝 1) (𝓝 (0 : M2 v)) :=
        continuous_toAdd.tendsto _
      exact this h0)
  let e : Multiplicative (M2 v) → M2 v := fun y => x + Multiplicative.toAdd y
  have he : IsOpenEmbedding e := (Homeomorph.addLeft x).isOpenEmbedding
  refine ⟨e '' U, he.isOpenMap _ hUo, hUc.image he.continuous, ⟨1, U.one_mem, by simp [e]⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hUN hy

theorem UpperTheory.ConvolutionTheory.R2.I.ext :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (a : SB (SL v)), ∃ b : SB (M2 v), ∀ m : SL v, b.1 m.1 = a.1 m := by
  intro F _ _ v a
  obtain ⟨b, hb, h⟩ := extend_SB (closedEmbedding_val F v) (compactOpen_basis F v) a.1 a.2
  exact ⟨⟨b, hb⟩, h⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] {v : P F}

private noncomputable def Jm (c : Fin 2 → Kv v) : Fin 2 → Kv v := ![-c 1, c 0]

private lemma Jm_Jm (c : Fin 2 → Kv v) : Jm (Jm c) = -c := by
  funext i; fin_cases i <;> simp [Jm]

private lemma Jm_measurable : Measurable (Jm (v := v)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i
  · have h : Measurable fun c : Fin 2 → Kv v => -c 1 := measurable_neg.comp (measurable_pi_apply (1 : Fin 2))
    simpa [Jm] using h
  · simpa [Jm] using measurable_pi_apply (0 : Fin 2)

private noncomputable def JmE : (Fin 2 → Kv v) ≃ᵐ (Fin 2 → Kv v) where
  toFun := Jm
  invFun := fun c => -Jm c
  left_inv := fun c => by
    show -Jm (Jm c) = c
    rw [Jm_Jm, neg_neg]
  right_inv := fun c => by
    show Jm (-Jm c) = c
    funext i; fin_cases i <;> simp [Jm]
  measurable_toFun := Jm_measurable
  measurable_invFun := measurable_neg.comp Jm_measurable

private lemma Jm_mp : MeasurePreserving (Jm (v := v)) (μ2 v) (μ2 v) := by
  have hs := measurePreserving_piCongrLeft (α := fun _ : Fin 2 => Kv v)
    (fun _ => GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v)) (Equiv.swap (0 : Fin 2) 1)
  have hn := measurePreserving_pi (fun _ : Fin 2 => GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v))
    (fun _ : Fin 2 => GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v))
    (f := fun (i : Fin 2) (x : Kv v) => if i = 0 then -x else x) (by
      intro i
      fin_cases i
      · simpa using Measure.measurePreserving_neg _
      · convert MeasurePreserving.id (GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v)) using 1
        funext x
        simp)
  have h := hn.comp hs
  have hf : Jm (v := v) = (fun (a : Fin 2 → Kv v) (i : Fin 2) => if i = 0 then -a i else a i) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => Kv v) (Equiv.swap (0 : Fin 2) 1)) := by
    funext c i
    fin_cases i <;> simp [Jm, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  rw [hf]
  exact h

private lemma cols_col (c c' : Fin 2 → Kv v) : (fun i => cols c c' i 1) = c' := by
  funext i; fin_cases i <;> simp [cols]

private lemma sw_cols (p q : Fin 2 → Kv v) : sw (cols p q) = cols q p := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sw, cols]

private lemma sw_sw (m : M2 v) : sw (sw m) = m := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sw]

private lemma eq_cols (m : M2 v) : m = cols (fun i => m i 0) (fun i => m i 1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cols]

private lemma sw_continuous : Continuous (sw (v := v)) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [sw] <;> fun_prop

private noncomputable def swH : M2 v ≃ₜ M2 v where
  toFun := sw
  invFun := sw
  left_inv := sw_sw
  right_inv := sw_sw
  continuous_toFun := sw_continuous
  continuous_invFun := sw_continuous

private lemma comp_sw_mem {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) : (fun X => a (sw X)) ∈ SB (M2 v) :=
  ⟨ha.1.comp_continuous sw_continuous, ha.2.comp_homeomorph swH⟩

private lemma slice_mem {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) (c : Fin 2 → Kv v) :
    (fun c' => a (cols c c')) ∈ localSchwartzBruhatPi (Kv v) (ι := Fin 2) := by
  have hc : Continuous fun c' : Fin 2 → Kv v => cols c c' := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [cols] <;> fun_prop
  have hr : Continuous fun X : M2 v => (fun i => X i 1 : Fin 2 → Kv v) := by
    refine continuous_pi fun i => ?_
    exact (continuous_id.matrix_elem i 1)
  have he : IsClosedEmbedding fun c' : Fin 2 → Kv v => cols c c' :=
    Function.LeftInverse.isClosedEmbedding (f := fun X : M2 v => (fun i => X i 1 : Fin 2 → Kv v))
      (fun c' => cols_col c c') hr hc
  exact ⟨ha.1.comp_continuous hc, ha.2.comp_isClosedEmbedding he⟩

private lemma Pt_cols (a : M2 v → ℂ) (c₁ c : Fin 2 → Kv v) :
    Pt a (cols c₁ c) = localFourierPi (localAdelicChar F v) (fun c' => a (cols c c')) (Jm c₁) := by
  simp only [Pt, localFourierPi, cols_col]
  unfold μ2
  refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
  have h : c₁ 0 * c' 1 - c₁ 1 * c' 0 = ∑ i, c' i * Jm c₁ i := by
    simp [Jm, Fin.sum_univ_two]; ring
  simp only [ψl]
  rw [← h]
  simp [cols]

private lemma fourier_rot (G : (Fin 2 → Kv v) → ℂ) (q : Fin 2 → Kv v) :
    localFourierPi (localAdelicChar F v) (fun c => G (Jm c)) (Jm q) =
      localFourierPi (localAdelicChar F v) G (-q) := by
  have h := (Jm_mp (v := v)).integral_comp (JmE (v := v)).measurableEmbedding
    (fun y => G y * ((localAdelicChar F v (∑ i, y i * (-q) i) : Circle) : ℂ))
  change ∫ x, G (Jm x) * ((localAdelicChar F v (∑ i, x i * Jm q i) : Circle) : ℂ) ∂(μ2 v) =
    ∫ y, G y * ((localAdelicChar F v (∑ i, y i * (-q) i) : Circle) : ℂ) ∂(μ2 v)
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  have : ∑ i, c i * Jm q i = ∑ i, Jm c i * (-q) i := by
    simp [Jm, Fin.sum_univ_two]
  simp only [this]

private lemma part1 {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) (p q : Fin 2 → Kv v) :
    Pt (fun X => Pt a (sw X)) (cols q p) = a (cols p q) := by
  have hc := continuous_localAdelicChar (K := F) v
  have hn : localAdelicChar F v ≠ 1 := localAdelicChar_ne_one v
  have hb := slice_mem ha p
  have hG := localFourierPi_mem hc hn hb
  rw [Pt_cols]
  have h1 : (fun c' => Pt a (sw (cols p c'))) =
      fun c' => localFourierPi (localAdelicChar F v) (fun c'' => a (cols p c'')) (Jm c') := by
    funext c'
    rw [sw_cols, Pt_cols]
  rw [h1, fourier_rot, localFourierPi_localFourierPi hc hn hb]
  simp

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.I.ptInv :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), ∀ a ∈ SB (M2 v), (∀ m, Pt (fun X => Pt a (sw X)) (sw m) = a m) ∧ ∃ a' ∈ SB (M2 v), Pt a' = a := by
  intro F _ _ v a ha
  have h1 : ∀ b ∈ SB (M2 v), ∀ m, Pt (fun X => Pt b (sw X)) (sw m) = b m := by
    intro b hb m
    rw [eq_cols m, sw_cols]
    exact part1 hb _ _
  refine ⟨h1 a ha, ?_⟩
  obtain ⟨T, hT⟩ := UpperTheory.ConvolutionTheory.R2.I.ptMem F v
  have hb := comp_sw_mem ha
  have hTb : Pt (fun X => a (sw X)) ∈ SB (M2 v) := by
    have := (T ⟨_, hb⟩).2
    rwa [hT] at this
  refine ⟨fun X => Pt (fun Y => a (sw Y)) (sw X), comp_sw_mem hTb, ?_⟩
  funext m
  have := h1 _ hb (sw m)
  rw [sw_sw] at this
  simpa [sw_sw] using this
end
