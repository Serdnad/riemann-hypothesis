module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumEqConstMulPetersson
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle388
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle650
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle399
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle056
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle346
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCBase
import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNd
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeNormal

open GlobalTheory.HeckeStdFacts GlobalTheory.CoefDuty

theorem eq_smul_of_normal {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (V : Submodule ℂ M)
    (T S : M →ₗ[ℂ] M) (hpos : ∀ x ∈ V, B x x = 0 → x = 0)
    (hT : ∀ x ∈ V, T x ∈ V) (hS : ∀ x ∈ V, S x ∈ V) (hadj : ∀ x ∈ V, ∀ y ∈ V, B (T x) y = B x (S y))
    (hc : ∀ x ∈ V, T (S x) = S (T x)) {f : M} (hf : f ∈ V) (μ : ℂ)
    (h : T (T f - μ • f) = μ • (T f - μ • f)) : T f = μ • f := by
  have hg : T f - μ • f ∈ V := V.sub_mem (hT f hf) (V.smul_mem μ hf)
  have adj : ∀ x ∈ V, ∀ y ∈ V, B (T x - μ • x) y = B x (S y - starRingEnd ℂ μ • y) := by
    intro x hx y hy
    rw [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, hadj x hx y hy]
  have hfg := adj f hf _ hg
  rw [← sub_eq_zero]
  generalize T f - μ • f = g at hg h hfg ⊢
  have hu : S g - starRingEnd ℂ μ • g ∈ V := V.sub_mem (hS g hg) (V.smul_mem _ hg)
  have h0 : T (S g - starRingEnd ℂ μ • g) - μ • (S g - starRingEnd ℂ μ • g) = 0 := by
    rw [map_sub, map_smul, hc g hg, h, map_smul, smul_sub, smul_comm μ (starRingEnd ℂ μ) g, sub_self]
  have h1 := adj _ hu g hg
  rw [h0, map_zero, LinearMap.zero_apply] at h1
  rw [hpos _ hu h1.symm, map_zero] at hfg
  exact hpos g hg hfg

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem rt_mem_all {a : NG.AlgWt L n} (h : GAf L n) {f : GAf L n → a.W} (hf : f ∈ NG.AFall L n a.ρ) :
    NG.rt L n h f ∈ NG.AFall L n a.ρ := by
  obtain ⟨N, hN, h2⟩ := hf.2
  obtain ⟨⟨N', hN', hc⟩, -, -⟩ :=
    GlobalTheory.CongIndex.finite_index_conj L n (Umax L n) GlobalTheory.ClassPet.umax_bounded h N hN
  exact (GlobalTheory.ClassPet.rt_mem a hf hN' h2 hc).1

def sph (a : NG.AlgWt L n) (v : HeightOneSpectrum (𝓞 L⁺)) : Submodule ℂ (GAf L n → a.W) where
  carrier := {f | f ∈ NG.AFall L n a.ρ ∧ ∀ κ ∈ locK n v, NG.rt L n κ f = f}
  zero_mem' := ⟨zero_mem _, fun _ _ => map_zero _⟩
  add_mem' := fun hf hg => ⟨add_mem hf.1 hg.1, fun κ hκ => by rw [map_add (f := _), hf.2 κ hκ, hg.2 κ hκ]⟩
  smul_mem' := fun c f hf => ⟨Submodule.smul_mem _ c hf.1, fun κ hκ => by rw [map_smul, hf.2 κ hκ]⟩

def IsReps (v : HeightOneSpectrum (𝓞 L⁺)) (α : GAf L n) (R : Finset (GAf L n)) : Prop :=
  (∀ γ ∈ R, ∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, γ = k₁ * α * k₂) ∧
    ∀ x, (∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n

theorem IsReps.card_ne_zero {v : HeightOneSpectrum (𝓞 L⁺)} {α : GAf L n} {R : Finset (GAf L n)} (h : IsReps v α R) :
    (R.card : ℂ) ≠ 0 := by
  obtain ⟨γ, ⟨hγ, -⟩, -⟩ := h.2 α ⟨1, one_mem _, 1, one_mem _, by simp⟩
  exact_mod_cast Finset.card_ne_zero_of_mem hγ

theorem sum_mem_sph {a : NG.AlgWt L n} {v : HeightOneSpectrum (𝓞 L⁺)} {α : GAf L n} (hα : TrivOutside {v} α)
    {R : Finset (GAf L n)} (h : IsReps v α R) {f : GAf L n → a.W} (hf : f ∈ sph a v) :
    ∑ γ ∈ R, NG.rt L n γ f ∈ sph a v := by
  classical
  refine ⟨sum_mem fun γ _ => rt_mem_all γ hf.1, fun κ hκ => ?_⟩
  have hD : ∀ x ∈ {x : GAf L n | ∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, x = k₁ * α * k₂}, TrivOutside {v} x := by
    rintro _ ⟨k₁, h₁, k₂, h₂, rfl⟩
    exact triv_mul (triv_mul h₁.2 hα) h₂.2
  have hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f := fun κ h1 h2 => hf.2 κ ⟨h1, h2⟩
  have e1 := heckeD_eq_sum (J := Umax L n) hD h.1 h.2 hfix
  have e2 := heckeD_eq_sum (J := Umax L n) hD (R := R.image fun γ => κ * γ)
    (by
      intro γ hγ
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
      obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h.1 δ hδ
      exact ⟨κ * k₁, mul_mem hκ h₁, k₂, h₂, by simp only [mul_assoc]⟩)
    (by
      rintro _ ⟨k₁, h₁, k₂, h₂, rfl⟩
      obtain ⟨γ, ⟨hγ, hm⟩, hu⟩ := h.2 (κ⁻¹ * k₁ * α * k₂) ⟨κ⁻¹ * k₁, mul_mem (inv_mem hκ) h₁, k₂, h₂, rfl⟩
      refine ⟨κ * γ, ⟨Finset.mem_image.2 ⟨γ, hγ, rfl⟩, ?_⟩, ?_⟩
      · convert hm using 1
        group
      · rintro _ ⟨hδ, hm'⟩
        obtain ⟨δ, hδ', rfl⟩ := Finset.mem_image.1 hδ
        rw [hu δ ⟨hδ', ?_⟩]
        convert hm' using 1
        group) hfix
  rw [Finset.sum_image (mul_right_injective κ).injOn, e1] at e2
  conv_rhs => rw [e2]

  simp only [map_sum, rt_rt]

theorem form_sum {a : NG.AlgWt L n} {B : (GAf L n → a.W) →ₗ⋆[ℂ] (GAf L n → a.W) →ₗ[ℂ] ℂ} (hB : IsPetersson a B)
    {v : HeightOneSpectrum (𝓞 L⁺)} {α : GAf L n} {R : Finset (GAf L n)} (h : IsReps v α R)
    {f g : GAf L n → a.W} (hf : f ∈ sph a v) (hg : g ∈ sph a v) :
    B f (∑ γ ∈ R, NG.rt L n γ g) = R.card * B f (NG.rt L n α g) := by

  rw [map_sum, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h.1 γ hγ
  rw [← rt_rt, hg.2 k₂ h₂, ← rt_rt]
  conv_lhs => rw [← hf.2 k₁ h₁]
  exact (hB f hf.1 _ (rt_mem_all α hg.1)).2.2 k₁

theorem form_sum_left {a : NG.AlgWt L n} {B : (GAf L n → a.W) →ₗ⋆[ℂ] (GAf L n → a.W) →ₗ[ℂ] ℂ} (hB : IsPetersson a B)
    {v : HeightOneSpectrum (𝓞 L⁺)} {α : GAf L n} {R : Finset (GAf L n)} (h : IsReps v α R)
    {f g : GAf L n → a.W} (hf : f ∈ sph a v) (hg : g ∈ sph a v) :
    B (∑ γ ∈ R, NG.rt L n γ f) g = R.card * B f (NG.rt L n α⁻¹ g) := by

  rw [map_sum, LinearMap.sum_apply, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h.1 γ hγ
  have e : g = NG.rt L n (k₁ * α) (NG.rt L n α⁻¹ g) := by
    rw [rt_rt, mul_inv_cancel_right, hg.2 k₁ h₁]
  rw [← rt_rt, hf.2 k₂ h₂]
  conv_lhs => rw [e]
  exact (hB f hf.1 _ (rt_mem_all α⁻¹ hg.1)).2.2 _

theorem sum_semisimple (a : NG.AlgWt L n) (s : SplitPlace L) {α : GAf L n} (hα : TrivOutside {s.v} α)
    {R : Finset (GAf L n)} (h : IsReps s.v α R) (c : ℂ) {f : GAf L n → a.W} (hf : f ∈ sph a s.v) (μ : ℂ)
    (hμ : c • ∑ γ ∈ R, NG.rt L n γ (c • ∑ γ ∈ R, NG.rt L n γ f - μ • f) = μ • (c • ∑ γ ∈ R, NG.rt L n γ f - μ • f)) :
    c • ∑ γ ∈ R, NG.rt L n γ f = μ • f := by
  obtain ⟨β, hβ⟩ := GlobalTheory.InvFormBdd.exists_isInvForm L n a
  obtain ⟨B, hB, -⟩ := GlobalTheory.ClassPet.classSum_eq_pet L n a β hβ
  obtain ⟨R', h'⟩ : ∃ R', IsReps s.v α⁻¹ R' := exists_repsU s.v α⁻¹
  have key := eq_smul_of_normal B (sph a s.v) (c • ∑ γ ∈ R, NG.rt L n γ)
    ((starRingEnd ℂ c * R.card / R'.card) • ∑ γ ∈ R', NG.rt L n γ)
    (fun x hx h0 => by
      by_contra hne
      have := (hB x hx.1 x hx.1).2.1 hne
      rw [h0] at this
      simp at this)
    (fun x hx => by
      rw [LinearMap.smul_apply, LinearMap.sum_apply]
      exact Submodule.smul_mem _ _ (sum_mem_sph hα h hx))
    (fun x hx => by
      rw [LinearMap.smul_apply, LinearMap.sum_apply]
      exact Submodule.smul_mem _ _ (sum_mem_sph (triv_inv hα) h' hx))
    (fun x hx y hy => by
      rw [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sum_apply, map_smulₛₗ,
        LinearMap.smul_apply, map_smul, form_sum_left hB h hx hy, form_sum hB h' hx hy, smul_eq_mul, smul_eq_mul]
      have := h'.card_ne_zero
      field_simp)
    (fun x hx => by
      have conv : ∀ (δ x : GAf L n), (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧
          x = k₁ * δ * k₂) ↔ ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * δ * k₂ := fun δ x =>
        ⟨fun ⟨k₁, h₁, k₂, h₂, t₁, t₂, e⟩ => ⟨k₁, ⟨h₁, t₁⟩, k₂, ⟨h₂, t₂⟩, e⟩,
          fun ⟨k₁, h₁, k₂, h₂, e⟩ => ⟨k₁, h₁.1, k₂, h₂.1, h₁.2, h₂.2, e⟩⟩
      have e := GlobalTheory.SplitHeckeComm.doubleCoset_comm L n a.W s α α⁻¹ R R' hα (triv_inv hα)
        (fun y hy => h.2 y ((conv _ _).1 hy)) (fun y hy => (conv _ _).2 (h.1 y hy))
        (fun y hy => h'.2 y ((conv _ _).1 hy)) (fun y hy => (conv _ _).2 (h'.1 y hy)) x
        (fun κ h1 h2 => hx.2 κ ⟨h1, h2⟩)
      rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul,
        smul_comm]
      simp only [LinearMap.sum_apply]
      rw [e]) hf μ
  simp only [LinearMap.smul_apply, LinearMap.sum_apply] at key
  exact key hμ

theorem tN_semisimple : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → NG.HypOutside J χ B → ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), s.v ∉ B → IsUnif L s.v ϖ → 1 ≤ k → k ≤ n → ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ μ : ℂ, NG.tN J s ϖ k (NG.tN J s ϖ k f - μ • f) = μ • (NG.tN J s ϖ k f - μ • f) → NG.tN J s ϖ k f = μ • f := by
  intro L _ _ _ n a J χ B hN hB s ϖ k hv hϖ _ _ f hf μ hμ
  obtain ⟨α, hα, hset⟩ := exists_tSet_eq (n := n) s ϖ k hϖ
  obtain ⟨R, h⟩ : ∃ R, IsReps s.v α R := exists_repsU s.v α
  have hT : ∀ g ∈ NG.TypeSp a.ρ J χ, NG.tN J s ϖ k g = ((s.q : ℂ) ^ (k * (n - 1)))⁻¹ • ∑ γ ∈ R, NG.rt L n γ g := by
    intro g hg
    unfold NG.tN
    rw [heckeD_type hB hv (fun γ hγ => (hset γ).2 (h.1 γ hγ)) (fun x hx => h.2 x ((hset x).1 hx)) hg]
  have hg : NG.tN J s ϖ k f - μ • f ∈ NG.TypeSp a.ρ J χ :=
    sub_mem (Submodule.smul_mem _ _ (heckeD_mem hN hB hv hϖ k hf)) (Submodule.smul_mem _ _ hf)
  rw [hT _ hg, hT f hf] at hμ
  rw [hT f hf]
  exact sum_semisimple a s hα h _
    ⟨hf.1, fun κ hκ => fixed_of_type hB hv hf κ ((hyp_at hB hv κ hκ.2).1.2 hκ.1) hκ.2⟩ μ hμ

end GlobalTheory.HeckeNormal
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt

open scoped TensorProduct

theorem reGL_rfl (n : ℕ) (R : Type) [CommRing R] (g : GL (Fin n) R) : Formalism.L2.Forms.reGL (rfl : n = n) R g = g := by
  ext a b
  simp [Formalism.L2.Forms.reGL]

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem adStep_re {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E)
    (U : Subgroup (GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) (y y' : GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (γ : GL (Fin a) E) (w : HeightOneSpectrum (𝓞 F)) (J' : Matrix (Fin b) (Fin b) E)
    (U' : Subgroup (GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) (z z' : GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (δ : GL (Fin b) E) (hJ : J' = J.reindex (finCongr h) (finCongr h)) (hU : U' = U.map (Formalism.L2.Forms.reGL h _).toMonoidHom)
    (hz : z = Formalism.L2.Forms.reGL h _ y) (hz' : z' = Formalism.L2.Forms.reGL h _ y') (hδ : δ = Formalism.L2.Forms.reGL h _ γ)
    (H : Formalism.L2.Herm.AdStep σ J' U' z z' δ w) : Formalism.L2.Herm.AdStep σ J U y y' γ w := by
  subst h hJ hU hz hz' hδ
  have hm : U.map (Formalism.L2.Forms.reGL (rfl : a = a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).toMonoidHom = U := by
    ext g
    simp [reGL_rfl]
  rw [hm, reGL_rfl, reGL_rfl, reGL_rfl] at H
  simpa using H

end

theorem toGLb_reindex {E V : Type} [Field E] [AddCommGroup V] [Module E V] {n k : ℕ} (b : Module.Basis (Fin n) E V)
    (h : n = k) (f : V ≃ₗ[E] V) :
    Formalism.L2.Herm.toGLb (b.reindex (finCongr h)) f = Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b f) := by
  subst h
  rw [reGL_rfl]
  ext a c
  simp [Formalism.L2.Herm.toGLb]

theorem reGL_trans {a b c : ℕ} (h1 : a = b) (h2 : b = c) (R : Type) [CommRing R] (g : GL (Fin a) R) :
    Formalism.L2.Forms.reGL h2 R (Formalism.L2.Forms.reGL h1 R g) = Formalism.L2.Forms.reGL (h1.trans h2) R g := by
  subst h1 h2
  rw [reGL_rfl, reGL_rfl]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen
variable {D : D7}

theorem ad0 (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) (hcar : CarH H F) (u : D.what₂.Word)
    (hi : 0 ≤ D.R.m) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 hi))
    (hA : AdC (F u) 0 hi c c' γ.1 ((F u).atT.eV v).1) : AdOf H u 0 c c' (gx 0 hi γ) v := by
  have h0 := hA.1 (Or.inl rfl)
  have hc := hcar.car0 u
  rw [hcar.eV u] at h0
  show Formalism.L2.Herm.Ad0S D H u c c' (gx 0 hi γ) v
  unfold Formalism.L2.Herm.Ad0S
  refine adStep_re (rank_eq_first_level D.R) _ _ _ _ _ _ _ _ _ _ _ _ ?_ hc.U_eq (hc.y_eq c) (hc.y_eq c') ?_ h0
  · ext a b
    simp [gramN, Formalism.BasicNotions.Spaces.gram0]
  · rw [toGLb_reindex, reGL_trans]
    exact (reGL_lin (D.sp.X 0) (rankN D 0 hi) γ.1).symm

theorem adC (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) (hcar : CarH H F) (u : D.what₂.Word)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hA : AdC (F u) i hi c c' γ.1 ((F u).atT.eV v).1) : Formalism.L2.Herm.AdIS D H u i h1 hi c c' (gx i hi γ) v := by
  obtain ⟨hβ, h0⟩ := hA.2 h1 h2
  have hc := hcar.carC u i h1 h2 (H.chOf u i c)
  rw [hcar.eV u] at h0
  refine ⟨hβ, ?_⟩
  refine adStep_re (rankN D i hi) _ _ _ _ _ _ _ _ _ _ _ _ rfl hc.U_eq (hc.y_eq _) (hc.y_eq _) ?_ h0
  exact (reGL_lin (D.sp.X i) (rankN D i hi) γ.1).symm

theorem adM (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) (hcar : CarH H F) (u : D.what₂.Word)
    (i : ℕ) (h1 : 1 ≤ i) (hm : i = D.R.m) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hA : AdC (F u) i hi c c' γ.1 ((F u).atT.eV v).1) : Formalism.L2.Herm.AdIS D H u i h1 hi c c' (gx i hi γ) v := by
  subst hm
  have h0 := hA.1 (Or.inr rfl)
  have hc := hcar.carM u
  rw [hcar.eV u] at h0
  have hβ : H.chOf u D.R.m c' = H.chOf u D.R.m c := (chOf_m H u c').trans (chOf_m H u c).symm
  refine ⟨hβ, ?_⟩
  have key : ∀ (β : H.Ch u D.R.m) (e : β = chM H u) (hb : H.chOf u D.R.m c = β) (hb' : H.chOf u D.R.m c' = β),
      Formalism.L2.Herm.AdStep D.sp.cm.sig (D.sp.X D.R.m).gram (H.lev u D.R.m h1 hi β).U
        ((H.cls u D.R.m h1 hi β).y ⟨c, hb⟩) ((H.cls u D.R.m h1 hi β).y ⟨c', hb'⟩)
        (Formalism.L2.Herm.toGLb (D.sp.X D.R.m).frame (gx D.R.m hi γ).1) (H.vT u v).1 := by
    intro β e hb hb'
    subst e
    refine adStep_re (rankN D D.R.m hi) _ _ _ _ _ _ _ _ _ _ _ _ rfl hc.U_eq (hc.y_eq c) (hc.y_eq c') ?_ h0
    exact (reGL_lin (D.sp.X D.R.m) (rankN D D.R.m hi) γ.1).symm
  exact key _ (chOf_m H u c) rfl hβ

theorem adOf_of_adC_gen (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) (hcar : CarH H F)
    (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hA : AdC (F u) i hi c c' γ.1 ((F u).atT.eV v).1) : AdOf H u i c c' (gx i hi γ) v := by
  cases i with
  | zero => exact ad0 H F hcar u hi v c c' γ hA
  | succ i =>
    intro hm
    rcases Nat.lt_or_eq_of_le hi with h | h
    · exact adC H F hcar u (i + 1) (Nat.succ_pos i) h hi v c c' γ hA
    · exact adM H F hcar u (i + 1) (Nat.succ_pos i) h hi v c c' γ hA

end Gen

theorem adOf_of_adC : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v (c c' : ((I.rec7 l Z).mem u).C.cls i) (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)), AdC (F u) i hi c c' γ.1 ((F u).atT.eV v).1 → AdOf H u i c c' (gx i hi γ) v := by
  intro B X I _ _ l Z H F _ hcar u i hi v c c' γ hA
  exact adOf_of_adC_gen H F hcar u i hi v c c' γ hA

end GlobalTheory.Mem.Col2.HAt
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.TopIntegrand

def extId {R : Type} [CommRing R] {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) (P : Matrix (Fin n) (Fin m) R)
    (x : Matrix (Fin n) (Fin n) R) : Matrix (Fin m) (Fin m) R := 1 + M * (x - 1) * P

theorem map_emb {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m n : ℕ} (M : Matrix (Fin m) (Fin n) R)
    (P : Matrix (Fin n) (Fin m) R) (x : Matrix (Fin n) (Fin n) R) :
    (extId M P x).map f = extId (M.map f) (P.map f) (x.map f) := by
  rw [extId, extId, Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub f),
    Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_one _ (map_zero f) (map_one f)]

theorem sum_norm_emb {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (P : Matrix (Fin n) (Fin m) ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Matrix (Fin n) (Fin n) ℂ,
      ∑ i, ∑ j, ‖extId M P x i j‖ ≤ c * (1 + ∑ k, ∑ l, ‖x k l‖) := by
  refine ⟨∑ i, ∑ j, (‖(1 - M * P : Matrix (Fin m) (Fin m) ℂ) i j‖ + ∑ l, ∑ k, ‖M i k‖ * ‖P l j‖), by positivity, fun x => ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have e : extId M P x = (1 - M * P) + M * x * P := by
    rw [extId, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]; abel
  have hS : 0 ≤ ∑ k, ∑ l, ‖x k l‖ := by positivity
  have hx : ∀ k l, ‖x k l‖ ≤ 1 + ∑ k, ∑ l, ‖x k l‖ := fun k l =>
    ((Finset.single_le_sum (f := fun l => ‖x k l‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun k => ∑ l, ‖x k l‖) (fun _ _ => by positivity) (Finset.mem_univ k))).trans
      (by linarith)
  rw [e, Matrix.add_apply, add_mul]
  refine (norm_add_le _ _).trans (add_le_add (le_mul_of_one_le_right (norm_nonneg _) (by linarith)) ?_)
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_mul, mul_right_comm]
  exact mul_le_mul_of_nonneg_left (hx k l) (by positivity)

variable {D : D7} {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (hι : HSpace.IsIsomEmb B A ι)

abbrev emb : GA D B →* GA D A := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embA D.sp.cm B A ι hι

theorem matHom_emb (h : GA D B) : (matHom A (emb hι h)).1 =
    extId ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat B A ι).map (incA D)) ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projMat D.sp.cm B A ι).map (incA D))
      (matHom B h).1 := rfl

theorem emb_ker {S : Type} [CommRing S] (f : AF D.host.F ⊗[D.host.F] D.host.E →+* S) (h : GA D B)
    (hh : Formalism.UG.bc f (matHom B h) = 1) : Formalism.UG.bc f (matHom A (emb hι h)) = 1 := by
  have h1 : (matHom B h).1.map f = 1 := congrArg Units.val hh
  refine Units.ext ?_
  change (matHom A (emb hι h)).1.map f = 1
  rw [matHom_emb, map_emb, h1, extId, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem emb_GfC {h : GA D B} (hh : h ∈ GfC B) : emb hι h ∈ GfC A := emb_ker hι _ h hh

theorem emb_GinfC {h : GA D B} (hh : h ∈ GinfC B) : emb hι h ∈ GinfC A := emb_ker hι _ h hh

theorem infMat_emb (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) : ∃ M P, ∀ h : GA D B,
    infMat D.sp.cm.sig A.gram θ (emb hι h) = extId M P (infMat D.sp.cm.sig B.gram θ h) := by
  refine ⟨?_, ?_, fun h => ?_⟩
  rotate_left 2
  change ((matHom A (emb hι h)).1.map
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom).map θ = _
  rw [matHom_emb, map_emb, map_emb]
  rfl

theorem normInf_emb (θ : InfF D) : ∃ c : ℝ, 0 ≤ c ∧ ∀ h : GA D B,
    normInf θ A (emb hι h) ≤ c * (1 + normInf θ B h) := by
  choose M P hMP using fun τ => infMat_emb hι (θ τ)
  choose c hc0 hc using fun τ => sum_norm_emb (M τ) (P τ)
  refine ⟨∑ τ, 2 * c τ, Finset.sum_nonneg fun τ _ => by have := hc0 τ; positivity, fun h => ?_⟩
  rw [Finset.sum_mul, normInf]
  refine Finset.sum_le_sum fun τ _ => ?_
  have h0 : ∑ i, ∑ j, (‖infMat D.sp.cm.sig B.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig B.gram (θ τ) h⁻¹ i j‖) ≤
      normInf θ B h := Finset.single_le_sum (f := fun τ => ∑ i, ∑ j,
        (‖infMat D.sp.cm.sig B.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig B.gram (θ τ) h⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ)
  simp only [Finset.sum_add_distrib] at h0 ⊢
  rw [← map_inv, hMP, hMP]
  have h1 := hc τ (infMat D.sp.cm.sig B.gram (θ τ) h)
  have h2 := hc τ (infMat D.sp.cm.sig B.gram (θ τ) h⁻¹)
  have h3 := mul_le_mul_of_nonneg_left h0 (hc0 τ)
  have h4 := mul_nonneg (hc0 τ) (GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) h)
  nlinarith

theorem emb_moderate {θ : InfF D} (hθ : IsInfFam θ) (hc : Continuous (emb hι)) (hQ : ∀ γ ∈ GQ B, emb hι γ ∈ GQ A)
    {φ : GA D A → ℂ} (hφ : IsAutFunSm θ A φ) :
    ∃ (N : ℕ) (C : ℝ), ∀ g, ‖φ (emb hι g)‖ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ B g : ℝ) ^ N := by
  obtain ⟨U, hU, hUφ⟩ := hφ.level
  obtain ⟨S, C₀, M, hS⟩ := GlobalTheory.SmoothForms.reduction hθ ((GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ B) (U.comap (emb hι)) (hU.preimage hc)
  obtain ⟨N, hN⟩ := hφ.growth
  choose C hC using hN [] (by simp)
  obtain ⟨c, hc0, hc⟩ := normInf_emb hι θ
  refine ⟨M * N, (∑ x ∈ S, |C (emb hι x)|) * (c * (1 + |C₀|)) ^ N, fun g => ?_⟩
  obtain ⟨γ, hγ, x, hx, a, ha, k, hk, hk', e, hb⟩ := hS g
  rw [← hφ.left _ (hQ γ hγ), ← map_mul, e, map_mul, map_mul, hUφ _ hk (emb_GfC hι hk'), pow_mul, mul_assoc, ← mul_pow]
  have h1 : (1 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ B g : ℝ) ^ M :=
    one_le_pow₀ (by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ B g)
  have h2 : normInf θ A (emb hι a) ≤ c * (1 + |C₀|) * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ B g : ℝ) ^ M := by
    refine (hc a).trans ?_
    rw [mul_assoc, add_mul, one_mul]
    exact mul_le_mul_of_nonneg_left (add_le_add h1 (hb.trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (zero_le_one.trans h1)))) hc0
  exact (hC _ _ (emb_GinfC hι ha)).trans (mul_le_mul ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun x => |C (emb hι x)|) (fun _ _ => abs_nonneg _) hx))
    (pow_le_pow_left₀ (GlobalTheory.SmoothForms.normInf_nonneg _) h2 N) (pow_nonneg (GlobalTheory.SmoothForms.normInf_nonneg _) N)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _))

theorem topInt (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) : TopInt D := by
  intro θ hθ A B ι hι μ 𝓕 hq s hs φ φ' hφ hφ'
  obtain rfl : s = emb hι := funext fun h => (GlobalTheory.AutFunCompare.embRel_iff A B ι hι _ _).1 (hs h)
  obtain ⟨s, hc, hrel, hQ⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D A B ι hι
  have e : ∀ h, emb hι h = s h := fun h => (hrel h _).1 (hs h)
  have hc' : Continuous (emb hι) := by rw [show ⇑(emb hι) = s from funext e]; exact hc
  have hQ' : ∀ γ ∈ GQ B, emb hι γ ∈ GQ A := fun γ hγ => e γ ▸ hQ γ hγ
  obtain ⟨N, C, hC⟩ := emb_moderate hι hθ hc' hQ' hφ
  obtain ⟨K, hK⟩ := (GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ hφ'.1 hφ'.2).mul_bounded
    (ψ := fun g => φ (emb hι g)) (fun γ hγ g => by simp only [map_mul]; exact hφ.left _ (hQ' γ hγ) _) hC
  have : BorelSpace (GA D B) := ⟨rfl⟩
  refine Measure.integrableOn_of_bounded (M := K)
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B μ 𝓕 hq.1 hq.2).ne
    (((hφ.cont.comp hc').star.mul hφ'.1.cont).measurable.aestronglyMeasurable) (.of_forall fun g => ?_)
  rw [norm_mul, norm_star]
  exact hK g

end GlobalTheory.Mem.TopIntegrand

end
end
