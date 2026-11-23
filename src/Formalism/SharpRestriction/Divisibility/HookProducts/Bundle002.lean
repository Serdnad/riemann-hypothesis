module

public import Formalism.HarderNarasimhan.Statement
public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Module

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.RBTie

theorem slope_eq_of_norm_eq {R V E F : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ : V →+ E) (ρ₂ : V →+ F) (hn : ∀ x, ‖ρ₂ x‖ = ‖ρ x‖) (N : Submodule R V) :
    Formalism.HN.slope ρ₂ N = Formalism.HN.slope ρ N := by
  classical
  have memL : ∀ y : E, y ∈ Formalism.HN.zl ρ N ↔ ∃ x ∈ N.toAddSubgroup, ρ x = y := by
    intro y
    show y ∈ (N.toAddSubgroup.map ρ) ↔ _
    exact AddSubgroup.mem_map
  have memM : ∀ y : F, y ∈ Formalism.HN.zl ρ₂ N ↔ ∃ x ∈ N.toAddSubgroup, ρ₂ x = y := by
    intro y
    show y ∈ (N.toAddSubgroup.map ρ₂) ↔ _
    exact AddSubgroup.mem_map
  let pre : Formalism.HN.zl ρ N → V := fun y => Classical.choose ((memL y).1 y.2)
  have pre_mem : ∀ y, pre y ∈ N.toAddSubgroup := fun y =>
    (Classical.choose_spec ((memL y).1 y.2)).1
  have pre_eq : ∀ y, ρ (pre y) = y := fun y => (Classical.choose_spec ((memL y).1 y.2)).2
  let f0 : Formalism.HN.zl ρ N →+ Formalism.HN.zl ρ₂ N :=
    AddMonoidHom.mk' (fun y => ⟨ρ₂ (pre y), (memM _).2 ⟨pre y, pre_mem y, rfl⟩⟩) (by
      intro y z
      apply Subtype.ext
      show ρ₂ (pre (y + z)) = ρ₂ (pre y) + ρ₂ (pre z)
      rw [← map_add (f := _)]
      apply Formalism.HN.Rerealization.eq_of_eq ρ ρ₂ hn
      rw [map_add (f := _), pre_eq, pre_eq, pre_eq]
      rfl)
  have f0_apply : ∀ y, ((f0 y : Formalism.HN.zl ρ₂ N) : F) = ρ₂ (pre y) := fun y => rfl
  have f0_norm : ∀ y, ‖((f0 y : Formalism.HN.zl ρ₂ N) : F)‖ = ‖(y : E)‖ := by
    intro y
    rw [f0_apply, hn, pre_eq]
  have hinj : Function.Injective f0 := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have h0 : ‖(y : E)‖ = 0 := by
      rw [← f0_norm, hy]
      simp
    exact Subtype.ext (norm_eq_zero.1 h0)
  have hsurj : Function.Surjective f0 := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, rfl⟩ := (memM z).1 hz
    refine ⟨⟨ρ x, (memL _).2 ⟨x, hx, rfl⟩⟩, Subtype.ext ?_⟩
    rw [f0_apply]
    exact Formalism.HN.Rerealization.eq_of_eq ρ ρ₂ hn (pre_eq _)
  let e : Formalism.HN.zl ρ N ≃+ Formalism.HN.zl ρ₂ N := AddEquiv.ofBijective f0 ⟨hinj, hsurj⟩
  have e_norm : ∀ y, ‖e y‖ = ‖y‖ := fun y => f0_norm y
  have e_symm_norm : ∀ z, ‖e.symm z‖ = ‖z‖ := by
    intro z
    rw [← e_norm (e.symm z), e.apply_symm_apply]
  have iso : Isometry e := AddMonoidHomClass.isometry_of_norm e e_norm
  have iso_symm : Isometry e.symm := AddMonoidHomClass.isometry_of_norm e.symm e_symm_norm
  have hiff : DiscreteTopology (Formalism.HN.zl ρ N) ↔ DiscreteTopology (Formalism.HN.zl ρ₂ N) := by
    constructor
    · intro h
      exact iso_symm.isEmbedding.discreteTopology
    · intro h
      exact iso.isEmbedding.discreteTopology
  have hrk : Formalism.F.rk (Formalism.HN.zl ρ₂ N) = Formalism.F.rk (Formalism.HN.zl ρ N) := by
    unfold Formalism.F.rk
    exact e.toIntLinearEquiv.finrank_eq.symm
  have hcov : Formalism.F.covol (Formalism.HN.zl ρ₂ N) = Formalism.F.covol (Formalism.HN.zl ρ N) := by
    by_cases h : DiscreteTopology (Formalism.HN.zl ρ N)
    · exact (Formalism.HN.Rerealization.covol_rk_eq ρ ρ₂ hn N.toAddSubgroup h (hiff.1 h)).1
    · have h' : ¬ DiscreteTopology (Formalism.HN.zl ρ₂ N) := fun h' => h (hiff.2 h')
      unfold Formalism.F.covol
      rw [dite_eq_right h, dite_eq_right h']
  unfold Formalism.HN.slope Formalism.F.slope Formalism.F.deg
  rw [hcov, hrk]

end Formalism.MainNotions.DIV.HookProducts.RBTie
end
end

section

open Module NumberField

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.FunSharp

variable {K : Type} [Field K] [NumberField K] [StarRing K]

private theorem norm_realize_sq_eq_sum_majAt_re {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    ‖Formalism.HermitianLatticesTheory.realize b X x‖ ^ 2 = ∑ v, (Formalism.HermitianLatticesTheory.majAt b X v x x).re := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type, Formalism.HermitianLatticesTheory.majAt, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, Complex.mul_re]
  ring

private theorem slope_map_eq_of_norm_eq {G E F : Type} [AddCommGroup G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (α : G →+ E) (β : G →+ F) (hn : ∀ g, ‖β g‖ = ‖α g‖) (H : AddSubgroup G) :
    Formalism.F.slope (H.map β).toIntSubmodule = Formalism.F.slope (H.map α).toIntSubmodule := by
  have hz : ∀ g, β g = 0 ↔ α g = 0 := fun g => by rw [← norm_eq_zero, hn g, norm_eq_zero]
  have key : ∀ {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
      (α₁ : G →+ E₁) (α₂ : G →+ E₂), (∀ g, ‖α₂ g‖ = ‖α₁ g‖) →
      DiscreteTopology (H.map α₁).toIntSubmodule → DiscreteTopology (H.map α₂).toIntSubmodule := by
    intro E₁ E₂ _ _ α₁ α₂ hn' hd
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff] at hd ⊢
    obtain ⟨ε, hε, h⟩ := hd
    refine ⟨ε, hε, fun y hy => ?_⟩
    obtain ⟨w, hw⟩ := y
    have hw' : w ∈ H.map α₂ := hw
    obtain ⟨g, hg, rfl⟩ := AddSubgroup.mem_map.1 hw'
    have hmem : α₁ g ∈ (H.map α₁).toIntSubmodule := AddSubgroup.mem_map_of_mem α₁ hg
    have h1 := h ⟨α₁ g, hmem⟩ (by
      have hy' := hy
      simp only [Subtype.dist_eq, ZeroMemClass.coe_zero, dist_zero_right] at hy' ⊢
      change ‖α₂ g‖ < ε at hy'
      change ‖α₁ g‖ < ε
      rw [← hn']
      exact hy')
    have h2 : α₁ g = 0 := congrArg Subtype.val h1
    have h3 : α₂ g = 0 := by rw [← norm_eq_zero, hn', h2, norm_zero]
    exact Subtype.ext h3
  have hd : DiscreteTopology (H.map β).toIntSubmodule ↔ DiscreteTopology (H.map α).toIntSubmodule :=
    ⟨key β α (fun g => (hn g).symm), key α β hn⟩
  by_cases hα : DiscreteTopology (H.map α).toIntSubmodule
  · obtain ⟨hc, hr⟩ := Formalism.HN.Rerealization.covol_rk_eq α β hn H hα (hd.2 hα)
    unfold Formalism.F.slope Formalism.F.deg
    rw [hc, hr]
  · have hβ : ¬ DiscreteTopology (H.map β).toIntSubmodule := fun h => hα (hd.1 h)
    unfold Formalism.F.slope Formalism.F.deg Formalism.F.covol
    rw [dite_eq_right hα, dite_eq_right hβ]
    simp

theorem muMax_tie (A : Formalism.BasicNotions.HLat K) {n : ℕ} (L : Submodule (𝓞 K) (Fin n → K))
    (XE : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (e : (Fin n → K) ≃ₗ[K] A.V)
    (hlat : A.L = L.map ((e : (Fin n → K) →ₗ[K] A.V).restrictScalars (𝓞 K)))
    (hmet : ∀ v x y, Formalism.HermitianLatticesTheory.majAt A.b A.X v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) XE v x y) :
    Formalism.HN.muMaxDef (Pi.basisFun K (Fin n)) XE L = A.muMax := by
  set f : (Fin n → K) →ₗ[𝓞 K] A.V := (e : (Fin n → K) →ₗ[K] A.V).restrictScalars (𝓞 K) with hf
  set g : A.V →ₗ[𝓞 K] (Fin n → K) := (e.symm : A.V →ₗ[K] (Fin n → K)).restrictScalars (𝓞 K) with hg
  have hgf : ∀ N : Submodule (𝓞 K) (Fin n → K), (N.map f).map g = N := by
    intro N
    rw [← Submodule.map_comp]
    have : g.comp f = LinearMap.id := by
      ext x; simp [hf, hg]
    rw [this, Submodule.map_id]
  have hfg : ∀ N : Submodule (𝓞 K) A.V, (N.map g).map f = N := by
    intro N
    rw [← Submodule.map_comp]
    have : f.comp g = LinearMap.id := by
      ext x; simp [hf, hg]
    rw [this, Submodule.map_id]
  have hn : ∀ x, ‖(Formalism.HermitianLatticesTheory.realize A.b A.X).comp f.toAddMonoidHom x‖ =
      ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) XE x‖ := by
    intro x
    have h1 := norm_realize_sq_eq_sum_majAt_re A.b A.X (e x)
    have h2 := norm_realize_sq_eq_sum_majAt_re (Pi.basisFun K (Fin n)) XE x
    simp_rw [hmet] at h1
    show ‖Formalism.HermitianLatticesTheory.realize A.b A.X (e x)‖ = _
    rw [← Real.sqrt_sq (norm_nonneg (Formalism.HermitianLatticesTheory.realize A.b A.X (e x))),
      ← Real.sqrt_sq (norm_nonneg (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) XE x)), h1, h2]
  have hslope : ∀ N : Submodule (𝓞 K) (Fin n → K),
      Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize A.b A.X) (N.map f) =
        Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) XE) N := by
    intro N
    unfold Formalism.HN.slope Formalism.HN.zl
    rw [Submodule.map_toAddSubgroup, AddSubgroup.map_map]
    exact slope_map_eq_of_norm_eq _ _ hn N.toAddSubgroup
  have hne : ∀ N : Submodule (𝓞 K) (Fin n → K), N ≠ ⊥ → N.map f ≠ ⊥ := by
    intro N hN h
    apply hN
    rw [← hgf N, h, Submodule.map_bot]
  have hne' : ∀ N : Submodule (𝓞 K) A.V, N ≠ ⊥ → N.map g ≠ ⊥ := by
    intro N hN h
    apply hN
    rw [← hfg N, h, Submodule.map_bot]
  have hmu : Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) XE) L =
      Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize A.b A.X) A.L := by
    unfold Formalism.HN.muMax
    congr 1
    ext t
    constructor
    · rintro ⟨N, hNL, hN0, hs⟩
      refine ⟨N.map f, ?_, hne N hN0, (hslope N).trans hs⟩
      rw [hlat]; exact Submodule.map_mono hNL
    · rintro ⟨N, hNL, hN0, hs⟩
      refine ⟨N.map g, ?_, hne' N hN0, ?_⟩
      · rw [← hgf L]
        apply Submodule.map_mono
        rw [← hlat]; exact hNL
      · rw [← hslope, hfg]; exact hs
  unfold Formalism.BasicNotions.HLat.muMax Formalism.HN.muMaxDef
  rw [hmu]

end Formalism.MainNotions.DIV.HookProducts.FunSharp
end
end
