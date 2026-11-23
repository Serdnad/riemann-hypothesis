module

public import Formalism.RealPlaceAnalysis.Bundle003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.AnyAdj
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfCharDataA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeKType
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.VNormSqLowKSubRootLt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IrredA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin

@[expose] public section

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem anyCap_word_mem {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {V : Submodule ℂ M} (w : List (Fin n × Fin n)) {x : M} (hx : x ∈ genSub E V) :
    (w.map fun p => E p.1 p.2).prod x ∈ genSub E V := by
  induction w with
  | nil => simpa using hx
  | cons p w ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact ICD.gen_stable ih p.1 p.2

theorem anyCap_adj {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E) (V : Submodule ℂ M) (u : ℂ) :
    ∃ C : Module.End ℂ M, (∀ x ∈ genSub E V, C x ∈ genSub E V) ∧
      ∀ x y : M, inner ℂ x (Formalism.REAL.qdet E u y) = inner ℂ (C x) y := by
  classical
  obtain ⟨l, hl⟩ := qdet_eq_sum_words E u
  refine ⟨(l.map fun c => (starRingEnd ℂ c.1 * (c.2.map fun p => adjSign ε p.1 p.2).prod) •
      ((c.2.reverse.map Prod.swap).map fun p => E p.1 p.2).prod).sum, ?_, ?_⟩
  · intro x hx
    clear hl
    induction l with
    | nil => simp
    | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply]
      exact add_mem (Submodule.smul_mem _ _ (anyCap_word_mem _ hx)) ih
  · intro x y
    rw [hl]
    clear hl
    induction l with
    | nil => simp
    | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply,
        inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
      rw [ih]
      congr 1
      have h := eword_adjoint hU c.2 y x
      have h' : inner ℂ x ((c.2.map fun p => E p.1 p.2).prod y) =
          starRingEnd ℂ (c.2.map fun p => adjSign ε p.1 p.2).prod *
            inner ℂ (((c.2.reverse.map Prod.swap).map fun p => E p.1 p.2).prod x) y := by
        rw [← inner_conj_symm, h, map_mul, inner_conj_symm]
      rw [h', map_mul, starRingEnd_self_apply]
      ring

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Data

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem kType_map_of_inj {μ : Fin n → ℝ} {S : Submodule ℂ H} (hS : Formalism.MainNotions.S.IsKTypeOf ε σ μ S)
    (f : H →ₗ[ℂ] H) (hf : ∀ k ∈ Formalism.REAL.Kset ε, ∀ x, f (σ k x) = σ k (f x))
    (hinj : ∀ x ∈ S, f x = 0 → x = 0) : Formalism.MainNotions.S.IsKTypeOf ε σ μ (S.map f) := by
  obtain ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hwt⟩ := hS
  have hwt' : ∀ x ∈ S, ∀ ν, Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ ν (f x) →
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ ν x := by
    intro x hx ν h θ hθ
    have h1 := h θ hθ
    rw [← hf _ hθ, ← map_smul] at h1
    have := hinj _ (S.sub_mem (hst _ hθ x hx) (S.smul_mem _ hx)) (by rw [map_sub, h1, sub_self])
    exact sub_eq_zero.1 this
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ g x, hst g hg x hx, hf g hg x⟩
  · intro S' hS' hK
    let T : Submodule ℂ H := S ⊓ S'.comap f
    have hT : Formalism.MainNotions.S.IsKStableOn ε σ T := fun g hg x hx =>
      ⟨hst g hg x hx.1, by
        show f (σ g x) ∈ S'
        rw [hf g hg]
        exact hK g hg _ hx.2⟩
    rcases hirr T inf_le_left hT with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hS' hy
      have hxT : x ∈ T := ⟨hx, hy⟩
      rw [h, Submodule.mem_bot] at hxT
      rw [hxT, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨x, hx, rfl⟩
      have hxT : x ∈ T := by rw [h]; exact hx
      exact hxT.2
  · refine ⟨f v, Submodule.mem_map_of_mem hvS, fun h => hv0 (hinj v hvS h), fun θ hθ => ?_⟩
    rw [← hf _ hθ, hvw θ hθ, map_smul]
  · rintro ν _ ⟨x, hx, rfl⟩ h0 hν
    exact hwt ν x hx (fun h => h0 (by rw [h, map_zero])) (hwt' x hx ν hν)

theorem exists_khw_genSub_of_kType (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hVf : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V) {μ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : S ≤ closGen E V) (hST : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) :
    ∃ w : D, w ∈ genSub E V ∧ w ≠ 0 ∧ IsKHWVec ε E μ w := by
  classical
  have hE := hD.glRep
  obtain ⟨v, hvS, hv0, -⟩ := hST.2.2.2.1
  have hex : ∃ y : D, y ∈ genSub E V ∧ inner ℂ v (y : H) ≠ 0 := by
    by_contra hno
    push Not at hno
    have h1 : (genSub E V).map D.subtype ≤ (ℂ ∙ v)ᗮ := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact hno y hy
    have h2 : closGen E V ≤ (ℂ ∙ v)ᗮ :=
      Submodule.topologicalClosure_minimal _ h1 (Submodule.isClosed_orthogonal _)
    have h3 := h2 (hS hvS)
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at h3
    exact hv0 (inner_self_eq_zero.1 h3)
  obtain ⟨y, hyg, hyv⟩ := hex
  obtain ⟨m, hym⟩ := exists_layer_of_mem_genSub hE hVk hyg
  have hLf : FiniteDimensional ℂ (layer ε E V m) := finiteDimensional_layer hVf m
  have hLk := kStable_of_isKStableSub hσ hD (layer ε E V m) hLf (layer_kStable hE hVk m)
  set W : Submodule ℂ H := (layer ε E V m).map D.subtype with hWdef
  have : FiniteDimensional ℂ W := inferInstance
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hWK : ∀ k ∈ Kset ε, ∀ x ∈ W, σ k x ∈ W := by
    rintro k hk _ ⟨u, hu, rfl⟩
    obtain ⟨w, hw, e⟩ := hLk k hk u hu
    exact ⟨w, hw, e⟩
  have hWoK : ∀ k ∈ Kset ε, ∀ x ∈ Wᗮ, σ k x ∈ Wᗮ := by
    intro k hk
    obtain ⟨hk', hkk⟩ := UnitaryGroupOfForm.K_inv hk
    exact UnitaryGroupOfForm.orth_stable hσ (UnitaryGroupOfForm.K_mem_UJ hk) (UnitaryGroupOfForm.K_mem_UJ hk') hkk W (hWK _ hk')
  have hPc : ∀ k ∈ Formalism.REAL.Kset ε, ∀ x, W.starProjection.toLinearMap (σ k x) =
      σ k (W.starProjection.toLinearMap x) := fun k hk x =>
    UnitaryGroupOfForm.proj_comm W (σ k) (hWK k hk) (hWoK k hk) x
  have hyW : (y : H) ∈ W := ⟨y, hym, rfl⟩
  have hinj : ∀ x ∈ S, W.starProjection.toLinearMap x = 0 → x = 0 := by
    intro x hx hPx
    let T : Submodule ℂ H := S ⊓ LinearMap.ker W.starProjection.toLinearMap
    have hT : Formalism.MainNotions.S.IsKStableOn ε σ T := fun g hg z hz =>
      ⟨hST.2.1 g hg z hz.1, LinearMap.mem_ker.2 (by rw [hPc g hg, LinearMap.mem_ker.1 hz.2, map_zero])⟩
    rcases hST.2.2.1 T inf_le_left hT with h | h
    · have hxT : x ∈ T := ⟨hx, hPx⟩
      rw [h, Submodule.mem_bot] at hxT
      exact hxT
    · exfalso
      have hvT : v ∈ T := by rw [h]; exact hvS
      apply hyv
      have e1 : inner ℂ v (y : H) = inner ℂ (W.starProjection v) (y : H) := by
        rw [Submodule.inner_starProjection_left_eq_right, W.starProjection_eq_self_iff.2 hyW]
      rw [e1, show W.starProjection v = 0 from hvT.2, inner_zero_left]
  have hKT := kType_map_of_inj hST W.starProjection.toLinearMap hPc hinj
  have hSD : S.map W.starProjection.toLinearMap ≤ D := by
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨u, -, e⟩ := W.starProjection_apply_mem x
    show W.starProjection x ∈ D
    rw [← e]
    exact u.2
  obtain ⟨w, hwS, hw0, hwK⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hKT hSD
  refine ⟨w, ?_, hw0, hwK⟩
  obtain ⟨x, -, e⟩ := hwS
  obtain ⟨u, hu, e'⟩ := W.starProjection_apply_mem x
  have huw : u = w := Subtype.ext (e'.trans e)
  exact layer_le_genSub m (huw ▸ hu)

theorem data_casValK_gap (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {μ : Fin n → ℝ} (S : Submodule ℂ H)
    (hS : S ≤ closGen E V) (hST : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) (hμ : μ ≠ lowK ε lam) :
    casValK ε (lowK ε lam) + 2 * (h - n + 1) ≤ casValK ε μ := by
  obtain ⟨w, hwg, hw0, hwK⟩ := exists_khw_genSub_of_kType hσ hD hV.1 hV.2.1 hS hST
  obtain ⟨j, -, hpos, hle⟩ := casimir_gap_at_noncompact_weight hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap.1 hh hbig
    hwg hw0 hwK hμ
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

theorem data_vogan (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {μ : Fin n → ℝ} (S : Submodule ℂ H) (hS : S ≤ closGen E V)
    (hST : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) :
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) ≤ Formalism.MainNotions.S.vNormSq ε μ := by
  obtain ⟨w, hwg, hw0, hwK⟩ := exists_khw_genSub_of_kType hσ hD hV.1 hV.2.1 hS hST
  exact vogan_min hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap hwg hw0 hwK

theorem data_isKTypeOf (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) : Formalism.MainNotions.S.IsKTypeOf ε σ (lowK ε lam) (V.map D.subtype) := by
  exact isKTypeOf_of_isKIrrHW hσ hD hV hVK (fun μ x hx hx0 hμ =>
    weights_le_of_irr_hw hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hx hx0 hμ)

theorem data_casU (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (x : D) (hx : x ∈ genSub E V) :
    casU ε σ (x : H) = ((casVal lam : ℝ) : ℂ) • (x : H) := by
  rw [casU_eq_casimir hD x, casimir_genSub hD.glRep hc x hx, Submodule.coe_smul]

theorem data_closGen_eq_top (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hirr : Formalism.MainNotions.S.IsIrredOn (UJset ε) σ) (hV0 : V ≠ ⊥) :
    closGen E V = ⊤ := by
  rcases hirr (closGen E V) (Submodule.isClosed_topologicalClosure _)
      (closGen_stable hgap hσ hD hV hc hVK) with h | h
  · exfalso
    obtain ⟨w, hw, hw0, -⟩ := hV.2.2.2
    have hwc : (w : H) ∈ closGen E V := UnitaryGroupOfForm.mem_closGen (E := E) V w hw
    rw [h, Submodule.mem_bot] at hwc
    exact hw0 (by exact_mod_cast hwc)
  · exact h

end Data

section Two

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {D₁ : Submodule ℂ H₁}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {V₁ : Submodule ℂ D₁}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {D₂ : Submodule ℂ H₂}
  {E₂ : Fin n → Fin n → Module.End ℂ D₂} {V₂ : Submodule ℂ D₂}

end Two

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem data_admissible (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (μ : Fin n → ℝ) :
    FiniteDimensional ℂ
      (sSup {S : Submodule ℂ H | S ≤ closGen E V ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H) := by
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hE := hD.glRep
  obtain ⟨k, hk⟩ := khw_mem_layer hE hU hV hc hgap μ
  have hLf : FiniteDimensional ℂ (layer ε E V k) := finiteDimensional_layer hV.1 k
  have hLK := kStable_of_isKStableSub hσ hD (layer ε E V k) hLf (layer_kStable hE hV.2.1 k)
  have hMf : FiniteDimensional ℂ ((layer ε E V k).map D.subtype) := Module.Finite.map _ _
  have hle : (sSup {S : Submodule ℂ H | S ≤ closGen E V ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H) ≤
      (layer ε E V k).map D.subtype := by
    refine sSup_le fun S hSmem => ?_
    obtain ⟨hS, hST⟩ := hSmem
    obtain ⟨hSf, hSK, hirr, -, -⟩ := id hST
    have hSM := data_kfin_le hgap hσ hD hV hc hVK S hS hSf (fun g hg x hx => hSK g hg x hx)
    have hSD : S ≤ D := hSM.trans (Submodule.map_subtype_le _ _)
    obtain ⟨w, hwS, hw0, hwμ⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hST hSD
    have hwg : w ∈ genSub E V := by
      obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hSM hwS)
      have : y = w := Subtype.ext hyw
      exact this ▸ hy
    have hwL := hk w hwg hwμ
    have hS'K : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ (layer ε E V k).map D.subtype) := by
      intro g hg v hv
      refine ⟨hSK g hg v hv.1, ?_⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv.2
      obtain ⟨z, hz, hzeq⟩ := hLK g hg y hy
      exact Submodule.mem_map.2 ⟨z, hz, hzeq⟩
    rcases hirr _ inf_le_left hS'K with h0 | hEq
    · exfalso
      have hmem : (w : H) ∈ S ⊓ (layer ε E V k).map D.subtype :=
        ⟨hwS, Submodule.mem_map_of_mem hwL⟩
      rw [h0, Submodule.mem_bot] at hmem
      exact hw0 (Subtype.ext hmem)
    · rw [← hEq]
      exact inf_le_right
  exact Submodule.finiteDimensional_of_le hle

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

def dinj_jLin (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) : T.V →ₗ[ℂ] L2 ε where
  toFun := uniformisationL2 ε Ψ v₀
  map_add' := datumEmbedding_add hP v₀
  map_smul' := datumEmbedding_smul hP v₀

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem dinj_continuousOn_of_smoothOnGV {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f) : ContinuousOn f (UJset ε) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  have hFc : ContinuousAt F g₀ := hF.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfF g₀ hg₀U hg₀)
  filter_upwards [inter_mem_nhdsWithin (UJset ε) (hU.mem_nhds hg₀U)] with g hg
  exact hfF g hg.2 hg.1

end

theorem uniformisationL2_injective (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) :
    Function.Injective (uniformisationL2 ε Ψ v₀) := by
  have hmem : ∀ g : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat g ∈ UJset ε := fun g => g.2
  have hum : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hΨu : Continuous (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) :=
    (dinj_continuousOn_of_smoothOnGV hP.2.2.1).comp_continuous hum hmem
  have hfc : ∀ v, Continuous (fun g : Formalism.REAL.UJ ε => jfun Ψ v₀ v (Formalism.MainNotions.S.umat g)) := by
    intro v
    simp only [jfun]
    exact continuous_const.inner (hΨu.clm_apply continuous_const)
  have hML : ∀ v, MemLp (fun g : Formalism.REAL.UJ ε => jfun Ψ v₀ v (Formalism.MainNotions.S.umat g)) 2
      (Formalism.REAL.muG ε) := by
    intro v
    have hH : (Formalism.REAL.muG ε).IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
    have h0 := hP.2.2.2.2 (Formalism.REAL.muG ε) hH
    have h2 := ((innerSL ℂ v₀).comp (ContinuousLinearMap.apply ℂ T.V v)).comp_memLp' h0
    refine MemLp.ae_eq (Filter.Eventually.of_forall fun g => ?_) h2
    simp [jfun] <;> rfl
  haveI : (Formalism.REAL.muG ε).IsOpenPosMeasure := by unfold Formalism.REAL.muG; infer_instance
  have hz : ∀ v, uniformisationL2 ε Ψ v₀ v = 0 ↔
      ∀ g : Formalism.REAL.UJ ε, jfun Ψ v₀ v (Formalism.MainNotions.S.umat g) = 0 := by
    intro v
    have hm := hML v
    have e1 : uniformisationL2 ε Ψ v₀ v = hm.toLp _ := by
      unfold uniformisationL2 toL2
      exact dif_pos hm
    rw [e1, Lp.eq_zero_iff_ae_eq_zero]
    constructor
    · intro h g
      have h5 := ((hfc v).ae_eq_iff_eq (Formalism.REAL.muG ε) continuous_zero).mp
        (hm.coeFn_toLp.symm.trans h)
      exact congrFun h5 g
    · intro h
      exact hm.coeFn_toLp.trans (Filter.Eventually.of_forall fun g => h g)
  have hstab : ∀ (k : S7.KG ε) (v : T.V),
      (∀ g : Formalism.REAL.UJ ε, jfun Ψ v₀ v (Formalism.MainNotions.S.umat g) = 0) →
      ∀ g : Formalism.REAL.UJ ε, jfun Ψ v₀ (T.op k v) (Formalism.MainNotions.S.umat g) = 0 := by
    intro k v hv g
    have hk := hP.1 1 k (Formalism.MainNotions.S.umat g) (hmem g)
    have ht1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
    have ho1 : T.op 1 = 1 := by simp [S7.KType.op]
    rw [ht1, ho1, one_mul, one_mul] at hk
    let y : Formalism.REAL.UJ ε := (k : S7.UJ ε)
    have hy : Formalism.MainNotions.S.umat (g * y) = Formalism.MainNotions.S.umat g * S7.toMK k := rfl
    have h3 := hv (g * y)
    rw [hy] at h3
    simp only [jfun] at h3 ⊢
    rw [hk] at h3
    simpa using h3
  have hne : uniformisationL2 ε Ψ v₀ v₀ ≠ 0 := by
    intro h0
    have h6 : jfun Ψ v₀ v₀ 1 = 0 := (hz v₀).1 h0 1
    simp only [jfun, hP.2.1, ContinuousLinearMap.one_apply] at h6
    exact hv₀ (inner_self_eq_zero.mp h6)
  have hker : ∀ v, v ∈ LinearMap.ker (dinj_jLin hP v₀) ↔
      ∀ g : Formalism.REAL.UJ ε, jfun Ψ v₀ v (Formalism.MainNotions.S.umat g) = 0 :=
    fun v => LinearMap.mem_ker.trans (hz v)
  rcases T.irred (LinearMap.ker (dinj_jLin hP v₀))
      (fun k v hv => (hker _).2 (hstab k v ((hker v).1 hv))) with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exfalso
    have hv : v₀ ∈ LinearMap.ker (dinj_jLin hP v₀) := by
      rw [h]
      exact Submodule.mem_top
    exact hne (LinearMap.mem_ker.1 hv)

end ReciprocityTheory.ChartRestriction.DS
end
end
