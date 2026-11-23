module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle010
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

@[expose] public section

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section GlueDefs

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def Corr (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') (n₁ n₂ : V) : Prop :=
  ∃ (h₁ : n₁ ∈ H.W0 t₁.f t₁.f') (h₂ : n₂ ∈ H.W0 t₂.f t₂.f'),
    φ (H.mkW t₁.f ⟨n₁, mem_perp_isotropicSpan_of_mem_framePerp H h₁⟩) = H.mkW t₂.f ⟨n₂, mem_perp_isotropicSpan_of_mem_framePerp H h₂⟩ ∧
    φ' (H.mkW t₁.f' ⟨n₁, mem_perp_isotropicSpan_of_mem_framePerp' H h₁⟩) = H.mkW t₂.f' ⟨n₂, mem_perp_isotropicSpan_of_mem_framePerp' H h₂⟩

def ThCond (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (Λ₂ : Submodule M.L.O V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') : Prop :=
  ∀ n₁ n₂, Corr H t₁ t₂ φ φ' n₁ n₂ → (n₁ ∈ t₁.abelian₂ ↔ n₂ ∈ Λ₂)

def GlueRel (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (Λ₂ : Submodule M.L.O V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f')
    (m₁ : ↥(MMsharp H t₁)) (m₂ : ↥(MMsharp H t₂)) : Prop :=
  ∃ n₁ n₂, Corr H t₁ t₂ φ φ' n₁ n₂ ∧ (m₁ : V) + n₁ ∈ t₁.abelian₂ ∧ (m₂ : V) + n₂ ∈ Λ₂

def GamCond (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) : Prop :=
  (M.split = none →
      (fun p => (θ p.1, φ p.2)) '' Gam H t₁ = Gam H t₂ ∧ (fun p => (θ p.1, φ' p.2)) '' Gam' H t₁ = Gam' H t₂) ∧
    (∀ g : SplitG M.L, M.split = some g →
      (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) =
        GamR H t₂ (algebraMap F E (g.q : F)))

end GlueDefs

section GlueProps

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def Glue (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    ∃ e : {Λ₂ : Submodule M.L.O V // H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
        ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ'} ≃
      {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ //
        IsUnit (H.Dl f₂ f₂' (r + 1)) ∧ MMInt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ ∧ IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ},
      ∀ x m₁ m₂, (e x).1 (ddMk H t₁ m₁) = ddMk H _ m₂ ↔
        GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ x.1 φ φ' m₁ m₂

def ClaimR (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    ∀ Λ₂ : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' →
    ∀ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩,
      (∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂) →
      (H.Respects t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' ↔
        GamCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' θ)

theorem latSide_of (M : Model F E) (r n : ℕ) (hG : Glue M r n) (hR : ClaimR M r n) : LatSide M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp
  obtain ⟨e, he⟩ := hG V H hn t₁ f₂ f₂' φ φ' hyp
  have hR' := hR V H hn t₁ f₂ f₂' φ φ' hyp
  have thc : ∀ Λ₂ : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ →
      H.Respects t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' → ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' := by
    intro Λ₂ hg hr n₁ n₂ hc
    obtain ⟨h₁, h₂, c₁, c₂⟩ := hc
    exact thCorr_holds M r V H t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' hyp.1 hg hr n₁ h₁ n₂ h₂ c₁ c₂
  have heq : ∀ y, ∀ m₁ m₂, y.1 (ddMk H t₁ m₁) = ddMk H _ m₂ ↔
      GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ (e.symm y).1 φ φ' m₁ m₂ := by
    intro y m₁ m₂
    have := he (e.symm y) m₁ m₂
    rwa [e.apply_symm_apply] at this
  refine Nat.card_congr
    { toFun := fun Λ => ⟨(e ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩).1,
        (e ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩).2.1, (e ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩).2.2.1,
        (e ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩).2.2.2,
        ((hR' Λ.1 Λ.2.1 (thc Λ.1 Λ.2.1 Λ.2.2) _ (he ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩)).1 Λ.2.2).1,
        ((hR' Λ.1 Λ.2.1 (thc Λ.1 Λ.2.1 Λ.2.2) _ (he ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩)).1 Λ.2.2).2⟩
      invFun := fun θ => ⟨(e.symm ⟨θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1⟩).1, (e.symm ⟨θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1⟩).2.1,
        (hR' _ (e.symm ⟨θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1⟩).2.1 (e.symm ⟨θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1⟩).2.2 θ.1
          (heq ⟨θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1⟩)).2 θ.2.2.2.2⟩
      left_inv := fun Λ => by
        apply Subtype.ext
        simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
      right_inv := fun θ => by
        apply Subtype.ext
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply] }

end GlueProps

end Formalism.L2.SG.LsDatumA
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.NGCut.NormalIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

instance instCM (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

def Jsub (Λ : Submodule (𝓞 D.host.E) (VS D).V) (X : Submodule D.host.E (VS D).V) (y0 : (VS D).V) :
    Submodule (𝓞 D.host.E) D.host.E where
  carrier := {l | l • y0 ∈ Λ ⊔ X.restrictScalars (𝓞 D.host.E)}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, add_smul] at *
    exact Submodule.add_mem _ ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at *
    rw [smul_assoc]
    exact Submodule.smul_mem _ c ha

section Hyp

variable (Λ : Submodule (𝓞 D.host.E) (VS D).V) (X : Submodule D.host.E (VS D).V) (y0 : (VS D).V)

theorem pair_int (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    (hiso : ∀ x ∈ X, ∀ x' ∈ X, brS (VS D) x x' = 0) (horth : ∀ x ∈ X, brS (VS D) y0 x = 0)
    {l m : D.host.E} (hl : l ∈ Jsub Λ X y0) (hm : m ∈ Jsub Λ X y0) :
    ∃ c : 𝓞 D.host.E, (c : D.host.E) = brS (VS D) (l • y0) (m • y0) := by
  have hl0 : l • y0 ∈ Λ ⊔ X.restrictScalars (𝓞 D.host.E) := hl
  have hm0 : m • y0 ∈ Λ ⊔ X.restrictScalars (𝓞 D.host.E) := hm
  obtain ⟨a1, ha1, x1, hx1, e1⟩ := Submodule.mem_sup.mp hl0
  obtain ⟨a2, ha2, x2, hx2, e2⟩ := Submodule.mem_sup.mp hm0
  have hx1' : x1 ∈ X := by simpa using hx1
  have hx2' : x2 ∈ X := by simpa using hx2

  have hy1 : ∀ x ∈ X, (VS D).hT x y0 = 0 := fun x hx => horth x hx
  have hxx : (VS D).hT x2 x1 = 0 := hiso x1 hx1' x2 hx2'
  have hsym : starRingEnd D.host.E ((VS D).hT x1 y0) = (VS D).hT y0 x1 := by
    first
      | exact (VS D).herm x1 y0
      | exact (VS D).herm.eq x1 y0
  have hy2 : (VS D).hT y0 x1 = 0 := by
    rw [← hsym, hy1 x1 hx1', map_zero]
  have ea1 : a1 = l • y0 - x1 := by rw [← e1]; abel
  have ea2 : a2 = m • y0 - x2 := by rw [← e2]; abel
  have c1 : (VS D).hT x2 a1 = 0 := by
    rw [ea1, map_sub, map_smul, hy1 x2 hx2', hxx]
    simp
  have c2 : (VS D).hT a2 x1 = 0 := by
    rw [ea2, map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy2, hxx]
    simp
  have e : brS (VS D) (l • y0) (m • y0) = (VS D).hT a2 a1 := by
    show (VS D).hT (m • y0) (l • y0) = _
    rw [← e1, ← e2]
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [c1, c2, hxx]
    simp

  have ha1d : a1 ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by
    rw [show Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ from hun]
    exact ha1
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at ha1d
  have h2 := (Submodule.mem_iInf _).mp ha1d a2
  have h3 := (Submodule.mem_iInf _).mp h2 ha2
  have h4 := Submodule.mem_comap.mp h3
  obtain ⟨c, hc⟩ := Submodule.mem_one.mp h4
  refine ⟨c, ?_⟩
  rw [e]
  exact hc

end Hyp

end Formalism.L2.SG.NGCut.NormalIntegrality
end
end

section

noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section CorrLemmas

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

private theorem h_finset_sum_smul_left {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • v i) y = ∑ i ∈ s, c i * H.h (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    simpa using H.h_smul_left 0 0 y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

private theorem h_add_right_rank_point_counts (x y z : V) : H.h x (y + z) = H.h x y + H.h x z := by
  rw [H.h_herm (y + z) x, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm]

private theorem h_smul_right_eq_cj_mul (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]

private theorem h_zero_right_rank_point_counts (x : V) : H.h x 0 = 0 := by
  simpa using h_add_right_rank_point_counts H x 0 0

theorem mem_perpX_of {f : Fin (r + 1) → V} {v : V} (h : ∀ j : Fin r, H.h v (f j.castSucc) = 0) :
    v ∈ H.perp (H.X f) := by
  show ∀ x ∈ H.X f, H.h v x = 0
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact h j
  | zero => exact h_zero_right_rank_point_counts H v
  | add y z _ _ hy hz => rw [h_add_right_rank_point_counts, hy, hz, add_zero]
  | smul a y _ hy => rw [h_smul_right_eq_cj_mul, hy, mul_zero]

theorem z_mem_perpX {f : Fin (r + 1) → V} {T : F} (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) :
    f (Fin.last r) ∈ H.perp (H.X f) :=
  mem_perpX_of H fun j => hF.1 _ _ (Or.inr (Fin.castSucc_lt_last j).ne)

theorem om'_mem_perpX (f f' : Fin (r + 1) → V) : H.om' f f' ∈ H.perp (H.X f) := by
  refine mem_perpX_of H fun j => ?_
  unfold HermSp.om'
  rw [h_sum_smul_left]
  have e := congrFun (congrFun (mul_adjugate (H.Zhat f f')) j.castSucc) (Fin.last r)
  rw [Matrix.smul_apply, one_apply_ne (Fin.castSucc_lt_last j).ne, smul_zero, Matrix.mul_apply] at e
  rw [← e]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [HermSp.Zhat, Matrix.of_apply]
  ring

theorem om'_mem_U (f f' : Fin (r + 1) → V) :
    H.om' f f' ∈ Submodule.span E (Set.range (Sum.elim f f')) := by
  unfold HermSp.om'
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)

theorem decomp_U_perpX {f f' : Fin (r + 1) → V} {T : F} (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hZ : IsUnit (H.Zhat f f').det) {u : V} (hu : u ∈ Submodule.span E (Set.range (Sum.elim f f')))
    (hp : u ∈ H.perp (H.X f)) :
    ∃ x ∈ H.X f, ∃ β γ : E, u = x + β • f (Fin.last r) + γ • H.om' f f' := by
  classical
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hu
  obtain ⟨a, p, rfl⟩ : ∃ a p, c = Sum.elim a p := ⟨c ∘ Sum.inl, c ∘ Sum.inr, by ext (i | i) <;> rfl⟩
  have hp' : ∀ x ∈ H.X f, H.h (∑ i, Sum.elim a p i • Sum.elim f f' i) x = 0 := hp
  rw [Fintype.sum_sum_type] at hp' ⊢
  simp only [Sum.elim_inl, Sum.elim_inr] at hp' ⊢
  obtain ⟨d, hd⟩ := hZ
  have hperp : ∀ j : Fin r, (H.Zhat f f' *ᵥ p) j.castSucc = 0 := by
    intro j
    have h0 := hp' (f j.castSucc) (Submodule.subset_span ⟨j, rfl⟩)
    rw [H.h_add_left, h_finset_sum_smul_left, h_finset_sum_smul_left,
      Finset.sum_eq_zero (fun i _ => by rw [hF.1 _ _ (Or.inr (Fin.castSucc_lt_last j).ne), mul_zero]),
      zero_add] at h0
    refine Eq.trans ?_ h0
    simp only [Matrix.mulVec, dotProduct, HermSp.Zhat, Matrix.of_apply]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hZp : H.Zhat f f' *ᵥ p = Pi.single (Fin.last r) ((H.Zhat f f' *ᵥ p) (Fin.last r)) := by
    funext k
    by_cases hk : k = Fin.last r
    · subst hk
      simp
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hk
      rw [hperp j, Pi.single_eq_of_ne hk]
  have hp2 : ∀ b, p b = (↑d⁻¹ * (H.Zhat f f' *ᵥ p) (Fin.last r)) * (H.Zhat f f').adjugate b (Fin.last r) := by
    intro b
    have h1 : (H.Zhat f f').adjugate *ᵥ (H.Zhat f f' *ᵥ p) = (H.Zhat f f').det • p := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 := congrFun h1 b
    rw [hZp] at h2
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul] at h2
    rw [← hd] at h2
    calc p b = ↑d⁻¹ * (↑d * p b) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by
        rw [← h2]
        simp only [Matrix.mulVec, dotProduct]
        ring
  refine ⟨∑ j : Fin r, a j.castSucc • f j.castSucc, ?_, a (Fin.last r),
    ↑d⁻¹ * (H.Zhat f f' *ᵥ p) (Fin.last r), ?_⟩
  · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Fin.sum_univ_castSucc (fun i => a i • f i)]
    congr 1
    unfold HermSp.om'
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_smul, ← hp2 b]

theorem Gdet_rel (f₁ f₁' f₂ f₂' : Fin (r + 1) → V) (T T' : F)
    (h : H.Dl f₁ f₁' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) :
    H.Gdet f₂ f₂' T T' * H.normE (H.Dl f₁ f₁' (r + 1)) =
      H.normE (H.Dl f₂ f₂' (r + 1)) * H.Gdet f₁ f₁' T T' := by
  unfold HermSp.Gdet HermSp.normE
  have h' : M.L.cj (H.Dl f₁ f₁' r) * M.L.cj (H.Dl f₂ f₂' (r + 1)) =
      M.L.cj (H.Dl f₂ f₂' r) * M.L.cj (H.Dl f₁ f₁' (r + 1)) := by
    rw [← map_mul, ← map_mul, h]
  linear_combination (algebraMap F E (T * T')) * (M.L.cj (H.Dl f₁ f₁' r) * M.L.cj (H.Dl f₂ f₂' (r + 1))) * h +
    (algebraMap F E (T * T')) * (H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) * h'

end CorrLemmas

end Formalism.L2.SG.LsDatumA
end
end
