module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

@[expose] public section

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section GDefs

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def ThL (H : HermSp M V) {r : ℕ} (t : Term V M r) : Submodule M.L.O V :=
  t.abelian₂ ⊓ (H.W0 t.f t.f').restrictScalars M.L.O

def ThSharp (H : HermSp M V) {r : ℕ} (t : Term V M r) (N : Submodule M.L.O V) : Submodule M.L.O V where
  carrier := {w | w ∈ H.W0 t.f t.f' ∧ ∀ n ∈ N, H.h w n ∈ M.L.O}
  add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun m hm => by
    rw [H.h_add_left]; exact M.L.O.add_mem (ha.2 m hm) (hb.2 m hm)⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun m _ => by rw [H.h_zero_left]; exact M.L.O.zero_mem⟩
  smul_mem' := fun c u hu => ⟨by rw [Subring.smul_def]; exact Submodule.smul_mem _ _ hu.1, fun m hm => by
    rw [Subring.smul_def, H.h_smul_left]; exact M.L.O.mul_mem c.2 (hu.2 m hm)⟩

abbrev DDW (H : HermSp M V) {r : ℕ} (t : Term V M r) (N : Submodule M.L.O V) : Type :=
  ↥(ThSharp H t N) ⧸ N.comap (ThSharp H t N).subtype

def dwMk (H : HermSp M V) {r : ℕ} (t : Term V M r) (N : Submodule M.L.O V) (w : ↥(ThSharp H t N)) : DDW H t N :=
  Submodule.Quotient.mk w

end GDefs

section GProps

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def CorrIso (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl f₂ f₂' (r + 1)) →
    ∃ ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 f₂ f₂'), (∀ x y, H.h (ψ x) (ψ y) = H.h x y) ∧
      ∀ n₁ n₂ : V, Corr H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' n₁ n₂ ↔
        ∃ h₁ : n₁ ∈ H.W0 t₁.f t₁.f', (ψ ⟨n₁, h₁⟩ : V) = n₂

def GlueEta (M : Model F E) (r : ℕ) : Prop :=
  M.OK → ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r), H.IsGeneric t →
    ∃ η : DDt H t ≃ₗ[M.L.O] DDW H t (ThL H t),
      (∀ (m : ↥(MMsharp H t)) (w : ↥(ThSharp H t (ThL H t))),
        η (ddMk H t m) = dwMk H t _ w ↔ (m : V) + w ∈ t.abelian₂) ∧
      (∀ (m m' : ↥(MMsharp H t)) (w w' : ↥(ThSharp H t (ThL H t))),
        η (ddMk H t m) = dwMk H t _ w → η (ddMk H t m') = dwMk H t _ w' →
          H.h m m' + H.h w w' ∈ M.L.O)

def GlueConv (M : Model F E) (r : ℕ) : Prop :=
  M.OK → ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r),
    IsUnit (H.gram (H.MMfam t)).det → MMInt H t →
    ∀ N : Submodule M.L.O V, N ≤ (H.W0 t.f t.f').restrictScalars M.L.O → N.FG →
      Submodule.span E (N : Set V) = H.W0 t.f t.f' → (∀ x ∈ N, ∀ y ∈ N, H.h x y ∈ M.L.O) →
    ∀ η : DDt H t ≃ₗ[M.L.O] DDW H t N,
      (∀ (m m' : ↥(MMsharp H t)) (w w' : ↥(ThSharp H t N)),
        η (ddMk H t m) = dwMk H t N w → η (ddMk H t m') = dwMk H t N w' → H.h m m' + H.h w w' ∈ M.L.O) →
      ∃! Λ : Submodule M.L.O V, H.IsSelfDual Λ ∧ H.Prim Λ (H.MMfam t) ∧
        Λ ⊓ (H.W0 t.f t.f').restrictScalars M.L.O = N ∧
        ∀ (m : ↥(MMsharp H t)) (w : ↥(ThSharp H t N)), η (ddMk H t m) = dwMk H t N w ↔ (m : V) + w ∈ Λ

def GenOfPrim (M : Model F E) (r n : ℕ) : Prop :=
  M.OK → ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl f₂ f₂' (r + 1)) →
    ∀ Λ₂ : Submodule M.L.O V, H.IsSelfDual Λ₂ → H.Prim Λ₂ (H.MMfam ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩) →
      H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩

end GProps

end Formalism.L2.SG.LsDatumA
end
end

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section G3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def GlueFwd (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    ∀ Λ₂ : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' →
    ∃ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩, IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ ∧
      ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂

def GlueBack (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl f₂ f₂' (r + 1)) → MMInt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ →
    ∀ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩, IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ →
    ∃ Λ₂ : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' ∧
      ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂

def GlueInj (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    ∀ Λ₂ Λ₂' : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' → H.IsGeneric ⟨Λ₂', f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂' φ φ' →
      (∀ m₁ m₂, GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂ ↔
        GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂' φ φ' m₁ m₂) → Λ₂ = Λ₂'

theorem mmInt_of_generic {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (Λ₂ : Submodule M.L.O V) (f₂ f₂' : Fin (r + 1) → V) (T T' : F)
    (hg : H.IsGeneric ⟨Λ₂, f₂, f₂', T, T'⟩) : MMInt H (⟨⊥, f₂, f₂', T, T'⟩ : Term V M r) := by
  have hsub : MMo H (⟨⊥, f₂, f₂', T, T'⟩ : Term V M r) ≤ Λ₂ := by
    refine (Submodule.span_le (R := M.L.O)).2 ?_
    rintro _ ⟨a, rfl⟩
    exact hg.2.1 a
  intro m hm m' hm'
  exact (hg.1.1.2.2 m).1 (hsub hm) m' (hsub hm')

theorem dd_ext {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    {t₁ t₂ : Term V M r} (θ θ' : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂)
    (h : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ ↔ θ' (ddMk H t₁ m₁) = ddMk H t₂ m₂) : θ = θ' := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨m₁, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m₂, hm₂⟩ := Submodule.Quotient.mk_surjective _ (θ (Submodule.Quotient.mk m₁))
  have h₁ : θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ := hm₂.symm
  exact h₁.trans ((h m₁ m₂).1 h₁).symm

theorem glue_of (M : Model F E) (r n : ℕ) (hF : GlueFwd M r n) (hB : GlueBack M r n) (hI : GlueInj M r n) :
    Glue M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp
  have fw := hF V H hn t₁ f₂ f₂' φ φ' hyp
  have bk := hB V H hn t₁ f₂ f₂' φ φ' hyp
  have inj := hI V H hn t₁ f₂ f₂' φ φ' hyp
  let toθ : {Λ₂ : Submodule M.L.O V // H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ'} →
      {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ //
        IsUnit (H.Dl f₂ f₂' (r + 1)) ∧ MMInt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ ∧
          IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ} :=
    fun x => ⟨(fw x.1 x.2.1 x.2.2).choose, x.2.1.1.2.2.2.1, mmInt_of_generic H x.1 f₂ f₂' t₁.T t₁.T' x.2.1,
      (fw x.1 x.2.1 x.2.2).choose_spec.1⟩
  have toθ_spec : ∀ x m₁ m₂, (toθ x).1 (ddMk H t₁ m₁) = ddMk H _ m₂ ↔
      GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ x.1 φ φ' m₁ m₂ :=
    fun x => (fw x.1 x.2.1 x.2.2).choose_spec.2
  have hinj : Function.Injective toθ := by
    intro x y hxy
    apply Subtype.ext
    refine inj x.1 y.1 x.2.1 x.2.2 y.2.1 y.2.2 fun m₁ m₂ => ?_
    rw [← toθ_spec x, ← toθ_spec y, hxy]
  have hsurj : Function.Surjective toθ := by
    intro θ
    obtain ⟨Λ₂, hg, hth, hrel⟩ := bk θ.2.1 θ.2.2.1 θ.1 θ.2.2.2
    refine ⟨⟨Λ₂, hg, hth⟩, Subtype.ext (dd_ext H _ _ fun m₁ m₂ => ?_)⟩
    rw [toθ_spec, hrel]
  exact ⟨Equiv.ofBijective toθ ⟨hinj, hsurj⟩, toθ_spec⟩

end G3

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

section Frac

variable (Λ : Submodule (𝓞 D.host.E) (VS D).V) (X : Submodule D.host.E (VS D).V) (y0 : (VS D).V)
  (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
  (hiso : ∀ x ∈ X, ∀ x' ∈ X, brS (VS D) x x' = 0) (horth : ∀ x ∈ X, brS (VS D) y0 x = 0)
  (hy0 : y0 ∈ Λ) (c0 : 𝓞 D.host.E) (hc0 : (c0 : D.host.E) = brS (VS D) y0 y0) (hc0ne : c0 ≠ 0)

include hy0 in
theorem one_mem_J : (1 : D.host.E) ∈ Jsub Λ X y0 := by
  change (1 : D.host.E) • y0 ∈ Λ ⊔ X.restrictScalars (𝓞 D.host.E)
  rw [one_smul]
  exact Submodule.mem_sup_left hy0

include hun hiso horth hy0 hc0 hc0ne in
theorem isFractional_J : IsFractional (nonZeroDivisors (𝓞 D.host.E)) (Jsub Λ X y0) := by
  refine ⟨c0, mem_nonZeroDivisors_of_ne_zero hc0ne, fun b hb => ?_⟩
  obtain ⟨c, hc⟩ := pair_int (Λ := Λ) (X := X) (y0 := y0) hun hiso horth hb (one_mem_J Λ X y0 hy0)
  refine ⟨c, ?_⟩
  rw [Algebra.smul_def]
  show (c : D.host.E) = (c0 : D.host.E) * b
  rw [hc, hc0]
  simp only [brS, one_smul, map_smul, smul_eq_mul]
  ring

def Jfrac : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ⟨Jsub Λ X y0, isFractional_J Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne⟩

theorem mem_Jfrac {l : D.host.E} : l ∈ Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne ↔ l • y0 ∈ Λ ⊔ X.restrictScalars (𝓞 D.host.E) := Iff.rfl

theorem Jfrac_ne_zero : Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne ≠ 0 := by
  intro h
  have h1 : (1 : D.host.E) ∈ Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne :=
    (mem_Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne).2 (by rw [one_smul]; exact Submodule.mem_sup_left hy0)
  rw [h, FractionalIdeal.mem_zero_iff] at h1
  exact one_ne_zero h1

theorem normZ_cO (d : 𝓞 D.host.E) :
    Algebra.norm ℤ (TorsionTotientBound.cO D.host.E d) = Algebra.norm ℤ d := by
  exact Algebra.norm_eq_of_algEquiv (TorsionTotientBound.cO D.host.E).toIntAlgEquiv d

theorem norm_bound :
    (1 : ℝ) ≤ ((FractionalIdeal.absNorm (Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne) : ℚ) : ℝ) ^ 2 *
      |((Algebra.norm ℚ (c0 : D.host.E) : ℚ) : ℝ)| := by
  classical
  have key : ∀ l ∈ Jsub Λ X y0, ∀ m ∈ Jsub Λ X y0,
      ∃ c : 𝓞 D.host.E, (c : D.host.E) = star m * l * c0 := by
    intro l hl m hm
    obtain ⟨c, hc⟩ := pair_int (Λ := Λ) (X := X) (y0 := y0) hun hiso horth hl hm
    refine ⟨c, ?_⟩
    rw [hc, hc0]
    simp only [brS, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
    ring
  set J := Jfrac Λ X y0 hun hiso horth hy0 c0 hc0 hc0ne with hJ
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (c0 : D.host.E) * J ≤ 1 := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hx
    obtain ⟨c, hc⟩ := key l hl 1 (one_mem_J Λ X y0 hy0)
    rw [FractionalIdeal.mem_one_iff]
    refine ⟨c, ?_⟩
    show (c : D.host.E) = (c0 : D.host.E) * l
    rw [hc, star_one, one_mul, mul_comm]
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hmemI : ∀ i : 𝓞 D.host.E, i ∈ I → ∃ l ∈ Jsub Λ X y0, (i : D.host.E) = c0 * l := by
    intro i hi
    have h1 : algebraMap (𝓞 D.host.E) D.host.E i ∈
        (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
      FractionalIdeal.mem_coeIdeal_of_mem (S := nonZeroDivisors (𝓞 D.host.E)) hi
    rw [hI, FractionalIdeal.mem_singleton_mul] at h1
    obtain ⟨l, hl, h⟩ := h1
    exact ⟨l, hl, h⟩
  have hc0I : c0 ∈ I := by
    have h1 : (c0 : D.host.E) ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      rw [hI, FractionalIdeal.mem_singleton_mul]
      exact ⟨1, one_mem_J Λ X y0 hy0, (mul_one _).symm⟩
    rw [FractionalIdeal.mem_coeIdeal] at h1
    obtain ⟨x', hx', hx'e⟩ := h1
    have hx'c : x' = c0 := IsFractionRing.injective (𝓞 D.host.E) D.host.E hx'e
    rw [← hx'c]
    exact hx'
  set e := TorsionTotientBound.cO D.host.E with he
  have hcoe : ∀ d : 𝓞 D.host.E, ((e d : 𝓞 D.host.E) : D.host.E) = star (d : D.host.E) := fun d => rfl
  have hA : Ideal.span {c0} * (I * Ideal.map e I) ≤ Ideal.span {c0 * e c0} := by
    rw [Ideal.span_singleton_mul_le_iff]
    intro z hz
    refine Submodule.mul_induction_on hz (fun r hr s hs => ?_) (fun a b ha hb => ?_)
    · obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_of_equiv e s).1 hs
      obtain ⟨l, hl, hrl⟩ := hmemI r hr
      obtain ⟨m, hm, hxm⟩ := hmemI x hx
      obtain ⟨c, hc⟩ := key l hl m hm
      rw [Ideal.mem_span_singleton']
      refine ⟨c, IsFractionRing.injective (𝓞 D.host.E) D.host.E ?_⟩
      show ((c * (c0 * e c0) : 𝓞 D.host.E) : D.host.E) = ((c0 * (r * e x) : 𝓞 D.host.E) : D.host.E)
      push_cast
      show (c : D.host.E) * ((c0 : D.host.E) * star (c0 : D.host.E)) =
        (c0 : D.host.E) * ((r : D.host.E) * star (x : D.host.E))
      rw [hc, hrl, hxm, star_mul']
      ring
    · rw [mul_add]
      exact Ideal.add_mem _ ha hb
  have hIne : I ≠ ⊥ := by
    intro h
    rw [h] at hc0I
    exact hc0ne ((Submodule.mem_bot _).1 hc0I)
  have hNIc : Ideal.absNorm (Ideal.map e I) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv I (Ideal.map e I) e rfl).toEquiv.symm
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hA
  rw [map_mul, map_mul, hNIc, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton, map_mul,
    normZ_cO, Int.natAbs_mul] at hdvd
  have hn0 : (Algebra.norm ℤ c0).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact Algebra.norm_ne_zero_iff.2 hc0ne
  have ha0 : Ideal.absNorm I ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hIne
  have hna : (Algebra.norm ℤ c0).natAbs ≤ Ideal.absNorm I * Ideal.absNorm I := by
    have h1 := Nat.le_of_dvd (by positivity) hdvd
    have h2 : (Algebra.norm ℤ c0).natAbs * (Algebra.norm ℤ c0).natAbs ≤
        (Algebra.norm ℤ c0).natAbs * (Ideal.absNorm I * Ideal.absNorm I) := by
      calc _ ≤ _ := h1
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left h2 (Nat.pos_of_ne_zero hn0)
  have hJn : ((Ideal.absNorm I : ℕ) : ℚ) = |Algebra.norm ℚ (c0 : D.host.E)| * FractionalIdeal.absNorm J := by
    rw [← FractionalIdeal.coeIdeal_absNorm (K := D.host.E), hI, map_mul, FractionalIdeal.absNorm_span_singleton]
  have hq : |Algebra.norm ℚ (c0 : D.host.E)| = (((Algebra.norm ℤ c0).natAbs : ℕ) : ℚ) := by
    rw [← Algebra.coe_norm_int, Nat.cast_natAbs, Int.cast_abs]
  set q := |Algebra.norm ℚ (c0 : D.host.E)| with hqdef
  set j := FractionalIdeal.absNorm J with hjdef
  have hqpos : 0 < q := by
    rw [hq]
    exact_mod_cast Nat.pos_of_ne_zero hn0
  have hmain : (1 : ℚ) ≤ j ^ 2 * q := by
    have h3 : (((Algebra.norm ℤ c0).natAbs : ℕ) : ℚ) ≤ ((Ideal.absNorm I : ℕ) : ℚ) * ((Ideal.absNorm I : ℕ) : ℚ) := by
      exact_mod_cast hna
    rw [← hq, hJn] at h3
    have h4 : q * 1 ≤ q * (j ^ 2 * q) := by nlinarith
    exact le_of_mul_le_mul_left h4 hqpos
  have hmainR : ((1 : ℚ) : ℝ) ≤ ((j ^ 2 * q : ℚ) : ℝ) := by exact_mod_cast hmain
  rw [hqdef] at hmainR
  push_cast at hmainR
  exact hmainR

end Frac

end Formalism.L2.SG.NGCut.NormalIntegrality
end
end
