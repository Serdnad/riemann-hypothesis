module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1850
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3418
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2833
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTGlueLie
variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]

theorem inr_one_mul (y : TrivSqZeroExt k k) :
    (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) * y = TrivSqZeroExt.inr y.fst := by
  ext
  · simp
  · simp

theorem fstC_inr_smul (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    fstC A₀ ((TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • e) = 0 := by
  ext c
  rw [fstC_apply]
  change ((TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) * e ((GlobalTheory.FODef.constMorV k k A₀).pull c)).fst = 0
  rw [inr_one_mul, TrivSqZeroExt.fst_inr]

theorem sndC_inr_smul (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    (sndC A₀ ((TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • e) : HdR A₀) = fstC A₀ e := by
  ext c
  change (sndC A₀ _) c = fstC A₀ e c
  rw [sndC_apply, fstC_apply]
  change ((TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) * e ((GlobalTheory.FODef.constMorV k k A₀).pull c)).snd = _
  rw [inr_one_mul, TrivSqZeroExt.snd_inr]

theorem exists_of_coords_self (hA : IsAbelianScheme A₀) (x : HdR A₀) (y : primDR A₀ →ₗ[k] k) :
    ∃ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀, fstC A₀ e = x ∧ sndC A₀ e = y :=
  exists_of_coords hA x y

theorem ext_coords_self (hA : IsAbelianScheme A₀) {e e' : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀}
    (h1 : fstC A₀ e = fstC A₀ e') (h2 : (sndC A₀ e : HdR A₀) = sndC A₀ e') : e = e' :=
  ext_coords hA h1 h2



theorem dualNumber_hodge_summand_eq_graph_coords_of_compl (hA : IsAbelianScheme A₀) (f : HdR A₀ →ₗ[k] HdR A₀)
    (E M : Submodule (TrivSqZeroExt k k)
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
    (hEM : IsCompl E M)
    (h2 : ∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ e ∈ E,
      (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl A₀).Corr e y)
    (h3 : ∀ x ∈ Fil A₀, ∃ e ∈ E, ∀ c, e ((GlobalTheory.FODef.constMorV k k A₀).pull c) =
      TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c))
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    e ∈ E ↔ (fstC A₀ e ∈ Fil A₀ ∧ (sndC A₀ e : HdR A₀) - f (fstC A₀ e) ∈ Fil A₀) := by
  have hε := fun e' ↦ And.intro (fstC_inr_smul (A₀ := A₀) e') (sndC_inr_smul (A₀ := A₀) e')
  have hc : ∀ x ∈ Fil A₀, ∃ e ∈ E, fstC A₀ e = x ∧ (sndC A₀ e : HdR A₀) = f x := by
    intro x hx
    refine (h3 x hx).elim fun e₁ hh ↦ ⟨e₁, hh.1, ?_, ?_⟩
    · ext c; rw [fstC_apply, hh.2 c, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    · ext c; show (sndC A₀ e₁) c = _; rw [sndC_apply, hh.2 c, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  have hfil : ∀ a ∈ E, fstC A₀ a ∈ Fil A₀ := fun a ha ↦ (h2 _).2 ⟨a, ha, (corr_iff_fstC hA a _).2 rfl⟩
  constructor
  · intro he
    have hx := hfil e he
    obtain ⟨e₁, he₁, h1, h1'⟩ := hc _ hx
    refine ⟨hx, ?_⟩
    have hh := exists_of_coords_self hA ((sndC A₀ e : HdR A₀) - f (fstC A₀ e)) 0
    obtain ⟨yh, hy1, -⟩ := hh
    have hεy : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • yh = e - e₁ := by
      refine ext_coords_self hA ?_ ?_
      · rw [(hε yh).1, map_sub, h1, sub_self]
      · have h5 := (hε yh).2
        rw [hy1] at h5
        show (sndC A₀ _ : HdR A₀) = sndC A₀ (e - e₁)
        rw [h5, map_sub]
        show _ = (sndC A₀ e : HdR A₀) - (sndC A₀ e₁ : HdR A₀)
        rw [h1']
    have hmem : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • yh ∈ E := hεy ▸ E.sub_mem he he₁
    have hyt : yh ∈ E ⊔ M := hEM.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨a, ha, m, hm, hsum⟩ := Submodule.mem_sup.1 hyt
    have hεm : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • m ∈ E := by
      have := E.sub_mem hmem (E.smul_mem (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) ha)
      rwa [← hsum, smul_add, add_sub_cancel_left] at this
    have hm0 : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • m = 0 :=
      (Submodule.disjoint_def.1 hEM.disjoint) _ hεm (M.smul_mem _ hm)
    have hm1 : fstC A₀ m = 0 := by rw [← (hε m).2, hm0, map_zero]
    rw [← hy1, ← hsum, map_add (f := _), hm1, add_zero]
    exact hfil a ha
  · rintro ⟨hx, hz⟩
    obtain ⟨e₁, he₁, h1, h1'⟩ := hc _ hx
    obtain ⟨e₂, he₂, h2a, -⟩ := hc _ hz
    have : e = e₁ + (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • e₂ := by
      refine ext_coords_self hA ?_ ?_
      · rw [map_add (f := _), (hε e₂).1, h1, add_zero]
      · show (sndC A₀ e : HdR A₀) = (sndC A₀ (e₁ + _) : HdR A₀)
        rw [map_add (f := _)]
        show _ = (sndC A₀ e₁ : HdR A₀) + (sndC A₀ (_ • e₂) : HdR A₀)
        rw [(hε e₂).2, h1', h2a, add_sub_cancel]
    rw [this]
    exact E.add_mem he₁ (E.smul_mem _ he₂)

theorem fo_summand_coords : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (f : HdR A₀ →ₗ[k] HdR A₀) (E : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀)), (∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀), IsCompl E M) → (∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ e ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl A₀).Corr e y) → (∀ x ∈ Fil A₀, ∃ e ∈ E, ∀ c, e ((GlobalTheory.FODef.constMorV k k A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c)) → ∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀, e ∈ E ↔ (GlobalTheory.HTGlueLie.fstC A₀ e ∈ Fil A₀ ∧ (GlobalTheory.HTGlueLie.sndC A₀ e : HdR A₀) - f (GlobalTheory.HTGlueLie.fstC A₀ e) ∈ Fil A₀) := fun _ _ _ _ hA f E ⟨M, hEM⟩ h2 h3 e ↦
  dualNumber_hodge_summand_eq_graph_coords_of_compl hA f E M hEM h2 h3 e

end GlobalTheory.HTGlueLie
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlueLie

section Coords

variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]

theorem fstC_push_sub {V : Type} [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    (g : A₀ ⟶ A₀) [IsMonHom g] (r : k)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) :
    fstC A₀ (push (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g e -
      algebraMap k (TrivSqZeroExt k V) r • e) = push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e := by
  rw [map_sub, fstC_push, fstC_smul]

theorem sndC_push_sub {V : Type} [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    (g : A₀ ⟶ A₀) [IsMonHom g] (r : k)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) :
    sndC A₀ (push (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g e -
      algebraMap k (TrivSqZeroExt k V) r • e) = sndC A₀ e ∘ₗ primPull (dp0 k) (𝟙 _) g - r • sndC A₀ e := by
  rw [map_sub, sndC_push, sndC_smul]

theorem proj_comp_sub {d : ℕ} {M : Type*} [AddCommGroup M] [Module k M] (a : M →ₗ[k] (Fin d → k))
    (P : M →ₗ[k] M) (r : k) (j : Fin d) :
    LinearMap.proj j ∘ₗ (a ∘ₗ P - r • a) = (LinearMap.proj j ∘ₗ a) ∘ₗ P - r • (LinearMap.proj j ∘ₗ a) := by
  ext; simp



theorem push_sub_mem_glueFil_iff {d : ℕ} (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) (g : A₀ ⟶ A₀) [IsMonHom g] (r : k)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) :
    push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) g e -
        algebraMap k (TrivSqZeroExt k (Fin d → k)) r • e ∈ GlobalTheory.HTGlue.glueFil A₀ f ↔
      push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e ∈ Fil A₀ ∧
      ∀ j, push (dp0 k) (𝟙 _) g (LinearMap.proj j ∘ₗ sndC A₀ e) - r • (LinearMap.proj j ∘ₗ sndC A₀ e) -
        f j (push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e) ∈ Fil A₀ := by
  rw [mem_glueFil_iff, fstC_push_sub]
  refine and_congr Iff.rfl (forall_congr' fun j ↦ ?_)
  have h0 := sndC_push_sub (V := Fin d → k) g r e
  rw [h0, proj_comp_sub]
  rfl



theorem sub_sum_mem_glueFil_iff {d a : ℕ} (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀))
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (w : Fin a → Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k)))
      (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) :
    e - ∑ i, w i ∈ GlobalTheory.HTGlue.glueFil A₀ f ↔
      fstC A₀ e - ∑ i, fstC A₀ (w i) ∈ Fil A₀ ∧
      ∀ j, (LinearMap.proj j ∘ₗ sndC A₀ e - ∑ i, LinearMap.proj j ∘ₗ sndC A₀ (w i)) -
        f j (fstC A₀ e - ∑ i, fstC A₀ (w i)) ∈ Fil A₀ := by

  rw [mem_glueFil_iff, map_sub, map_sum]
  refine and_congr Iff.rfl (forall_congr' fun j ↦ ?_)
  have hs : ∀ h : Fin a → (primDR A₀ →ₗ[k] (Fin d → k)),
      LinearMap.proj j ∘ₗ ∑ x, h x = ∑ x, LinearMap.proj j ∘ₗ h x := fun h ↦ by
    ext c; simp [LinearMap.sum_apply]

  rw [map_sub, map_sum, LinearMap.comp_sub, hs]

variable (f : HdR A₀ →ₗ[k] HdR A₀)
  (E : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
  (hE : ∀ e, e ∈ E ↔ (fstC A₀ e ∈ Fil A₀ ∧ (sndC A₀ e : HdR A₀) - f (fstC A₀ e) ∈ Fil A₀))
include hE


theorem push_sub_mem_iff (g : A₀ ⟶ A₀) [IsMonHom g] (r : k)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) g e -
        algebraMap k (TrivSqZeroExt k k) r • e ∈ E ↔
      push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e ∈ Fil A₀ ∧
      push (dp0 k) (𝟙 _) g (sndC A₀ e) - r • (sndC A₀ e : HdR A₀) -
        f (push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e) ∈ Fil A₀ := by
  rw [hE, fstC_push_sub, sndC_push_sub]
  rfl


theorem push_mem_iff (g : A₀ ⟶ A₀) [IsMonHom g]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) g e ∈ E ↔
      push (dp0 k) (𝟙 _) g (fstC A₀ e) ∈ Fil A₀ ∧
      push (dp0 k) (𝟙 _) g (sndC A₀ e) - f (push (dp0 k) (𝟙 _) g (fstC A₀ e)) ∈ Fil A₀ := by
  rw [hE, fstC_push, sndC_push]
  rfl


theorem sub_sum_mem_iff {a : ℕ}
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀)
    (w : Fin a → Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    e - ∑ i, w i ∈ E ↔ fstC A₀ e - ∑ i, fstC A₀ (w i) ∈ Fil A₀ ∧
      ((sndC A₀ e : HdR A₀) - ∑ i, (sndC A₀ (w i) : HdR A₀)) - f (fstC A₀ e - ∑ i, fstC A₀ (w i)) ∈ Fil A₀ := by

  rw [hE, map_sub, map_sub, map_sum, map_sum]

omit hE

end Coords

end GlobalTheory.HTGlueLie
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.GmPhiBij

theorem inj (q : ℕ) [NeZero q] (R : Type) [CommRing R] (hq : IsUnit (q : R)) (i : ℤ) : Function.Injective (gmPhi q R i) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  refine GlobalTheory.T.class_zero_of_geometric_points q R hq (i - 1) a fun K _ _ f => ?_
  have hqK : IsUnit (q : K) := by simpa using hq.map f
  have hK : AIC K := fun p _ hd => IsAlgClosed.exists_root p (Polynomial.natDegree_pos_iff_degree_pos.mp hd).ne'
  apply (GlobalTheory.T.units_cohomology_bijective q K hK hqK i).1
  rw [map_zero, ← gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q f hq, ha, map_zero]

theorem surj_noeth (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A] (hA : SH A) (hq : IsUnit (q : A)) (i : ℤ) :
    Function.Surjective (gmPhi q A i) := by
  intro x
  obtain ⟨A', _, _, hint, hker, a', ha'⟩ := GlobalTheory.T.laurent_class_from_integral q A hA hq i x
  have hq' : IsUnit (q : A') := by simpa using hq.map (algebraMap A A')
  set L := (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom with hLdef
  set R := (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom with hRdef
  have hLR : L.comp (algebraMap A A') = R.comp (algebraMap A A') := by
    refine RingHom.ext fun a => ?_
    change (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A') (algebraMap A A' a) =
      (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A') (algebraMap A A' a)
    rw [AlgHom.commutes, AlgHom.commutes]
  have hq2 : IsUnit (q : A' ⊗[A] A') := by simpa using hq'.map L
  have heq : pull _ (spMap L) _ 0 a' = pull _ (spMap R) _ 0 a' := by
    apply inj q _ hq2 i
    rw [← gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q L hq', ← gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q R hq', ← ha', ← GmPhiNat.pull_spMap_comp,
      ← GmPhiNat.pull_spMap_comp, ← GmPhiNat.laurentMap_comp, ← GmPhiNat.laurentMap_comp, hLR]
  obtain ⟨a, ha⟩ := GlobalTheory.T.descent_equalizer_degree_zero q A A' hint hker hq (i - 1) a' heq
  refine ⟨a, ?_⟩
  have hsub : gmPhi q A i a - x = 0 := by
    apply GlobalTheory.T.laurent_cohomology_injective q A A' hint hker hq (fun j => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) A hA (tw q j) 1 one_pos) i
    rw [map_sub, gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q (algebraMap A A') hq, ha, ha', sub_self]
  exact sub_eq_zero.mp hsub

end GmPhiBij

theorem gmPhi_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ,
    Function.Bijective (gmPhi q A i) := by
  intro q _ A _ hA hq i
  exact ⟨GmPhiBij.inj q A hq i, GlobalTheory.T.surjective_of_noetherian_case q (fun B _ _ hB hqB j => GmPhiBij.surj_noeth q B hB hqB j) A hA hq i⟩

end GlobalTheory.EtC

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev

theorem epi_sp_field {k k' : Type} [Field k] [Field k'] (x' : Sp k' ⟶ Sp k) : Epi x' := by
  rw [← Spec.map_preimage x']
  have : Flat (Spec.map (Spec.preimage x')) := by
    rw [show Spec.preimage x' = CommRingCat.ofHom (Spec.preimage x').hom from rfl]; infer_instance
  have : Surjective (Spec.map (Spec.preimage x')) :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint k', Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem pt_ext_of_pullback {S : Scheme.{0}} {A : Over S} {k k' : Type} [Field k] [Field k'] (x : Sp k ⟶ S)
    (x' : Sp k' ⟶ Sp k) (g₁ g₂ : Over.mk x ⟶ A)
    (h : (Over.homMk x' rfl : Over.mk (x' ≫ x) ⟶ Over.mk x) ≫ g₁ =
      (Over.homMk x' rfl : Over.mk (x' ≫ x) ⟶ Over.mk x) ≫ g₂) : g₁ = g₂ := by
  haveI := epi_sp_field x'
  apply Over.OverMorphism.ext
  have := congrArg CommaMorphism.left h
  simp only [Over.comp_left, Over.homMk_left] at this
  exact (cancel_epi x').1 this

theorem exists_etLevOver_geomPt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ l : D.La → (Over.mk x ⟶ o.A), IsEtLevOver o w0 r l := by
  intro p _ D R _ b N w0 r _hN hw S s o k _ _ x
  have hw0 : w0 ≠ ⊥ := by
    intro h
    have hp : (p : 𝓞 D.F) ∈ w0 := hw.2.1
    rw [h, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)
  haveI : Finite (𝓞 D.F ⧸ w0 ^ r) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ hw0)
  obtain ⟨f, fadd, fsm, finj, fsurj⟩ := GlobalTheory.T.torsion_points_additive_parametrization p D R b N w0 r hw S s o k x
  have hmul : ∀ (c : D.O) (g h : Over.mk x ⟶ o.A), (g * h) ≫ o.act.act c = (g ≫ o.act.act c) * (h ≫ o.act.act c) := by
    intro c g h; haveI := o.act.hom c; exact MonObj.mul_comp _ _ _
  obtain ⟨l, ladd, llin, lker, lsurj⟩ := GlobalTheory.T.exists_morita_lattice_quotient_torsion p D w0 r hw.1 hw.2.1 (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun c g h => hmul c g h) (fun g => by simp only [o.act.one, Category.comp_id])
    (fun b c g => by simp only [o.act.mul, Category.assoc])
    (fun b c g => by simp only [o.act.add]; exact MonObj.comp_mul _ _ _) f fadd fsm finj fsurj
  have f0 : f 0 = 1 := by
    have h := fadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have tor : ∀ a, ∀ c ∈ w0 ^ r, f a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro a c hc
    rw [← fsm, (Ideal.Quotient.eq_zero_iff_mem).2 hc, zero_smul, f0]
  refine ⟨l, ladd, llin, fun y hy => (lker y).2 hy, ?_⟩
  intro k' _ _ x'
  refine ⟨fun y hy => ?_, fun g hg => ?_⟩
  · apply (lker y).1
    apply pt_ext_of_pullback x x'
    rw [hy]
    exact (MonObj.comp_one _).symm
  · obtain ⟨f', -, -, -, f'surj⟩ := GlobalTheory.T.torsion_points_additive_parametrization p D R b N w0 r hw S s o k' (x' ≫ x)
    let π : Over.mk (x' ≫ x) ⟶ Over.mk x := Over.homMk x' rfl
    have tor' : ∀ a, ∀ c ∈ w0 ^ r, (π ≫ f a) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro a c hc
      rw [Category.assoc, tor a c hc, MonObj.comp_one]
    let φ : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) → (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) :=
      fun a => (f'surj _ (tor' a)).choose
    have hφ : ∀ a, f' (φ a) = π ≫ f a := fun a => (f'surj _ (tor' a)).choose_spec
    have φinj : Function.Injective φ := fun a a' h =>
      finj (pt_ext_of_pullback x x' _ _ (by rw [← hφ, ← hφ, h]))
    obtain ⟨a', rfl⟩ := f'surj g hg
    obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 φinj) a'
    obtain ⟨y, hy⟩ := lsurj (f a) (tor a)
    exact ⟨y, by rw [hy, ← ha, hφ]⟩
end GlobalTheory.UPel.HT.EtLev
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledLocus

theorem exists_open_kerKilled_locus : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → KerKilledOn d G P V) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → Set.range g.base ⊆ (U : Set S') := by
  intro d S' _ G _ _ P hG hP h1 h2 hs
  refine ⟨sSup {V | GlobalTheory.KerKilledLocus.KerKilledOn d G P V}, ?_, ?_⟩
  · intro V hV
    refine GlobalTheory.T.kernelKilledOverOpen_of_local d S' G P V ?_
    intro p hp
    obtain ⟨W, hW, hpW⟩ := (TopologicalSpace.Opens.mem_sSup).1 (hV hp)
    exact ⟨W, hpW, hW⟩
  · intro T g A' _ _ φ φ₂ P' hpb hsq hP' hiso hu hamp hker
    rintro _ ⟨t, rfl⟩
    obtain ⟨V, hV, hK⟩ := GlobalTheory.T.exists_open_kernel_killed_near_point d S' G P hG hP h1 h2 hs T g A' φ φ₂ P' hpb hsq hP' hiso hu hamp hker t
    exact (TopologicalSpace.Opens.mem_sSup).2 ⟨V, hK, hV⟩

end GlobalTheory.KerKilledLocus
end
