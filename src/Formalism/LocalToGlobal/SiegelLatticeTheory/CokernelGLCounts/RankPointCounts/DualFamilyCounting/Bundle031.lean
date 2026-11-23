module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle020
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle025
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Assemble
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle010
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField Module Formalism.MainNotions.S
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem emb_surj (D : Formalism.BasicNotions.D7) : Function.Surjective D.host.emb := by
  intro φ
  unfold Formalism.BasicNotions.Host.emb Formalism.BasicNotions.Host.sigmaOf

  have key : ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, D.host.φ₀.comp (σ : D.host.E →+* D.host.E) = φ := by
    classical
    let f : (D.host.E ≃ₐ[ℚ] D.host.E) → (D.host.E →ₐ[ℚ] ℂ) :=
      fun σ => (D.host.φ₀.toRatAlgHom).comp (σ : D.host.E →ₐ[ℚ] D.host.E)
    have hinj : Function.Injective f := by
      intro σ τ h
      ext x
      have h1 : D.host.φ₀ (σ x) = D.host.φ₀ (τ x) := congrArg (fun g : D.host.E →ₐ[ℚ] ℂ => g x) h
      exact D.host.φ₀.injective h1
    have hcard : Fintype.card (D.host.E ≃ₐ[ℚ] D.host.E) = Fintype.card (D.host.E →ₐ[ℚ] ℂ) := by
      haveI : IsGalois ℚ D.host.E := inferInstance
      rw [AlgHom.card ℚ D.host.E ℂ, ← IsGalois.card_aut_eq_finrank ℚ D.host.E, Fintype.card_eq_nat_card]
    obtain ⟨σ, hσ⟩ := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩).2 φ.toRatAlgHom
    refine ⟨σ, ?_⟩
    ext x
    have h2 : D.host.φ₀ (σ x) = φ x := congrArg (fun g : D.host.E →ₐ[ℚ] ℂ => g x) hσ
    exact h2
  obtain ⟨σ, hσ⟩ := key
  refine ⟨D.host.gal σ, ?_⟩
  simp only [Equiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  exact hσ

theorem totally_positive_all : TotPosAll := by
  intro D x hx hpos φ
  obtain ⟨g, rfl⟩ := emb_surj D φ
  by_cases hg : g ∈ D.R.Psi
  · have h1 := hpos (D.eTau.symm ⟨g, hg⟩)
    simpa using h1
  · have hmem : g * D.R.cc ∈ D.R.Psi := by
      rw [Formalism.HC.Frame.mem_Psi_iff] at hg ⊢
      have h2 : g.1.2 = -1 := (Int.units_eq_one_or _).resolve_left hg
      rw [Prod.fst_mul, Prod.snd_mul, h2]
      first
        | rfl
        | decide
        | (simp [Formalism.HC.Frame.cc]; done)
        | (simp [Formalism.HC.Frame.cc, Formalism.HC.c0])
    have h1 := hpos (D.eTau.symm ⟨g * D.R.cc, hmem⟩)
    simp only [Equiv.apply_symm_apply] at h1
    have hc : D.host.conj x = x := (Formalism.MainNotions.S.Inh.tie_star D x).symm.trans hx
    have he : D.host.emb (g * D.R.cc) x = D.host.emb g x := by
      change D.host.φ₀ ((D.host.gal.symm (g * D.R.cc)) x) = D.host.φ₀ ((D.host.gal.symm g) x)
      rw [map_mul, AlgEquiv.mul_apply]
      congr 2
    rw [he] at h1
    exact h1

end Formalism.L2.SG.Pf.Cnt.R1

namespace Formalism.L2.SG.Pf.Cnt


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem rational_pair_holds : RatPair := ratPair_of R1.totally_positive_all

end Formalism.L2.SG.Pf.Cnt
end
end

section

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mmInt_of_EZ {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word}
    (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    {F0 : FlagG (VS D) D.R.rS (Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hR : IsRowReps D F0 what₂)
    {Z : MatZ D} {F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')} (hz : F'.zt = F'.fl.z) (hZ : ZhatL (lf D F0) F' = Z)
    (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z)) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : IsRowLat D F0 Λ) (hE : F' ∈ EZ (Tn u') F0 Λ Z) :
    Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') := by
  have hG := (((mmChar_of local_unimodular_holds) D u u' hT F0 what₂ hR Z F' hz hZ hP).2 Λ).mp ⟨hΛ, hE⟩
  by_contra hI
  rw [Formalism.L2.SG.Pf.Asm.glueSet_eq_empty (U := UPair D F0 F') hI] at hG
  exact hG

end Formalism.L2.SG.Pf.Cnt
end
