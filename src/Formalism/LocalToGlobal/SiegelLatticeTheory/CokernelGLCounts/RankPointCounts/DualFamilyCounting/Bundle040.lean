module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle038
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle012
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PushforwardOrthComplement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ReImESymmAdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.L2.SG.Pf.Cnt

theorem gluing_mass_holds : GlueMass :=
  glueMass_of' jordan_splitting_exists jordan_invariants_holds alpha_discriminant_holds local_gluing_holds gluing_product_holds

end Formalism.L2.SG.Pf.Cnt
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LatA

open Alg

variable {D : D7} (X : HidaSetting D)

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

theorem fi_smul_mem {I : FI} {x : D.host.E} (hx : x ∈ I) (o : 𝓞 D.host.E) : (o : D.host.E) * x ∈ I := by
  have h := (I : Submodule (𝓞 D.host.E) D.host.E).smul_mem o hx
  rw [Algebra.smul_def] at h
  exact h

theorem coef_span_e (y : (VS D).V) (hy : y ∈ latSpanS (fun a => aaD D a) X.eX) :
    (∀ a, (VS D).hT (X.fY a) y ∈ aaD D a) ∧ (∀ a, (VS D).hT (X.eX a) y = 0) ∧ pW X y = 0 := by
  unfold latSpanS at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, t, ht, rfl⟩ := hz
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [map_smul, hfe, smul_eq_mul]
      split_ifs with hab
      · subst hab
        simpa using ht
      · rw [mul_zero]
        exact Submodule.zero_mem (aaD D a : Submodule (𝓞 D.host.E) D.host.E)
    · rw [map_smul, X.ee, smul_zero]
    · rw [pW_smul, pW_e, smul_zero]
  | zero => exact ⟨fun a => by rw [map_zero]; exact Submodule.zero_mem (aaD D a : Submodule (𝓞 D.host.E) D.host.E), fun a => by simp, by simpa using pW_smul X 0 0⟩
  | add z w _ _ hz hw =>
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [map_add (f := _)]
      exact Submodule.add_mem (aaD D a : Submodule (𝓞 D.host.E) D.host.E) (hz.1 a) (hw.1 a)
    · rw [map_add (f := _), hz.2.1 a, hw.2.1 a, add_zero]
    · rw [pW_add, hz.2.2, hw.2.2, add_zero]
  | smul o z _ hz =>
    rw [← algebraMap_smul D.host.E o z]
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [map_smul, smul_eq_mul]
      exact fi_smul_mem (hz.1 a) o
    · rw [map_smul, hz.2.1 a, smul_zero]
    · rw [pW_smul, hz.2.2, smul_zero]

theorem pW_f (b : Fin D.R.rS) : pW X (X.fY b) = 0 := by
  unfold pW
  simp [X.ff, X.ef, ite_smul, Finset.sum_ite_eq']

theorem coef_span_f (y : (VS D).V) (hy : y ∈ latSpanS (fun a => (aaD D a)⁻¹) X.fY) :
    (∀ a, (VS D).hT (X.fY a) y = 0) ∧ (∀ a, (VS D).hT (X.eX a) y ∈ (aaD D a)⁻¹) ∧ pW X y = 0 := by
  unfold latSpanS at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, t, ht, rfl⟩ := hz
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [map_smul, X.ff, smul_zero]
    · rw [map_smul, X.ef, smul_eq_mul]
      split_ifs with hab
      · subst hab
        simpa using ht
      · rw [mul_zero]
        exact Submodule.zero_mem (((aaD D a)⁻¹ : FI) : Submodule (𝓞 D.host.E) D.host.E)
    · rw [pW_smul, pW_f, smul_zero]
  | zero => exact ⟨fun a => by simp, fun a => by rw [map_zero]; exact Submodule.zero_mem (((aaD D a)⁻¹ : FI) : Submodule (𝓞 D.host.E) D.host.E), by simpa using pW_smul X 0 0⟩
  | add z w _ _ hz hw =>
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [map_add (f := _), hz.1 a, hw.1 a, add_zero]
    · rw [map_add (f := _)]
      exact Submodule.add_mem (((aaD D a)⁻¹ : FI) : Submodule (𝓞 D.host.E) D.host.E) (hz.2.1 a) (hw.2.1 a)
    · rw [pW_add, hz.2.2, hw.2.2, add_zero]
  | smul o z _ hz =>
    rw [← algebraMap_smul D.host.E o z]
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [map_smul, hz.1 a, smul_zero]
    · rw [map_smul, smul_eq_mul]
      exact fi_smul_mem (hz.2.1 a) o
    · rw [pW_smul, hz.2.2, smul_zero]

theorem mem_hermitianStandardLattice_iff_pairing_integral (x : (VS D).V) : x ∈ (VS D).L0 ↔
    (∀ a, (VS D).hT (X.fY a) x ∈ aaD D a) ∧ (∀ a, (VS D).hT (X.eX a) x ∈ (aaD D a)⁻¹) ∧ pW X x ∈ X.Lb := by
  rw [X.Lam_split]
  constructor
  · intro hx
    obtain ⟨y, hy, f, hf, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨e, he, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨he1, he2, he3⟩ := coef_span_e X e he
    obtain ⟨hf1, hf2, hf3⟩ := coef_span_f X f hf
    have hwp := X.Lb_perp w hw
    have hwW : InW X w := fun c => hwp c
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [map_add (f := _), map_add (f := _), (hwp a).2, hf1 a, add_zero, add_zero]
      exact he1 a
    · rw [map_add (f := _), map_add (f := _), (hwp a).1, he2 a, zero_add, zero_add]
      exact hf2 a
    · rw [pW_add, pW_add, he3, hf3, pW_of_inW X hwW, zero_add, add_zero]
      exact hw
  · rintro ⟨h1, h2, h3⟩
    rw [decomp X x, add_right_comm]
    refine Submodule.add_mem_sup (Submodule.add_mem_sup ?_ h3) ?_
    · unfold latSpanS
      exact Submodule.sum_mem _ fun d _ => Submodule.subset_span ⟨d, _, h1 d, rfl⟩
    · unfold latSpanS
      exact Submodule.sum_mem _ fun d _ => Submodule.subset_span ⟨d, _, h2 d, rfl⟩

end LatA

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem ddS_ne' : ddS D ≠ 0 := Formalism.L2.SG.Pf.NcReal.JX.CovB.ddS_ne

theorem star_mem_zpow (m : ℤ) {x : D.host.E} (hx : x ∈ ddS D ^ m) : star x ∈ ddS D ^ m := by
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, Formalism.L2.SG.Pf.NcReal.JX.CovB.ddS_eq, ← FractionalIdeal.coeIdeal_pow] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
    obtain ⟨y', hy', e⟩ := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_mem_pow n y hy
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨y', hy', e⟩
  · rw [_root_.zpow_neg, zpow_natCast, Formalism.L2.SG.Pf.NcReal.JX.CovB.ddS_eq, ← FractionalIdeal.coeIdeal_pow] at hx ⊢
    exact Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_mem_inv n hx

theorem iQ_eq (b a : Fin D.R.rS) :
    iQ D b a = ((ddS D ^ ((b : ℤ) - a) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) := by
  unfold iQ aaD
  congr 1
  rw [← _root_.zpow_neg, ← zpow_add₀ ddS_ne']
  congr 1
  ring

theorem iP_eq (b a : Fin D.R.rS) :
    iP D b a = ((ddS D ^ (-((D.R.rS : ℤ) - b) - ((D.R.rS : ℤ) - a)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) := by
  unfold iP aaD
  congr 1
  rw [← zpow_add₀ ddS_ne']
  congr 1

theorem star_mem_iQ {b a : Fin D.R.rS} {x : D.host.E} (hx : x ∈ iQ D b a) : star x ∈ iQ D b a := by
  rw [iQ_eq] at hx ⊢; exact star_mem_zpow _ hx

theorem star_mem_iP {b a : Fin D.R.rS} {x : D.host.E} (hx : x ∈ iP D b a) : star x ∈ iP D b a := by
  rw [iP_eq] at hx ⊢; exact star_mem_zpow _ hx

theorem iP_comm (b a : Fin D.R.rS) : iP D b a = iP D a b := by
  rw [iP_eq, iP_eq]; congr 2; ring

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end
