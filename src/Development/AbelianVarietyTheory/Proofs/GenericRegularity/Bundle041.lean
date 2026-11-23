module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle020
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle038
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle030
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle033
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsOpenSameModel
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

theorem _root_.GlobalTheory.T.frameNorm_conjugate_points_eq_pointwise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))), (∀ Z, CBase h Z (yP Z)) → FnConj Xo c fn yP ∧ ValAtCx h yP ∧ ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ) a n, ∀ f ∈ sec Xo c a n, nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P = ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (sgOf P) (fn (sgOf P)) (ex Dw a n) f (yP Z P) := by
  first | exact @GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm | exact GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm | (intros; apply GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm <;> assumption)
end

section

open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.Reg
open scoped Matrix

attribute [local instance 1100] Subalgebra.algebra in
theorem _root_.GlobalTheory.T.exists_countable_flagSpace_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (h : GenFrEx Xo c), ∃ (ι : Type) (_ : Countable ι) (C : ι → FChart h), ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L), ∃ (i : ι) (ψ : (C i).R →ₐ[c.F] L) (z : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ (C i).y z ∧ FrBor t z y := by
  first | exact @GlobalTheory.Reg.exists_countable_atlas | exact GlobalTheory.Reg.exists_countable_atlas | (intros; apply GlobalTheory.Reg.exists_countable_atlas <;> assumption)
end

section

open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.Reg
open scoped Matrix

noncomputable section

namespace GlobalTheory.OneComp

open GlobalTheory.CompModel GlobalTheory.SupGeneric

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem wchar_zero {S : Type} [CommRing S] (t : Ix Dw → Sˣ) : wchar (ex Dw 0 0) t = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  have : ex Dw 0 0 i = 0 := by rcases i with _ | ⟨τ, i⟩ <;> simp [ex]
  rw [this, pow_zero]

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem evR_eq_natCast (hL : EvLaws Xo c) {h : GenFrEx Xo c} {χ : Rul Xo c} (hχ : χ ∈ sec Xo c 0 0) (C : FChart h)
    {L : Type} [Field L] [Algebra c.F L] (ψ : C.R →ₐ[c.F] L) {z w : FrPt Xo c L} {t : Ix Dw → Lˣ}
    (hz : FrMap ψ C.y z) (hb : FrBor t z w) (n : ℕ) (hn : evC h C.Z χ = n) : evR Xo c χ w = n := by
  have h1 : evR Xo c χ C.yg = n := by
    rw [hL.wt 0 0 χ hχ _ C.t _ _ (hL.test _ _) (hL.test _ _) C.bor, wchar_zero]
    unfold evC at hn
    rw [hn]
    simp
  have h2 : evR Xo c χ C.y = n := by
    rw [evR_of_frMap hL hχ C.R.val C.gen] at h1
    exact Subtype.ext (h1.trans (map_natCast C.R.val n).symm)
  have h3 : evR Xo c χ z = n := by rw [evR_of_frMap hL hχ ψ hz, h2, map_natCast]
  rw [hL.wt 0 0 χ hχ _ t _ _ (hL.test _ _) (hL.test _ _) hb, wchar_zero, h3]
  simp

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem exists_comp_of_charts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → ∀ (h : GenFrEx Xo c) (k : U.Comp), ∃ Z : Comp Xo c, ∀ (x : (U.X k).dom) (C : FChart h) (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap ψ C.y z → FrBor t z (U.un k x) → C.Z = Z := by
  intro E _ _ _ H Dw l Xo c σ r U hU h k
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨x₀, hx₀⟩ := (GlobalTheory.frames_isConnected E r (U.X k)).nonempty
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨C₀, ψ₀, z₀, t₀, hz₀, hb₀⟩ := hA h (CAt σ) (U.un k ⟨x₀, hx₀⟩)
  refine ⟨C₀.Z, fun x C ψ z t hz hb => ?_⟩
  by_contra hne
  obtain ⟨χ, hχ, hi, h1, h0⟩ := exists_idem_section E H Dw l Xo c hL h (hA h) C₀.Z
  have hD : Dom (E := E) 0 0 := ⟨fun τ _ _ _ => le_rfl, Even.zero⟩
  have hs := hU.2.2.2.2.1 0 0 hD χ hχ k
  rw [IdemCusp.laU_zero] at hs
  have hid : IdemCusp.IsIdemFn (U.X k) (Formalism.L2.PjFree.rdU U χ k) := by
    refine IdemCusp.isIdemFn_of_isSec _ hs ?_
    have := congrFun (IdemCusp.rdU_mul U χ χ) k
    rw [hi] at this
    exact this.symm
  have hT : Set.MapsTo (Formalism.L2.PjFree.rdU U χ k) (U.X k).dom ({0, 1} : Set ℂ) := by
    intro s hs
    rcases hid.1 _ hs with h | h <;> simp [h]
  have hc := (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected.constant_of_mapsTo
    (Set.toFinite ({0, 1} : Set ℂ)).isDiscrete hid.2.1.continuousOn hT x.2 hx₀
  have e0 := evR_eq_natCast hL hχ C ψ hz hb 0 ((h0 _ hne).trans Nat.cast_zero.symm)
  have e1 := evR_eq_natCast hL hχ C₀ ψ₀ hz₀ hb₀ 1 (h1.trans Nat.cast_one.symm)
  rw [rdU_apply, rdU_apply U χ k ⟨x₀, hx₀⟩, e0, e1] at hc
  have hc' : ((0 : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := hc
  simp at hc'

end GlobalTheory.OneComp
end
end
