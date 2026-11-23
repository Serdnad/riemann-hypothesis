module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle009
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Formalism.LocalToGlobal.ProjectiveLattices.RegModelA
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle005
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem extPt (Y : Model Xo c β) (T : CDVR) (b : O →+* T.V) (x : Sp T.Fr ⟶ Xo.XF c)
    (hx : x ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b) :
    ∃ yt : Sp T.V ⟶ Y.X, Out.jK T.V ≫ yt = x ≫ Y.j ∧ yt ≫ Y.s = spMap b := by
  haveI : IsProper Y.s := projProper _ _ _ Y.proj
  have hE : ValuativeCriterion.Existence Y.s := by
    have h1 : UniversallyClosed Y.s := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h1
    exact h1.1
  let S : ValuativeCommSq Y.s :=
    { R := T.V, K := FractionRing T.V, i₁ := x ≫ Y.j, i₂ := spMap b,
      commSq := ⟨by rw [Category.assoc]; exact hx⟩ }
  obtain ⟨⟨⟨l, hl1, hl2⟩⟩⟩ := hE S
  exact ⟨l, hl1, hl2⟩

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem sepX (Xo : Moduli Dw l) : SepXSt Xo := by
  unfold SepXSt
  have hq := Xo.qproj
  unfold IsQProjOver at hq
  obtain ⟨N, i, hi, -, hcomp⟩ := hq
  rw [← hcomp]
  haveI := hi
  infer_instance

theorem spMap_isDominant {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (hφ : Function.Injective φ) :
    IsDominant (spMap φ) := by
  unfold spMap
  constructor
  have hd : DenseRange (PrimeSpectrum.comap φ) := by
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact hd

theorem x_eq_of_inj (Xo : Moduli Dw l) {S T : Type} [CommRing S] [IsReduced S] [CommRing T] (φ : S →+* T)
    (hφ : Function.Injective φ) {f g : Sp S ⟶ Xo.X} (hs : f ≫ Xo.s = g ≫ Xo.s)
    (h : spMap φ ≫ f = spMap φ ≫ g) : f = g := by
  haveI : IsSeparated Xo.s := sepX Xo
  haveI : IsDominant (spMap φ) := spMap_isDominant φ hφ
  first
  | exact ext_of_isDominant_of_isSeparated Xo.s hs (spMap φ) h
  | exact ext_of_isDominant_of_isSeparated Xo.s hs h
  | exact ext_of_isDominant_of_isSeparated (s := Xo.s) hs (ι := spMap φ) h

end Formalism.L2.Pj
end
end

section

namespace Formalism.L2.Pj.RegC

open IsLocalRing ReciprocityTheory.ChartRestriction.G.T0

private theorem hdvr_lemma {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1) (f : FractionRing A)
    (hno : ¬ ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a) :
    ∃ a s : A, a ∈ P ∧ s ∉ P ∧ f⁻¹ * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  classical
  haveI := ReciprocityTheory.ChartRestriction.G.T0.regVert_valuationRing P hP
  obtain ⟨a0, b0, hb0, rfl⟩ := IsFractionRing.div_surjective (A := A) f
  have hb0' : algebraMap A (FractionRing A) b0 ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb0
  have h1P : (1 : A) ∉ P := (Ideal.ne_top_iff_one P).1 (Ideal.IsPrime.ne_top ‹_›)
  obtain ⟨c, hc | hc⟩ := ValuationRing.cond (algebraMap A (Localization.AtPrime P) a0)
    (algebraMap A (Localization.AtPrime P) b0)
  · obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    have h1 : algebraMap A (Localization.AtPrime P) (a0 * r) =
        algebraMap A (Localization.AtPrime P) (b0 * s) := by
      rw [map_mul, map_mul, ← hc, mul_assoc, IsLocalization.mk'_spec]
    obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)).1 h1
    have hK : algebraMap A (FractionRing A) (u * (a0 * r)) =
        algebraMap A (FractionRing A) (u * (b0 * s)) := by rw [hu]
    simp only [map_mul] at hK
    have ha0 : algebraMap A (FractionRing A) a0 ≠ 0 := by
      intro h0
      apply hno
      exact ⟨0, 1, h1P, by simp [h0]⟩
    by_cases hr : (u : A) * r ∈ P
    · refine ⟨u * r, u * s, hr, ?_, ?_⟩
      · exact P.primeCompl.mul_mem u.2 s.2
      · rw [map_mul, map_mul, inv_div, div_mul_eq_mul_div, div_eq_iff ha0]
        linear_combination -1 * hK
    · exfalso
      apply hno
      refine ⟨u * s, u * r, hr, ?_⟩
      rw [map_mul, map_mul, div_mul_eq_mul_div, div_eq_iff hb0']
      linear_combination hK
  · obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    have h1 : algebraMap A (Localization.AtPrime P) (b0 * r) =
        algebraMap A (Localization.AtPrime P) (a0 * s) := by
      rw [map_mul, map_mul, ← hc, mul_assoc, IsLocalization.mk'_spec]
    obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)).1 h1
    have hK : algebraMap A (FractionRing A) (u * (b0 * r)) =
        algebraMap A (FractionRing A) (u * (a0 * s)) := by rw [hu]
    simp only [map_mul] at hK
    exfalso
    apply hno
    refine ⟨u * r, u * s, P.primeCompl.mul_mem u.2 s.2, ?_⟩
    rw [map_mul, map_mul, div_mul_eq_mul_div, div_eq_iff hb0']
    linear_combination -1 * hK

theorem key_centre {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    [IsIntegrallyClosed A] (f : FractionRing A) (e : A) (he : e ≠ 0)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 → φ e ≠ 0 →
      ∃ v : V, φ a = v * φ b)
    (qq : Ideal A) [qq.IsPrime] (hqq : qq ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤) :
    ∃ a s : A, s ∉ qq ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  haveI : IsNoetherianRing A := by
    first
    | exact Algebra.FiniteType.isNoetherianRing O A
    | infer_instance
  refine Formalism.L2.Pj.RegB.mem_loc_of_heightOne qq f (fun P hP h1 hle => ?_)
  haveI := hP
  by_cases hv : Ideal.map (algebraMap O A) (maximalIdeal O) ≤ P
  · exact Formalism.L2.Pj.RegA.reg_vertical_e f e he hf P h1 hv
  · refine ReciprocityTheory.ChartRestriction.G.T0.reg_horizontal P hv ?_ e he f (hdvr_lemma P h1 f) hf
    intro htop
    apply hqq
    rw [eq_top_iff, ← htop]
    exact sup_le_sup_right hle _

end Formalism.L2.Pj.RegC
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section ValCrit

theorem valCrit_proj {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (hf : IsProjOver f)
    (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] (b : R →+* V) (y : Sp K ⟶ X) (hy : y ≫ f = spMap (algebraMap V K) ≫ spMap b) :
    ∃ y' : Sp V ⟶ X, y' ≫ f = spMap b ∧ spMap (algebraMap V K) ≫ y' = y := by
  obtain ⟨N, i, hi, hif⟩ := hf
  haveI : IsClosedImmersion i := hi
  haveI : IsProper (PSpace.str R N) := isProper_str R N
  have hU : UniversallyClosed (i ≫ PSpace.str R N) := inferInstance
  rw [hif] at hU
  have h2 : (ValuativeCriterion.Existence ⊓ @QuasiCompact) f := by
    rw [← UniversallyClosed.eq_valuativeCriterion]
    exact hU
  have hE : ValuativeCriterion.Existence f := h2.1
  haveI : ValuationRing V := by
    first
      | exact inferInstance
      | exact ValuationRing.of_isDiscreteValuationRing V
  let S : ValuativeCommSq f := ⟨V, K, y, spMap b, ⟨hy⟩⟩
  obtain ⟨l⟩ := (hE S).exists_lift
  exact ⟨l.l, l.fac_right, l.fac_left⟩

end ValCrit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Open

variable {D : Datum H} {l : Level H}

end Open

section Proofs

variable {D : Datum H} {l : Level H}

theorem exists_family {D : Datum H} {l : Level H} (X0 : Moduli D l) (hN : ∀ l' : Level H, Nonempty (Moduli D l')) :
    ∃ XoF : ∀ l' : Level H, Moduli D l', XoF l = X0 := by
  classical
  refine ⟨fun l' => if h : l' = l then cast (congrArg (Moduli D) h.symm) X0 else (hN l').some, ?_⟩
  first
    | (beta_reduce
       rw [dite_eq_left rfl]
       rfl)
    | simp

end Proofs

section Place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end Place

section Level

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end Level

section Definite

open Formalism.BasicNotions Formalism.MainNotions

end Definite

end Formalism.L2.Pj
end
end
