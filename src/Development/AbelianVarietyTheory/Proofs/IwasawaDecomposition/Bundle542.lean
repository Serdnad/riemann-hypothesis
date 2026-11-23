module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle103
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle016
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
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
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SvalEqZeroOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TriplesAlong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem mem_V_of_forall (W : ValuationSubring ℂ) (h : ∀ p : ℕ, p.Prime → (p : ℂ) ∉ W.nonunits) (x : c.F) :
    x ∈ c.V W := by
  have hv1 : ∀ n : ℕ, n ≠ 0 → W.valuation (n : ℂ) = 1 := by
    intro n hn
    induction n using Nat.recOnMul with
    | zero => exact absurd rfl hn
    | one => simp
    | prime p hp =>
      refine le_antisymm ((W.valuation_le_one_iff _).2 (natCast_mem W p)) (not_lt.1 fun hlt => h p hp ?_)
      exact (W.mem_nonunits_iff).2 hlt
    | mul a b iha ihb =>
      have ha : a ≠ 0 := left_ne_zero_of_mul hn
      have hb : b ≠ 0 := right_ne_zero_of_mul hn
      rw [Nat.cast_mul, map_mul, iha ha, ihb hb, one_mul]
  have hvi : ∀ n : ℤ, n ≠ 0 → ((n : ℂ))⁻¹ ∈ W := by
    intro n hn
    have hn' : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
    have e : W.valuation (n : ℂ) = 1 := by
      rcases Int.natAbs_eq n with h1 | h1
      · rw [h1, Int.cast_natCast]; exact hv1 _ hn'
      · rw [h1, Int.cast_neg, Int.cast_natCast, Valuation.map_neg]; exact hv1 _ hn'
    refine (W.valuation_le_one_iff _).1 ?_
    rw [map_inv₀, e, inv_one]
  haveI := c.fin
  obtain ⟨n, hn, hint⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) (z := x)
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).mpr (Algebra.IsAlgebraic.isAlgebraic _))
  let i : c.F →+* ℂ := c.F.val.toRingHom
  have h1 : _root_.IsIntegral ℤ (i (n • x)) := hint.map i.toIntAlgHom
  have h2 : _root_.IsIntegral W (i (n • x)) := h1.tower_top
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have h3 : i (n • x) ∈ W := by
    have hw' : (w : ℂ) = i (n • x) := hw
    rw [← hw']; exact w.2
  have h4 : i x = ((n : ℂ))⁻¹ * i (n • x) := by
    have hn0 : (n : ℂ) ≠ 0 := Int.cast_ne_zero.2 hn
    rw [zsmul_eq_mul, map_mul, map_intCast, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  change i x ∈ W
  rw [h4]
  exact W.mul_mem _ _ (hvi n hn) h3

theorem isOpenImmersion_j (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype) : IsOpenImmersion Y.j := by
  by_cases h : ∃ p : ℕ, p.Prime ∧ (p : ℂ) ∈ W.nonunits
  · obtain ⟨p, hp, hW⟩ := h
    exact GlobalTheory.LocM.BaseMdl.isOpenImmersion_j hp hW Y
  · push_neg at h
    have hbij : Function.Bijective (c.V W).subtype :=
      ⟨Subtype.val_injective, fun x => ⟨⟨x, mem_V_of_forall W h x⟩, rfl⟩⟩
    have h1 : IsIso (CommRingCat.ofHom (c.V W).subtype) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hbij
    have : IsIso (spMap (c.V W).subtype) := by
      unfold spMap; infer_instance
    have := Y.jQ_open
    unfold Model.j
    infer_instance

end GlobalTheory.TriplesAlong

namespace GlobalTheory.TriplesAlong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end GlobalTheory.TriplesAlong

end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ArcChartExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sabMap_cast_φ {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f₁ f₂ : S' ⟶ S} (h : f₁ = f₂)
    (n : SABMap t' t f₁) : (h ▸ n).φ = n.φ := by
  subst h; rfl

theorem exists_sab_cancel_id {S S' : Scheme.{0}} {t : SAB H S} {t' t'' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (n : SABMap t'' t f) : ∃ m' : SABMap t'' t' (𝟙 S'), n.φ = m'.φ ≫ m.φ := by
  obtain ⟨m', hm'⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := 𝟙 S') m ((Category.id_comp f).symm ▸ n)
  exact ⟨m', (sabMap_cast_φ (Category.id_comp f).symm n).symm.trans hm'⟩

end GlobalTheory.ArcChartExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.ArcBuild

open GlobalTheory.TauTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {T : CDVR} {t : SAB H (Sp T.V)} (P : PELUnif (maximalIdeal T.V) t) {ϖ : T.V} (hϖ : Irreducible ϖ)

def qv : P.D.toPre.X → ℤ := fun χ => (QForm.exists_QVal hϖ P.D χ).choose

theorem isQ_qv : QForm.IsQ P.D.toPre ϖ (qv P hϖ) := fun χ => (QForm.exists_QVal hϖ P.D χ).choose_spec

def beF : LinearMap.BilinForm ℤ P.D.toPre.X :=
  LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ P.D (isQ_qv P hϖ) a b)
    (fun a a' b => by simp [map_add (f := _)]) (fun n a b => by simp [map_zsmul])
    (fun a b b' => by simp [map_add (f := _)]) (fun n a b => by simp [map_zsmul])

theorem beF_symm (a b : P.D.toPre.X) : beF P hϖ a b = beF P hϖ b a := QForm.bOf_comm P.D a b

theorem beF_self (a : P.D.toPre.X) : beF P hϖ a a = 2 * qv P hϖ a :=
  (QForm.two_Q_eq hϖ P.D (isQ_qv P hϖ) a).symm

theorem beF_adj (x : 𝓞 E) (a b : P.D.toPre.X) : beF P hϖ (x • a) b = beF P hϖ a (H.bar x • b) :=
  letI := H.starRing
  QForm.bOf_balance hϖ P.D GlobalTheory.abelianSchemeLaws_all.1 P.oD (isQ_qv P hϖ) x a b

theorem beF_w0 (a : P.D.toPre.X) : beF P hϖ a (H.w0 • a) = qv P hϖ a := by
  have h₁ := beF_adj P hϖ H.w0 a a
  have hb : H.bar H.w0 = 1 - H.w0 := by rw [HostModel.cmHost_bar_halfIntegerGenerator]
  rw [hb, sub_smul, one_smul, map_sub, beF_symm P hϖ (H.w0 • a) a] at h₁
  have h₂ := beF_self P hϖ a
  omega

def piK : (FractionRing T.V)ˣ :=
  Units.mk0 (algebraMap T.V (FractionRing T.V) ϖ)
    ((map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 hϖ.ne_zero)

def tF (a b : P.D.toPre.X) : (FractionRing T.V)ˣ := piK hϖ ^ (-(beF P hϖ a b))

theorem cmIdempotent_add_star_eq_one : letI := H.starRing; H.w0 + star H.w0 = 1 := halfUnit_add_star H

abbrev D0 : DegPre T.V := letI := H.starRing; GlobalTheory.TauTwist.twist P.D.toPre H.w0 (tF P hϖ)

section ThetaShiftProofs

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  (Y : Model Xo c β) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (m : SABMap t Y.t y)



end ThetaShiftProofs

end GlobalTheory.ArcBuild
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.IntFam

def IntegralCharts {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (J : (Spec (CommRingCat.of (FractionRing R)) ⟶ D.P.A.left) → D.P.L.ι) : Prop :=
  ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
    p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))

end GlobalTheory.IntFam
end
end
