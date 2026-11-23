module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
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
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle001
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem _root_.GlobalTheory.T.exists_smooth_affine_presentation_pair : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData) (U : X.affineOpens), Smooth g → Smooth (Z.subschemeι ≫ g) → ∃ φ : k →+* Γ(X, U.1), φ.Smooth ∧ ((Ideal.Quotient.mk (Z.ideal U)).comp φ).Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart | exact GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.Glob.ResKCoords

theorem isCoords_basicOpen_of_away :
    ∀ (K : Type) [Field K] (Y : Scheme.{0}) (g : Y ⟶ Sp K) (U : Y.affineOpens) (s : Γ(Y, U.1)) {n : ℕ}
      (x : Fin n → Γ(Y, U.1)),
      (letI := secAlgebra g U.1;
        ∀ (B : Type) [CommRing B] [Algebra Γ(Y, U.1) B] [Algebra K B] [IsScalarTower K Γ(Y, U.1) B]
          [IsLocalization.Away s B],
          LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) ∧
            Submodule.span B (Set.range fun i =>
              KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) = ⊤) →
        IsCoords g (Y.basicOpen s) (fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)) := by
  intro K _ Y g U s n x h
  letI aU : Algebra K Γ(Y, U.1) := secAlgebra g U.1
  letI aB : Algebra K Γ(Y, Y.basicOpen s) := secAlgebra g (Y.basicOpen s)
  letI aUB : Algebra Γ(Y, U.1) Γ(Y, Y.basicOpen s) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op).hom.toAlgebra
  haveI tower : IsScalarTower K Γ(Y, U.1) Γ(Y, Y.basicOpen s) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appLE ⊤ (Y.basicOpen s) (fun _ _ => trivial)).hom = _
    have e : g.appLE ⊤ U.1 (fun _ _ => trivial) ≫ Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op =
        g.appLE ⊤ (Y.basicOpen s) (fun _ _ => trivial) := by
      exact Scheme.Hom.appLE_map _ _ _
    rw [← e]
    rfl
  haveI loc : IsLocalization.Away s Γ(Y, Y.basicOpen s) := U.2.isLocalization_basicOpen s
  exact h Γ(Y, Y.basicOpen s)

end GlobalTheory.CompanionTheory.Glob.ResKCoords
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.ResKCoords

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

theorem kaehler_atPrime_of_away (K A : Type) [Field K] [CommRing A] [Algebra K A] (D : ℕ) (s : Set A)
    (hs : Ideal.span s = ⊤)
    (h : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t))
    (P : Ideal A) [P.IsPrime] :
    Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  obtain ⟨t, ht, htP⟩ : ∃ t ∈ s, t ∉ P := by
    by_contra hc
    push_neg at hc
    exact (‹P.IsPrime›).ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  have hle : Submonoid.powers t ≤ P.primeCompl := by
    rintro _ ⟨n, rfl⟩
    exact fun hm => htP (‹P.IsPrime›.mem_of_pow_mem n hm)
  letI : Algebra (Localization.Away t) (Localization.AtPrime P) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers t) P.primeCompl hle
  haveI : IsScalarTower A (Localization.Away t) (Localization.AtPrime P) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  haveI : IsScalarTower K (Localization.Away t) (Localization.AtPrime P) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply K A (Localization.Away t),
        ← IsScalarTower.algebraMap_apply A (Localization.Away t) (Localization.AtPrime P),
        ← IsScalarTower.algebraMap_apply K A (Localization.AtPrime P)]
  haveI := IsLocalization.isLocalization_of_submonoid_le (Localization.Away t) (Localization.AtPrime P)
    (Submonoid.powers t) P.primeCompl hle
  haveI : Algebra.FormallyEtale (Localization.Away t) (Localization.AtPrime P) :=
    Algebra.FormallyEtale.of_isLocalization
      (P.primeCompl.map (algebraMap A (Localization.Away t)))
  haveI := h t ht
  haveI : Nontrivial (Localization.Away t) :=
    (algebraMap (Localization.Away t) (Localization.AtPrime P)).domain_nontrivial
  haveI : Algebra.IsStandardSmooth K (Localization.Away t) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D
  have r := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := K)
    (S := Localization.Away t) D
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (Localization.Away t)
    (Localization.AtPrime P)
  refine ⟨.of_equiv e, .equiv e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_baseChange, Module.finrank, r]
  simp

theorem finitePresentation_of_away (K A : Type) [Field K] [CommRing A] [Algebra K A] (D : ℕ) (s : Set A)
    (hs : Ideal.span s = ⊤)
    (h : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t)) :
    Algebra.FinitePresentation K A := by
  refine RingHom.finitePresentation_algebraMap.1
    (RingHom.finitePresentation_ofLocalizationSpanTarget (algebraMap K A) s hs fun r => ?_)
  haveI := h r.1 r.2
  haveI : Algebra.IsStandardSmooth K (Localization.Away r.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D
  rw [← IsScalarTower.algebraMap_eq K A (Localization.Away r.1)]
  exact (RingHom.finitePresentation_algebraMap).2 inferInstance

theorem finitePresentation_and_kaehler_atPrime :
    ∀ (K : Type) [Field K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K), SmoothOfRelativeDimension D g →
      ∀ (U : Y.affineOpens) (P : Ideal Γ(Y, U.1)) [P.IsPrime],
      letI := secAlgebra g U.1
      Algebra.FinitePresentation K Γ(Y, U.1) ∧
        Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
        Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
        Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  intro K _ D Y g hg U P _
  letI := secAlgebra g U.1
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) g hg
    ⟨⊤, isAffineOpen_top _⟩ U (fun _ _ => trivial)
  have key : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t) := by
    intro t ht
    have h2 := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := D)).2
      _ (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv (h' t ht)
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    rw [IsScalarTower.algebraMap_eq K Γ(Y, U.1) (Localization.Away t)]
    exact h2
  exact ⟨finitePresentation_of_away K _ D s hs key, kaehler_atPrime_of_away K _ D s hs key P⟩

end GlobalTheory.CompanionTheory.ResKCoords
end
end
