module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle069
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle042
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFamilyMemberFunctionalNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem exists_extend_embedding {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K] [Algebra F K]
    (σ : F →+* ℂ) : ∃ em : K →+* ℂ, em.comp (algebraMap F K) = σ := by
  letI : Algebra F ℂ := σ.toAlgebra
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  let f : K →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨f.toRingHom, RingHom.ext fun x => f.commutes x⟩

theorem killQ_of_gamAt : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → KillQ h j ka CR Tt cc := by
  intro hK D T h j ka CR Tt cc hG hj hm K₁ _ _ _ d hd F hF
  have key : ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
      (∀ k, rdU (T.U j σ) F.1 k ∈ ((T.U j σ).X k).SSgt (laU (T.U j σ) (wtA ka) ka.n k) (WeightFamilies.c1 D CR Tt cc j)) →
      cfOf d.yF d.μ d.jj F.1 = 0 := by
    intro σ hσ hr
    obtain ⟨em, rfl⟩ := exists_extend_embedding (K := K₁) σ
    have hc : F.1 ∈ T.C j ka := cutR_le T.C j ka F.2
    exact GlobalTheory.T.cmArcFunctional_vanishes_low_fourierJacobi hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d _ _ _ em _
      (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) (wtA ka) ka.n hd hσ (h.unf j hj _ hσ) (dom_wtA ka)
      (GlobalTheory.TransvPrinc.transvIn_of_hasPrinc _ _ _ _ (T.Q.Xo j) T.Q.c _ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) (wtA ka) ka.n
        (hG j hj _ hσ) (h.chiTriv j hj _ hσ _ _ (dom_wtA ka))) F.1 hc.1 hr
  exact key T.σ₀ T.good_σ₀ ((GlobalTheory.T.mem_forms_low_coeffs_vanish_iff_fourierJacobi D T h j ka CR Tt cc hj hm F).2.1 hF)

end GlobalTheory.ArcCM
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

theorem _root_.GlobalTheory.T.cmArcDatumFamily_functional_bounded_linear_on_cuspForms :
    Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ)
    (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (large₂ : SizeData₂ D),
    GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m →
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁), FamQ T j ka CR Tt cc K₁ d →
    ∃ φ : @LinearMap T.Q.c.F T.Q.c.F _ _ (RingHom.id T.Q.c.F) ((recB h).Cusp j ka) K₁
        ((recB h).acgC j ka).toAddCommMonoid _ ((recB h).modC j ka) _,
      (∀ F, φ F = cfOf d.yF d.μ d.jj F.1) ∧
      @NumGood T.Q.c.F ((recB h).Cusp j ka) _ _ ((recB h).acgC j ka) ((recB h).modC j ka)
        {F | F ∈ (recB h).Mlat j ka} (fun σ F => (recB h).supN j ka σ F)
        (beOf D.host.E (nAt D j ka CR Tt cc) (absA (T.Q.Dw j) (wtA ka)))
        (CarchAt D j ka CR Tt cc) (BdegAt large₂ j ka CR Tt cc) K₁ _ _ _ φ := by
  exact @GlobalTheory.ArcCM.numGood_of_famQ
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_familyMember_functional_ne_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c c.F.val.toRingHom r) (k : U.Comp) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ w : ℝ), ModelsAt Xo c → Formalism.L2.PjFree.IsUnf U → l.A = 1 → 3 ≤ r → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (Formalism.L2.PjFree.laU U a' n k) gm = 1) → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → Xx.g = l.M → 0 < c₁ → ((absA Dw a' : ℝ) + (fdeg E : ℝ) * n + r ≤ w) → ∀ F ∈ sec Xo c a' n, (∀ k', rdU U F k' ∈ (U.X k').SS (Formalism.L2.PjFree.laU U a' n k')) → rdU U F k ∉ (U.X k).SSgt (Formalism.L2.PjFree.laU U a' n k) c₁ → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra c.F K₁) (d : ArcDatum Xo c K₁), Fam (nQ E r l.M Xx.NA Xx.NC c₁ w) (LaQ E r Dw.q l.M Xx.NA Xx.NC c₁ w) c₁ d ∧ cfOf d.yF d.μ d.jj F ≠ 0 := by
  first | exact @GlobalTheory.ArcDetect.exists_fam_cfOf_ne_zero | exact GlobalTheory.ArcDetect.exists_fam_cfOf_ne_zero | (intros; apply GlobalTheory.ArcDetect.exists_fam_cfOf_ne_zero <;> assumption)
end
