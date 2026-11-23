module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2454
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle107
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle031
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

theorem _root_.GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z), (∀ (τ : Psi H) (s : FlatSec U ξ Z τ), P.degLie τ.1 = -s.deg) ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 → Dw.mult τ = 0 := by
  first | exact @GlobalTheory.DefPt.degLie_eq_neg_deg_flat | exact GlobalTheory.DefPt.degLie_eq_neg_deg_flat | (intros; apply GlobalTheory.DefPt.degLie_eq_neg_deg_flat <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.measure_heightShell_le_isotropicFrame_quotient : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ (μ : Measure (GAd σ J)) (D : Set (GAd σ J)), μ.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) : Subgroup (GAd σ J)) D μ → ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ j : ℕ, μ.restrict D {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} ≤ B * ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) := by
  first | exact @GlobalTheory.ResidueEisenstein.measure_shell_le | exact GlobalTheory.ResidueEisenstein.measure_shell_le | (intros; apply GlobalTheory.ResidueEisenstein.measure_shell_le <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem GlobalTheory.DegVal.compDeg_between : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → Proport U → EqVolume U → ∀ u : GlobalTheory.AllWt.Weight Dw, (∀ τ, StrictAnti (u τ)) → (∀ τ, StrictAnti (uPrime Dw u τ)) → (∀ Z, BirOn U Z (wtOf Dw u 0)) → (∀ Z, ValMult U Z (wtOf Dw u 0) (wtOf Dw (uPrime Dw u) 0)) → ∀ Z Z' : Comp Xo c, delPrime U Z' u ≤ compDeg U Z (wtOf Dw u 0) ∧ (compDeg U Z (wtOf Dw u 0) : ℝ) ≤ delPrime U Z' u / (1 - rhoB Dw u) := by
  intro E _ _ _ H Dw l Xo c r U hU hP hV u hu hu' hB hM Z Z'
  have h1 : 0 < 1 - rhoB Dw u := sub_pos.2 (rhoOf_lt_one hu' hu)
  have h2 : ∀ la, topDeg U Z' la = topDeg U Z la := fun la => by rw [topDeg, topDeg, hV Z' Z]
  constructor
  · rw [delPrime, h2]
    have hlow := GlobalTheory.T.cuspFormGrowth_le_imageDegree_lowerWeight E H Dw l Xo c r U hU Z (wtOf Dw u 0) (wtOf Dw (uPrime Dw u) 0) (even_wtOf u 0)
      (even_wtOf _ 0) (by rw [hP Z u hu]; exact ENNReal.ofReal_ne_top) (hB Z) (hM Z)
    rw [hP Z _ hu', ← ENNReal.ofReal_natCast] at hlow
    exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).1 hlow
  · rw [delPrime_eq U Z' (vdm_pos hu).ne', mul_div_cancel_left₀ _ h1.ne', h2]
    exact GlobalTheory.DegTop.compDeg_le hP Z hu
end
end

section

open NumberField

theorem _root_.GlobalTheory.T.exists_selfDual_lattice_cmHomomorphisms_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∃ Λ : Submodule (𝓞 E) (Fin p → E), Λ.FG ∧ (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) ∧
      (∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
        ∀ d : Fin p → E, d ∈ Λ ↔ ∀ c ∈ Λ, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) ∧
      ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          FB.eigLat X.B.t.act τ = Submodule.span (𝓞 K)
            {w | ∃ c ∈ Λ, ∃ e ∈ FP.eigLat (X.A true).t.act τ, w = ∑ a, τE (c a) • MP a e} := by
  first | exact @GlobalTheory.FlatCM.HomLat.exists_selfDual_lieSpan | exact GlobalTheory.FlatCM.HomLat.exists_selfDual_lieSpan | (intros; apply GlobalTheory.FlatCM.HomLat.exists_selfDual_lieSpan <;> assumption)
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.definite_cuspForms_finite_regularRepresentation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), (M.p0 = 0 ∨ M.p0 = r) → ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → Module.Finite ℂ (M.cusp ka) ∧ ∀ H : Subgroup U, LevelHyp (sub M H) → (∃ n : ℕ, GlobalTheory.BadCount.EmbReg ρ H n ∧ n * Nat.card H = finrank ℂ (M.cusp ka)) ∧ ∀ lam : H →* ℂˣ, Nat.card H * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) = finrank ℂ (M.cusp ka) := by
  first | exact @GlobalTheory.ShareOn.Definite.share_definite | exact GlobalTheory.ShareOn.Definite.share_definite | (intros; apply GlobalTheory.ShareOn.Definite.share_definite <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
namespace GlobalTheory.RefSum

theorem nuBetween_sum_and_eLoc_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (cx : Lt1 Dw → ℕ), (∀ A B : Lt1 Dw → ℝ, (∀ f, FacBetween Xo la f (cx f) (A f) (B f)) → NuBetween Xo la cx (∑ f, A f) (∑ f, B f) ∧ ∃ n : ℕ, NuBetween Xo la cx n (n + (∑ f, (B f - A f) + 1))) ∧ ∀ b : ℝ, OscLe Xo c p cx b → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Comp Xo c), (letI := H.starRing; eLoc Y Z la cx ≤ (b : EReal)) := by
  intro E _ _ _ H Dw l Xo c p _ la cx
  letI := H.starRing
  have hcs : ∀ g : Lt1 Dw → ℝ, (((∑ f, g f : ℝ)) : EReal) = ∑ f, ((g f : ℝ) : EReal) := fun g =>
    map_sum (⟨⟨((↑) : ℝ → EReal), EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) g Finset.univ
  refine ⟨fun A B hAB => ⟨fun T io e ho y => ⟨?_, fun ha => ?_⟩, ?_⟩, ?_⟩
  · rw [hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).1
  · rw [hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).2 ha
  · set s : ℝ := ∑ f, A f with hs
    refine ⟨⌊max 0 s⌋₊, fun T io e ho y => ⟨?_, fun ha => ?_⟩⟩
    · have h0 : (0 : EReal) ≤ nuP p y cx := Finset.sum_nonneg fun f _ =>
        (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1 T io e ho y |>.1 |> fun h => by simpa using h
      have h1 : ((s : ℝ) : EReal) ≤ nuP p y cx := by
        rw [hs, hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).1
      have hn : ((⌊max 0 s⌋₊ : ℕ) : ℝ) ≤ max 0 s := Nat.floor_le (le_max_left _ _)
      rcases le_total 0 s with h | h
      · exact (EReal.coe_le_coe_iff.2 (hn.trans (max_eq_right h).le)).trans h1
      · exact (EReal.coe_le_coe_iff.2 (hn.trans (max_eq_left h).le)).trans (by simpa using h0)
    · have hu : nuP p y cx ≤ ((∑ f, B f : ℝ) : EReal) := by
        rw [hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).2 ha
      refine hu.trans (EReal.coe_le_coe_iff.2 ?_)
      have hlt : max 0 s < ((⌊max 0 s⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      have hsd : ∑ f, (B f - A f) = ∑ f, B f - s := by rw [Finset.sum_sub_distrib]
      have hm : s ≤ max 0 s := le_max_right _ _
      linarith
  · intro b hb O _ β Y Z
    obtain ⟨A, hA⟩ := hb la
    calc eLoc Y Z la cx ≤ ((((A : ℝ) + b : ℝ)) : EReal) - (((A : ℝ)) : EReal) :=
          EReal.sub_le_sub (nuPSup_le fun T io e ho y hy => (hA T io e ho y).2 hy.2)
            (le_nuPInf fun T io e ho y _ => (hA T io e ho y).1)
      _ = (b : EReal) := by rw [← EReal.coe_sub]; congr 1; ring

end GlobalTheory.RefSum

end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

theorem _root_.GlobalTheory.T.weight_bound_holds : WtN := by
  first | exact @GlobalTheory.CovTop.WtShape.wtN | exact GlobalTheory.CovTop.WtShape.wtN | (intros; apply GlobalTheory.CovTop.WtShape.wtN <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.Published.ChebotarevDegreeOne → ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool) (P : Par) (W : Wts ι), (∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ))) → ∀ (F : Frame l ι P.Nr), F.Ok → ∀ (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (jK : F.K →* alg F.O P.Nr W.lam), F.IsJ W.lam jK → ∀ (ϖ : F.O), Irreducible ϖ → ϖ ∣ ((l : ℕ) : F.O) → (∀ τ, Antitone (res P.Nr (W.lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O P.Nr W.lam) Gm] [IsScalarTower F.O (alg F.O P.Nr W.lam) Gm] [Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)], F.IsHecke W.lam jK Gm → IsSimpleModule (alg F.O P.Nr W.lam) Gm → SubQ F.O P.Nr W.lam ϖ Gm → ∀ (mu : ι → ℕ → ℕ), (∀ τ, Antitone (res P.Nr (mu τ)) ∧ ∑ a : Fin P.Nr, mu τ a = ∑ a : Fin P.Nr, W.lam τ a ∧ (∀ a : Fin P.Nr, W.lam τ (P.Nr - 1) ≤ mu τ a ∧ mu τ a ≤ W.lam τ 0)) → Embeds F.O P.Nr W.lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal] (θ0 : F.I → PadicAlgCl l), F.IsEig W.lam θ0 → Bk θ0 → F.Over θ0 m → ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  intro E Ω _ _ _ _ _ _ hCheb l _ ι _ _ inc fr cjj P W hlink F hF Bk hG jK hJ ϖ hϖ hϖl hlam Gm _ _ _ _ _ hH hS hSQ mu hmu hemb m _ θ0 h0e h0b h0o hns
  obtain ⟨θ, hθe, hθo⟩ := GlobalTheory.T.exists_charZero_eigenform_surviving_compositionFactor l ι P.Nr F W.lam mu jK ϖ hF hJ hϖ Gm hH hemb m hns
  obtain ⟨θ', hθ'e, -, hc⟩ := GlobalTheory.T.exists_galoisConj_eigenSystem_congruent l ι P.Nr F mu hF θ θ0 m hθe hθo h0o
  have hB : BlockFor Ω inc P W mu :=
    GlobalTheory.T.blockData_of_congruent_heckeSystem hCheb E Ω l ι inc P W F Bk hG mu θ' θ0 (fun τ => (hmu τ).1) hθ'e h0e h0b hc
  have hnt : Nontrivial Gm := IsSimpleModule.nontrivial (alg F.O P.Nr W.lam) Gm
  have hlnk := GlobalTheory.T.simpleModule_linkage_dualWeylLattice_reduction F.O P.Nr ι W.lam mu l ϖ (Fact.out) hϖ hϖl hlam (fun τ => (hmu τ).1) Gm hnt hSQ hemb
  exact hlink mu (fun τ => ⟨(hmu τ).1, (hmu τ).2.1, (hmu τ).2.2, hlnk τ⟩) hB
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckePairCount

theorem card_pairs_eq {G : Type} [Group G] (J L : Subgroup G) (x y : G) (A B : Finset G)
    (hθ : ∃ θ : G → G, (∀ g ∈ L, θ g ∈ L) ∧ (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧ (∀ x ∈ L, θ (θ x) = x) ∧
      (∀ k ∈ J ⊓ L, θ k ∈ J) ∧ ∀ g ∈ L, ∃ a ∈ J ⊓ L, ∃ b ∈ J ⊓ L, θ g = a * g * b)
    (hAL : ∀ a ∈ A, a ∈ L) (hBL : ∀ a ∈ B, a ∈ L) (hA : Bridge.IsDC J x A) (hB : Bridge.IsDC J y B) (c : G ⧸ J) :
    ((A ×ˢ B).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c)).card =
      ((B ×ˢ A).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c)).card := by
  obtain ⟨θ, hL, hm, hi, hK, hdc⟩ := hθ
  by_cases hc : ∃ z ∈ L, (z : G ⧸ J) = c
  · obtain ⟨z, hz, rfl⟩ := hc
    have key : ∀ C E : Finset G, (∀ a ∈ C, a ∈ L) → (∀ a ∈ E, a ∈ L) →
        (C ×ˢ E).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = (z : G ⧸ J)) =
          (C ×ˢ E).filter (fun p => (z : G ⧸ (J ⊓ L)) = ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) := by
      intro C E hC hE
      refine Finset.filter_congr fun p hp => ?_
      rw [Finset.mem_product] at hp
      rw [eq_comm, QuotientGroup.eq, QuotientGroup.eq]
      exact ⟨fun h => ⟨h, L.mul_mem (L.inv_mem hz) (L.mul_mem (hC _ hp.1) (hE _ hp.2))⟩, fun h => h.1⟩
    rw [key A B hAL hBL, key B A hBL hAL]
    have e1 := GlobalTheory.DoubleCosetComm.card_pairs (A := A) hB hAL hBL hz
    have e2 := GlobalTheory.DoubleCosetComm.card_pairs (A := B) hA hBL hAL hz
    have e3 := le_antisymm (GlobalTheory.DoubleCosetComm.card_conv_le hm hi hK hL hdc hA hB hAL hz)
      (GlobalTheory.DoubleCosetComm.card_conv_le hm hi hK hL hdc hB hA hBL hz)
    exact e1.trans (e3.trans e2.symm)
  · have key : ∀ C E : Finset G, (∀ a ∈ C, a ∈ L) → (∀ a ∈ E, a ∈ L) →
        (C ×ˢ E).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c) = ∅ := by
      intro C E hC hE
      refine Finset.filter_eq_empty_iff.2 fun p hp h => hc ?_
      rw [Finset.mem_product] at hp
      exact ⟨_, L.mul_mem (hC _ hp.1) (hE _ hp.2), h⟩
    rw [key A B hAL hBL, key B A hBL hAL]



theorem side_count {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hβ : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1) {Pl0 : Type}
    (pl : Pl0 → Formalism.L2.DIV.Pl D.host.E) (ok : Set Pl0) (Sp : Set (Formalism.L2.DIV.Pl D.host.E))
    (hok : ∀ P, P ∈ ok ↔ Bridge.SplitOff (pl P) Sp) (hS : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ∈ Sp) (i i' : ok × ℕ)
    (hv : (pl i.1).under (𝓞 D.host.F) = (pl i'.1).under (𝓞 D.host.F)) (hi : i.2 ≤ V.rank)
    (x y : Bridge.Gf V) (A B : Finset (Bridge.Gf V)) (hx : isTEnv V pl ok i x)
    (hA : ∀ a ∈ A, isLocEnv V pl ok i a) (hB : ∀ a ∈ B, isLocEnv V pl ok i' a)
    (dA : Bridge.IsDC (levEnv V β L).J x A) (dB : Bridge.IsDC (levEnv V β L).J y B)
    (c : Bridge.Gf V ⧸ (levEnv V β L).J) :
    ((A ×ˢ B).filter (fun p => ((p.1 * p.2 : Bridge.Gf V) : Bridge.Gf V ⧸ (levEnv V β L).J) = c)).card =
      ((B ×ˢ A).filter (fun p => ((p.1 * p.2 : Bridge.Gf V) : Bridge.Gf V ⧸ (levEnv V β L).J) = c)).card := by
  refine (hx hi).elim fun α h0 => h0.1.elim fun e h1 => h1.elim fun ϖ h2 => ?_
  have he := h2.1
  have hsp := (hok _).1 i.1.2
  have hl := GlobalTheory.SplitHeckeAdj.local_group V β Λ L hβ (pl i.1) e he
    fun PP h => GlobalTheory.SplitHeckeAdj.off_of_splitOff hsp PP (hS PP h)
  refine hl.elim fun Lc hl => ?_
  have l1 := hl.1
  have l4 := hl.2.2.2.1
  have hm : ∀ x, isLocEnv V pl ok i x → x ∈ Lc := fun x hx => by
    refine (GlobalTheory.SplitHeckeAdj.loc_supp V hx he).elim fun g hg => ?_
    rw [← hg.2]
    exact l1 g hg.1
  have hm' : ∀ x, isLocEnv V pl ok i' x → x ∈ Lc := fun x hx => by
    refine hm x (GlobalTheory.FrameProdLoc.isLocEnv_of_mem V pl ok i x e he ?_)
    rw [hv]
    exact GlobalTheory.FrameProdLoc.mem_locGrp_of_isLocEnv V pl ok i' x hx
  exact card_pairs_eq (levEnv V β L).J Lc x y A B l4 (fun a ha => hm a (hA a ha)) (fun a ha => hm' a (hB a ha)) dA dB c



theorem card_pairs_comm : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (i i' : (blk p j t).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → 1 ≤ i'.2 → i'.2 ≤ (Vc D j).rank → (plOf p j t i.1).under (𝓞 D.host.F) = (plOf p j t i'.1).under (𝓞 D.host.F) → ∀ c : Bridge.Gf (Vc D j) ⧸ levJ p j t, ((hkA p j t i ×ˢ hkA p j t i').filter (fun x => ((x.1 * x.2 : Bridge.Gf (Vc D j)) : Bridge.Gf (Vc D j) ⧸ levJ p j t) = c)).card = ((hkA p j t i' ×ˢ hkA p j t i).filter (fun x => ((x.1 * x.2 : Bridge.Gf (Vc D j)) : Bridge.Gf (Vc D j) ⧸ levJ p j t) = c)).card := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t i i' h1 h2 h1' h2' hv c
  have hb := p.charW.base
  refine hb.fam.tie.elim fun gramR h3 => h3.elim fun c0R h4 => h4.elim fun c0L tie => ?_
  refine (hb.lev.βV j).elim fun c' hc => ?_
  rw [one_pow] at hc
  have main := side_count (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) hc p.R.pl (p.P.A3.A.ok t) _ (tie.ok t)
    (fun PP hP => hP.elim (fun h1 => Or.inl (hb.fam.Sb h1)) Or.inr) i i' hv h2
    ((p.R.B.L j t).hecke.hx i) ((p.R.B.L j t).hecke.hx i') (hkA p j t i) (hkA p j t i')
    ((p.R.B.L j t).hecke.hx_ok i ⟨h1, h2⟩) ((p.R.B.L j t).hecke.hA_loc i ⟨h1, h2⟩) ((p.R.B.L j t).hecke.hA_loc i' ⟨h1', h2'⟩)
    ((p.R.B.L j t).hecke.hDC i ⟨h1, h2⟩) ((p.R.B.L j t).hecke.hDC i' ⟨h1', h2'⟩) c
  exact main

end GlobalTheory.HeckePairCount

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem DivOver.ord_zpow_int {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) (f : X.functionFieldˣ) (r : ℤ) : E.ord (f ^ r) = r * E.ord f := by
  obtain ⟨m, rfl | rfl⟩ := r.eq_nat_or_neg
  · rw [zpow_natCast, E.ord_pow]
  · rw [zpow_neg, zpow_natCast, E.ord_inv, E.ord_pow]; ring

theorem DivOver.ord_finsetProd_zpow {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (E : DivOver p) {ι : Type} (s : Finset ι) (f : ι → X.functionFieldˣ)
    (e : ι → ℤ) : E.ord (∏ j ∈ s, f j ^ e j) = ∑ j ∈ s, e j * E.ord (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, E.ord_mul, ih, E.ord_zpow_int]

theorem DivOver.ord_eq_zero_of_unitAt_through {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (E : DivOver p) {y : X} (hE : E.Through y) (v : X.functionFieldˣ)
    (h : UnitAt y (v : X.functionField)) : E.ord v = 0 := by
  obtain ⟨a, ha, e⟩ := h
  have h1 : (v : X.functionField) ∈ E.ring := hE _ ⟨a, e⟩
  have h2 : ((v⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring := by
    refine hE _ ⟨(ha.unit⁻¹ : (X.presheaf.stalk y)ˣ), ?_⟩
    rw [Units.val_inv_eq_inv_val, ← e]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  have a1 := (E.ord_nonneg_iff v).2 h1
  have a2 := (E.ord_nonneg_iff v⁻¹).2 h2
  rw [E.ord_inv] at a2
  omega

end GlobalTheory.Discrepancy

namespace GlobalTheory.Discrepancy

theorem IsSncChart.discrep_eq_formOrd_sub_sum : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (g : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → (Θ + m • K).IsEqn y g → ∀ E : DivOver q, E.Through y → discrep E η m g = ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, ((Θ.mult (w j) : ℚ) / m) * E.ord (u j) := by
  intro Y _ _ q n _ B y U hy z J w u hc η K Θ m g hη hK hm hΘ hg E hE
  classical
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := by
    have hd (V : Y.Opens) (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) :
        topologicalKrullDim (V : Set Y) = n := by
      rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
        hV.range_fromSpec]
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, V))).trans
        (SmoothDim.ringKrullDim_affineOpen ℂ _ q _ inferInstance V hV hne)
    refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨V, V.isOpen, hx, (hd V hV ⟨x, hx⟩).le⟩
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top y)
      exact (hd V hV ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)
  set ω := formOf U (gen_mem hy) (dOn q z) with hω
  have hgen := isFreeGen_formOf (gen_mem hy) hc.frame
  have h0 : ω ≠ 0 := fun h =>
    one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [← hω, h]))
  obtain ⟨c, hcη⟩ := hgen.2 η
  have hc0 : c ≠ 0 := fun h => hη (by rw [← hcη]; simp [h])
  set k0 : Y.functionFieldˣ := Units.mk0 c hc0 with hk0
  have hηk : η = (k0 : Y.functionField) • ω := by rw [hk0, Units.val_mk0]; exact hcη.symm
  have hKy : K.IsEqn y k0 := hK U (dOn q z) hc.frame y hy k0 hηk
  have hΘy := GlobalTheory.T.snc_chart_divisor_equation ℂ Y q n B y U hy z J w u hc Θ hΘ
  set M : Y.functionFieldˣ := ∏ j ∈ J, u j ^ Θ.mult (w j) with hM
  have hsum : (Θ + m • K).IsEqn y (M * k0 ^ m) := hΘy.add (hKy.nsmul m)
  set v : Y.functionFieldˣ := g * (M * k0 ^ m)⁻¹ with hv
  have hvu : UnitAt y (v : Y.functionField) := by
    have := hsum.iff_unitAt.1 hg
    rwa [hv, Units.val_mul, Units.val_inv_eq_inv_val, ← div_eq_mul_inv]
  have hv0 : E.ord v = 0 := E.ord_eq_zero_of_unitAt_through hE v hvu
  have hvo : E.ord v = E.ord g - (E.ord M + m * E.ord k0) := by
    rw [hv, E.ord_mul, E.ord_inv, E.ord_mul, E.ord_pow]; ring
  have hMo : E.ord M = ∑ j ∈ J, Θ.mult (w j) * E.ord (u j) := by
    rw [hM, E.ord_finsetProd_zpow]
  have hordg : E.ord g = ∑ j ∈ J, Θ.mult (w j) * E.ord (u j) + m * E.ord k0 := by
    rw [← hMo]; omega
  have hform : E.formOrd η = E.ord k0 + E.formOrd ω := by
    rw [hηk]; exact E.formOrd_smul hn h0 k0
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [discrep, hform, hordg]
  push_cast
  have hs : ∑ j ∈ J, ((Θ.mult (w j) : ℚ) / m) * (E.ord (u j) : ℚ) =
      (∑ j ∈ J, (Θ.mult (w j) : ℚ) * E.ord (u j)) / m := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => div_mul_eq_mul_div _ _ _
  rw [hs]
  unfold DivOver.formOrd
  field_simp
  ring

end GlobalTheory.Discrepancy
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.PairStep

theorem exists_sncChart_isEqn_affine : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ (A : CartierDiv Y) (ι : Type) (s : ι → Y.functionField), (∀ i, s i ∈ A.sections) → ∀ y₀ : Y, ∃ (W : Y.Opens) (hW : y₀ ∈ W) (z : Fin n → Γ(Y, W)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ) (e : Y.functionFieldˣ) (f : ι → Γ(Y, W)), IsFrame (dOn q z) ∧ (∀ y ∈ W, A.IsEqn y e) ∧ (∀ i, fnOf W (gen_mem hW) (f i) = s i * e) ∧ ∀ (y : Y) (hy : y ∈ W), ∃ J : Finset (Fin n), IsSncChart q n B y W hy z J w u ∧ ∀ j ∈ J, y ∉ Y.basicOpen (z j) := by
  intro Y _ _ q n _ B hB A ι s hs y₀
  obtain ⟨U, hy₀, z, J, w, u, hc⟩ := GlobalTheory.T.exists_snc_chart ℂ Y q n B hB y₀
  have hgen : genericPoint Y ∉ B := GlobalTheory.PairStep.genericPoint_notMem_of_snc Y B hB
  obtain ⟨V, hyV, hV⟩ := GlobalTheory.T.isSncAdaptedCoordinates_of_mem_nhds Y q n B y₀ U hy₀ z J w u hgen hc
  obtain ⟨N, hyN, e, he⟩ := A.exists_isEqn_nhds y₀
  obtain ⟨W, hWa, hyW, hWle⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (show y₀ ∈ U ⊓ V ⊓ N from ⟨⟨hy₀, hyV⟩, hyN⟩)
  have hWU : W ≤ U := hWle.trans (inf_le_left.trans inf_le_left)
  have hWV : W ≤ V := hWle.trans (inf_le_left.trans inf_le_right)
  have hWN : W ≤ N := hWle.trans inf_le_right
  have hf : ∀ i, ∃ a : Γ(Y, W), fnOf W (gen_mem hyW) a = s i * e := fun i =>
    exists_fnOf_eq (gen_mem hyW) fun x hx =>
      (he x (hWN hx)).regularAt_iff.1 (CartierDiv.mem_sections.1 (hs i) x)
  choose f hf using hf
  have hfr : IsFrame (dOn q fun j => resG Y hWU (z j)) := by
    have := hc.frame.res hWa hWU
    rwa [resForm_dOn] at this
  refine ⟨W, hyW, fun j => resG Y hWU (z j), w, u, e, f, hfr, fun y hy => he y (hWN hy), hf, ?_⟩
  intro y hy
  obtain ⟨hyU, J', -, hc', hJ'⟩ := hV y (hWV hy)
  refine ⟨J', ⟨hfr, ?_, hc'.spec, hc'.coheight, hc'.inj, hc'.ord_self, hc'.ord_other, hc'.mem⟩, ?_⟩
  · intro j hj
    rw [hc'.val j hj, fnOf_resG]
  · intro j hj hmem
    have hb : Y.basicOpen (resG Y hWU (z j)) = W ⊓ Y.basicOpen (z j) :=
      Y.basicOpen_res (z j) (homOfLE hWU).op
    rw [hb] at hmem
    exact hJ' j hj hmem.2

end GlobalTheory.PairStep
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

theorem _root_.GlobalTheory.T.birational_primeDivisor_orders_functions_topForms : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (n : ℕ),
    topologicalKrullDim X = n → ∀ (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) →
    ∀ (E : DivOver p) (E' : DivOver (s ≫ p)), DivOver.Over s E' E →
      (∀ g : X.functionFieldˣ, E'.ord (fnPull s g) = E.ord g) ∧
      ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (ratPull p s n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  first | exact @GlobalTheory.BirOrd.ord_and_formOrd_of_over | exact GlobalTheory.BirOrd.ord_and_formOrd_of_over | (intros; apply GlobalTheory.BirOrd.ord_and_formOrd_of_over <;> assumption)
end
