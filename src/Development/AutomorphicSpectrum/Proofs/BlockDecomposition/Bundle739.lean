module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle343
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle681
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle360
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle726
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle715
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle675
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle366
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle615
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle449
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle736
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle735
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle676
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle654
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle686
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle662
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle624
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle738
public import GroundTheory.IdeleRoots.TorusPowers.HeckeTensor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle737
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleConjugationInvariantStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg GlobalTheory.CompanionTheory.SegCoarse

namespace GlobalTheory.CompanionTheory.SegCoarse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fineJac_all (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) :
    ∀ Δ : Segment k, FineJac Δ := by
  intro Δ
  induction h : Δ.len using Nat.strong_induction_on generalizing Δ with
  | _ n ih =>
    have hp := Δ.len_pos
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · omega
      · exact @GlobalTheory.T.fine_jacquet_length_one k _ _ _ _ hA Δ h
      · exact @GlobalTheory.T.fine_jacquet_segment_length_two k _ _ _ _ hA hZ Δ h
    · exact @GlobalTheory.T.fine_jacquet_segment_induction k _ _ _ _ hA Δ (h ▸ h3) fun Δ' hlt => ih _ (h ▸ hlt) Δ' rfl

theorem occurs_topCut (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation)
    (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hπ : IsLSeg Δ π) {s : ℕ} (y : Fin s → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (hpos : ∀ a, 0 < (y a).1)
    (h1 : 1 ≤ jm y hd π) :
    ∃ (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (_ : ∑ a, c a = Δ.len)
      (hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N),
      jm y hd π ≤ jm (concat c (fun a => dec (topCut Δ c hc a))) hcat π ∧
        ∀ a, IsLSeg (topCut Δ c hc a) (y a).rep := by
  choose c x hx hcusp hemb using fun a =>
    GlobalTheory.T.support_subscheme_embedding k (y a).1 _ (y a).rep (y a).2.rep.smooth (y a).2.rep.irr
  have hjx : ∀ a, 1 ≤ jm (x a) (hx a) (y a).rep := fun a => by
    obtain ⟨φ, hφ⟩ := hemb a
    have := Model.nontrivial_of_isIrreducible (y a).2.rep.irr
    obtain ⟨v, hv⟩ := exists_ne (0 : (y a).2.rep.V)
    exact GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA (x a) (hx a) (y a).rep (y a).2.rep.smooth φ
      ⟨v, fun e => hv (hφ (e.trans (map_zero φ).symm))⟩
  have hcat0 : ∑ i, (concat c x i).1 = N := by
    rw [sum_concat, ← hd]
    exact Finset.sum_congr rfl fun a _ => hx a
  have hirr : π.IsIrreducible := hπ.2.1
  have hsm : IsSmooth π := hπ.hasSupport.isSmooth
  have hle := GlobalTheory.T.jacquet_multiplicity_concat hA y hd c x hx hcat0 hjx π hsm (hasFiniteLength_of_isIrreducible hirr)
  have h1' : 1 ≤ jm (concat c x) hcat0 π := h1.trans hle
  obtain ⟨hl, hfine⟩ := (fineJac_all hA hZ Δ π hπ).2 _ (concat c x) hcat0 (fun i => hcusp _ _) h1'
  have hc : ∀ a, 0 < c a := fun a => by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have : IsEmpty (Fin (c a)) := by rw [h0]; infer_instance
    have := hx a
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact (hpos a).ne this
  have hxeq : x = fun a => dec (topCut Δ c hc a) :=
    concat_injective (funext fun i => (hfine i).trans (concat_dec_topCut Δ c hc hl i).symm)
  subst hxeq
  refine ⟨c, hc, hl, hcat0, hle, fun a => ?_⟩
  obtain ⟨φ, hφ⟩ := hemb a
  exact GlobalTheory.T.irreducible_sub_segment_product hA hZ (topCut Δ c hc a) (hx a) (y a).rep (y a).2.rep.smooth (y a).2.rep.irr φ hφ

theorem lSegJacquet : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation), LSegJacquet k := by
  intro k _ _ _ _ hA hZ Δ N V _ _ π hπ s y hd hpos
  have hdΔ : ∑ a, (dec Δ a).1 = N := (sum_dec Δ).trans hπ.deg_eq
  have hone := (fineJac_all hA hZ Δ π hπ).1 hdΔ
  have hirr : π.IsIrreducible := hπ.2.1
  have hsm : IsSmooth π := hπ.hasSupport.isSmooth

  have hread : ∀ (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (hl : ∑ a, c a = Δ.len)
      (hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N),
      jm (concat c (fun a => dec (topCut Δ c hc a))) hcat π = 1 := fun c hc hl hcat =>
    (jm_reindex hl _ _ (concat_dec_topCut Δ c hc hl) hcat hdΔ π).trans hone
  have hB : 1 ≤ jm y hd π → ∃ Γ : Fin s → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (y a).rep := fun h1 => by
    obtain ⟨c, hc, hl, -, -, hL⟩ := occurs_topCut hA hZ Δ π hπ y hd hpos h1
    exact ⟨topCut Δ c hc, isTopCut_topCut Δ c hc hl, hL⟩
  have hC : jm y hd π ≤ 1 := by
    by_cases h0 : jm y hd π = 0
    · rw [h0]; exact zero_le_one
    · obtain ⟨c, hc, hl, hcat, hle, -⟩ := occurs_topCut hA hZ Δ π hπ y hd hpos (ENat.one_le_iff_ne_zero.2 h0)
      exact hle.trans (hread c hc hl hcat).le
  have hD : (∃ Γ : Fin s → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (y a).rep) → 1 ≤ jm y hd π := by
    rintro ⟨Γ, hΓ, hL⟩
    have hΓe := eq_topCut hΓ
    set c : Fin s → ℕ := fun a => (Γ a).len with hcdef
    have hc : ∀ a, 0 < c a := fun a => (Γ a).len_pos
    have hl : ∑ a, c a = Δ.len := hΓ.1
    have hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N :=
      (Fintype.sum_equiv (finCongr hl) _ _ fun i => by rw [concat_dec_topCut Δ c hc hl]; rfl).trans hdΔ
    have hxpos : ∀ a, 0 < ∑ i, (dec (topCut Δ c hc a) i).1 := fun a => by
      rw [sum_dec, deg_topCut]; exact Nat.mul_pos (hc a) Δ.d_pos
    obtain ⟨σ, hσ, hσd, h1σ⟩ := GlobalTheory.T.concatenated_jacquet_multiplicity_factorization hA c (fun a => dec (topCut Δ c hc a)) hxpos hcat π hsm
      (hasFiniteLength_of_isIrreducible hirr) (hread c hc hl hcat).ge
    have hσpos : ∀ a, 0 < (σ a).1 := fun a => (hσd a).symm ▸ hxpos a
    obtain ⟨c', hc', hl', -, -, hL'⟩ := occurs_topCut hA hZ Δ π hπ σ hσ hσpos h1σ
    have hsd : ∀ a, ∑ i : Fin (c a), (dec (topCut Δ c hc a) i).1 = c a * Δ.d := fun a =>
      (sum_dec _).trans (deg_topCut Δ c hc a)
    have hcc : c' = c := funext fun a => by
      have e1 := (hL' a).deg_eq
      rw [deg_topCut, hσd a, hsd a] at e1
      exact Nat.eq_of_mul_eq_mul_right Δ.d_pos e1
    subst hcc
    have hσy : σ = y := funext fun a => by
      have h2 : IsLSeg (topCut Δ c hc' a) (y a).rep := by
        have := hL a
        rw [hΓe] at this
        exact this
      exact eq_of_isLSeg (hL' a) h2
    subst hσy
    exact h1σ
  refine ⟨fun h => le_antisymm hC (hD h), fun h => ?_⟩
  by_contra h0
  exact h (hB (ENat.one_le_iff_ne_zero.2 h0))

end GlobalTheory.CompanionTheory.SegCoarse

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegLDual

theorem lSegDual : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation), LSegDual k := by
  intro k _ _ _ _ hA hZ Δ N V _ _ π hπ
  obtain ⟨hd, hco⟩ := id hπ
  have hsm : IsSmooth π := hco.isSubquotient.isSmooth (isSmooth_prodIrr _ hd)
  obtain ⟨hirr, f, hf, -⟩ := hco
  have hci : (contra π).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k N) (hA k N V π hsm hirr) hirr
  obtain ⟨hd', ⟨e⟩⟩ := GlobalTheory.T.contragredient_segment_product_equiv hA Δ hd
  have hinj : Function.Injective (GlobalTheory.ContraRefl.contraMap f) := fun a b h => Subtype.ext (LinearMap.ext fun v => by
    obtain ⟨w, rfl⟩ := hf v
    exact LinearMap.congr_fun (congrArg Subtype.val h) w)
  exact GlobalTheory.T.irreducible_sub_segment_product hA hZ (segDual Δ) hd' (contra π) (isSmooth_smoothRep _) hci
    (e.toIntertwiningMap.comp (GlobalTheory.ContraRefl.contraMap f))
    (e.toLinearEquiv.injective.comp hinj)

end GlobalTheory.CompanionTheory.SegLDual

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilTheta

theorem weilThetaConvergence_of_siegelSet (hRT : GlobalTheory.Published.SiegelSetUnitary) : GlobalTheory.Published.WeilThetaConvergence := by
  intro D n V _hn hV θ hθ ν hν Φ
  obtain ⟨hcontΦ, -⟩ := GlobalTheory.T.schwartz_bound_finite_infinite D θ hθ V.rank n Φ.1 Φ.2
  obtain ⟨r, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame (GlobalTheory.AdelicU.isCMExt_host D) (isHermND_gram V)
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hRT D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) V.rank V.gram (isHermND_gram V) r Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas ν hν
  obtain ⟨C, hC⟩ := GlobalTheory.T.siegel_set_compact_reduction D θ hθ V n Φ.1 Φ.2 Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hconj
  set S := GlobalTheory.SiegelSet.siegelSet D.sp.cm.sig V.gram Xf Yf Ω c K with hSdef
  have hSm : MeasurableSet S := hcl.measurableSet
  have hScov : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ S := fun g => by
    obtain ⟨γ, hγ, s, hs, e⟩ := hcov g
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [e, inv_mul_cancel_left]
    exact hs
  have hI : ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
      ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
        ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹) < ⊤ := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      exact GlobalTheory.CompanionTheory.SiegelCone.cone_integral_zero_vars_lt_top D.host.F V.rank (2 * n) c
    · have hw := GlobalTheory.T.witt_frame_rank_le_witt_index D V Xf Yf hW
      have h2 : n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank := hV.resolve_left (by omega)
      exact GlobalTheory.T.lintegral_siegelCone_inv_modulus_lt_top_weil D.host.F V.rank r (2 * n) hc (by omega)
  calc absThetaInt V ν Φ.1 ≤ ∫⁻ g in S, absTheta V Φ.1 g ∂ν :=
        GlobalTheory.T.theta_integral_le_fundamental_set D V ν hν Φ.1 hcontΦ S hSm hScov
    _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
          ENNReal.ofReal (max C 0 * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹) := by
        refine hC₁ (absTheta V Φ.1) _ (by fun_prop) fun p hp t ht a ha k hk => ?_
        have ht0 : ∀ i, 0 < t i := ht.1
        have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n)) :=
          Finset.prod_nonneg fun i _ => pow_nonneg (ht0 i).le _
        refine (hC p hp t ht a ha k hk).trans (ENNReal.ofReal_le_ofReal ?_)
        gcongr
        exact le_max_left _ _
    _ = C₁ * (ENNReal.ofReal (max C 0) * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
          ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul (le_max_right _ _), mul_assoc]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI)

end GlobalTheory.CompanionTheory.WeilTheta

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem pure_term : ∀ (F : Type) [Field F] [NumberField F] (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ), S ⊆ T →
    (∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧ ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) →
    ∀ (δ : ℝ), 0 < δ → ∀ t : Fˣ,
    PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) (pr t * (a * r δ)) =
      if ∀ v, v ∉ T → algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (phiA G a (fun _ => θ δ * algebraMap F (Ainf F) (t : F)) *
          ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) (t : F))) else 0 := by
  intro F _ _ θ r hr S T G g a hST hT δ hδ t
  obtain ⟨h1, h2⟩ := hr δ hδ
  have c1 : ((pr t * (a * r δ) : (AF F)ˣ) : AF F).1 = (a : AF F).1 * (θ δ * algebraMap F (Ainf F) (t : F)) := by
    have : ((pr t * (a * r δ) : (AF F)ˣ) : AF F).1 = algebraMap F (Ainf F) (t : F) * ((a : AF F).1 * (r δ : AF F).1) := rfl
    rw [this, h1]; ring
  have c2 : ∀ v, ((pr t * (a * r δ) : (AF F)ˣ) : AF F).2 v = (a : AF F).2 v * algebraMap F (Fv F v) (t : F) := by
    intro v
    have : ((pr t * (a * r δ) : (AF F)ˣ) : AF F).2 v = algebraMap F (Fv F v) (t : F) * ((a : AF F).2 v * (r δ : AF F).2 v) := rfl
    rw [this, h2]
    have h3 : ((1 : FiniteAdeleRing (𝓞 F) F)) v = 1 := rfl
    rw [h3, mul_one, mul_comm]
  have inv : ∀ v, (a : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v = 1 := by
    intro v
    have : ((a * a⁻¹ : (AF F)ˣ) : AF F).2 v = (a : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v := rfl
    rw [← this]; simp
  have key : ∀ v, v ∉ T → ((a : AF F).2 v * algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F ↔
      algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F) := by
    intro v hv
    constructor
    · intro h
      have h' := mul_mem (hT v hv).2 h
      have e : ((a⁻¹ : (AF F)ˣ) : AF F).2 v * ((a : AF F).2 v * algebraMap F (Fv F v) (t : F)) =
          algebraMap F (Fv F v) (t : F) := by
        rw [← mul_assoc, mul_comm (((a⁻¹ : (AF F)ˣ) : AF F).2 v), inv, one_mul]
      rwa [e] at h'
    · exact fun h => mul_mem (hT v hv).1 h
  rw [GlobalTheory.T.pure_adelic_function_formula F S G g (pr t * (a * r δ))]
  simp only [c1, c2]
  by_cases ht : ∀ v, v ∉ T → algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F
  · rw [if_pos ht]
    by_cases h : ∀ v, v ∉ S → (a : AF F).2 v * algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F
    · rw [if_pos h]
      have hp : ∏ v ∈ S, g v ((a : AF F).2 v * algebraMap F (Fv F v) (t : F)) =
          ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) (t : F)) := by
        rw [← Finset.prod_subset hST]
        · refine Finset.prod_congr rfl fun v hv => ?_
          simp [psiA, hv]
        · intro v _ hv
          simp [psiA, hv, h v hv]
      rw [hp]
      rfl
    · rw [if_neg h]
      push_neg at h
      obtain ⟨v, hvS, hv⟩ := h
      have hvT : v ∈ T := by
        by_contra hvT
        exact hv ((key v hvT).2 (ht v hvT))
      have hz : ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) (t : F)) = 0 :=
        Finset.prod_eq_zero hvT (by simp [psiA, hvS, hv])
      rw [hz]
      simp
  · rw [if_neg ht, if_neg]
    intro h
    exact ht fun v hv => (key v hv).1 (h v fun hs => hv (hST hs))

end GlobalTheory.CompanionTheory.BasePsi
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem finite_contributing : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ),
    Continuous G → HasCompactSupport G → (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) → S ⊆ T →
    (∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧ ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) →
    ∀ δ : ℝ, 0 < δ →
    {x : F | (∀ v, v ∉ T → algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F) ∧
      phiA G a (fun _ => θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) x) ≠ 0}.Finite := by
  intro F _ _ _ θ _ S T G g a _ hGc hg hST ha δ hδ
  obtain ⟨N, hN, hNint⟩ := GlobalTheory.T.bounded_denominators_compact_idele_set F {a} isCompact_singleton S (fun v => tsupport (g v))
    (fun v hv => (hg v hv).2)
  have h1 : ((↑a⁻¹ : AF F)).1 * (↑a : AF F).1 = 1 := congrArg Prod.fst (Units.inv_mul a)
  have h2 : θ δ⁻¹ * θ δ = 1 := by rw [← map_mul, inv_mul_cancel₀ hδ.ne', map_one]
  have hcd : ∀ z : Ainf F, θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * ((↑a : AF F).1 * (θ δ * z)) = z := by
    intro z
    calc θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * ((↑a : AF F).1 * (θ δ * z))
        = θ δ⁻¹ * (((↑a⁻¹ : AF F)).1 * (↑a : AF F).1) * θ δ * z := by ring
      _ = z := by rw [h1, mul_one, h2, one_mul]
  have hK : IsCompact ((fun z => θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * z) '' tsupport G) :=
    hGc.image (continuous_const.mul continuous_id)
  choose C hC using fun w : NumberField.InfinitePlace F =>
    hK.exists_bound_of_continuousOn (f := fun z : NumberField.InfiniteAdeleRing F => z w)
      (continuous_apply w).continuousOn
  refine ((NumberField.Embeddings.finite_of_norm_le F ℂ ((N : ℝ) * ∑ w, ‖C w‖)).image
    (fun y => y / (N : F))).subset ?_
  rintro x ⟨hxT, hne⟩
  have hG0 := left_ne_zero_of_mul hne
  have hpsi : ∀ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) x) ≠ 0 :=
    fun v hv => Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hne) v hv
  have hS : ∀ v ∈ S, algebraMap F (Fv F v) x * (↑a : AF F).2 v ∈ tsupport (g v) := by
    intro v hv
    have h := hpsi v (hST hv)
    simp only [psiA, if_pos hv] at h
    rw [mul_comm]
    exact subset_tsupport _ h
  have hnS : ∀ v ∉ S, algebraMap F (Fv F v) x * (↑a : AF F).2 v ∈ v.adicCompletionIntegers F := by
    intro v hv
    by_cases hvT : v ∈ T
    · have h := hpsi v hvT
      simp only [psiA, if_neg hv] at h
      rw [mul_comm]
      by_contra hc
      exact h (if_neg hc)
    · exact mul_mem (hxT v hvT) (ha v hvT).1
  obtain ⟨y, hy⟩ := hNint a (Set.mem_singleton a) x hS hnS
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have harch : ∀ w : NumberField.InfinitePlace F, w x ≤ C w := by
    intro w
    have hmem : (↑a : AF F).1 * (θ δ * algebraMap F (Ainf F) x) ∈ tsupport G :=
      subset_tsupport _ hG0
    have hx' : algebraMap F (Ainf F) x ∈ (fun z => θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * z) '' tsupport G :=
      ⟨_, hmem, hcd _⟩
    have hb := hC w _ hx'
    have hn : ‖(algebraMap F (NumberField.InfiniteAdeleRing F) x) w‖ = w x := by
      rw [NumberField.InfiniteAdeleRing.algebraMap_apply, NumberField.InfinitePlace.Completion.norm_coe]
      simp
    rw [← hn]
    exact hb
  have hφ : ∀ φ : F →+* ℂ, ‖φ x‖ ≤ ∑ w, ‖C w‖ := by
    intro φ
    calc ‖φ x‖ = NumberField.InfinitePlace.mk φ x := (NumberField.InfinitePlace.apply φ x).symm
      _ ≤ C (NumberField.InfinitePlace.mk φ) := harch _
      _ ≤ ‖C (NumberField.InfinitePlace.mk φ)‖ := Real.le_norm_self _
      _ ≤ ∑ w, ‖C w‖ := Finset.single_le_sum (f := fun w => ‖C w‖) (fun w _ => norm_nonneg _)
          (Finset.mem_univ _)
  refine ⟨(N : F) * x, ⟨?_, fun φ => ?_⟩, ?_⟩
  · rw [← hy]
    exact NumberField.RingOfIntegers.isIntegral_coe y
  · rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hφ φ) (Nat.cast_nonneg N)
  · field_simp

end GlobalTheory.CompanionTheory.BasePsi
end

section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.fourier_jacobi_eisenstein : ZUnfold → ThTwist → FJEis := by
  first | exact @GlobalTheory.CompanionTheory.FJE.fjEis | exact GlobalTheory.CompanionTheory.FJE.fjEis | (intros; apply GlobalTheory.CompanionTheory.FJE.fjEis <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

theorem _root_.GlobalTheory.T.theta_series_vanishes_large_module : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), HasCompactSupport G → (∀ v ∈ S, HasCompactSupport (g v)) →
    ∃ R : ℝ, ∀ a : (AF F)ˣ, R < md a → th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.th_pure_vanish | exact GlobalTheory.CompanionTheory.BasePsi.th_pure_vanish | (intros; apply GlobalTheory.CompanionTheory.BasePsi.th_pure_vanish <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem ideleModule_eq_md_of_isNm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (x : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ x n → (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) = md n := by
  intro F E _ _ _ _ _ σ hcm x n h
  have h1 := GlobalTheory.T.idele_module_conjugation_invariant F E σ hcm x
  have h2 := GlobalTheory.T.idele_module_base_change_sq F E σ hcm n
  have hu : (ofF n : (AF F ⊗[F] E)ˣ) = Units.map (sigR (AF F) σ).toMonoidHom x * x := Units.ext h
  rw [hu, map_mul, map_mul] at h2
  have h3 : ((IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (Units.map (sigR (AF F) σ).toMonoidHom x)) : ℝ)) *
      (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) = md n ^ 2 := h2
  rw [h1] at h3
  have hp : 0 < (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) :=
    (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x)).2
  have hq : 0 < md n := (IdeleGroup.ideleModule F n).2
  nlinarith [sq_nonneg ((IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) - md n)]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
end
