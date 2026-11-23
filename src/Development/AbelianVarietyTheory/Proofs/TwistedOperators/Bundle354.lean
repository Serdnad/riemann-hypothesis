module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle301
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPermOfCardFalse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle248
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle232
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle336
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseAdjacentStepsInvariantVertex
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle338
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaPairingLaws

theorem ipO_self {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (f : Mx D m n → ℂ) :
    ipO μ 𝓕 f f = (nrm2 μ 𝓕 f : ℂ) := by
  unfold ipO nrm2
  rw [← integral_complex_ofReal]
  congr 1
  funext w
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem countable_ratL' {D : D7} (S T : HSp D) : Countable ↥(ratL T S) := by
  haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := D.host.E)
  haveI : Countable (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
    inferInstanceAs (Countable (Fin T.rank → Fin S.rank → D.host.E))
  have h : (ratL T S : Set (WO S T)).Countable := by
    rw [ratL, AddMonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

theorem ipO_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsCovolOne (ratL T S) μ 𝓕 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IntegrableOn (fun w => f w * (starRingEnd ℂ) (g w)) 𝓕 μ ∧ ipO μ 𝓕 g f = (starRingEnd ℂ) (ipO μ 𝓕 f g) ∧ (∀ c : ℂ, ipO μ 𝓕 (c • f) g = c * ipO μ 𝓕 f g ∧ ipO μ 𝓕 f (c • g) = (starRingEnd ℂ) c * ipO μ 𝓕 f g) ∧ (∀ f', IsThetaFunO ψ S T f' → ipO μ 𝓕 (f + f') g = ipO μ 𝓕 f g + ipO μ 𝓕 f' g ∧ ipO μ 𝓕 g (f + f') = ipO μ 𝓕 g f + ipO μ 𝓕 g f') ∧ ipO μ 𝓕 f f = (nrm2 μ 𝓕 f : ℂ) ∧ (nrm2 μ 𝓕 f = 0 → f = 0) ∧ (∀ w, ipO μ 𝓕 (heisO ψ S T w f) (heisO ψ S T w g) = ipO μ 𝓕 f g ∧ ipO μ 𝓕 (heisO ψ S T w f) g = ipO μ 𝓕 f (heisO ψ S T (-w) g)) ∧ ∀ μ' 𝓕', IsCovolOne (ratL T S) μ' 𝓕' → ipO μ' 𝓕' f g = ipO μ 𝓕 f g := by
  intro D ψ S T μ 𝓕 hψ hμ f g hf hg
  have hμ₀ := hμ
  unfold IsCovolOne at hμ₀
  obtain ⟨hHaar, hFD, -⟩ := hμ₀
  haveI := hHaar
  obtain ⟨-, hL2⟩ := GlobalTheory.ThetaSquare.theta_square_integrable D S T
  obtain ⟨hSq, hHeis, -⟩ := hL2 ψ hψ
  obtain ⟨-, hInvol, hPres, hUnit, -⟩ := hHeis
  obtain ⟨-, -, ⟨-, hHL⟩, -⟩ := (GlobalTheory.ThetaAllChar.thetaFacts D).std hψ S T

  have hInt : ∀ a b : WO S T → ℂ, IsThetaFunO ψ S T a → IsThetaFunO ψ S T b →
      IntegrableOn (fun w => a w * (starRingEnd ℂ) (b w)) 𝓕 μ :=
    fun a b ha hb => (hHL μ μ 𝓕 𝓕 hμ hμ a b ha hb).2.1
  refine ⟨hInt f g hf hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    unfold ipO
    rw [← integral_conj]
    congr 1
    funext w
    rw [map_mul, Complex.conj_conj, mul_comm]
  · intro c
    constructor
    · unfold ipO
      rw [← integral_const_mul]
      congr 1
      funext w
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_mul, map_add]
      ring
    · unfold ipO
      rw [← integral_const_mul]
      congr 1
      funext w
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_mul, map_add]
      ring
  · intro f' hf'
    constructor
    · unfold ipO
      rw [← integral_add (hInt f g hf hg) (hInt f' g hf' hg)]
      congr 1
      funext w
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_mul, map_add]
      ring
    · unfold ipO
      rw [← integral_add (hInt g f hg hf) (hInt g f' hg hf')]
      congr 1
      funext w
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_mul, map_add]
      ring
  · exact ipO_self μ 𝓕 f
  ·

    intro h0
    haveI := countable_ratL' S T
    haveI : BorelSpace (WO S T) := ⟨rfl⟩
    haveI : MeasurableConstVAdd ↥(ratL T S) (WO S T) := ⟨fun γ => measurable_const_add (γ : WO S T)⟩
    haveI : VAddInvariantMeasure ↥(ratL T S) (WO S T) μ :=
      ⟨fun γ s _ => measure_preimage_add μ (γ : WO S T) s⟩
    unfold nrm2 at h0
    have hI : IntegrableOn (fun w => ‖f w‖ ^ 2) 𝓕 μ := by
      refine (hInt f f hf hf).norm.congr (Filter.Eventually.of_forall fun w => ?_)
      simp only [norm_mul, Complex.norm_conj, sq]
    have hae : (fun w => ‖f w‖ ^ 2) =ᵐ[μ.restrict 𝓕] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun w => sq_nonneg ‖f w‖) hI).1 h0
    have hae' : ∀ᵐ w ∂μ.restrict 𝓕, f w = 0 :=
      hae.mono fun w hw => by simpa using hw
    have htopen : IsOpen {x : WO S T | f x ≠ 0} := isOpen_ne_fun hf.cont continuous_const
    have hts : μ ({x : WO S T | f x ≠ 0} ∩ 𝓕) = 0 := by
      rw [← Measure.restrict_apply₀' hFD.nullMeasurableSet]
      exact ae_iff.1 hae'
    have hzero : μ {x : WO S T | f x ≠ 0} = 0 := by
      refine hFD.measure_zero_of_invariant _ (fun γ => ?_) hts
      ext y
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change f ((↑(-γ) : WO S T) + y) ≠ 0 ↔ f y ≠ 0
      rw [← norm_ne_zero_iff, (hSq f hf).1 (↑(-γ)) (-γ).2 y, norm_ne_zero_iff]
    have hempty := (htopen.measure_eq_zero_iff μ).1 hzero
    funext x
    by_contra hx
    have hmem : x ∈ {x : WO S T | f x ≠ 0} := hx
    rw [hempty] at hmem
    exact hmem
  · intro w
    refine ⟨hUnit μ 𝓕 hHaar hFD w f g hf hg, ?_⟩
    have hg' : IsThetaFunO ψ S T (heisO ψ S T (-w) g) := hPres (-w) g hg
    have e := hInvol (-w) g
    rw [neg_neg] at e
    calc ipO μ 𝓕 (heisO ψ S T w f) g
        = ipO μ 𝓕 (heisO ψ S T w f) (heisO ψ S T w (heisO ψ S T (-w) g)) := by rw [e]
      _ = ipO μ 𝓕 f (heisO ψ S T (-w) g) := hUnit μ 𝓕 hHaar hFD w f _ hf hg'
  ·
    intro μ' 𝓕' h'
    have a := (hHL μ' μ 𝓕' 𝓕 h' hμ f g hf hg).2.2
    have b := (hHL μ μ 𝓕 𝓕 hμ hμ f g hf hg).2.2
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.RealDirectionThetaNonzero.heisO_apply_zero] at a b
    unfold ipO
    rw [a, b]

end GlobalTheory.ThetaPairingLaws
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

theorem eq_smul_of_stable_graph : ∀ (D : D7) (X : HSp D) (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi), IsIrred X Pi rf rl → Module.rank ℂ Pi ≤ Cardinal.aleph0 → ∀ S : Submodule ℂ (Pi × Pi), (∀ g ∈ GfC X, ∀ x ∈ S, (rf g x.1, rf g x.2) ∈ S) → (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ S, (rl τ Y x.1, rl τ Y x.2) ∈ S) → (∀ x : Pi, ((x, 0) : Pi × Pi) ∈ S → x = 0) → (∀ y : Pi, ((0, y) : Pi × Pi) ∈ S → y = 0) → (∀ x : Pi, ∃ y : Pi, ((x, y) : Pi × Pi) ∈ S) → ∃ c : ℂ, c ≠ 0 ∧ ∀ x y : Pi, ((x, y) : Pi × Pi) ∈ S → y = c • x := by
  intro D X Pi rf rl hirr hrank S hf hl h1 h2 hon
  classical
  haveI : Nontrivial Pi := hirr.1
  choose t ht using hon
  have huniq : ∀ x y, ((x, y) : Pi × Pi) ∈ S → t x = y := by
    intro x y hxy
    have h0 : (((0 : Pi), t x - y) : Pi × Pi) ∈ S := by
      have := S.sub_mem (ht x) hxy
      simpa using this
    exact sub_eq_zero.1 (h2 _ h0)
  let T : Module.End ℂ Pi :=
    { toFun := t
      map_add' := fun a b => huniq _ _ (by simpa using S.add_mem (ht a) (ht b))
      map_smul' := fun r a => by
        simp only [RingHom.id_apply]
        exact huniq _ _ (by simpa using S.smul_mem r (ht a)) }
  have hTf : ∀ g ∈ GfC X, ∀ x, T (rf g x) = rf g (T x) := fun g hg x => huniq _ _ (hf g hg _ (ht x))
  have hTl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x, T (rl τ Y x) = rl τ Y (T x) := fun τ Y hY x => huniq _ _ (hl τ Y hY _ (ht x))
  obtain ⟨c, hc⟩ := GlobalTheory.LocGL.exists_not_isUnit_sub hrank T
  set A := T - algebraMap ℂ (Module.End ℂ Pi) c with hA
  have hAx : ∀ x, A x = T x - c • x := fun x => by simp [hA]
  have hAf : ∀ g ∈ GfC X, ∀ x, A (rf g x) = rf g (A x) := by
    intro g hg x; rw [hAx, hAx, hTf g hg, map_sub, map_smul]
  have hAl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x, A (rl τ Y x) = rl τ Y (A x) := by
    intro τ Y hY x; rw [hAx, hAx, hTl τ Y hY, map_sub, map_smul]
  have hA0 : A = 0 := by
    rcases hirr.2 (LinearMap.ker A)
        (fun g hg x hx => by rw [LinearMap.mem_ker] at hx ⊢; rw [hAf g hg, hx, map_zero])
        (fun τ Y hY x hx => by rw [LinearMap.mem_ker] at hx ⊢; rw [hAl τ Y hY, hx, map_zero]) with hk | hk
    · rcases hirr.2 (LinearMap.range A)
          (fun g hg x hx => by obtain ⟨z, rfl⟩ := hx; exact ⟨rf g z, hAf g hg z⟩)
          (fun τ Y hY x hx => by obtain ⟨z, rfl⟩ := hx; exact ⟨rl τ Y z, hAl τ Y hY z⟩) with hr | hr
      · exact LinearMap.range_eq_bot.1 hr
      · exact absurd ((Module.End.isUnit_iff _).2 ⟨LinearMap.ker_eq_bot.1 hk, LinearMap.range_eq_top.1 hr⟩) hc
    · exact LinearMap.ker_eq_top.1 hk
  have hTc : ∀ x, t x = c • x := fun x => by
    have := congrArg (fun f : Module.End ℂ Pi => f x) hA0
    simp only [hAx, LinearMap.zero_apply] at this
    exact sub_eq_zero.1 this
  refine ⟨c, ?_, fun x y hxy => by rw [← huniq x y hxy, hTc]⟩
  rintro rfl
  obtain ⟨x, hx⟩ := exists_ne (0 : Pi)
  exact hx (h1 x (by simpa [hTc] using ht x))

end GlobalTheory.SquareAgree
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri FieldCond)

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem squareNuHeckeCharacter_not_unramified_at_chosenPlace {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    ¬ (SqNum.nuH G t i j).UnrAt (G.pl.w G.pl.v0) := by
  intro hnu

  have hunder : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0 :=
    G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have hnotS1 : G.pl.v0 ∉ S1 D := G.ch.basePlace_not_mem_chiGridBadPlaces

  have hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t →
      (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ (G.pl.w G.pl.v0).under (𝓞 D.host.F) := by
    intro PP hPP
    rw [hunder]
    rcases hPP with hP | hP
    · intro heq
      apply hnotS1
      obtain ⟨k, hk⟩ := (hL.Pg PP).1 hP
      have hmem := GlobalTheory.LevelPlaces.mem_of_div L.C.P k PP hk
      have hF : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
        simpa using hmem
      rw [← heq, S1_mem_OmF]
      fin_cases k
      · exact Or.inl hF
      · exact Or.inr (Or.inl hF)
    · exact G.pl.levelPlace_ne_basePlace t PP hP
  obtain ⟨hxi, hmu⟩ := (GlobalTheory.levCh_unramified_places D T L μ₀ hL t).2.2.2 _ hoff

  have hchi := (G.ch.lev0 (D.R.m - i) (by omega) (by omega) _ hunder).2
  apply hchi
  intro x hx
  have h := hnu x hx
  change (L.C.mu0 j * L.xiH t / G.ch.chiH (D.R.m - i)).loc (G.pl.w G.pl.v0) x = 1 at h
  change (L.C.mu0 j).loc (G.pl.w G.pl.v0) x * (L.xiH t).loc (G.pl.w G.pl.v0) x * ((G.ch.chiH (D.R.m - i)).loc (G.pl.w G.pl.v0) x)⁻¹ = 1 at h
  rw [hmu j x hx, hxi x hx, one_mul, one_mul] at h
  exact inv_eq_one.mp h

end GlobalTheory.RowTest

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

theorem _root_.GlobalTheory.T.fourierJacobiPhase_adjacentInnerSteps_invariant : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (j : ℕ) (hA : j + 2 < Γ.m) (x x' : ColArgs Γ) (e e' : Vars Γ),
    (∀ i, i ≠ j → i ≠ j + 1 → x' i = x i) → (∀ i : Fin (Γ.m - 1), i.val ≠ j → i.val ≠ j + 1 → e' i = e i) →
    ch (stepPt (x' j) (e' ⟨j, by omega⟩)) + ch (stepPt (x' (j + 1)) (e' ⟨j + 1, by omega⟩)) +
        (if Even (Γ.m - 2 - j) then ∑ r, rowVar x' e' (j + 1) r * colVar x' e' ⟨j, by omega⟩ r else 0) =
      ch (stepPt (x j) (e ⟨j, by omega⟩)) + ch (stepPt (x (j + 1)) (e ⟨j + 1, by omega⟩)) +
        (if Even (Γ.m - 2 - j) then ∑ r, rowVar x e (j + 1) r * colVar x e ⟨j, by omega⟩ r else 0) →
    (Odd (Γ.m - 2 - j) → ∀ s : Fin (topRank Γ j), rowVar x' e' j s = rowVar x e j s) →
    (Odd (Γ.m - 2 - j) → ∀ r : Fin (topRank Γ (j + 1 + 1)), colVar x' e' ⟨j + 1, by omega⟩ r = colVar x e ⟨j + 1, by omega⟩ r) →
    phase x e = phase x' e' := by
  first | exact @GlobalTheory.TopLevelInv.phase_eq_of_two_steps | exact GlobalTheory.TopLevelInv.phase_eq_of_two_steps | (intros; apply GlobalTheory.TopLevelInv.phase_eq_of_two_steps <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

theorem _root_.GlobalTheory.T.fourierJacobiPhase_lastInnerVertex_invariant : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (j : ℕ) (hB : j + 2 = Γ.m) (κ : GL (Fin (topRank Γ (j + 1))) k) (x x' : ColArgs Γ) (e e' : Vars Γ),
    (∀ i, i ≠ j → i ≠ j + 1 → x' i = x i) → x' (j + 1) = x (j + 1) * κ.val →
    (∀ i : Fin (Γ.m - 1), i.val ≠ j → e' i = e i) →
    stepPt (x' j) (e' ⟨j, by omega⟩) = ((embX (Γ.m - 2 - j) κ)⁻¹).val * stepPt (x j) (e ⟨j, by omega⟩) →
    phase x e = phase x' e' := by
  first | exact @GlobalTheory.TopLevelInv.phase_eq_of_lastMove | exact GlobalTheory.TopLevelInv.phase_eq_of_lastMove | (intros; apply GlobalTheory.TopLevelInv.phase_eq_of_lastMove <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

theorem _root_.GlobalTheory.T.downwardVertexMap_lastVertex_mul_of_frame : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (j : ℕ) (hj : j + 1 < Γ.m) (hB : j + 2 = Γ.m)
    (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k) (κ : GL (Fin (topRank Γ (j + 1))) k),
    toFrame hs hj g = embX (Γ.m - 1 - (j + 1)) κ → ∀ (x x' : ColArgs Γ) (e e' : Vars Γ), x' (j + 1) = x (j + 1) * κ.val →
    downMap hs x' e' (j + 1) = downMap hs x e (j + 1) * g.val := by
  first | exact @GlobalTheory.TopLevelInv.downMap_last_mul_of_toFrame_eq | exact GlobalTheory.TopLevelInv.downMap_last_mul_of_toFrame_eq | (intros; apply GlobalTheory.TopLevelInv.downMap_last_mul_of_toFrame_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

theorem _root_.GlobalTheory.T.unfoldingFilledArgs_moveInnerLastColumnVertex : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (j : ℕ) (hj : j + 1 < Γ.m) (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k)
    (x x' : ColArgs Γ) (y : RowArgs Γ) (e e' : Vars Γ),
    (∀ l, l ≠ j → l ≠ j + 1 → downMap hs x' e' l = downMap hs x e l) →
    downMap hs x' e' j = (g⁻¹).val * downMap hs x e j →
    downMap hs x' e' (j + 1) = downMap hs x e (j + 1) * g.val →
    Γ.moveArgs .one (Pi.mulSingle (Γ.m, j + 1) g) (fill hs x y e) = fill hs x' y e' := by
  first | exact @GlobalTheory.TopLevelInv.fill_moveVertex | exact GlobalTheory.TopLevelInv.fill_moveVertex | (intros; apply GlobalTheory.TopLevelInv.fill_moveVertex <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.fourierJacobiPhase_adjacentSteps_invariant_vertex : ∀ {k : Type} [Field k] {n₀ n n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n] [DecidableEq n] [Fintype n₂] [DecidableEq n₂] {c : ℕ},
    ∀ v ∈ symN k n (c + 1), ∀ (κ : GL n k) (x₀ : Matrix n n₀ k) (e₀ : StepVar n (c + 1) n₀ → k) (x₁ : Matrix n₂ n k) (e₁ : StepVar n₂ c n → k)
      (d₀ : Matrix (n ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k) (d₁ : Matrix (n₂ ⊕ Fin c) (n ⊕ Fin (c + 1)) k),
      d₀ = ((v * embX (c + 1) κ)⁻¹).val * stepPt x₀ e₀ → d₁ = stepPt x₁ e₁ * (v * embX (c + 1) κ).val →
      (ch d₀ + ch d₁ + (if Even (c + 1) then ∑ r : n, (∑ l : Fin c, if l.val = c / 2 then d₁ (.inr l) (.inl r) else 0) *
          d₀ (.inl r) (.inr ⟨(c + 1) / 2, by omega⟩) else 0) =
        ch (stepPt x₀ e₀) + ch (stepPt x₁ e₁) + (if Even (c + 1) then ∑ r : n,
          (∑ l : Fin c, if l.val = c / 2 then stepPt x₁ e₁ (.inr l) (.inl r) else 0) *
            stepPt x₀ e₀ (.inl r) (.inr ⟨(c + 1) / 2, by omega⟩) else 0)) ∧
      (Odd (c + 1) → (∀ s : n₀, d₀ (.inr ⟨(c + 1) / 2, by omega⟩) (.inl s) = stepPt x₀ e₀ (.inr ⟨(c + 1) / 2, by omega⟩) (.inl s)) ∧
        ∀ r : n₂, d₁ (.inl r) (.inr ⟨c / 2, by omega⟩) = stepPt x₁ e₁ (.inl r) (.inr ⟨c / 2, by omega⟩)) := by
  first | exact @GlobalTheory.PhaseStep.phase_step_inv | exact GlobalTheory.PhaseStep.phase_step_inv | (intros; apply GlobalTheory.PhaseStep.phase_step_inv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepRows

open Matrix

theorem exists_model_of_enum {D : D7} (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) {V : HSp D} (hV : V.SigOK)
    {S : D.what₂.Tau → SPar} (O C : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hS : ∀ τ, ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧
      (Finset.univ.filter fun a => ε a = false).card = (V.sig (tauE D τ)).2)
    (hO : ∀ τ, ∃ ε : Fin V.rank → Bool, (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε ∧ C τ * O τ = O τ * Formalism.REAL.Jm ε) :
    ∃ M : DSModel V S, cart M = C := by
  classical
  have key : ∀ τ, ∃ σ : Equiv.Perm (Fin V.rank), ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧
      Formalism.QuantumDeterminants.IsHCParam lam ∧ ((O τ).submatrix id σ)ᴴ * gramAt D V τ * (O τ).submatrix id σ = Formalism.REAL.Jm ε ∧
      C τ * (O τ).submatrix id σ = (O τ).submatrix id σ * Formalism.REAL.Jm ε := by
    intro τ
    obtain ⟨lam, ε', hE, hH, hc⟩ := hS τ
    obtain ⟨ε, h1, h2⟩ := hO τ
    obtain ⟨σ, hσ⟩ := GlobalTheory.GridJoin.exists_perm_of_card_false ε ε' (by rw [GlobalTheory.GridJoin.card_false_of_gram hV τ h1, hc])
    have e : ε ∘ σ = ε' := funext hσ
    refine ⟨σ, lam, ε', hE, hH, ?_, ?_⟩
    · rw [GlobalTheory.GridJoin.gram_submatrix, h1, GlobalTheory.GridJoin.jm_submatrix, e]
    · rw [GlobalTheory.GridJoin.mul_submatrix_cols, h2, GlobalTheory.GridJoin.submatrix_mul_jm, e]
  choose σ lam ε hE hH h1 h2 using key
  obtain ⟨M, hM, -⟩ := GlobalTheory.T.exists_discreteSeriesModel_of_orthonormalBasis_cartan D hDS V S (fun τ => (O τ).submatrix id (σ τ)) C
    (fun τ => ⟨lam τ, ε τ, hE τ, hH τ, h1 τ⟩) (fun τ => ⟨ε τ, h1 τ, h2 τ⟩)
  exact ⟨M, hM⟩

theorem isHCParam_dual_parV (D : D7) (i j : ℕ) (τ : D.what₂.Tau) {n : ℕ} (lam : Fin n → ℝ) (ε : Fin n → Bool)
    (hn : n = rankV D i j) (hE : IsEnum (dualPar (parV D 1 i j τ)) lam ε) : Formalism.QuantumDeterminants.IsHCParam lam := by
  refine ⟨hE.1, fun a' => ?_⟩
  obtain ⟨-, q, hq, hS⟩ := hE
  have hmem : (q a', ε a') ∈ dualPar (parV D 1 i j τ) := by
    rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  simp only [parV, dualPar, GlobalTheory.SignedHC.shift, Finset.mem_image, Prod.mk.injEq] at hmem
  obtain ⟨y, ⟨x, hx, rfl⟩, hy1, -⟩ := hmem
  rw [← GlobalTheory.GridParDCount.grid_eq_num] at hx
  obtain ⟨z, hz⟩ := GlobalTheory.Grid.parD_entry_int D τ i j hx
  have hpar : Even (rankV D i j) ↔ Odd (i + j) := GlobalTheory.Grid.even_rkV_iff D i j
  rw [hq a', ← hy1]
  by_cases ho : Odd (i + j)
  · obtain ⟨N, hN⟩ := hpar.2 ho
    rw [if_pos ho]
    refine ⟨-z + 1 - N, ?_⟩
    have : (n : ℝ) = N + N := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring
  · have hne : ¬ Even (rankV D i j) := fun h => ho (hpar.1 h)
    obtain ⟨N, hN⟩ := Nat.not_even_iff_odd.1 hne
    rw [if_neg ho]
    refine ⟨-z - N, ?_⟩
    have : (n : ℝ) = 2 * N + 1 := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring

end GlobalTheory.SepRows
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.sum_quotientIntegerMatrices_invariant_integralGL_mul_left : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ϖ : kˣ) (e : ℕ), IsUnif ϖ → ∀ f : Matrix A B k → ℂ, (∀ Z Z' : Matrix A B k, (∀ i j, Z' i j ∈ 𝒪[k]) → f (Z + Z') = f Z) →
    ∀ M : GL A k, M ∈ KO k A →
      ∑ S : A → B → Res k e, f (M.val * ((ϖ ^ e)⁻¹ • liftRes S)) = ∑ S : A → B → Res k e, f ((ϖ ^ e)⁻¹ • liftRes S) := by
  first | exact @GlobalTheory.ResSumInv.sum_res_mul_left | exact GlobalTheory.ResSumInv.sum_res_mul_left | (intros; apply GlobalTheory.ResSumInv.sum_res_mul_left <;> assumption)
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (1 : Cls P (Fv F v)) ∈ XSet P (Fv F v) J ∧ (∀ (γ : GLoc σ J v) q, HasCls P (Fv F v) J γ q → (∃ g, g⁻¹ * γ * g ∈ stabLoc σ J L v) → q = 1) ∧ (∀ (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin r → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), gam h ∈ stabLoc σ J L v → ∀ t, torEmb h t ∈ stabLoc σ J L v ↔ t ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v) ∧ ∀ (μ : Measure (GLoc σ J v)) (dt : Measure (Tor P (Fv F v))), μ.IsHaarMeasure → dt.IsHaarMeasure → μ (stabLoc σ J L v) = 1 → dt (stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v) = 1 → ∀ q : XSet P (Fv F v) J, (q.1 = 1 → orbCls μ dt (unitLoc σ J L v) q = 1) ∧ (q.1 ≠ 1 → orbCls μ dt (unitLoc σ J L v) q = 0) := by
  first | exact @GlobalTheory.TrEll.eventually_unitLoc_orbCls | exact GlobalTheory.TrEll.eventually_unitLoc_orbCls | (intros; apply GlobalTheory.TrEll.eventually_unitLoc_orbCls <;> assumption)
end
