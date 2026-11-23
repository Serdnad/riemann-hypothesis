module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualIsotropicLineMemCompletionIff
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle326
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle599
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle211
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle503
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle200
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle201
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle240
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle369
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle010
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle429
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle402
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle504
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianPairing_onto_inverseIdeal_at_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A L : HSp D) (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D), IsSelfDualC S M → LineId o ζ M 𝔠 v → 𝔠 ≠ 0 →
      ∀ g ∈ idV 𝔠⁻¹ v, ∃ y ∈ latV S M (· = v), cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) = g := by
  first | exact @GlobalTheory.SeeSaw.HzOnto.hz_onto | exact GlobalTheory.SeeSaw.HzOnto.hz_onto | (intros; apply GlobalTheory.SeeSaw.HzOnto.hz_onto <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.dualIsotropicLine_mem_completion_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (L : Lat S) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (v : Pl D), IsSelfDualC S L → MonoId d L L₀ 𝔟 v → ∀ i : Fin ρ, 𝔟 i ≠ 0 →
      ∀ t ∈ idAt D (· = v), colMul d.jY i t ∈ latV S L (· = v) ↔ cA D t ∈ idV (𝔟 i)⁻¹ v := by
  first | exact @GlobalTheory.DualLine.dualLine_mem_iff | exact GlobalTheory.DualLine.dualLine_mem_iff | (intros; apply GlobalTheory.DualLine.dualLine_mem_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem sphFun_of_isParamFun : ∀ (D : D7) (V : HSp D) (Λ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Lat V) (Sf : Finset (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D)) (f : GA D V → ℂ)
    (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.LFun.IsParamFun D.sp.cm.sig V.gram Λ (Sf : Set (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D)) f B →
    GlobalTheory.Core.Rk.IP.SphFun V Λ Sf f := by
  intro D V Λ Sf f B hf v hv k hk g
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hx := (hf v (by simpa using hv) w hw).mem_fixed
  have := congrFun (hx ⟨k, hk⟩) g
  simpa [GlobalTheory.PRep.rightReg, LinearMap.funLeft] using this

theorem upNe_of_heckeForm : ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → MetEx D → LevFacts D → ZetaNe D → UpNe D := by
  intro D hHF _ _ hZ hgap c hc k hk s s' hs hs' p hp u B hB hL
  obtain ⟨mX, hmX⟩ : ∃ mX : Measure (WO s.V s'.V) × Set (WO s.V s'.V), IsCovolOne (ratL s'.V s.V) mX.1 mX.2 := by
    obtain ⟨ξ, f₀, hv⟩ := hp.vec
    exact hv.1.2.norm.1
  obtain ⟨φ, v, hvK, hZ'⟩ := hZ hgap c hc k hk s s' hs hs' p hp mX.1 mX.2 hmX
  refine ⟨φ, v, hvK, ?_⟩
  obtain ⟨hu0, hpar⟩ := hB
  obtain ⟨hI, hInt⟩ := hZ' u hu0
  have hF : PiLocalization₂.val u v ≠ 0 := by
    intro h0
    apply hI
    have : ∀ g, p.zint mX.1 mX.2 φ (PiLocalization₂.val u v) g = 0 := by
      intro g; simp [Step.zint, h0, PiLocalization₂.pet, Lift.pet, rTr]
    simp [this]
  have hparF := hpar v hF
  obtain ⟨cA, a, hcA, hcart, hJ, hmaj, hmaj_eq, hA0⟩ := GlobalTheory.T.thetaChainStage_realData_conj_value_mem_cuspForms D c hc k hk.le s hs
  obtain ⟨-, -, -, hcartB, -, -, -, -⟩ := GlobalTheory.T.thetaChainStage_realData_conj_value_mem_cuspForms D c hc (k + 1) hk s' hs'
  have hu1 : (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := hA0 u v hvK
  obtain ⟨hwitt, htwo⟩ := GlobalTheory.T.thetaChainStage_wittIndex_lt_and_places_two_split D c (k + 1) s' hk hs'
  obtain ⟨hfock, -, hunrT⟩ := GlobalTheory.T.thetaChainStep_fockVector_sphericalOffS D hgap c hc k hk s s' hs hs' p hp
  obtain ⟨-, -, hoff⟩ := GlobalTheory.T.doubledLatticeHeightFun_properties D s.V s.Λ a hs.selfDual hmaj
  have hmeas : MeasurableSet (intOff c s) := (hoff c.S).1.measurableSet
  have hr1 : 1 ≤ s.V.rank := by
    rw [hs.rank]; simp only [Ranks.rankY, Ranks.r]; have := D.R.two_le_m; omega
  have ht1 : 1 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hrk : s'.V.rank = s.V.rank + D.R.t := by rw [hs'.rank, hs.rank]; simp only [Ranks.rankY]; ring
  have hPair : GlobalTheory.Core.Rk.IP.Pair c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
      mX.1 mX.2 :=
    { setting := ⟨hr1, ht1, hrk, hc.inf, hs.sigOK, hcA, hcart, hcartB, hJ⟩
      maj := hmaj
      maj_eq := hmaj_eq
      weil := hp.weil
      covol := hmX }
  have hUnr : GlobalTheory.Core.Rk.IP.Unram c.ψ s.V s'.V (c.chT (k + 1)) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) :=
    ⟨hs.selfDual, hs'.selfDual, fun w _ h2 => htwo w h2, hunrT, (hfock φ).2, (hfock φ).2⟩
  have hsph := sphFun_of_isParamFun D s.V s.Λ c.S _ B hparF
  set F := PiLocalization₂.val u v with hFdef
  have hAut : Formalism.L2.Theta.IsAutFunSm c.θ s.V (fun g => conj (F g)) := hu1.1.1
  have hFl : ∀ γ ∈ GQ s.V, ∀ g, F (γ * g) = F g := fun γ hγ g => by
    simpa using congrArg (starRingEnd ℂ) (hAut.left γ hγ g)
  have hFc : Continuous F := by
    have h := hAut.cont.star
    change Continuous (fun g => star (star (F g))) at h
    simpa only [star_star] using h
  have hΦ : IsThetaFunO c.ψ s.V s'.V (p.pt φ) := (hfock φ).1.1
  have hθl : ∀ h, ∀ γ ∈ GQ s.V, ∀ g, thetaKO p.ω (γ * g) h (p.pt φ) = thetaKO p.ω g h (p.pt φ) := by
    intro h γ hγ g
    have e : ((γ * g, h) : GA D s.V × GA D s'.V) = (γ, 1) * (g, h) := by simp
    simp only [thetaKO, e, map_mul, Module.End.mul_apply]
    exact hp.weil.om_aut γ hγ 1 (one_mem _) _ (hp.weil.om_pres _ _ hΦ)
  have hθc : ∀ h, Continuous fun g => thetaKO p.ω g h (p.pt φ) := fun h =>
    (hp.weil.om_cont _ hΦ 0).comp (continuous_id.prodMk continuous_const)
  have hrc : ∀ g, GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F x)) (fun x => conj (F x)) g = conj (s.pet (rTr s.V g F) F) := by
    intro g
    have := GlobalTheory.T.integral_quotient_eq_setIntegral_fundamentalDomain D s.V s.ν s.fd hs.haar hs.fund (fun x => conj (F (x * g)) * conj (conj (F x)))
      (fun γ hγ x => by simp only [mul_assoc, hFl γ hγ]) (by fun_prop)
    simp only [GlobalTheory.Core.Rk.IP.rcoef, PiLocalization₂.pet, Lift.pet, rTr]
    rw [← integral_conj]
    simp only [map_mul]
    exact this
  have hup : ∀ h, GlobalTheory.Core.Rk.IP.up p.ω s.ν (p.pt φ) (fun x => conj (F x)) h = conj (p.up φ F h) := by
    intro h
    have := GlobalTheory.T.integral_quotient_eq_setIntegral_fundamentalDomain D s.V s.ν s.fd hs.haar hs.fund (fun g => thetaKO p.ω g h (p.pt φ) * conj (F g))
      (fun γ hγ x => by simp only [hθl h γ hγ, hFl γ hγ]) (by have := hθc h; fun_prop)
    simp only [GlobalTheory.Core.Rk.IP.up, Step.up]
    rw [← integral_conj]
    simp only [map_mul, Complex.conj_conj]
    exact this
  have hsZ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V = (D.R.t : ℂ) / 2 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, hrk]; push_cast; ring
  have hwz : ∀ g, GlobalTheory.Core.Rk.IP.wcoef p.ω mX.1 mX.2 (p.pt φ) (p.pt φ) g *
      GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F x)) (fun x => conj (F x)) g = p.zint mX.1 mX.2 φ F g := by
    intro g; simp only [Step.zint, hrc]; rfl
  have hint : ∃ s₁ : ℝ, s₁ < (D.R.t : ℝ) / 2 ∧ IntegrableOn (GlobalTheory.Core.Rk.IP.integrand p.ω s.ν mX.1 mX.2 s.Λ a (p.pt φ)
      (p.pt φ) (fun x => conj (F x)) (fun x => conj (F x)) s₁) (GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S) s.ν := by
    obtain ⟨s₁, hs₁, hi⟩ := hInt a hmaj hmaj_eq
    refine ⟨s₁, hs₁, hi.congr_fun (fun g hg => ?_) hmeas⟩
    simp only [GlobalTheory.Core.Rk.IP.integrand, GlobalTheory.Doubling.npow, (hoff c.S).2 g hg, hsZ, hrc]
    simp only [Step.zint, coefW, GlobalTheory.Core.Rk.IP.wcoef, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, hgtS]
    ring
  obtain ⟨-, -, -, hval⟩ := hHF c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
    mX.1 mX.2 hPair (Or.inr hwitt) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) (hfock φ).1 (hfock φ).1 hUnr s.ν s'.ν hs.haar hs'.haar
    _ hu1 _ hu1 B hparF hsph hint
  obtain ⟨l, hl0, hlv⟩ := hL
  have key := hval l hlv
  intro hup0
  have hz : GlobalTheory.Core.Rk.IP.up p.ω s.ν (p.pt φ) (fun x => conj (F x)) = 0 := by
    funext h; rw [hup, hup0]; simp
  rw [hz] at key
  have hlhs : GlobalTheory.Cusp.petersson s'.V s'.ν (0 : GA D s'.V → ℂ) 0 = 0 := by
    simp [GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet, GlobalTheory.AutomorphicL2Unitary.descend]
  rw [hlhs] at key
  have hvol : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν := by
    have := hs'.haar; exact GlobalTheory.RallisIP.Model.vol_pos s'.ν
  have hd : GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E (c.S : Set (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D)) s.V.rank s'.V.rank
      ((D.R.t : ℂ) / 2) ≠ 0 := by
    refine ((GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero D _ _ _).2 _ ?_).1
    simp only [Complex.div_ofNat_re, Complex.natCast_re]; positivity
  have hI' : ∫ g in GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S, GlobalTheory.Core.Rk.IP.wcoef p.ω mX.1 mX.2 (p.pt φ) (p.pt φ) g *
      GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F x)) (fun x => conj (F x)) g ∂s.ν ≠ 0 := by
    simp only [hwz]; exact hI
  have hvolC : ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hvol.ne'
  exact hI' (by
    have := key.symm
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hvolC
      · exact absurd h (div_ne_zero hl0 hd)
    · exact h)

end GlobalTheory.ChainOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.ComCols

variable {D : D7}

theorem isTypePlaces_of_levCh {L : LevCh D Unit} (hL : L.Is ()) : GlobalTheory.Core.Mi.IsTypePlaces L.Pg := by
  classical
  refine ⟨fun PP hPP => ?_, fun v hv => ?_⟩
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPP
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := L.C.P.overP hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ h1
    · exact Ideal.mul_mem_left _ _ h1
  · have := v.isMaximal
    obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    let W : Formalism.L2.DIV.Pl D.host.E := ⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
    have hW : W.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hQ'.over.symm
    have hk : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal := by
      rw [← hW] at hv
      have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ W.asIdeal := hv
      rw [map_natCast, Nat.cast_mul] at h2
      exact (W.isPrime.mem_or_mem h2).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
    obtain ⟨k, hk⟩ := hk
    have hS := GlobalTheory.ChainOnto.Model.mem_S hL (GlobalTheory.Member.exists_isInfFam_family D).choose 1 L.triv k W hk
    unfold GlobalTheory.ChainOnto.Com.S at hS
    obtain ⟨P, hP, e⟩ := Finset.mem_image.1 hS
    refine ⟨P, ⟨hP, e.trans hW⟩, ?_⟩
    rintro P' ⟨hP', e'⟩
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (e'.trans (e.trans hW).symm) with h | h
    · exact h
    · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 h) (GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL () (Or.inl hP) (Or.inl hP'))

theorem com_is_of_levCh {L : LevCh D Unit} (hL : L.Is ()) (c : GlobalTheory.ChainOnto.Com D) (hθ : IsInfFam c.θ) (hψ : IsStdChar D c.ψ (-1))
    (hP : c.Pg = L.Pg) (hμ : ∀ j : Fin D.R.m, ChrEq (c.μ ((j : ℕ) + 1)) (L.C.mu0 j)) (hη : ChrEq c.η L.C.eta)
    (hχ : ∀ j : Fin D.R.m, ∀ PP ∈ c.Pg, IsRes (L.C.mu0 j) PP (c.chi ((j : ℕ) + 1) PP)⁻¹) : c.Is := by
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D c.η L.C.eta hη L.C.isEta
  have hS : ∀ (k : Fin 2) (Q : Formalism.L2.DIV.Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      Q.under (𝓞 D.host.F) ∈ c.S := fun k Q hk => by
    have := GlobalTheory.ChainOnto.Model.mem_S hL c.θ c.ψ L.triv k Q hk
    unfold GlobalTheory.ChainOnto.Com.S at this ⊢
    rw [hP]
    exact this
  refine ⟨hθ, hψ, ⟨hη.1, GlobalTheory.Mem.TupChar.unramEverywhere hη L.C.isEta.unr, ⟨⟨_, hres⟩, fun η h a => ?_⟩, fun τ => ?_,
    fun j hj => ?_⟩, fun j τ => ?_, fun j w hw => ?_, fun j => ⟨_, hμ j, hχ j⟩, ?_⟩
  · rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique h hres, pow_one, MonoidHom.comp_apply]
  · exact GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hη
      (GlobalTheory.InnerSteps.hasInfQ_tauE (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hi : i < D.R.m := by omega
    refine ⟨(hμ ⟨i, hi⟩).1, ⟨_, hres⟩, fun η _ a => ?_⟩
    show c.μ (i + 1) (idF D a) = _
    rw [pow_zero]
    exact GlobalTheory.GridWeil.triv_base (hμ ⟨i, hi⟩) (L.C.isMu0 ⟨i, hi⟩).triv a
  · have h1 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hμ j) (GlobalTheory.InnerSteps.hasInfQ_tauE (L.C.isMu0 j).inf) τ
    simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
    exact h1
  · exact (GlobalTheory.LFun.unrAt_iff_of_chrEq (hμ j) w).2 ((L.C.isMu0 j).unr w fun k hk => hw (hS k w hk))
  · rw [hP]
    exact GlobalTheory.CentralShift.exists_idemSum _ fun Q hQ Q' hQ' => GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL () (Or.inl hQ) (Or.inl hQ')

end GlobalTheory.SeeSaw.ComCols
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)

namespace GlobalTheory.LastSeeSawDatum

section Helpers

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem comb_apply' {S T : HSp D} (c : WO S T →₀ ℂ) (g : WO S T → ℂ) (u : WO S T) :
    comb ψ S T c g u = ∑ x ∈ c.support, c x * (ψ (symplOH S T u x) * g (u + x)) := by
  simp only [comb, Finset.sum_apply, Pi.smul_apply, heisO, smul_eq_mul]

theorem isThetaFunO_add' {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) := {
  quasi γ w := by simp only [Pi.add_apply]; rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    obtain ⟨U', hUo', hU'⟩ := hg.level
    refine ⟨U ⊓ U', hUo.inter hUo', fun u hu hi => ?_⟩
    funext w
    have h1 := congrFun (hU u hu.1 hi) w
    have h2 := congrFun (hU' u hu.2 hi) w
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  cont := hf.cont.add hg.cont
  smooth k L hL hfin w := (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w) }

theorem heisO_smul' {S T : HSp D} (u : WO S T) (r : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (r • f) = r • heisO ψ S T u f := by
  funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem heisO_add' {S T : HSp D} (u : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g := by
  funext w; simp only [heisO, Pi.add_apply]; ring

theorem heisO_zero' {S T : HSp D} (u : WO S T) : heisO ψ S T u (0 : WO S T → ℂ) = 0 := by
  funext w; simp only [heisO, Pi.zero_apply, mul_zero]

theorem isThetaFunO_zero' (S T : HSp D) : IsThetaFunO ψ S T (0 : WO S T → ℂ) := {
  quasi γ w := by simp only [Pi.zero_apply, mul_zero]
  level := ⟨⊤, isOpen_univ, fun u _ _ => heisO_zero' u⟩
  cont := continuous_const
  smooth k L hL hfin w := by simp only [Pi.zero_apply]; exact contDiff_const }

theorem isThetaFunO_smul' {S T : HSp D} (r : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (r • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    exact ⟨U, hUo, fun u hu hi => by rw [heisO_smul', hU u hu hi]⟩
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := by
    simp only [Pi.smul_apply, smul_eq_mul]; exact contDiff_const.mul (hf.smooth k L hL hfin w) }

variable {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop}

theorem vac_zero : Vac ψ S T LS LT P 0 :=
  ⟨isThetaFunO_zero' S T, fun u _ => heisO_zero' _, fun e _ u _ _ => heisO_zero' _⟩

theorem vac_add {f g : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) (hg : Vac ψ S T LS LT P g) :
    Vac ψ S T LS LT P (f + g) :=
  ⟨isThetaFunO_add' hf.1 hg.1, fun u hu => by rw [heisO_add', hf.2.1 u hu, hg.2.1 u hu],
    fun e he u hu hu' => by rw [heisO_add', hf.2.2 e he u hu hu', hg.2.2 e he u hu hu']⟩

theorem vac_smul (r : ℂ) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT P (r • f) :=
  ⟨isThetaFunO_smul' r hf.1, fun u hu => by rw [heisO_smul', hf.2.1 u hu],
    fun e he u hu hu' => by rw [heisO_smul', hf.2.2 e he u hu hu']⟩

theorem vac_sum {ι : Type} (s : Finset ι) (r : ι → ℂ) (f : ι → WO S T → ℂ)
    (h : ∀ i ∈ s, Vac ψ S T LS LT P (f i)) : Vac ψ S T LS LT P (∑ i ∈ s, r i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (vac_zero : Vac ψ S T LS LT P 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact vac_add (vac_smul _ (h a (Finset.mem_insert_self a s))) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem comb_smul_fun (c : WO S T →₀ ℂ) (r : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (r • f) = r • comb ψ S T c f := by
  funext u
  simp only [comb_apply', Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem comb_sum_fun {ι : Type} (c : WO S T →₀ ℂ) (s : Finset ι) (r : ι → ℂ) (f : ι → WO S T → ℂ) :
    comb ψ S T c (∑ i ∈ s, r i • f i) = ∑ i ∈ s, r i • comb ψ S T c (f i) := by
  funext u
  simp only [comb_apply', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring

theorem comb_swap {A S X : HSp D} (c : WO A S →₀ ℂ) (c' : WO S X →₀ ℂ) (G : WO A S → WO S X → ℂ)
    (u : WO A S) (x : WO S X) :
    comb ψ S X c' (fun x' => comb ψ A S c (fun u' => G u' x') u) x =
      comb ψ A S c (fun u' => comb ψ S X c' (G u') x) u := by
  simp only [comb_apply', Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Helpers

theorem lastDatum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → IsSumFrame o'' ζ₀ γ γ₀ → ∀ (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsFullLattice k] (Ψ : Matrix n n' k → ℂ) (LA : Lat A) (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → β.IsLat LS Q.lat → γ.IsLat LT Λ → ∀ (c : WO A S →₀ ℂ) (c' : WO S X →₀ ℂ), CombAt (· = p.v) c → CombAt (· = p.v) c' → (∀ f₀, Vac ψ A S LA LS (· = p.v) f₀ → Over ψ α β LA LS f₀ Ψ (comb ψ A S c f₀)) → (∀ f₀, Vac ψ S X LS LX (· = p.v) f₀ → Over ψ β γ₀ LS LX f₀ (phiOne (ε • Q) (lastPair q Λ)) (comb ψ S X c' f₀)) → ∃ (e : WO A S →₀ ℂ) (e' : WO S X →₀ ℂ), CombAt (· = p.v) e ∧ CombAt (· = p.v) e' ∧ ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ (charInd (resChar χ hχ q) Q)) Ξ → Vac ψ S T LS LT (· = p.v) Φ₂ → BiVacAt ψ LA LS LX (· = p.v) (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) ∧ lastBi o o'' τ Ξ Φ₂ = biComb ψ A S X c c' (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) := by
  intro D k _ _ _ _ p q ψ hψ hU χ hχ hIC n n' n'' _ _ _ _ _ _ V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  obtain ⟨ε, hε⟩ := GlobalTheory.T.lastSeesaw_datum_eq_lattice_pair_over_vacuum D k p q ψ hψ hU χ hχ hIC n n' n'' V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  refine ⟨ε, ?_⟩
  intro α α₀ β γ γ₀ hα hγ Q Λ _ Ψ LA LS LT LX hLA hLS hLT hLX hβQ hγΛ c c' hc hc' hcv hcv'
  obtain ⟨e, he, heP⟩ := GlobalTheory.T.splitPlaceDatum_carried_back_to_baseVacuum D k p n n' ψ hψ hU A S α β LA LS hLA hLS Ψ c hc hcv
  obtain ⟨e', he', heP'⟩ := GlobalTheory.T.splitPlaceDatum_carried_back_to_baseVacuum D k p (n'' ⊕ Fin 1) n ψ hψ hU S X β γ₀ LS LX hLS hLX _ c' hc' hcv'
  refine ⟨e, e', he, he', ?_⟩
  intro L₁ L₂ f₁ Ξ Φ₂ hΞ hΦ₂
  have ha : charInd (resChar χ hχ q) Q ≠ 0 := by
    intro h
    have hev : Q.ev 0 = 0 := by
      unfold Pair.ev
      rw [dite_eq_left Q.lat.zero_mem]
      exact map_zero Q.fn
    have h0 := congrFun h 0
    simp only [charInd, vecInd, hev, neg_zero, AddChar.map_zero_eq_one, Q.lat.zero_mem, if_true, mul_one,
      Pi.zero_apply] at h0
    exact one_ne_zero h0
  have hA : ∀ y : WO L S, Vac ψ A S LA LS (· = p.v) (comb ψ A S e (fun u => Ξ ((o.resS S).symm (u, y)))) ∧
      comb ψ A S c (comb ψ A S e (fun u => Ξ ((o.resS S).symm (u, y)))) = fun u => Ξ ((o.resS S).symm (u, y)) := by
    intro y
    obtain ⟨g, hg⟩ := GlobalTheory.T.sliceAlongLine_datum_over_vacuum_splitPlace D k p n n' ψ hψ hU V₀ A L S o ζ hζ α α₀ β hα Ψ _ ha LA LS hLA hLS L₁ L₂ f₁ Ξ hΞ y
    exact heP g _ hg
  have hcol : ∀ x, (fun u => lastBi o o'' τ Ξ Φ₂ u x) =
      Φ₂ (o''.resT S x).1 • fun u => Ξ ((o.resS S).symm (u, kap τ S (o''.resT S x).2)) := by
    intro x; funext u; rfl
  have hAc : ∀ x, Vac ψ A S LA LS (· = p.v) (comb ψ A S e (fun u => lastBi o o'' τ Ξ Φ₂ u x)) ∧
      comb ψ A S c (comb ψ A S e (fun u => lastBi o o'' τ Ξ Φ₂ u x)) = fun u => lastBi o o'' τ Ξ Φ₂ u x := by
    intro x
    rw [hcol x, comb_smul_fun, comb_smul_fun]
    exact ⟨vac_smul _ (hA _).1, by rw [(hA _).2]⟩
  have hX : ∀ u, Vac ψ S X LS LX (· = p.v) (comb ψ S X e' (lastBi o o'' τ Ξ Φ₂ u)) ∧
      comb ψ S X c' (comb ψ S X e' (lastBi o o'' τ Ξ Φ₂ u)) = lastBi o o'' τ Ξ Φ₂ u := by
    intro u
    obtain ⟨g, hg⟩ := hε α α₀ β γ γ₀ hα hγ Q Λ Ψ LS LT LX hLS hLT hLX hβQ hγΛ L₁ L₂ f₁ Ξ Φ₂ hΞ hΦ₂ u
    exact heP' g _ hg
  generalize lastBi o o'' τ Ξ Φ₂ = C at hAc hX ⊢
  refine ⟨⟨fun x => ?_, fun u => ?_⟩, ?_⟩
  · have e1 : (fun u' => comb ψ S X e' (C u') x) =
        ∑ j ∈ e'.support, (e' j * ψ (symplOH S X x j)) • fun u' => C u' (x + j) := by
      funext u'
      simp only [comb_apply', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    show Vac ψ A S LA LS (· = p.v) (comb ψ A S e (fun u' => comb ψ S X e' (C u') x))
    rw [e1, comb_sum_fun]
    exact vac_sum _ _ _ fun j _ => (hAc (x + j)).1
  · have e2 : (fun x => comb ψ A S e (fun u' => comb ψ S X e' (C u') x) u) =
        ∑ i ∈ e.support, (e i * ψ (symplOH A S u i)) • comb ψ S X e' (C (u + i)) := by
      funext x
      simp only [comb_apply', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    show Vac ψ S X LS LX (· = p.v) (fun x => comb ψ A S e (fun u' => comb ψ S X e' (C u') x) u)
    rw [e2]
    exact vac_sum _ _ _ fun i _ => (hX (u + i)).1
  · funext u x
    have hsw : ∀ u', comb ψ S X c' (fun x' => comb ψ A S e (fun u'' => comb ψ S X e' (C u'') x') u') x =
        comb ψ A S e (fun u'' => C u'' x) u' := by
      intro u'
      have h1 := comb_swap (ψ := ψ) e c' (fun u'' x' => comb ψ S X e' (C u'') x') u' x
      beta_reduce at h1
      rw [h1]
      congr 1
      funext u''
      exact congrFun (hX u'').2 x
    show C u x = comb ψ A S c (fun u' => comb ψ S X c' (fun x' => comb ψ A S e (fun u'' => comb ψ S X e' (C u'') x') u') x) u
    simp only [hsw]
    exact (congrFun (hAc x).2 u).symm

end GlobalTheory.LastSeeSawDatum
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.lastSeeSaw_thetaIdentity : ∀ D : D7, SeeLast D := by
  first | exact @GlobalTheory.SeeLastPf.seeLast | exact GlobalTheory.SeeLastPf.seeLast | (intros; apply GlobalTheory.SeeLastPf.seeLast <;> assumption)
end
