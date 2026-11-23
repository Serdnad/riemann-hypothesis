module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle859
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle872
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenMapTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTermsMeanZeroUnipotentRadical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyDerivCompNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle884
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle352
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle889
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle885
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle886
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipMapsHalfTranslatesSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle879
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle506
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle883
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle115
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Order.Interval.Finset.Box
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum


noncomputable section

namespace GlobalTheory.SingleDatum.AddValue

theorem theta_transSum {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) (V W : HSp D) (l : Geo.Tor.Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E))
    (e : AE D) {f₀ : WO V W → ℂ} (hf : IsThetaFunO ψ V W f₀) (w : (Fin V.rank → LevQ Dw l) → ℂ) :
    IsThetaFunO ψ V W (transSum ψ V W l ι e f₀ w) := by
  haveI := GlobalTheory.AdTh.ShortSeries.finite_levQ Dw l
  letI : Fintype (Fin V.rank → LevQ Dw l) := Fintype.ofFinite _
  unfold transSum
  rw [finsum_eq_sum_of_fintype]
  refine GlobalTheory.WeilVacMove.isTheta_smul _ ?_
  exact Finset.sum_induction _ (IsThetaFunO ψ V W) (fun _ _ => GlobalTheory.WeilVacMove.isTheta_add) GlobalTheory.WeilVacMove.isTheta_zero
    fun q _ => GlobalTheory.WeilVacMove.isTheta_smul _ (GlobalTheory.AnisoMean.isTheta_heisO hψ hf _)

theorem fvar_eq {D : D7} {m n : ℕ} {τ : D.host.E →+* ℂ} {i p : ℕ} {j : Fin n} {x y : FVar D m n}
    (hx : x.2.2 = j ∧ ((τ = tauE D x.1 ∧ (x.2.1 : ℕ) = i) ∨ (τ = conjEmb (tauE D x.1) ∧ (x.2.1 : ℕ) = p + i)))
    (hy : y.2.2 = j ∧ ((τ = tauE D y.1 ∧ (y.2.1 : ℕ) = i) ∨ (τ = conjEmb (tauE D y.1) ∧ (y.2.1 : ℕ) = p + i)))
    (hne : ∀ s t : D.what₂.Tau, tauE D s ≠ conjEmb (tauE D t)) : x = y := by
  have hc : ∀ s t : D.what₂.Tau, conjEmb (tauE D s) = conjEmb (tauE D t) → s = t := fun s t h => by
    apply GlobalTheory.StdRat.tauE_injective D
    ext z
    have := congrArg (starRingEnd ℂ) (RingHom.congr_fun h z)
    simpa [conjEmb] using this
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := y
  obtain ⟨hx3, hx'⟩ := hx
  obtain ⟨hy3, hy'⟩ := hy
  dsimp only at hx3 hy3 hx' hy'
  have key : x1 = y1 ∧ (x2 : ℕ) = y2 := by
    rcases hx' with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hy' with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact ⟨GlobalTheory.StdRat.tauE_injective D (a1.symm.trans b1), by omega⟩
    · exact absurd (a1.symm.trans b1) (hne _ _)
    · exact absurd (b1.symm.trans a1) (hne _ _)
    · exact ⟨hc _ _ (a1.symm.trans b1), by omega⟩
  obtain ⟨k1, k2⟩ := key
  rw [k1, Fin.ext k2, hx3, hy3]

theorem sq_root_identity (S m z : ℂ) (hm : m ≠ 0) (hz : z = m * (S * S)) : S = S⁻¹ * (m⁻¹ * z) := by
  subst hz
  by_cases hS : S = 0
  · simp [hS]
  · field_simp

end GlobalTheory.SingleDatum.AddValue
end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum


namespace GlobalTheory.SingleDatum.ShortSum
open GlobalTheory.AdTh.ShortSeries



theorem thetaKO_transSum_eq_short_series : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW s f₀ → ∀ (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → ∀ (r g q0 : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (hq : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x₀ : Frame X.Ψ r) (vr : Harm.Var X.Ψ q0 X.p0 (Fin V.rank) ≃ FVar D W.rank V.rank) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsMod W hr X → IsSympl X bas → IsONFr X x₀ → IsInvOf W hr X x₀ s → IsBasOf W hr X hq x₀ BW → IsVarOf V W X q0 vr → ∀ (bad N : ℕ) (h : GA D V) (k : GA D W) (Λ : GenLat D.host.E V.rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (e' : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), l₂.M ∣ bad → IsIdemSum e' Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC V → SuppAt e' V h → IsDetAt e' V h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (finPt V h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ W hr ι k mk → ∀ Y : (Fin V.rank → LevQ Dw l₂) → Matrix (Fin V.rank) (Fin r) D.host.E, IsRoots l₂ (latR hr (latG W k)) mk N Y → ∀ (v : TF V.rank g) (a : ℂ), IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E V.rank) (latR hr (latG W k))) v → Reads θ V W hr X bas idx (om (1, k) f₀) (a • v) (frMove θ W hr X k x₀) → ∀ (w : (Fin V.rank → LevQ Dw l₂) → ℂ) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin V.rank)) (d : ℕ), P.IsHomogeneous d → thetaKO om h k (pureTensorO ψ θ V W (fun _ => 1) s (fun _ => 1) BW (transSum ψ V W l₂ ι e f₀ w) (MvPolynomial.rename vr P)) = (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d * a * (((χW y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ r) : ℂ)) * ((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ * thP X hq bas idx (gphi X bas (H.w0 : D.host.E) Λ.La (latR hr (latG W k)) v w Y) P (frMove θ W hr X k x₀) := by
  intro D H Dw ψ θ V W χV χW om ΛV ΛW s f₀ hVP ι hι hrt l₂ e he r g q0 hr X hq bas idx x₀ vr BW hM hS hx hinv hbas hvr
    bad N h k Λ mk e' Ps y hbad he' hPs hh hsupp hdet hΛ htriv hlev hmk Y hY v a hv hR w P d hd
  choose p hp using fun q => exists_finOf V W hr (Y q)
  obtain ⟨hthP, hdat⟩ := GlobalTheory.T.translateSum_vacuum_moved_by_adelicPair D H Dw ψ θ V W χV χW om ΛV ΛW s f₀ hVP
    ι hι l₂ e he r hr bad N h k Λ mk hbad ⟨hh, e', Ps, he', hPs, hsupp⟩ hΛ htriv hlev hmk Y (fun q => (p q).1)
    (fun q => (p q).2) hY hp w
  obtain ⟨hP, -, hV0, hW0, hVs, hWs, hVstd, -, hvac⟩ := hVP
  have hψ := hP.weil.std
  haveI := finite_levQ Dw l₂
  letI : Fintype (Fin V.rank → LevQ Dw l₂) := Fintype.ofFinite _
  obtain ⟨hhs, hks, -, hlat, hV1, -⟩ := GlobalTheory.MovedLat.moved_lattices D _ _ _ _ hV0 hW0 hVs hWs h k
  obtain ⟨-, -, hmv, -⟩ := GlobalTheory.MovedLat.moved_lattices D _ _ _ _ hV0 hW0 hVs hWs 1 k
  rw [show fin V 1 = 1 from map_one _, hV1] at hmv
  have hx' := isONFr_move hψ hP.inf hP.std hP.even hr X bas idx hM hS hx k
  have hvac' := GlobalTheory.WeilVacMove.isVacO_om D _ _ _ _ _ _ _ hP.weil hP.inf (fun _ => 1) (fun _ => 1) _
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt _ k) * s τ * compAt θ τ (Formalism.L2.Theta.mt _ k⁻¹))
    _ _ _ _ 1 k (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.mul_assoc, GlobalTheory.WeilVacMove.compAt_mt_inv_mul, Matrix.mul_one]) hmv _ hvac
  have hL : ∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E),
      L₀ = Submodule.span (𝓞 D.host.E)
        {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ Bridge.hLat W (fin W k), w = a • v} →
      latR hr (latG W k) = latR hr L₀ := fun L₀ h₀ => by rw [h₀, hlat]
  have hcl := GlobalTheory.T.weilRepresentation_split_support_projects_vacuum D _ _ _ _ _ _ _ hP _ g hr X bas idx hM hS H hrt _ _ Λ.La _ hV0 hVs hks hVstd hL _ _ hx'
    (isInvOf_move hr X hinv k) _ hvac' _ hR e' Ps h y he' hsupp hdet hΛ
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, projA_smul, smul_smul] at hcl
  obtain ⟨-, hsd, huni, hfg⟩ := LatOf.isLatOf_tens D _ _ _ _ _ g hr X bas idx hψ hP.inf hP.std hP.even hM hS
    _ _ Λ.La _ hhs hks hΛ hL
  obtain ⟨hth, hsum⟩ := reads_sum hψ hP.inf hP.std hP.even hr X bas idx hM hS hx'
    (hP.weil.om_pres (h, k) _ hvac.2.theta) hcl w (fun q => (p q).1) (fun q => (p q).2) (fun q => (hp q).2)
    Finset.univ
  rw [finsum_eq_sum_of_fintype] at hdat
  have hrd := (reads_linear_injective D _ _ _ _ _ g hr X bas idx hψ hP.inf hP.std hP.even hM hS _ hx'
    _ _ _ _ hsum hsum).1 ((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ 0
  rw [zero_smul, zero_smul, add_zero, add_zero, ← hdat] at hrd
  simp only [heisG_smul, (hp _).1] at hrd
  simp only [smul_comm (w _)] at hrd
  rw [← Finset.smul_sum, smul_smul, ← finsum_eq_sum_of_fintype] at hrd
  rw [kernel_of_reads hP hr X bas idx hM hS hq hx hinv hbas hvr hh k hthP hrd P d hd,
    theta_smul₂ idx hS hP.even hq hx'.mem_dom _ _ hrd.1]
  have hpar := Parity.thP_gphi_neg _ _ g _ X bas idx hS hP.even q0 hq (H.w0 : D.host.E) H.w0.isIntegral_coe (cmHost_idempotent_trace_eq_one H)
    _ hsd v hv Λ huni hfg _ w Y P d hd _ hx'.mem_dom
  unfold gphi at hpar ⊢
  rw [hpar]
  push_cast
  ring
end GlobalTheory.SingleDatum.ShortSum
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.halfTranslates_le_levelHalfTranslates_of_dvd : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (e₂ e' : AE D) (P' : Finset (Formalism.L2.DIV.Pl D.host.E)), IsHalfIdem l₂ e₂ → IsIdemSum e' P' → (∀ PP ∈ P', l₂.Mb ≤ PP.asIdeal) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (f₀ : WO V W → ℂ) (M : ℕ) (O : Subring ℂ), trSp ψ V W ΛV ΛW f₀ e' M O ≤ trSp ψ V W ΛV ΛW f₀ e₂ M O := by
  first | exact @GlobalTheory.LevelSeries.trSp_le_of_subhalf | exact GlobalTheory.LevelSeries.trSp_le_of_subhalf | (intros; apply GlobalTheory.LevelSeries.trSp_le_of_subhalf <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.specialised_universal_series_eq_twisted_thetaSeries : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) →
    ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      specXi ρ Y i j b k Q M χ h P = specSer ρ Y i j b k Q M χ h P := by
  first | exact @GlobalTheory.SpecFac.specXi_eq_specSer | exact GlobalTheory.SpecFac.specXi_eq_specSer | (intros; apply GlobalTheory.SpecFac.specXi_eq_specSer <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

theorem exists_pow_mul_mem_of_mem_fieldRange (z : ℂ) (l : ℕ) (hl : l.Prime) : ∃ c : ℕ, ∀ (k : Type) [Field k] [NumberField k]
    (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O →
    z ∈ σ.fieldRange → (l : ℂ) ^ c * z ∈ O := by
  classical
  by_cases h : ∃ m : ℕ, m ≠ 0 ∧ IsIntegral ℤ ((m : ℂ) * z)
  · obtain ⟨m, hm0, hint⟩ := h
    obtain ⟨c, m', hm', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 l hl.ne_one
    refine ⟨c, fun k _ _ σ la O hla hO hz => ?_⟩
    obtain ⟨y, rfl⟩ := hz
    have hti : IsIntegral ℤ ((m : k) * y) := by
      rw [← isIntegral_algHom_iff σ.toIntAlgHom σ.injective]
      simpa using hint
    have hm'0 : (m' : k) ≠ 0 := by
      rintro h0
      rw [Nat.cast_eq_zero] at h0
      subst h0
      simp at hmeq
      exact hm0 hmeq
    have hcop : IsCoprime (m' : ℤ) (l : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).2 hm'))
    have hnot : ((m' : ℕ) : 𝓞 k) ∉ la.asIdeal := by
      intro hmem
      obtain ⟨s, t, hst⟩ := hcop
      apply la.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have : ((s : 𝓞 k) * ((m' : ℕ) : 𝓞 k) + (t : 𝓞 k) * ((l : ℕ) : 𝓞 k)) = 1 := by
        have := congrArg (Int.cast : ℤ → 𝓞 k) hst
        push_cast at this
        exact this
      rw [← this]
      exact la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hmem) (la.asIdeal.mul_mem_left _ hla)
    have hv1 : la.valuation k (m' : k) = 1 := by
      have e : ((m' : ℕ) : k) = algebraMap (𝓞 k) k ((m' : ℕ) : 𝓞 k) := (map_natCast _ _).symm
      rw [e, HeightOneSpectrum.valuation_of_algebraMap]
      exact HeightOneSpectrum.intValuation_eq_one_iff.2 hnot
    have hvt : la.valuation k ((m : k) * y) ≤ 1 := by
      have := HeightOneSpectrum.valuation_le_one (K := k) la (⟨(m : k) * y, hti⟩ : 𝓞 k)
      exact this
    have heq : ((l : k) ^ c * y) = ((m : k) * y) / (m' : k) := by
      rw [hmeq]; push_cast; field_simp
    have hmem := hO ((l : k) ^ c * y) (by rw [heq, map_div₀, hv1, div_one]; exact hvt)
    simpa using hmem
  · refine ⟨0, fun k _ _ σ la O hla hO hz => ?_⟩
    exfalso
    obtain ⟨y, rfl⟩ := hz
    have hy : IsAlgebraic ℤ y := (IsFractionRing.isAlgebraic_iff ℤ ℚ k).2 (Algebra.IsAlgebraic.isAlgebraic y)
    obtain ⟨m, hm0, hmi⟩ := hy.exists_integral_multiple
    apply h
    refine ⟨m.natAbs, by simpa using hm0, ?_⟩
    have h2 : IsIntegral ℤ (σ (m • y)) := hmi.map σ.toIntAlgHom
    rcases Int.natAbs_eq m with hm | hm
    · rw [hm] at h2; simpa [zsmul_eq_mul] using h2
    · rw [hm] at h2
      have h3 := h2.neg
      simpa [zsmul_eq_mul, neg_mul] using h3

theorem flipScal_pow_mem : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l : ℕ), ChiData χW χ M₀ → l.Prime → M₀ ≠ 0 → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)), ∃ c : ℕ, ∀ (eT : AE D) (x : (AE D)ˣ), IsIdemSum eT T → (∀ PP ∈ T, ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsFlipDet V eT M₀ x → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → Odd M₀ → Nat.Coprime M₀ (GlobalTheory.Tow.badN D) → (l : ℂ) ^ c * flipScal χW V W T M₀ x ∈ O := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hVP hW χ M₀ l hχ hl hM T
  have hM' : ((M₀ : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hM
  set u : D.host.Eˣ := Units.mk0 _ hM' with hu
  set z : ℂ := (∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ V.rank) *
    ((Real.sqrt (flipIdx V W T M₀ : ℝ) : ℝ) : ℂ)⁻¹ with hz
  obtain ⟨c, hc⟩ := exists_pow_mul_mem_of_mem_fieldRange z l hl
  refine ⟨c, fun eT x hT hTM hx k _ _ σ la O hla hO hconj hval _ _ => ?_⟩
  have hfl : flipScal χW V W T M₀ x = z := by
    unfold flipScal
    rw [GlobalTheory.T.char_inv_centralFlipIdele_eq_prod_local_components D V χW χ M₀ u T eT x hχ.1 rfl hT hx]
  rw [hfl]
  refine hc k σ la O hla hO ?_
  obtain ⟨a, hai, hA1, hA2⟩ := GlobalTheory.T.exists_field_element_local_components_level_number D.host.E χ M₀ u rfl T
  have hinf := GlobalTheory.T.heckeChar_infinity_eq_coeff_mul_halfNorm_pow D ψ θ V W χV χW om ΛV ΛW sW f₀ hVP χ hχ.1 k σ hconj a
  have := GlobalTheory.T.centralFlipScalar_mem_coefficientField D.host.E χ M₀ V.rank W.rank u a T k σ hW rfl hai hTM (fun v hv => hχ.2.1 v hv) hval hinf hA1 hA2
  simpa [hz, flipIdx] using this

end GlobalTheory.LevelSeries

end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.centralFlip_maps_halfTranslates_span : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D) (z : GA D V) (s : ℂ) (Y : Finset (WO V W)), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → s ≠ 0 → (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → om (z⁻¹, 1) f₀ = s • ∑ y ∈ Y, heisO ψ V W y f₀ → ∀ (M u : ℕ) (e e' : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (O : Subring ℂ), M = m * u → (∀ PP ∈ T, ((u : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e P → T ⊆ P → e' = e - eT + cA D eT → zeta M ∈ O → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, ∃ F ∈ trSp ψ V W ΛV ΛW f₀ e' M O, om (z, 1) (s • F) = f := by
  first | exact @GlobalTheory.FlipTranslates.flip_translates | exact GlobalTheory.FlipTranslates.flip_translates | (intros; apply GlobalTheory.FlipTranslates.flip_translates <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.RSCell

theorem wtS_eq_sum (N : ℕ) (a : Fin N → ℤ) :
    GlobalTheory.CellDec.wtS N a = ∑ i : Fin N, ((N : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) * a i := by
  first
  | exact @_root_.GlobalTheory.WeightSumSplit.wtS_eq
  | exact _root_.GlobalTheory.WeightSumSplit.wtS_eq
  | (apply _root_.GlobalTheory.WeightSumSplit.wtS_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightSumSplit.wtS_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightSumSplit.wtS_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightSumSplit.wtS_eq ..)

theorem locFac_eq_wtS_sphZ : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α : Fin (n + 1) → ℂ) (x : ℝ) (ν : Fin (n + 1) → ℤ), 0 ≤ ν (Fin.last n) →
    ENNReal.ofReal ((q : ℝ) ^ GlobalTheory.CellDec.wtS (n + 1) ν) * ENNReal.ofReal ((q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x))) *
      ‖GlobalTheory.RSCell.sphZ q α ν‖ₑ ^ 2 = GlobalTheory.RSCell.locFac q α x ν := by
  intro q hq n α x ν hlast
  by_cases hA : Antitone ν
  · have hnn : ∀ i, 0 ≤ ν i := fun i => le_trans hlast (hA (Fin.le_last i))
    have hAn : Antitone (fun i => (ν i).toNat) := fun i j h => Int.toNat_le_toNat (hA h)
    rw [GlobalTheory.RSCell.locFac, if_pos ⟨hA, hnn⟩, GlobalTheory.RSCell.sphZ, if_pos hA, GlobalTheory.JSW.sphW, if_pos hAn]
    set s := GlobalTheory.JSW.schurAt (fun i => (ν i).toNat) α
    set w : ℤ := GlobalTheory.CellDec.wtS (n + 1) ν with hw
    have hc : (∑ i : Fin (n + 1), ((((n + 1 : ℕ)) : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)) * (((ν i).toNat : ℕ) : ℂ)) = ((w : ℤ) : ℂ) := by
      rw [hw, wtS_eq_sum]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (((ν i).toNat : ℕ) : ℂ) = ((ν i : ℤ) : ℂ) by exact_mod_cast Int.toNat_of_nonneg (hnn i)]
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hsum : (((∑ i, (ν i).toNat : ℕ)) : ℝ) = ∑ i, (ν i : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      exact_mod_cast Int.toNat_of_nonneg (hnn i)
    rw [hc, hsum]
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (zpow_nonneg hq'.le _), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq]
    have hre : (-((w : ℂ)) / 2).re = -(w : ℝ) / 2 := by simp
    rw [hre, mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ (-(w : ℝ) / 2)), ← Real.rpow_mul hq'.le,
      ← Real.rpow_intCast]
    have h1 : (q : ℝ) ^ (w : ℝ) * (q : ℝ) ^ (-(w : ℝ) / 2 * ((2 : ℕ) : ℝ)) = 1 := by
      rw [← Real.rpow_add hq']
      norm_num
    calc (q : ℝ) ^ (w : ℝ) * (q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x)) *
          ((q : ℝ) ^ (-(w : ℝ) / 2 * ((2 : ℕ) : ℝ)) * ‖s‖ ^ 2)
        = ((q : ℝ) ^ (w : ℝ) * (q : ℝ) ^ (-(w : ℝ) / 2 * ((2 : ℕ) : ℝ))) * (‖s‖ ^ 2 * (q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x))) := by ring
      _ = _ := by rw [h1, one_mul]
  · rw [GlobalTheory.RSCell.locFac, if_neg (fun h => hA h.1), GlobalTheory.RSCell.sphZ, if_neg hA]
    simp

end GlobalTheory.RSCell
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCellSum

theorem schurDir_eq_tsum_locFac (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) :
    GlobalTheory.RSPole.schurDir q α x = ∑' ν : Fin n → ℤ, GlobalTheory.RSCell.locFac q α x ν := by
  let g : {l : Fin n → ℕ // Antitone l} → (Fin n → ℤ) := fun l i => (l.1 i : ℤ)
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    funext i
    have := congrFun h i
    simpa [g] using this
  have hs : Function.support (GlobalTheory.RSCell.locFac q α x) ⊆ Set.range g := by
    intro ν hν
    rw [Function.mem_support] at hν
    unfold GlobalTheory.RSCell.locFac at hν
    split_ifs at hν with h
    · refine ⟨⟨fun i => (ν i).toNat, fun i j hij => Int.toNat_le_toNat (h.1 hij)⟩, ?_⟩
      funext i
      simp [g, Int.toNat_of_nonneg (h.2 i)]
    · exact absurd rfl hν
  rw [← hg.tsum_eq hs, GlobalTheory.RSPole.schurDir]
  refine tsum_congr fun l => ?_
  have hA : Antitone (g l) ∧ ∀ i, 0 ≤ g l i :=
    ⟨fun i j hij => by simpa [g] using l.2 hij, fun i => by simp [g]⟩
  rw [GlobalTheory.RSCell.locFac, if_pos hA]
  simp [g]

theorem tsum_cellProd_sub_eq_eulD (E : Type) [Field E] [NumberField E] (n : ℕ)
    (T : Finset (HeightOneSpectrum (𝓞 E)))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin n → ℂ) (x : ℝ) (l₀ : GlobalTheory.CellDec.abelian₂ E n T) :
    ∑' l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) =
      GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal) α x := by
  let sh : GlobalTheory.CellDec.abelian₂ E n T ≃ GlobalTheory.CellDec.abelian₂ E n T :=
    { toFun := fun l => ⟨l.1 - l₀.1, fun v hv => by simp [l.2 v hv, l₀.2 v hv]⟩
      invFun := fun l => ⟨l.1 + l₀.1, fun v hv => by simp [l.2 v hv, l₀.2 v hv]⟩
      left_inv := fun l => Subtype.ext (by simp)
      right_inv := fun l => Subtype.ext (by simp) }
  have h1 : ∑' l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) =
      ∑' l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x l.1 :=
    sh.tsum_eq (fun l => GlobalTheory.RSCell.cellProd T α x l.1)
  rw [h1]
  have hsupp : ∀ l : GlobalTheory.CellDec.abelian₂ E n T, ∀ w ∈ l.1.support, w ∉ T := fun l w hw hT =>
    (Finsupp.mem_support_iff.1 hw) (l.2 w hT)
  let e : GlobalTheory.CellDec.abelian₂ E n T ≃ ({w : HeightOneSpectrum (𝓞 E) // w ∉ T} →₀ (Fin n → ℤ)) :=
    { toFun := fun l => l.1.subtypeDomain (fun w => w ∉ T)
      invFun := fun ν => ⟨ν.extendDomain, fun v hv => by simp [Finsupp.extendDomain_apply, hv]⟩
      left_inv := fun l => Subtype.ext (Finsupp.extendDomain_subtypeDomain l.1 (hsupp l))
      right_inv := fun ν => Finsupp.subtypeDomain_extendDomain ν }
  let f : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → (Fin n → ℤ) → ℝ≥0∞ :=
    fun w ν => GlobalTheory.RSCell.locFac (Ideal.absNorm w.1.asIdeal) (α w) x ν
  have hf0 : ∀ w, f w 0 = 1 := fun w => GlobalTheory.RSCell.locFac_zero _ _ _
  let h : HeightOneSpectrum (𝓞 E) → (Fin n → ℤ) → ℝ≥0∞ := fun w ν =>
    if hw : w ∈ T then 1 else GlobalTheory.RSCell.locFac (Ideal.absNorm w.asIdeal) (α ⟨w, hw⟩) x ν
  have h2 : ∀ l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x l.1 = (e l).prod f := by
    intro l
    have : (e l).prod f = (l.1.subtypeDomain (fun w => w ∉ T)).prod (fun a b => h a.1 b) := by
      refine Finset.prod_congr rfl fun a _ => ?_
      simp only [h, dif_neg a.2, f]
      rfl
    rw [this, Finsupp.prod_subtypeDomain_index (hsupp l)]
    rfl
  rw [tsum_congr h2, e.tsum_eq (fun ν => ν.prod f),
    (GlobalTheory.EulerSum.euler_product_intVec_ennreal n f hf0).2, GlobalTheory.RSPole.eulD]
  refine tprod_congr fun w => ?_
  rw [schurDir_eq_tsum_locFac]

end GlobalTheory.RSCellSum
end
end
