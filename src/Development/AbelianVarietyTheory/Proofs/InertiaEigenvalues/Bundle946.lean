module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicCompletionIntegersLeIntAE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle866
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle817
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsXiOKEvenRamified
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle599
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmQAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle120
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle944
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle894
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle945
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle922
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle943
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle083
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle080
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryOfTraceEq
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle930
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistRat

theorem curveOver_of_rayIn : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ (N : ℕ), 3 ≤ N → ∀ (Fc : IntermediateField ℚ ℂ) (σ : Fc →+* ℂ), RayIn D N σ.fieldRange → GlobalTheory.CompRat.CurveOver Q.H Fc N := GlobalTheory.TwistRat.Field.curveOver_of_rayIn

theorem twist_mem_fieldRange : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ g, dd g ∈ σ.fieldRange := GlobalTheory.TwistValues.mem_fieldRange

theorem twist_eq_of_finHom : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ h h' : GA D V, finHom V h = finHom V h' → dd h = dd h' := GlobalTheory.TwistFinPart.twist_eq_of_finHom

theorem twist_mul_left : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ γ ∈ GQ V, ∀ h : GA D V, dd (γ * h) = dd h := GlobalTheory.TwistLeft.twist_left

theorem twist_mul_right : ∀ (D : D7) (V : HSp D) (M pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsAuxiliarySplitSquarefreeLevel D M pd → IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ u : GA D V, Formalism.L2.Pj.gLat V u = ↑(Formalism.L2.Pj.latHat V) → GlobalTheory.Member.FinCong V (M * pd) u → ∀ h : GA D V, dd (h * u) = dd h := GlobalTheory.TwistRat.Right.dd_mul_right

theorem muVal_cast {D : D7} {V W : HSp D} (h : V = W) (χ : (AE D)ˣ →* Circle) (dd : GA D W → ℂ) (hd : MuVal W χ dd) :
    MuVal V χ (castDict h.symm dd) := by
  subst h; exact hd

theorem castDict_mul {D : D7} {V W : HSp D} (h : V = W) (dd : GA D W → ℂ) (φ : GA D V → ℂ) :
    castDict h (fun g => castDict h.symm dd g * φ g) = fun g => dd g * castDict h φ g := by
  subst h; rfl

theorem isRat_twist : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
      ∀ (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist C.d.pd C.σ₂ δ δc →
      ∀ dd : GA D (Wc D i) → ℂ, MuVal (Wc D i) δc dd ∨ MuVal (Wc D i) δc⁻¹ dd →
      ∀ φ : GA D (Wc D i) → ℂ, IsRat T i hV C (κ i) φ → IsRat T i hV C (κ i) (fun g => dd g * φ g) := by
  intro hRF D G _ _ Pl0 T0 A T _ R F κ v₀ hL hLev hGrp hFam hMod hThP hTie i hV hFP gramR c0R c0L hFT u hu C hGC δ δc hTw dd hdd φ hφ
  obtain ⟨hU, -, hAux, -, hRay⟩ := hGC
  obtain ⟨φ', hφ', rfl⟩ := hφ
  have hlev : C.d.l₂.M = T.Q.l.M * C.d.pd := hU.1.2.1
  have hpd : 0 < C.d.pd := hAux.1.pos
  have hN3 : 3 ≤ T.Q.l.M * C.d.pd := le_trans T.Q.l.three_le (Nat.le_mul_of_pos_right _ hpd)
  have hcurve : GlobalTheory.CompRat.CurveOver T.Q.H C.d.c₂.F (T.Q.l.M * C.d.pd) :=
    curveOver_of_rayIn hRF D T.Q hL.pins.1 _ hN3 C.d.c₂.F C.σ₂ hRay
  set dd' : GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ := castDict hV.symm dd with hdd'
  have hdd2 : MuVal _ δc dd' ∨ MuVal _ δc⁻¹ dd' :=
    hdd.imp (muVal_cast hV δc dd) (muVal_cast hV δc⁻¹ dd)
  have hval := twist_mem_fieldRange D _ C.d.pd _ C.σ₂ δ δc hTw dd' hdd2
  choose w hw using fun g => RingHom.mem_fieldRange.1 (hval g)
  have hinj : ∀ g g', dd' g = dd' g' → w g = w g' := fun g g' h => C.σ₂.injective (by rw [hw, hw, h])
  have key := (GlobalTheory.CoverComp.forms_mul_comp D T hL ((i : ℕ) + 1) ⟨Nat.succ_pos _, i.2⟩ T.σ₀ rfl C hU
    (T.Q.l.M * C.d.pd) (Nat.mul_pos (by have := T.Q.l.three_le; omega) hpd) (by rw [hlev]) (Or.inr hcurve) w
    (fun h h' hh => hinj _ _ (twist_eq_of_finHom D _ C.d.pd _ C.σ₂ δ δc hTw dd' hdd2 h h' hh))
    (fun γ hγ h => hinj _ _ (twist_mul_left D _ C.d.pd _ C.σ₂ δ δc hTw dd' hdd2 γ hγ h))
    (fun u hu1 hu2 h => hinj _ _ (twist_mul_right D _ T.Q.l.M C.d.pd _ C.σ₂ δ δc hAux hTw dd' hdd2 u hu1 (hlev ▸ hu2) h))
    (wtA (κ i)) (κ i).n).1 φ' hφ'
  refine ⟨_, key, ?_⟩
  simp only [hw]
  exact castDict_mul hV dd φ'

end GlobalTheory.TwistRat
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

namespace GlobalTheory.TwistInt



theorem mul_twist_mem_intForms : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ C : Cover T j T.σ₀, C.IsUnif → (∃ φ : D.host.K →+* C.d.c₂.F, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ C.d.l₂.M) → ∀ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTwist C.σ₂ C.d.pd xi → ∀ (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), ∀ φ ∈ C.intForms wa n S, (fun g => ((xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g)) : ℂˣ) : ℂ) * φ g) ∈ C.intForms wa n S := by
  intro D T hL j hj C hU hRay xi hxi wa n S φ hφ
  have hP : T.Q.Pins := hL.pins
  have hlev : C.d.l₂.M = T.Q.l.M * C.d.pd := hU.1.2.1
  have hM3 : 3 ≤ C.d.l₂.M := C.d.l₂.three_le
  have hpd : 0 < C.d.pd := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hlev; omega

  have hsq : ∃ a : D.host.K, a ^ 2 = -(T.Q.H.d : D.host.K) := by
    refine ⟨⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩, ?_⟩
    rw [show T.Q.H.d = D.host.d from hP.1.1]
    apply Subtype.ext
    have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqrtMinusD_sq
    simpa using hb
  obtain ⟨φK, hφK⟩ := hRay
  have hW := (GlobalTheory.T.weberValues_mem_of_containsRayField D.host.E T.Q.H D.host.K C.d.c₂.F φK C.d.c₂.F.val.toRingHom (Formalism.L2.Pj.LPb.finrank_K D) hsq
    C.d.l₂.M hM3 hφK).1
  have hWc : GlobalTheory.FinalJoin.WeberIn T.Q.H C.d.c₂.F C.d.l₂.M := fun P hP' => by
    have hsub : ∀ z ∈ C.d.c₂.F.val.toRingHom.toRatAlgHom.fieldRange, z ∈ C.d.c₂.F := fun z hz' => by
      obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.1 hz'
      exact y.2
    obtain ⟨a1, a2⟩ := hW P hP'
    exact ⟨hsub _ a1, fun s hs => hsub _ (a2 s hs)⟩

  have hno : ∀ g : GA D (T.V j T.σ₀),
      GlobalTheory.FinalJoin.NormOne (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g)) := fun g => by
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (T.V j T.σ₀)).1 g
    rw [← GlobalTheory.NormOneTwist.finQuot_of_isDetRoot hx]
    exact GlobalTheory.NormOneTwist.normOne_finQuot x
  obtain ⟨m, hm, hexp⟩ := GlobalTheory.XiCounterexample.fin_of_rat_tame D C.d.pd hpd xi hxi.rat hxi.cond
  choose w hw using fun g => hxi.val _ (hno g)
  have hinj : ∀ g g', xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g)) =
      xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g')) → w g = w g' :=
    fun g g' h => C.σ₂.injective (by rw [hw, hw, h])
  have hleft : ∀ γ ∈ GQ (T.V j T.σ₀), xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) γ)) = 1 := by
    intro γ hγ
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (T.V j T.σ₀)).2.2.1 γ hγ
    rw [← GlobalTheory.NormOneTwist.finQuot_of_isDetRoot hx]
    exact hxi.rat _ _ (GlobalTheory.NormOneTwist.finQuot_incA x) (GlobalTheory.NormOneTwist.normOne_finQuot _)
  have hright : ∀ u : GA D (T.V j T.σ₀), GlobalTheory.Member.FinCong (T.V j T.σ₀) C.d.l₂.M u →
      xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) u)) = 1 := by
    intro u hu
    obtain ⟨k1, -, k3, k4, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D (T.V j T.σ₀)
    obtain ⟨w', hw', e⟩ := GlobalTheory.CharRead.det_cong_one D.host.F (GlobalTheory.Member.latC (T.V j T.σ₀)) k3 k4 C.d.l₂.M (by omega)
      (finHom (T.V j T.σ₀) u).1 (by rw [← k1]; exact hu)
    refine hxi.cond _ (hno u) ⟨T.Q.l.M • w', AddSubgroup.nsmul_mem _ (GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers D ▸ hw') _, ?_⟩
    rw [smul_smul, mul_comm, ← hlev]
    exact e
  have key := (GlobalTheory.CoverComp.forms_mul_comp D T hL j hj T.σ₀ rfl C hU C.d.l₂.M (by omega) dvd_rfl (Or.inl hWc) w
    (fun h h' hh => hinj _ _ (by rw [hh]))
    (fun γ hγ h => hinj _ _ (by rw [map_mul, map_mul, map_mul, hleft γ hγ, one_mul]))
    (fun u _ hu2 h => hinj _ _ (by rw [map_mul, map_mul, map_mul, hright u hu2, mul_one])) wa n).2 S ?_ φ hφ
  · simpa only [hw] using key
  · intro la _ h
    have hpow : w h ^ m = 1 := C.σ₂.injective (by
      rw [map_pow, hw, map_one, ← Units.val_pow_eq_pow_val, hexp _ (hno h), Units.val_one])
    have hint : IsIntegral ℤ (w h) := IsIntegral.of_pow hm (by rw [hpow]; exact isIntegral_one)
    have := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := C.d.c₂.F) la (⟨w h, hint⟩ : 𝓞 C.d.c₂.F)
    exact this

end GlobalTheory.TwistInt
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.weightZeroSection_value_on_markedPeriodSpace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (a : Tp) (C : GlobalTheory.Member.Ctx (M.dδ a).Xo₂ (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (Wc D i) D.R.r), C.OK → C.ι = iotaW T i → C.x₀ = T.x₀ ((i : ℕ) + 1) M.s0 → ∀ (f : Rul (M.dδ a).Xo₂ (M.dδ a).c₂) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ), f ∈ sec (M.dδ a).Xo₂ (M.dδ a).c₂ 0 0 → (∀ u : GA D (Wc D i), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ a).l₂.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1) → (∀ γ ∈ GQ (Wc D i), xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) γ)) = 1) → GlobalTheory.OneMapAll.CXiAt (Wc D i) (rank_Wc i) (inC M.c') { M.dδ a with cδ := f } (M.U₂ a) (M.dict₂ a) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) xi c0 → ∀ (y : FrPt (M.dδ a).Xo₂ (M.dδ a).c₂ (CAt ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)))) (k : Fin C.F.n) P, IsPeriod (C.F.Di k) (fun j => relab (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (C.e j).1) P → y.x = C.F.u k P → ∀ h γ : GA D (Wc D i), C.Mark h k γ → toC (evR (M.dδ a).Xo₂ (M.dδ a).c₂ f y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) (γ * h))) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.MarkVal.val_on_marked_space | exact GlobalTheory.MarkVal.val_on_marked_space | (intros; apply GlobalTheory.MarkVal.val_on_marked_space <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.coverCharacter_trivial_on_level_determinants : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (t : Tp) (u : GA D (Wc D i)), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ t).l₂.M : ℕ) • w) → M.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1 := by
  first | exact @GlobalTheory.CoverXiDet.main | exact GlobalTheory.CoverXiDet.main | (intros; apply GlobalTheory.CoverXiDet.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



noncomputable section

namespace GlobalTheory.TwInputs

variable {D : D7} {ρ : Setup D.ntw}

theorem de_mem_eO (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ) :
    (((ρ.B i j b).de.chi z : Circle) : ℂ) ∈ (ρ.eO i b).range := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i), ?_⟩
  rw [hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm

theorem e_mem_eO (ρ : Setup D.ntw) (i : D.ntw.Tw) (b : Bool) {a : FractionRing (D.ntw.O i)} {n : ℕ}
    (hn : n ≠ 0) (h : ρ.e i b a ^ n = 1) : ρ.e i b a ∈ (ρ.eO i b).range := by
  have h1 : a ^ n = 1 := (ρ.e i b).injective (by rw [map_pow, h, map_one])
  have hi : IsIntegral (D.ntw.O i) a := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h1]⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨y, rfl⟩

theorem typeCharacterExtension_value_mem_coefficientRing {hρ : ρ.Good} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd : Rd ρ D.nexp i j b}
    (T : CellTie hρ D.nexp rd) (g : G0 (ρ.B i j b).G.Pg (Wc D j).rank) :
    ((ext1 (ρ.B i j b).G.P.H (⇑(ρ.B i j b).G.P.chi) g : ℂˣ) : ℂ) ∈ (ρ.eO i b).range := by
  unfold ext1
  split_ifs with h
  · obtain ⟨g', rfl⟩ := (ρ.eG i j b).surjective g
    have e1 := T.psiU_eq ⟨g', (T.U_eq g').1 h⟩ h
    have hfin : ((ρ.B i j b).G.P.chi ⟨ρ.eG i j b g', h⟩) ^ Nat.card (ρ.B i j b).G.P.H = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    rw [e1]
    refine e_mem_eO ρ i b (n := Nat.card (ρ.B i j b).G.P.H) Nat.card_pos.ne' ?_
    rw [← e1, ← Units.val_pow_eq_pow_val, hfin, Units.val_one]
  · exact one_mem _

theorem card_residueField_of_type {k : Fin 2} {PP : Pl D.host.E} (h : PP ∈ placesOver D.host.E (D.host.g k)) :
    Nat.card (kP PP) = D.host.g k :=
  GlobalTheory.SplitResidueCard.card_quotient_of_ncard (F := D.host.E) (D.host.g_prime k) (D.nd.g_split k) PP h

theorem muC_mem_eO (hρ : ρ.Good)
    (hr : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange)
    (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {PP : Pl D.host.E} (hPP : PP ∈ (ρ.B i j b).G.Pg) (w : (kP PP)ˣ) :
    (((ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ∈ (ρ.eO i b).range := by
  obtain ⟨k, hk⟩ := hρ.Pg i j b PP hPP
  have hw : w ^ (D.host.g k - 1) = 1 := by
    rw [← card_residueField_of_type hk, ← Nat.card_units]
    exact pow_card_eq_one'
  have hz : (((ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ^ (D.host.g k * (D.host.g k - 1)) = 1 := by
    rw [mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, hw, map_one, Units.val_one, one_pow]
  obtain ⟨x, hx⟩ := hr k _ hz
  have h2 := (D.host.g_prime k).two_le
  have e : ρ.e i b (sideEmb D.ntw i b x) = (((ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) := (hρ.e_LL0 i b x).trans hx
  rw [← e] at hz ⊢
  exact e_mem_eO ρ i b (Nat.mul_ne_zero (by omega) (by omega)) hz

theorem locC_mem {t : Twist D Circle} (ht : t.Good) {O : Subring ℂ} (h : ∀ x, ((t.chi x : Circle) : ℂ) ∈ O)
    (PP : Pl D.host.E) (w : (kP PP)ˣ) : ((t.locC PP w : ℂˣ) : ℂ) ∈ O := by
  unfold Twist.locC
  split_ifs with hq
  · obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (ht.split.isIdemAt hq) w
    show ((t.res PP w : Circle) : ℂ) ∈ _
    rw [← hx.eq (ht.res PP hq)]
    exact h x
  · simp

theorem levLam_mem_eOk {hρ : ρ.Good}
    (hr : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange)
    {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd : Rd ρ D.nexp i j b} (T : CellTie hρ D.nexp rd) {k Q ψ} (hψ : TwOK i k Q ψ)
    (x : (ρ.B i j b).levJ (ρ.tw i b k Q ψ)) :
    (((ρ.B i j b).levLam (ρ.tw i b k Q ψ) x : ℂˣ) : ℂ) ∈ (ρ.eOk i b k).range := by
  obtain ⟨hg, -, hv⟩ := GlobalTheory.TwistGood.tw_good D _ _ ρ hρ i j b k Q ψ hψ
  have hle := hρ.range_le i b k
  have e : (ρ.B i j b).levLam (ρ.tw i b k Q ψ) x =
      levFn (ρ.B i j b).F.βS ((ρ.B i j b).levS (ρ.tw i b k Q ψ)) (Formalism.UG.bc (Lev.swapAE D) x.1.1) := by
    unfold Base.levLam Lev.levCharAfE
    rfl
  rw [e]
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod]
  refine mul_mem (mul_mem (hle (typeCharacterExtension_value_mem_coefficientRing T _)) (prod_mem fun PP hPP => prod_mem fun _ _ => hle (muC_mem_eO hρ hr i j b hPP _)))
    (prod_mem fun PP _ => ?_)
  rw [MonoidHom.mul_apply, Units.val_mul]
  exact mul_mem (hle (locC_mem (hρ.base i j b).de (de_mem_eO hρ i j b) PP _))
    (locC_mem (O := (ρ.eOk i b k).range) hg (fun z => (hv z).elim fun u hu => ⟨u, hu.symm⟩) PP _)

theorem admT4_of_full_compatibility : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd →
    (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) →
    ∀ E : IntegralHeckeForms.XD D, IntegralHeckeForms.admT4 D.nexp E := by
  intro D ρ hρ rd hT hr E i _ j hj b k Q ψ hψ Sg _
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨j', rfl⟩ : ∃ j' : Fin D.R.m, j = (j' : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  have T := hT.tie i j' b
  rw [IntegralHeckeForms.ThPsi, Submodule.span_le]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨d, -, hx⟩ := hx
  have hg := (T.thPsi_iff k Q ψ hψ d x).1 hx
  obtain ⟨F, hF, e⟩ := GlobalTheory.T.twistedThetaGenerator_eq_classSum_integralForm D ρ hρ i j' b k Q ψ hψ (levLam_mem_eOk hr T hψ) _ _ _ (T.dat d) _ hg
  obtain ⟨f, hf, rfl⟩ := (T.mtLat_iff k Q ψ hψ F).1 hF
  refine ⟨f, hf, T.injective_rdK k ?_⟩
  rw [T.thP_eq k Q ψ hψ f ⟨x, e⟩]
  exact e.symm

end GlobalTheory.TwInputs

end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.levelCover_forms_mul_componentFunction : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ N : ℕ, 0 < N → C.d.l₂.M ∣ N → (WeberIn T.Q.H C.d.c₂.F N ∨ CurveOver T.Q.H C.d.c₂.F N) → ∀ w : GA D (T.V j σ) → C.d.c₂.F, (∀ h h' : GA D (T.V j σ), finHom (T.V j σ) h = finHom (T.V j σ) h' → w h = w h') → (∀ γ ∈ GQ (T.V j σ), ∀ h, w (γ * h) = w h) → (∀ u : GA D (T.V j σ), gLat (T.V j σ) u = latHat (T.V j σ) → FinCong (T.V j σ) C.d.l₂.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ φ ∈ C.ratForms a n, (fun h => C.σ₂ (w h) * φ h) ∈ C.ratForms a n) ∧ ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), (∀ la ∈ S, ∀ h, la.valuation C.d.c₂.F (w h) ≤ 1) → ∀ φ ∈ C.intForms a n S, (fun h => C.σ₂ (w h) * φ h) ∈ C.intForms a n S := by
  first | exact @GlobalTheory.CoverComp.forms_mul_comp | exact GlobalTheory.CoverComp.forms_mul_comp | (intros; apply GlobalTheory.CoverComp.forms_mul_comp <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_coverDictionary_adelic_element_component : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ k₂ : C.U₂.Comp, ∃ h : GA D (T.V j σ), (C.dict₂ h).1 = k₂ := by
  first | exact @GlobalTheory.CoverOnto.exists_dict₂_comp | exact GlobalTheory.CoverOnto.exists_dict₂_comp | (intros; apply GlobalTheory.CoverOnto.exists_dict₂_comp <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_levelCover_uniformisation_dictionary : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) (d : DeltaDat (T.Q.Xo j) c' 0) (σ₂ : d.c₂.F →+* ℂ), d.IsLev → d.l₂.A = 1 → σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF T.Q.c c' hle)) = σ → ∃ (U₂ : Unf d.Xo₂ d.c₂ σ₂ D.R.r) (dict₂ : GA D (T.V j σ) → Σ k, Frame (U₂.X k).Ψ D.R.r), ∀ cc₂, (⟨c', hle, d, σ₂, U₂, dict₂, cc₂⟩ : Cover T j σ).IsUnif := by
  first | exact @GlobalTheory.CoverUnif.exists_unf_dict | exact GlobalTheory.CoverUnif.exists_unf_dict | (intros; apply GlobalTheory.CoverUnif.exists_unf_dict <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.LocalFactor

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem pureTensor_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : R.ptP i t 1 = R.vP i t := by
  unfold RealDat.ptP pureTensorO pureTensorL
  have : (1 : MvPolynomial (FVar D (Wc D i).rank (Vc D i).rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp
  rw [this, Module.Basis.constr_basis]
  simp [opPow]

theorem trivAt_one (V : HSp D) (f : AE D) : TrivAt V f 1 := by
  have : Formalism.L2.Theta.mt V 1 = 1 := rfl
  intro a b
  simp [this]

theorem finMult : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    Laws R F → R.FullP → ∀ i t, FinMult R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ v f hf γ hγ hγt k hk
  have hmul : ∀ g : GA D (Wc D i),
      R.ωP i t (1, g * k) (R.vP i t) = R.ωP i t (1, g) (R.ωP i t (1, k) (R.vP i t)) := by
    intro g
    have e : ((1 : GA D (Vc D i)), g * k) = (1, g) * (1, k) := by simp
    rw [e, map_mul, Module.End.mul_apply]
  have hone : R.ωP i t (1, 1) = 1 := map_one _
  unfold coef
  by_cases hbad : ∃ P, (P ∈ R.Pg ∨ P ∈ R.Q t) ∧ ∃ e, IsPrimeIdem P e f
  · obtain ⟨P, hP, e, he⟩ := hbad
    by_cases hkl : k ∈ levW R i
    · have hfix : R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
        have := GlobalTheory.T.coeffSpaceLevel_fixes_fockVectors D G Pl0 T A Ks R F hL hF i t k hkl 1
        rwa [pureTensor_one] at this
      rw [hmul γ, hfix]
      by_cases hN : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) = 0
      · simp [hN]
      · rw [div_self hN, mul_one]
    · have h0 := GlobalTheory.T.coefficient_vanishes_off_level_group_at_bad_prime D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ P hP e f he γ hγ hγt k hk hkl
      have h1 := GlobalTheory.T.coefficient_vanishes_off_level_group_at_bad_prime D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ P hP e f he 1 (one_mem _) (trivAt_one _ f) k hk hkl
      rw [one_mul] at h1
      rw [h0, h1]
      simp
  · have hgood : ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f :=
      fun P hP e f' he hff => hbad ⟨P, hP, e, hff ▸ he⟩
    obtain ⟨c, hc⟩ := GlobalTheory.T.matrixCoeff_finitePlace_offLevel_const_mul D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ v f hf hgood k hk
    have h1 := hc 1 (one_mem _) (trivAt_one _ f)
    rw [one_mul, hone, Module.End.one_apply] at h1
    rw [hc γ hγ hγt, h1]
    by_cases hN : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) = 0
    · simp [hN]
    · field_simp

end GlobalTheory.RawLift.LocalFactor

end
end
