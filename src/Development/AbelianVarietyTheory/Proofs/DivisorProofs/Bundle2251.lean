module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorValuedLiftFieldChange
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle208
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle009
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.diagonalSiegel_heisenbergInvariant_form_unique : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
            (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin (GlobalTheory.Doubling.dblSp T).rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
              fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO T S)) (𝓕 : Set (Formalism.IndefR.Datum.WO T S)),
            Formalism.IndefR.Datum.IsCovolOne (ratL S T) ν 𝓕 →
          ∀ l : ((κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ →
            (∀ z : Matrix (Fin S.rank) (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E),
              ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                l ((GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co).rho ψ
                  (GlobalTheory.DiagSiegel.diagMat z) Φ) = l Φ) →
            ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, l Φ = c * GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕
              (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) ψ Φ) := by
  first | exact @GlobalTheory.DiagSiegelUniq.uniq | exact GlobalTheory.DiagSiegelUniq.uniq | (intros; apply GlobalTheory.DiagSiegelUniq.uniq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_weilDatum_transport_adelicSchwartz_thetaTransform : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∃ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om := by
  first | exact @GlobalTheory.ThetaTransform.exists_isTransport | exact GlobalTheory.ThetaTransform.exists_isTransport | (intros; apply GlobalTheory.ThetaTransform.exists_isTransport <;> assumption)
end

section

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Merge

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}

variable {J : Type} {tup : J → T0} (src : ∀ j, OMDat C R i Unit (fun _ => tup j)) (c₃ : Coeff C.Q.l) (h₃ : C.Q.c.F ≤ c₃.F)
  (hs : ∀ j, (src j).c'.F ≤ c₃.F) (jL₃ : D.what₂.LL →+* c₃.F) (hV₃ : C.V ((i : ℕ) + 1) (sOv C c₃ h₃) = Wc D i)
  (c0₃ : VsV D i c₃.F →ₛₗ[inC c₃] (R.cV i).W)
  (lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La)
  (io₃ : VsV D i c₃.F →ₗ[c₃.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c₃.F) (hw₃ : VsV D i c₃.F)
  (u : J → c₃.F) (h : ∀ j, (src j).Cl' () → GA D (Vc D i)) (v₀ : (R.MW i (sg0 D A)).Vec)



theorem pins_merge_of_clauses (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (hF : R.IsFam) (hMo : R.IsModels)
    {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {ι x₀}
    (hsrc : ∀ j, (src j).Pins κ v₀ ι x₀)
    (hlift : ThPinsR R i jL₃ (inC c₃) v₀ c0₃ ι C.Q.l.M (Mfr C.Q.l) lev)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c fun g => (lev g, LinearMap.id))
    (hio : IoLFRec c₃ (fun τ => embF c₃ (tauE D τ)) (lamV D i) (wtA κ) io₃ hw₃)
    (hh : ∀ j, ∃ J', RepsR R i (tup j) (h j) ((src j).bad ()) J' ((src j).Lh ()) ((src j).gam ()) ((src j).vol ()))
    (c0 : ℂ) (hc0 : ∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) (cs : J → ℂ) (hu : ∀ j, (u j : ℂ) * cs j = c0)
    (hcs : ∀ j, CXiAt (Wc D i) (rank_Wc i) (inC (src j).c') ((src j).dδ ()) ((src j).U₂ ()) ((src j).dict₂ ()) ι x₀
      ((src j).xi ()) (cs j)) :
    (merge src c₃ h₃ hs jL₃ hV₃ c0₃ lev io₃ hw₃ u h v₀).Pins κ v₀ ι x₀ := by
  have hu0 : ∀ j, u j ≠ 0 := fun j h0 => by
    obtain ⟨m, hm, e⟩ := hc0
    rw [← hu j, h0] at e
    simp [hm.ne'] at e
  refine ⟨hlift, fun j => ⟨?_, ((hsrc j).tuple ()).B, ((hsrc j).tuple ()).xi, ((hsrc j).tuple ()).phi, ((hsrc j).tuple ()).half⟩,
    ⟨hact, (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ h₃ _ _ hact).1⟩, fun j => (hsrc j).bad (), fun j => (hsrc j).reps (),
    fun j => ⟨fun k => congrArg (incF _ c₃ (hs j)) (((hsrc j).ep ()).1 k), epIs_map (hs j) ((hsrc j).ep ()).2⟩, hio,
    fun j k q => phiHat_covBC (hs j) _ (u j) _ _ q ((hsrc j).w () k q),
    fun j => covPin_covBC (hs j) _ (hu0 j) ((hsrc j).cov ()), ?_, fun j => (hsrc j).model₂ ()⟩
  · obtain ⟨J', hr⟩ := hh j
    obtain ⟨_, _, _, hT, hc⟩ := hlift.c0
    exact ⟨h j, J', repsR_map _ hr,
      GlobalTheory.RationalValues.placeEx R i jL₃ (inC c₃) (tup j) (h j) c0₃ hMo.jV hT hc hL hW hF.pl_onto hF.muVal,
      thAdIs_thAdOf R i (tup j) (h j) c0₃ hMo.HV hr.2.2.1 hr.2.2.2.2.2.1 v₀, fun _ => Iff.rfl⟩
  · refine (cXiVal_iff _ _ _ _ _ _ _ _ _).2 ⟨c0, hc0, fun j => ?_⟩
    rw [← hu j]
    exact GlobalTheory.OneMapAll.cXiAt_covBC D _ _ _ _ _ _ _ _ (hs j) _ _ _ (u j) _ _ _ _ _ _ ((hsrc j).cov ()).1.2.2.2.2.2.2.2.1 (hcs j)

end Merge

section Row

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

variable {T R κ v₀}



theorem exists_extension_of_clauses (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (hF : R.IsFam) (hMo : R.IsModels)
    {i : Fin D.R.m} {ι x₀}
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (O' : OMDat T.toCore R i T0 id) (hle : O.c'.F ≤ O'.c'.F)
    (hO : O.Pins (κ i) (v₀ i (sg0 D A)) ι x₀) (hO' : O'.Pins (κ i) (v₀ i (sg0 D A)) ι x₀) :
    ∃ (M : OMDat T.toCore R i (Option T0) (fun o => o.getD A.μ0)) (h₁ : O.c'.F ≤ M.c'.F), M.lev = O.lev ∧
      M.Pins (κ i) (v₀ i (sg0 D A)) ι x₀ ∧
      ∀ x, O.Plc () x → ∃ x', M.Plc none x' ∧ M.thAd none x' = O.thAd () x ∧
        ∀ f ∈ sec _ O.c' (wtA (κ i)) (Vc D i).rank, IsSum O () x f → IsSum M none x' (rulBC h₁ f) := by
  obtain ⟨a, ha, hca⟩ := (cXiVal_iff _ _ _ _ _ _ _ _ _).1 hO.cxi
  obtain ⟨b, hb, hcb⟩ := (cXiVal_iff _ _ _ _ _ _ _ _ _).1 hO'.cxi
  obtain ⟨c₃, h', haF, hbF⟩ := exists_coeff_roots O'.c' ha hb
  have hb0 : b ≠ 0 := fun h0 => by
    obtain ⟨m, hm, e⟩ := hb
    simp [h0, hm.ne'] at e
  have h₁ : O.c'.F ≤ c₃.F := hle.trans h'
  have h₃ : T.Q.c.F ≤ c₃.F := O.hle.trans h₁
  have hV₃ : T.V ((i : ℕ) + 1) (sOv T.toCore c₃ h₃) = Wc D i := by
    rw [sOv_eq, ← sOv_eq T.toCore O.c' O.hle]; exact O.hV
  obtain ⟨c0₃, hc0⟩ := exists_coef_ext (incF O.c' c₃ h₁) (σ := inC O.c') (inC c₃) (fun _ => rfl) (lamV D i) O.c0'
  obtain ⟨io₃, hw₃, hio, hover⟩ := GlobalTheory.IoExtend.exists_ioLFRec_over _ _ _ _ O.c' c₃ h₁ _ _ (tauE D) (lamV D i) (wtA (κ i)) O.io O.hw hO.io
  have hlift : ThPinsR R i ((incF O.c' c₃ h₁).comp O.jL) (inC c₃) (v₀ i (sg0 D A)) c0₃ ι T.Q.l.M (Mfr T.Q.l) O.lev := by
    refine ⟨(RingHom.ext fun _ => rfl : _ = (inC O.c').comp O.jL).trans hO.lift.field, hO.lift.std, hO.lift.v0, ?_,
      hO.lift.lev⟩
    obtain ⟨g, r, c0L, hT, hc⟩ := hO.lift.c0
    refine ⟨g, r, c0L, hT, fun v => ?_⟩
    obtain ⟨v', hv', e⟩ := hc v
    obtain ⟨v'', hv''⟩ := GlobalTheory.FieldBCModel.exists_over h₁ (lamV D i) v'
    exact ⟨v'', by rw [hv'', hv', MvPolynomial.map_map], (hc0 v' v'' hv'').trans e⟩
  obtain ⟨h₀, J₀, hr₀, -, hth₀, hpl₀⟩ := (hO.tuple ()).reps
  choose hh Jt hrt _ using fun t => (hO'.tuple t).reps
  let src : ∀ o : Option T0, OMDat T.toCore R i Unit (fun _ => o.getD A.μ0) := fun o =>
    match o with
    | none => O
    | some t => comap O' (fun _ => t)
  have hs : ∀ o, (src o).c'.F ≤ c₃.F := fun o =>
    match o with
    | none => h₁
    | some _ => h'
  let u : Option T0 → c₃.F := fun o =>
    match o with
    | none => 1
    | some _ => ⟨a, haF⟩ / ⟨b, hbF⟩
  let h : ∀ o, (src o).Cl' () → GA D (Vc D i) := fun o =>
    match o with
    | none => h₀
    | some t => hh t
  have hP := pins_merge_of_clauses src c₃ h₃ hs _ hV₃ c0₃ O.lev io₃ hw₃ u h (v₀ i (sg0 D A)) hL hW hF hMo
    (fun o => match o with
      | none => hO
      | some t => pins_comap (fun _ => t) hO') hlift hO.act.1 hio
    (fun o => match o with
      | none => ⟨J₀, hr₀⟩
      | some t => ⟨Jt t, hrt t⟩) a ha (fun o => o.elim a fun _ => b)
    (fun o => match o with
      | none => one_mul a
      | some _ => div_mul_cancel₀ a hb0)
    (fun o => match o with
      | none => hca ()
      | some t => hcb t)
  refine ⟨_, h₁, rfl, hP, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := (hpl₀ x).1 hx
  choose x' hx' using fun k => GlobalTheory.FieldBCModel.exists_over h₁ (lamV D i) (x k)
  have hy' : Place R i A.μ0 h₀ c0₃ (jVx R i A.μ0 y) x' := fun k => (hy k).trans (hc0 _ _ (hx' k)).symm
  refine ⟨x', ⟨y, hy'⟩, (thAdIs_thAdOf R i A.μ0 h₀ c0₃ hMo.HV hr₀.2.2.1 hr₀.2.2.2.2.2.1 _ _ _ hy').trans
    (hth₀ _ _ hy).symm, fun f hf hfx => ?_⟩
  exact isThClsD_covBC_one h₁ (O.dδ ()) rfl _ _ _ _ _ _ O.io io₃ x x' (fun k => hover _ _ (hx' k))
    (hO.cov ()).1.2.2.2.2.2.2.2.1 hf hfx

variable (T R κ v₀)

theorem oneMapRowR_of_clauses (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m)
    (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (hF : R.IsFam) (hMo : R.IsModels)
    (hpins : OMPins T R κ v₀ O i) (htie : PhaseTie T R κ v₀ O ph i)
    (hrow0 : OneMapRow0 T R κ v₀ O i) (hex : PinnedDataExist T R κ v₀ i) (hid : IdentityRow T R κ v₀ i)
    (hspan : ClassSumsSpan (O i) (κ i)) : OneMapRowR T R κ v₀ O ph i := by
  refine ⟨hrow0, fun hG => ?_⟩
  obtain ⟨O', hLL', hP'⟩ := hex hG
  have hP := hpins.2
  rw [show O'.s0 = T.σ₀ from sOv_eq _ _ _] at hP'
  rw [show (O i).s0 = T.σ₀ from sOv_eq _ _ _] at hP
  obtain ⟨M, h₁, hlev, hM, hext⟩ := exists_extension_of_clauses hL hW hF hMo (O i) O' (hpins.1.le.trans hLL') hP hP'
  have hLM : D.what₂.embLL.toRatAlgHom.fieldRange ≤ M.c'.F := hpins.1.ge.trans h₁
  rw [← show M.s0 = T.σ₀ from sOv_eq _ _ _] at hM
  obtain ⟨cc', ph', hrow⟩ := hid _ _ M hLM hM
  exact ⟨comap M some, hLM, pins_comap some hM, oneMapOf_comap some
    (oneMapOf_of_extends (O i) M none h₁ hlev hM hext hspan (T.cE ((i : ℕ) + 1)) (htie hrow0) hrow)⟩

end Row

end GlobalTheory.OneMapAll
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HostDiagUniq

theorem eq_smul_diagInt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ),
      l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF D.host.F, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
        l (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
        @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  intro D ψ hψ κ _ l hl hinv μ hμ
  exact GlobalTheory.T.heisenbergInvariant_admissibleForm_eq_mul_diagonalIntegral D.host.F ψ (GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ) κ l hl hinv μ hμ

end GlobalTheory.HostDiagUniq
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTower.TopExists

section Sum

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Doubling GlobalTheory.AdelicU Matrix

theorem negIdx_of_orth {D : D7} {V₁ V₂ WW : HSp D} {p q : ℕ} (hr : V₁.rank + V₂.rank = WW.rank)
    (ι₁ : V₁.V →ₗ[D.host.E] WW.V) (ι₂ : V₂.V →ₗ[D.host.E] WW.V) (e₁ : Formalism.BasicNotions.HSpace.IsIsomEmb V₁ WW ι₁)
    (e₂ : Formalism.BasicNotions.HSpace.IsIsomEmb V₂ WW ι₂) (ho : ∀ x y, WW.hD (ι₁ x) (ι₂ y) = 0) (h1 : NegIdx V₁ p)
    (h2 : NegIdx V₂ q) : NegIdx WW (p + q) := by
  intro τ
  have c1 := (Formalism.UG.P.sig_data _ _ _ (h1 τ)).1
  have c2 := (Formalism.UG.P.sig_data _ _ _ (h2 τ)).1
  simp only [Fintype.card_fin] at c1 c2
  let v : Fin V₁.rank ⊕ Fin V₂.rank → WW.V :=
    Sum.elim (fun i => ι₁ (V₁.frame i)) (fun j => ι₂ (V₂.frame j))
  have hv : (Matrix.of fun k l => WW.hT (v k) (v l)) = fromBlocks V₁.gram 0 0 V₂.gram := by
    ext (i | i) (j | j)
    · simp only [v, HSpace.gram, Matrix.of_apply, Matrix.fromBlocks_apply₁₁, Sum.elim_inl]; exact e₁ _ _
    · have h := WW.herm.eq (ι₂ (V₂.frame j)) (ι₁ (V₁.frame i))
      have h0 : WW.hT (ι₂ (V₂.frame j)) (ι₁ (V₁.frame i)) = 0 := ho _ _
      rw [h0, map_zero] at h
      simp [v, ← h]
    · simp only [v, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply]
      exact ho (V₁.frame j) (V₂.frame i)
    · simp only [v, HSpace.gram, Matrix.of_apply, Matrix.fromBlocks_apply₂₂, Sum.elim_inr]; exact e₂ _ _
  have key := (GlobalTheory.SumSig.gram_family WW v).symm.trans hv
  set C := Matrix.of fun i k => WW.frame.repr (v k) i
  have hst : Function.Semiconj (tauE D τ) star star := fun a => D.sp.cm.cmUnram.2.1 _ a
  have hmap : (C.map (tauE D τ))ᴴ * gramAt D WW τ * C.map (tauE D τ) =
      fromBlocks (gramAt D V₁ τ) 0 0 (gramAt D V₂ τ) := by
    have := congrArg (fun M => M.map (tauE D τ)) key
    simp only [Matrix.map_mul, Matrix.conjTranspose_map _ hst, Matrix.fromBlocks_map, map_zero] at this
    simpa [gramAt] using this
  have hF := GlobalTheory.FrameComplement.hasSignature_fromBlocks (h1 τ) (h2 τ)
  obtain ⟨-, Q0, hQ0⟩ := Formalism.UG.P.sig_data _ _ _ hF
  have e : WW.rank - (p + q) = (V₁.rank - p) + (V₂.rank - q) := by omega
  rw [e]
  refine GlobalTheory.FrameComplement.hasSignature_of_frame (by simp; omega) (C.map (tauE D τ) * Q0) ?_
  calc (C.map (tauE D τ) * Q0)ᴴ * gramAt D WW τ * (C.map (tauE D τ) * Q0)
        = Q0ᴴ * ((C.map (tauE D τ))ᴴ * gramAt D WW τ * C.map (tauE D τ)) * Q0 := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hmap, hQ0]

end Sum

section Idem


open Formalism.IndefR.Lev in
theorem idem_exists {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}
    (hL : Lc.Is μ₀) (W : G.Weil) (t : T) : ∃ e : AE D, IsIdemSum e (locPl G t) := by
  classical
  obtain ⟨e0, he0, -⟩ := W.cosVec_is
  have hW := GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he0
  have hQ := hL.Q_pl t
  have key : ∀ P ∈ Lc.Q t, ∀ P' ∈ G.pl.W0, (IsConjPl P P' ∨ IsConjPl P' P) → P ∈ G.pl.W0 := by
    intro P hPQ P' hP' hc
    have hu : P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
      rcases hc with hc | hc
      · exact GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc
      · exact (GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc).symm
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP'
    rw [G.pl.under_w hv] at hu
    rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | h1
    · exact absurd hu (G.pl.levelPlace_ne_basePlace t P hPQ)
    · rw [G.pl.w_Q t P hPQ (hu ▸ h1), hu]
      exact Finset.mem_image_of_mem _ hv
  have hnc : ∀ P ∈ locPl G t, ∀ P' ∈ locPl G t, ¬ IsConjPl P P' := by
    intro P hP1 P' hP2 hc
    simp only [locPl, Finset.mem_union] at hP1 hP2
    rcases hP1 with h1 | h1 <;> rcases hP2 with h2 | h2
    · exact hW P h1 P' h2 hc
    · exact hW P h1 P' (key P' h2 P h1 (Or.inr hc)) hc
    · exact hW P (key P h1 P' h2 (Or.inl hc)) P' h2 hc
    · exact (hQ P h1).2 P' h2 hc
  let es : Formalism.L2.DIV.Pl D.host.E → AE D := fun PP =>
    if h : ¬ IsConjPl PP PP then (Formalism.IndefR.Fin.idem_exists_at PP h).choose else 0
  have hes : ∀ PP ∈ locPl G t, Formalism.L2.NTheta.IsIdemAt (es PP) PP := by
    intro PP hPP
    have h := hnc PP hPP PP hPP
    simp only [es, dif_pos h]
    exact (Formalism.IndefR.Fin.idem_exists_at PP h).choose_spec.1
  refine ⟨∑ PP ∈ locPl G t, es PP, ⟨es, hes, rfl⟩, ?_⟩

  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun PP hPP => Finset.sum_eq_zero fun PP' hPP' => ?_
  exact Formalism.IndefR.Fin.idem_orth_conj (hnc PP hPP PP hPP) (hes PP hPP) (hes PP' hPP') (hnc PP hPP PP' hPP')

end Idem

section Chars

open GlobalTheory.HeckeCharsOfSquare

theorem chars {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}
    (hL : Lc.Is μ₀) (W : G.Weil) (i j : Fin D.R.m) (t : T) :
    IsHeckeChar D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧
    IsHeckeChar D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧
    IsHeckeChar D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∧
    IsHeckeChar D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2) / (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))) ∧
    ResEta D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (rankV D i j) ∧
    ResEta D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (rankV D (i + 1) (j + 1)) ∧
    ResEta D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)))
      (rankV D (i + 1) (j + 1) + rankV D i j) ∧
    ResEta D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2) / (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)))
      (rankV D (i + 1) (j + 1) + rankV D i j) := by
  have ht : Odd D.R.t := D.R.t_odd
  have hr : Odd D.R.r := by
    have h1 := D.R.k_even; have h2 := D.R.m_even; have h3 := D.R.two_le_m
    unfold Ranks.r; grind
  have hs : Odd (sLen D) := hr.add_even (by decide : Even 6)
  have hi := i.2
  have hj := j.2
  have rk : ∀ a b : ℕ, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b := fun a b ha hb =>
    (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hth : ResEta D (Lc.mu t (j + 1)) 0 ∧ ResEta D Lc.eta 1 := by
    have hW := W.om_is (.mu t i j) (show Node.InRange D.R.m (.grid i (j + 1)) from ⟨by omega, by omega⟩)
    have hS := hW.resS
    have hT := hW.resT
    have e1 : (G.pS (.mu t i j)).rank = rankV D i j := rk _ _ (by omega) (by omega)
    have e2 : (G.pT (.mu t i j)).rank = rankV D i (j + 1) := rk _ _ (by omega) (by omega)
    rw [GridData.chrS, e1] at hS
    rw [GridData.chrT, e2] at hT
    refine GlobalTheory.HeckeCharsOfSquare.resEta_of_att hS hT ?_
    have e3 : rankV D i (j + 1) = rankV D i j + D.R.t := by simp only [rankV]; ring
    rw [e3, ← add_assoc]
    exact Even.add_odd ⟨_, rfl⟩ ht
  have hdn : ResEta D (G.ch.chi (D.R.m - i)) 0 := by
    have hW := W.om_is (.chi i (j + 1)) (show Node.InRange D.R.m (.grid (i + 1) (j + 1)) from ⟨by omega, by omega⟩)
    have hS := hW.resS
    have hT := hW.resT
    have e1 : (G.pS (.chi i (j + 1))).rank = rankV D (i + 1) (j + 1) := rk _ _ (by omega) (by omega)
    have e2 : (G.pT (.chi i (j + 1))).rank = rankV D i (j + 1) := rk _ _ (by omega) (by omega)
    rw [GridData.chrS, e1] at hS
    rw [GridData.chrT, e2] at hT
    refine (GlobalTheory.HeckeCharsOfSquare.resEta_of_att hS hT ?_).1
    have e3 : rankV D (i + 1) (j + 1) = rankV D i (j + 1) + sLen D := by simp only [rankV]; ring
    rw [e3, add_comm, ← add_assoc]
    exact Even.add_odd ⟨_, rfl⟩ hs
  have hη : IsHeckeChar D Lc.eta := hL.eta.1
  have hμ : IsHeckeChar D (Lc.mu t (j + 1)) := GlobalTheory.HeckeCharsOfSquare.isHeckeChar_mul (hL.mu0 j).1 (hL.xi t).1
  have hχ : IsHeckeChar D (G.ch.chi (D.R.m - i)) := (G.ch.chi_eq (D.R.m - i) (by omega) (by omega)).1
  have hα := GlobalTheory.HeckeCharsOfSquare.isHeckeChar_mul hμ (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_pow hη (rankV D i j % 2))
  have hβ := GlobalTheory.HeckeCharsOfSquare.isHeckeChar_mul hχ (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_pow hη (rankV D i j % 2))
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  obtain ⟨a, ha⟩ := ht
  obtain ⟨b, hb⟩ := hs
  have rα : ResEta D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (rankV D i j) :=
    GlobalTheory.HeckeCharsOfSquare.resEta_of_mod (GlobalTheory.HeckeCharsOfSquare.resEta_mul hth.1 (GlobalTheory.HeckeCharsOfSquare.resEta_pow hth.2 (rankV D i j % 2))) (by omega)
  have rβ : ResEta D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (rankV D (i + 1) (j + 1)) :=
    GlobalTheory.HeckeCharsOfSquare.resEta_of_mod (GlobalTheory.HeckeCharsOfSquare.resEta_mul hdn (GlobalTheory.HeckeCharsOfSquare.resEta_pow hth.2 (rankV D i j % 2))) (by omega)
  refine ⟨hα, hβ, GlobalTheory.HeckeCharsOfSquare.isHeckeChar_div hα hβ, GlobalTheory.HeckeCharsOfSquare.isHeckeChar_div hβ hα, rα, rβ, ?_, GlobalTheory.HeckeCharsOfSquare.resEta_div rβ rα⟩
  exact GlobalTheory.HeckeCharsOfSquare.resEta_of_mod (GlobalTheory.HeckeCharsOfSquare.resEta_div rα rβ) (by omega)

end Chars

end GlobalTheory.SqTower.TopExists

end
end
