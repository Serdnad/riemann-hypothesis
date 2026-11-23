module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle451
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle350
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle039
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle234
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle469
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle274
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle363
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle285
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle390
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle377
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle771
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle803
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle963
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle772
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle802
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle942
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle890
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

theorem _root_.GlobalTheory.T.thetaLocalModels_of_splitUnramified_joints : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex), (∀ μ, DV.Used D μ → JointsAt t μ) → (∀ u, ex.tw.e0 u D.what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _)) → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → GlobalTheory.TwU.ModelsOK D Gl ex.cmp Dx ex.tw := by
  first | exact @GlobalTheory.TwV.modelsOK_of_joints | exact GlobalTheory.TwV.modelsOK_of_joints | (intros; apply GlobalTheory.TwV.modelsOK_of_joints <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain



theorem GlobalTheory.Svd.jointsAt_all_std : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), Part w Z (ofObj O) → G.LatTied O.gatT O.Gx O.Gy → (∃ t : KerEntTied O.ex, ∀ μ, GlobalTheory.TwV.JointsAt t μ) ∧ ∀ u, O.ex.tw.e0 u (w.D Z).what₂.mu0 = O.ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  intro B f T w Z O P hL
  obtain ⟨htw, -, hpiT, -, t, hstd, -, -⟩ := GlobalTheory.Svd.Part.kerTie B f T w Z O P
  have hchi := (GlobalTheory.Mem.ChiDVal.chiD_values_and_cc_top B f T w Z).1
  obtain ⟨L, gatT, Gx, Gy, K, X, cX, ex⟩ := O
  obtain ⟨pin, col, errX, tp, xi, qp, ker0, ker_eq, ker⟩ := P
  simp only [ofObj, extraObj] at ker_eq
  have h1 := congrArg Sigma.fst ker_eq
  simp only at h1
  subst h1
  have h2 := eq_of_heq (Sigma.mk.inj ker_eq).2
  have h3 := congrArg Sigma.fst h2
  simp only at h3
  obtain ⟨lev, th, th_io, cmp, lat, tw, exker⟩ := ex
  simp only at h3
  subst h3
  exact GlobalTheory.T.kernel_relation_true_columns_joints_all_tuples w.I w.ok w.pins w.l w.l0 Z L col.Gt Gx Gy K X cX _ t col.C col.full col.g _ tp xi
    pin.isTw pin.jets htw hpiT hstd col.std col.stdLv col.stdDt col.herm_eq col.forms_eq hchi hL
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SummandEig

theorem irrScalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (α : Formalism.AUTREP.GAf L n), TrivOutside {s.v} α → ∀ (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n), (∀ γ ∈ R, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, r γ = k₁ * α * k₂) → (∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ (r γ)⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := GlobalTheory.T.sphericalDoubleCosetSum_scalar_irreducible_fixed

theorem isoScalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ), (∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f) → ∀ f ∈ Formalism.L2.NG.isoTyp a.ρ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := GlobalTheory.T.rightTranslationSum_scalar_isotypic

theorem frameReps : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (Ψ : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ψ → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab V Pp d → ∃ (s : SplitPlace D.host.E) (α : Formalism.AUTREP.GAf D.host.E n), Formalism.L2.NG.OverPl Pp s.v ∧ TrivOutside {s.v} α ∧ (∀ γ ∈ GlobalTheory.Hk3.rep V Pp d, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, Formalism.IndefR.principalLevelFrame.pre Ψ γ = k₁ * α * k₂) ∧ ∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ GlobalTheory.Hk3.rep V Pp d ∧ (Formalism.IndefR.principalLevelFrame.pre Ψ γ)⁻¹ * x ∈ Umax D.host.E n := GlobalTheory.T.standardFrame_sphericalDoubleCoset_reps_local

theorem rep_mem {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    {γ : Formalism.L2.Theta.GA D V} (hγ : γ ∈ GlobalTheory.Hk3.rep V Pp d) : γ ∈ Formalism.L2.Theta.GfC V := by
  unfold GlobalTheory.Hk3.rep at hγ
  split_ifs at hγ with hl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hR⟩ := hl.choose_spec
    exact (hR.1 γ hγ).1
  · simp at hγ

theorem cast_sum {D : D7} (M : MtFam D) (μ : D.what₂.Tup) {j k : ℕ} (e : j = k) (h1 : 1 ≤ k) (h2 : k ≤ D.R.m)
    (h1' : 1 ≤ j) (h2' : j ≤ D.R.m) (f' : D.what₂.Mt μ j) {ι : Type} (R : Finset ι) (r : ι → Formalism.AUTREP.GAf D.host.E D.R.nV)
    (c : ℂ) (h : ∑ γ ∈ R, Formalism.L2.NG.rt D.host.E D.R.nV (r γ) ((M μ k h1 h2).real (e ▸ f')) = c • (M μ k h1 h2).real (e ▸ f')) :
    ∑ γ ∈ R, Formalism.L2.NG.rt D.host.E D.R.nV (r γ) ((M μ j h1' h2').real f') = c • (M μ j h1' h2').real f' := by
  subst e
  exact h

theorem extV_inf {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (j : Fin D.R.m) (t : X.T) (y : (X.R.HV j t).H) {a b : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Vc D j)}
    (ha : a ∈ Formalism.L2.Theta.GinfC (Formalism.IndefR.Links.Vc D j)) (hb : b ∈ Formalism.L2.Theta.GfC (Formalism.IndefR.Links.Vc D j)) :
    X.R.extV j t y (a * b) = (X.R.cV j).ρ a⁻¹ (X.R.extV j t y b) := by
  have hcv := (X.given.core.models.cV j).1
  have e0 : ∀ g, X.R.extV j t y g = (X.R.cV j).ρ g⁻¹ ((X.R.HV j t).e y ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g)) := fun g => rfl
  have e1 : (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict a = 1 := by
    apply Subtype.ext
    exact (MonoidHom.mem_ker (f := Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j))).1 ha
  refine (e0 (a * b)).trans (Eq.trans ?_ (congrArg ((X.R.cV j).ρ a⁻¹) (e0 b)).symm)
  have e2 : (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict (a * b) = (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict b := by
    rw [map_mul, e1, one_mul]
  have e3 : (X.R.cV j).ρ (a * b)⁻¹ = (X.R.cV j).ρ a⁻¹ := by
    rw [mul_inv_rev, map_mul, hcv _ (inv_mem hb), one_mul]
  have e4 : (X.R.cV j).ρ b⁻¹ = 1 := hcv _ (inv_mem hb)
  have e5 : ∀ x, (X.R.cV j).ρ b⁻¹ x = x := fun x => by rw [e4]; rfl
  have e6 := congr (congrArg DFunLike.coe e3) (congrArg ((X.R.HV j t).e y) e2)
  exact e6.trans (congrArg ((X.R.cV j).ρ a⁻¹) (e5 _)).symm

end GlobalTheory.SummandEig
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LinModSpan

theorem isComp_mul_inv {E : Type} [Field E] [NumberField E] {μ η : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    {μw ηw : (w.adicCompletion E)ˣ →* ℂˣ} (hμ : IsComp μ w μw) (hη : IsComp η w ηw) :
    IsComp (μ * η⁻¹) w (μw * ηw⁻¹) := by
  refine ⟨?_, fun x => ?_⟩
  · have h1 := hμ.1
    have h2 := hη.1
    unfold GlobalTheory.SmGL.IsSmoothChar at h1 h2 ⊢
    have h3 : IsOpen (((μw.ker ⊓ ηw.ker : Subgroup _)) : Set (w.adicCompletion E)ˣ) := h1.inter h2
    exact Subgroup.isOpen_mono (H₁ := μw.ker ⊓ ηw.ker) (fun y hy => by
      simp only [Subgroup.mem_inf, MonoidHom.mem_ker] at hy ⊢
      simp [hy.1, hy.2]) h3
  · simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, hμ.2 x, hη.2 x]
    rfl

theorem main : ∀ (D : D7) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (V W : Formalism.BasicNotions.TH.HSp D) (n r : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (PW : Formalism.IndefR.principalLevelFrame.RowPsi W r) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.NJoin.StdFrame hF PV → GlobalTheory.NJoin.StdFrame hF PW → ∀ χV χW om, Formalism.IndefR.Datum.IsWeilDatumO ψ V W χV χW om → ∀ μ η : HChar D.host.E, Formalism.IndefR.Links.ChrEq χV μ → Formalism.IndefR.Links.ChrEq χW (μ * η⁻¹) → ∀ (s : SplitPlace D.host.E) μw ηw, IsComp μ s.w μw → IsComp η s.w ηw → ∀ f, Formalism.IndefR.Datum.IsThetaFunO ψ V W f → f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : IsLinAt (om.comp (PV.ψ.prodMap PW.ψ)) s μw ηw ι ∧ ∀ Φ, Formalism.IndefR.Datum.IsThetaFunO ψ V W (ι Φ)), LinearMap.range ι := by
  intro D ψ V W n r PV PW hF hV hW χV χW om hom μ η hμ hη s μw ηw hμw hηw f hf
  obtain ⟨p, hpe, hpr, FS, FT, c, hc, hci, hlocV, hlocW⟩ := GlobalTheory.T.standardFrames_read_splitPlace_unitaryGroup D V W n r PV PW hF hV hW s
  have cV := GlobalTheory.T.localComponent_of_idelicCharacterAgreement D s p hpe hpr χV μ hμ μw hμw
  have cW := GlobalTheory.T.localComponent_of_idelicCharacterAgreement D s p hpe hpr χW (μ * η⁻¹) hη (μw * ηw⁻¹) (isComp_mul_inv hμw hηw)
  obtain ⟨τ, hτ, hτom⟩ := GlobalTheory.T.linearModel_fourier_transform_exchange (s.w.adicCompletion D.host.E) n r
  have hOm := GlobalTheory.T.weilDatum_localModel_formula D
  have h2 := GlobalTheory.T.thetaFunction_mem_span_localSchrodingerModels_split D _ p (Fin r) (Fin n) V W FS FT ψ hom.std f hf
  refine (iSup₂_le fun Tm hTm => ?_ : (⨆ (Tm : GlobalTheory.SplitWeil.SB (Matrix (Fin r) (Fin n) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : p.IsModel ψ FS FT Tm), LinearMap.range Tm) ≤ _) h2
  have hr : LinearMap.range Tm = LinearMap.range (Tm ∘ₗ τ) := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.2 hτ, Submodule.map_top]
  rw [hr]
  refine le_iSup₂_of_le (f := fun (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : IsLinAt (om.comp (PV.ψ.prodMap PW.ψ)) s μw ηw ι ∧ ∀ Φ, Formalism.IndefR.Datum.IsThetaFunO ψ V W (ι Φ)) => LinearMap.range ι) (Tm ∘ₗ τ) ⟨?_, fun Φ => hTm.theta _⟩ le_rfl
  refine ⟨c, hc, hci, fun h g hh hg Φ Φ' hΦ => ?_⟩
  have hΦ'' : Φ'.1 = GlobalTheory.SplitWeil.om μw (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g)) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) Φ.1 := hΦ
  have key := hOm (s.w.adicCompletion D.host.E) p ψ V W χV χW om hom μw (μw * ηw⁻¹) cV cW (Fin r) (Fin n) FS FT Tm hTm
    (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) (PW.ψ g) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g))
    (hlocV h hh) (hlocW g hg) (τ Φ)
    (((ηw (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h))) : ℂˣ) : ℂ) • τ Φ') (by
      rw [Submodule.coe_smul, hτom μw _ _ Φ Φ' hΦ'']
      congr 2
      simp [mul_inv_rev, mul_comm])
  simp only [LinearMap.comp_apply, MonoidHom.comp_apply]
  show om (PV.ψ h, PW.ψ g) (Tm (τ Φ)) = _
  rw [key, map_smul]

end GlobalTheory.LinModSpan
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigTransport

theorem frame_hyp : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → ∀ (sp : SplitPlace D.host.E)
    (κ : Formalism.AUTREP.GAf D.host.E n), Ps.ψ κ ∈ GlobalTheory.Hk3.hyp V sp.w ↔ κ ∈ Umax D.host.E n ∧ TrivOutside {sp.v} κ := GlobalTheory.T.standardFrame_mem_hyperspecial_iff_maxCompact_trivOutside

theorem exists_std : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → V.rank = n → ∀ (sp : SplitPlace D.host.E)
    (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)), Formalism.AUTREP.IsUnif D.host.E sp.v ϖ →
    ∀ k ≤ n, ∃ x₀ ∈ Formalism.AUTREP.tSet D.host.E n sp ϖ k, ∃ (e f : Formalism.L2.Theta.AE D) (ϖ' : 𝓞 D.host.E),
      Formalism.IndefR.Mult.IsPrimeIdem sp.w e f ∧ ϖ' ∈ sp.w.asIdeal ∧ ϖ' ∉ sp.w.asIdeal ^ 2 ∧
        Formalism.IndefR.Mult.SuppF V f (Ps.ψ x₀) ∧
        Formalism.IndefR.Mult.DivAt V e (ϖ' : D.host.E) (List.replicate k 1 ++ List.replicate (n - k) 0) (Ps.ψ x₀) := GlobalTheory.T.standardElement_splitPlace_label

theorem tSet_dc : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (sp : SplitPlace L)
    (ϖ : (sp.v).adicCompletion (maximalRealSubfield L)) (k : ℕ), ∀ x₀ ∈ Formalism.AUTREP.tSet L n sp ϖ k,
    ∀ κ, κ ∈ Formalism.AUTREP.tSet L n sp ϖ k ↔ ∃ k₁, (k₁ ∈ Umax L n ∧ TrivOutside {sp.v} k₁) ∧
      ∃ k₂, (k₂ ∈ Umax L n ∧ TrivOutside {sp.v} k₂) ∧ κ = k₁ * x₀ * k₂ := GlobalTheory.T.mem_heckeSplitPlaceSet_iff_doubleCoset

theorem pairwise_lab (k m : ℕ) : List.Pairwise (fun a b : ℤ => b ≤ a) (List.replicate k 1 ++ List.replicate m 0) := by
  rw [List.pairwise_append]
  refine ⟨List.pairwise_replicate.2 (Or.inr le_rfl), List.pairwise_replicate.2 (Or.inr le_rfl), ?_⟩
  intro a ha b hb
  rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  norm_num

end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

theorem isLab_std {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hs : GlobalTheory.NJoin.StdFrame hF Ps) (hn : V.rank = n) (sp : SplitPlace D.host.E)
    (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)) (hϖ : Formalism.AUTREP.IsUnif D.host.E sp.v ϖ)
    (k : ℕ) (hk : k ≤ n) :
    GlobalTheory.Hk3.IsLab V sp.w (List.replicate k 1 ++ List.replicate (n - k) 0) := by
  obtain ⟨x₀, -, e, f, ϖ', h1, h2, h3, h4, h5⟩ := exists_std hF Ps hs hn sp ϖ hϖ k hk
  exact GlobalTheory.SphLabelOps.isLab_of_divAt h1 h2 h3 (pairwise_lab _ _) h4 h5

theorem tSet_iff {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hs : GlobalTheory.NJoin.StdFrame hF Ps) (hn : V.rank = n) (sp : SplitPlace D.host.E)
    (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)) (hϖ : Formalism.AUTREP.IsUnif D.host.E sp.v ϖ)
    (k : ℕ) (hk : k ≤ n) (κ : Formalism.AUTREP.GAf D.host.E n) :
    κ ∈ Formalism.AUTREP.tSet D.host.E n sp ϖ k ↔
      ∃ γ ∈ GlobalTheory.Hk3.rep V sp.w (List.replicate k 1 ++ List.replicate (n - k) 0),
        γ⁻¹ * Ps.ψ κ ∈ GlobalTheory.Hk3.hyp V sp.w := by
  obtain ⟨x₀, hx₀, e, f, ϖ', h1, h2, h3, h4, h5⟩ := exists_std hF Ps hs hn sp ϖ hϖ k hk
  have hLab := GlobalTheory.SphLabelOps.isLab_of_divAt h1 h2 h3 (pairwise_lab _ _) h4 h5
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V sp.w
  have hR := GlobalTheory.SphLabelOps.reps_of_sphOp hK h1 h2 h3 h4 h5 (GlobalTheory.SphLabelOps.sphOp_rep hLab)
  have memK : ∀ l, l ∈ K ↔ l ∈ GlobalTheory.Hk3.hyp V sp.w := fun l => by rw [hK]; rfl
  have pre : ∀ l ∈ K, ∃ m, (m ∈ Umax D.host.E n ∧ TrivOutside {sp.v} m) ∧ Ps.ψ m = l := by
    intro l hl
    have hl' := (memK l).1 hl
    obtain ⟨m, rfl⟩ := Ps.onto l hl'.1.1
    exact ⟨m, (frame_hyp hF Ps hs sp m).1 hl', rfl⟩
  have img : ∀ m, (m ∈ Umax D.host.E n ∧ TrivOutside {sp.v} m) → Ps.ψ m ∈ K := fun m hm =>
    (memK _).2 ((frame_hyp hF Ps hs sp m).2 hm)
  constructor
  · intro hκ
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (tSet_dc n sp ϖ k x₀ hx₀ κ).1 hκ
    obtain ⟨γ, ⟨hγ, hm⟩, -⟩ := hR.2 (Ps.ψ (k₁ * x₀ * k₂))
      ⟨Ps.ψ k₁, img _ hk₁, Ps.ψ k₂, img _ hk₂, by rw [map_mul, map_mul]⟩
    exact ⟨γ, hγ, (memK _).1 hm⟩
  · rintro ⟨γ, hγ, hm⟩
    obtain ⟨l₁, hl₁, l₂, hl₂, hγe⟩ := hR.1 γ hγ
    have hl : γ⁻¹ * Ps.ψ κ ∈ K := (memK _).2 hm
    obtain ⟨m₁, hm₁, e₁⟩ := pre l₁ hl₁
    obtain ⟨m₂, hm₂, e₂⟩ := pre (l₂ * (γ⁻¹ * Ps.ψ κ)) (mul_mem hl₂ hl)
    refine (tSet_dc n sp ϖ k x₀ hx₀ κ).2 ⟨m₁, hm₁, m₂, hm₂, Ps.inj ?_⟩
    rw [map_mul, map_mul, e₁, e₂, ← mul_assoc, ← mul_assoc, ← hγe, mul_inv_cancel, one_mul]

end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport


open Classical in
theorem finsum_cosets {G W ι : Type} [Group G] [AddCommGroup W] (J : Subgroup G) (T : Set G) (R : Finset ι)
    (x : ι → G) (F : G → W) (h1 : ∀ γ ∈ R, x γ ∈ T) (h2 : ∀ y ∈ T, ∃ γ ∈ R, (x γ)⁻¹ * y ∈ J)
    (h3 : ∀ γ ∈ R, ∀ γ' ∈ R, (x γ)⁻¹ * x γ' ∈ J → γ = γ')
    (hF : ∀ y ∈ T, ∀ y' ∈ T, y⁻¹ * y' ∈ J → ∀ g, F (g * y') = F (g * y)) (g : G) :
    (∑ᶠ c : G ⧸ J, if hc : ∃ y ∈ T, (y : G ⧸ J) = c then F (g * hc.choose) else 0) =
      ∑ γ ∈ R, F (g * x γ) := by
  classical
  have hsupp : (Function.support fun c : G ⧸ J =>
      if hc : ∃ y ∈ T, (y : G ⧸ J) = c then F (g * hc.choose) else 0) ⊆
      ↑(R.image fun γ => (x γ : G ⧸ J)) := by
    intro c hc
    by_cases h : ∃ y ∈ T, (y : G ⧸ J) = c
    · obtain ⟨y, hy, rfl⟩ := h
      obtain ⟨γ, hγ, hm⟩ := h2 y hy
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, hγ, QuotientGroup.eq.2 hm⟩)
    · exact absurd (by simp [h]) hc
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    have hc : ∃ y ∈ T, (y : G ⧸ J) = (x γ : G ⧸ J) := ⟨x γ, h1 γ hγ, rfl⟩
    rw [dif_pos hc]
    obtain ⟨hy, he⟩ := hc.choose_spec
    exact (hF _ hy _ (h1 γ hγ) (QuotientGroup.eq.1 he) g).symm
  · intro γ hγ γ' hγ' e
    exact h3 γ hγ γ' hγ' (QuotientGroup.eq.1 e)

theorem triv_mul {D : D7} {n : ℕ} {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))}
    {x y : Formalism.AUTREP.GAf D.host.E n} (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) :=
  fun v hv => by
    have e : (x * y).1.1 = x.1.1 * y.1.1 := rfl
    show (x * y).1.1.map (compAt D.host.E v) = 1
    rw [e, Matrix.map_mul]
    rw [show x.1.1.map (compAt D.host.E v) = 1 from hx v hv, show y.1.1.map (compAt D.host.E v) = 1 from hy v hv, mul_one]

theorem triv_inv {D : D7} {n : ℕ} {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))}
    {x : Formalism.AUTREP.GAf D.host.E n} (hx : TrivOutside T x) : TrivOutside T x⁻¹ := fun v hv => by
  have e : (x⁻¹).1.1.map (compAt D.host.E v) * x.1.1.map (compAt D.host.E v) = 1 := by
    rw [← Matrix.map_mul]
    have : (x⁻¹).1.1 * x.1.1 = 1 := by
      show (x⁻¹ * x).1.1 = 1
      rw [inv_mul_cancel]
      rfl
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  show (x⁻¹).1.1.map (compAt D.host.E v) = 1
  rwa [show x.1.1.map (compAt D.host.E v) = 1 from hx v hv, mul_one] at e

theorem rep_inj {D : D7} (V : TH.HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (hd : GlobalTheory.Hk3.IsLab V P d) : ∀ γ ∈ GlobalTheory.Hk3.rep V P d, ∀ γ' ∈ GlobalTheory.Hk3.rep V P d,
      γ⁻¹ * γ' ∈ GlobalTheory.Hk3.hyp V P → γ = γ' := by
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  obtain ⟨g₀, -, hR⟩ := GlobalTheory.SphLabelOps.exists_reps hK (GlobalTheory.SphLabelOps.sphOp_rep hd)
  intro γ hγ γ' hγ' hm
  rw [hK] at hm
  exact (hR.2 γ' (hR.1 γ' hγ')).unique ⟨hγ, hm⟩ ⟨hγ', by rw [inv_mul_cancel]; exact one_mem K⟩

end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

theorem sum_single {M : Type} [AddCommGroup M] [Module ℂ M] (d : List ℤ) (G : List ℤ → M) :
    ∑ d' ∈ (Finsupp.single d (1 : ℂ)).support, (Finsupp.single d (1 : ℂ)) d' • G d' = G d := by
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

theorem eig_sum {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp) {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m)
    (f : D.what₂.Mt μ (j.1 + 1)) (y) (hy : X.R.extV j (X.tupT μ) y = X.fn hμ j f) (h)
    (hOps : GlobalTheory.Hk3.IsOpsV X.R j (X.tupT μ) h) (s : GlobalTheory.DownLift.Sys D)
    (hEig : GlobalTheory.DownLift.IsEigV X.R j (X.tupT μ) h s y) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hG : GlobalTheory.Hk3.Good X.R (X.tupT μ) P) (d : List ℤ) (hd : GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) P d)
    (g : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Vc D j)) :
    ∑ a ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) P d, X.fn hμ j f (g * a) = s P d • X.fn hμ j f g := by
  have hc : (X.R.cV j).Is := X.given.core.models.cV j
  have e1 := hOps P hG (Finsupp.single d 1) y
  have e2 := hEig P d hG hd
  have e4 : GlobalTheory.Hk3.hkF (Formalism.IndefR.Links.Vc D j) P (Finsupp.single d 1) ((X.R.HV j (X.tupT μ)).e y) =
      s P d • (X.R.HV j (X.tupT μ)).e y :=
    e1.symm.trans ((congrArg (X.R.HV j (X.tupT μ)).e e2).trans (map_smul _ _ _))
  have e3 := ((congrArg (fun F => (X.R.cV j).ext F g) e4).symm.trans
    (GlobalTheory.DefLiftHecke.ext_hkF (X.R.cV j) hc P (Finsupp.single d 1) ((X.R.HV j (X.tupT μ)).e y) g)).trans
    (sum_single d _)
  have hy2 : ∀ x, (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e y) x = X.fn hμ j f x := fun x =>
    (show X.R.extV j (X.tupT μ) y x = (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e y) x from rfl).symm.trans (congrFun hy x)
  calc ∑ a ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) P d, X.fn hμ j f (g * a)
      = ∑ a ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) P d, (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e y) (g * a) :=
        Finset.sum_congr rfl fun a _ => (hy2 _).symm
    _ = (X.R.cV j).ext (s P d • (X.R.HV j (X.tupT μ)).e y) g := e3.symm
    _ = s P d • (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e y) g :=
        congrFun (map_smul (X.R.cV j).ext (s P d) ((X.R.HV j (X.tupT μ)).e y)) g
    _ = s P d • X.fn hμ j f g := by rw [hy2]

end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

end GlobalTheory.EigTransport
end

section

open Formalism.BasicNotions

namespace GlobalTheory.RawLift.Assembled

theorem rallisConv_of_siegelWeil : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary →
    ∀ D : D7, GlobalTheory.RawLift.RallisConv D :=
  fun hP hW D => GlobalTheory.RawLift.rallisConv_of_steps D (GlobalTheory.SWPairProof.swPair hW D) (GlobalTheory.EisAbsPf.eisAbs hP D)
    (GlobalTheory.RawLift.kerAbs_of_cuspRapidDecay hP D) (GlobalTheory.RawLift.Move.termMove D) (GlobalTheory.TermInvProof.termInv D)
    (GlobalTheory.CuspKillProof.cuspKill_holds D)

end GlobalTheory.RawLift.Assembled
end
