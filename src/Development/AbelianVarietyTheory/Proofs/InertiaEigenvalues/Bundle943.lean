module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle902
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle826
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle547
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.WeightZeroSectionValueConjPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFiniteHeisenbergFockVacuumThetaFunctions
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle330
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle327
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle089
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowClassNumberIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle211
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle126
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle938
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle089
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle104
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle118
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle940
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle788
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.MarkVal

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix



theorem val_at_mark {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n r : ℕ} (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) (d : DeltaDat Xo c n)
    (U₂ : Unf d.Xo₂ d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) r)
    (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (C : GlobalTheory.Member.Ctx d.Xo₂ d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) V r) (hC : C.OK) (hι : C.ι = ι)
    (hx : C.x₀ = x₀) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ) (hf : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0)
    (hxi1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
      ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (d.l₂.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V u)) = 1)
    (hxi2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
    (hv : GlobalTheory.OneMapAll.CXiAt V hr σ0 d U₂ dict₂ ι x₀ xi c0)
    (y : FrPt d.Xo₂ d.c₂ (CAt (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)))) (k : Fin C.F.n) (P : (C.F.Di k).La →+ (Fin C.g → ℂ))
    (hP : IsPeriod (C.F.Di k) (fun j => relab d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) (C.e j).1) P)
    (hy : y.x = C.F.u k P) (h γ : GA D V) (hM : C.Mark h k γ) :
    toC (evR d.Xo₂ d.c₂ d.cδ y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ) := by
  classical
  subst hr hι hx
  obtain ⟨hU, hW, g₀, e₀, F, ik, φ, th, hth, hD, hval⟩ := hv
  have hσ : GoodEmb d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) := hC.good
  have hor : ∀ j, IsOrthogonalFrame (U₂.X j) C.x₀ := by
    intro j τ hτ
    have h1 := hC.orth k
    have hG : (U₂.X j).Gm = (C.M.X k).Gm := by rw [(hW j).1, (hC.modelW k).1]
    have hp : (U₂.X j).p0 = (C.M.X k).p0 := ((hU.2.1 j).1).trans (hC.base.type k).1.symm
    have hΨ : τ ∈ (C.M.X k).Ψ := ((hC.base.type k).2 τ).2 (((hU.2.1 j).2 τ).1 hτ)
    rw [hG, hp]
    exact h1 τ hΨ

  have hdom := GlobalTheory.T.latticeDictionary_frame_mem_open_frames V U₂ dict₂ C.ι e₀ F ik φ th C.x₀ hσ hC.lA hU hW hD hth hor
  obtain ⟨h', hh'⟩ := GlobalTheory.TwistTie.exists_dict_over V U₂ dict₂ C.ι e₀ F ik φ th C.x₀ hσ hC.lA hC.pos hU hW hD hC.iota
    hth hor hdom y
  obtain ⟨P', -, hP', hy', -⟩ := hD.1.2 (dict₂ h').1 ⟨_, hdom h'⟩
  have hpt : C.F.u k P = F.u (ik (dict₂ h').1) P' := hy.symm.trans (hh'.trans hy')
  have hg : (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) (IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ) = H.rt0 := hC.good
  obtain ⟨gam, hgE, hgm⟩ := GlobalTheory.T.familyUniformisation_points_eq_marked_isometry C.F F hC.pos hg
    ((GlobalTheory.Relab.relab_good _ H d.l₂ d.c₂ _ hσ).2.2.2 Dw C.g C.e)
    ((GlobalTheory.Relab.relab_good _ H d.l₂ d.c₂ _ hσ).2.2.2 Dw g₀ e₀) (C.e.trans e₀.symm)
    (fun j => by simp) k (ik (dict₂ h').1) P P' hP hP' hpt
  obtain ⟨γ', hγ', hΛ', hm', -⟩ := hD.2 h'
  have hxe := GlobalTheory.T.detCharacter_eq_of_marked_lattice_isometry d.l₂ V C.ι hC.iota.emb.2 (C.F.Di k) (F.Di (ik (dict₂ h').1)) (C.F.t k) (F.t (ik (dict₂ h').1))
    (C.M.X k) (U₂.X (dict₂ h').1) (C.M.φ k) (φ (dict₂ h').1) (γ * h) (γ' * h') (hC.modelW k) (hW _)
    (hC.base.ef k) (hD.1.1 _) hM.2.1 hΛ' hM.2.2 hm' gam hgE hgm xi hxi1 hxi2
  have hv := hval h' γ' ⟨hγ', hΛ', hm'⟩
  rw [GlobalTheory.WeightZeroValue.evR_eq_of_same_point hf hh', ← hxe, ← hv]
  show _ = (if h'' : (dict₂ h').2 ∈ (U₂.X (dict₂ h').1).dom then toC (evR d.Xo₂ d.c₂ d.cδ (U₂.un _ ⟨_, h''⟩)) else 0)
  rw [dite_eq_left (hdom h')]

end GlobalTheory.MarkVal

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.MarkVal



theorem val_on_marked_space : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (a : Tp) (C : GlobalTheory.Member.Ctx (M.dδ a).Xo₂ (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (Wc D i) D.R.r), C.OK → C.ι = iotaW T i → C.x₀ = T.x₀ ((i : ℕ) + 1) M.s0 → ∀ (f : Rul (M.dδ a).Xo₂ (M.dδ a).c₂) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ), f ∈ sec (M.dδ a).Xo₂ (M.dδ a).c₂ 0 0 → (∀ u : GA D (Wc D i), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ a).l₂.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1) → (∀ γ ∈ GQ (Wc D i), xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) γ)) = 1) → GlobalTheory.OneMapAll.CXiAt (Wc D i) (rank_Wc i) (inC M.c') { M.dδ a with cδ := f } (M.U₂ a) (M.dict₂ a) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) xi c0 → ∀ (y : FrPt (M.dδ a).Xo₂ (M.dδ a).c₂ (CAt ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)))) (k : Fin C.F.n) P, IsPeriod (C.F.Di k) (fun j => relab (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (C.e j).1) P → y.x = C.F.u k P → ∀ h γ : GA D (Wc D i), C.Mark h k γ → toC (evR (M.dδ a).Xo₂ (M.dδ a).c₂ f y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) (γ * h))) : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hcore hfw i Tp tup M hM a C hOK hι hx f xi c0 hf hxi1 hxi2 hCX y k P hPer hy h γ hmk
  exact val_at_mark (Wc D i) (rank_Wc i) (inC M.c') { M.dδ a with cδ := f } (M.U₂ a) (M.dict₂ a) (iotaW T i)
    (T.x₀ ((i : ℕ) + 1) M.s0) C hOK hι hx xi c0 hf hxi1 hxi2 hCX y k P hPer hy h γ hmk

end GlobalTheory.MarkVal
end
end

section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneCover

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV GlobalTheory.TupleCover

variable {D : D7}



theorem exists_fun_cover {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {n r : ℕ} (d : DeltaDat Xo c n) (V : HSp D) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hio : IotaOK Dw V ι) (hpos : 1 ≤ Dw.p + Dw.q)
    (hx₀ : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hA : d.l₂.A = 1) :
    ∃ (U₂ : Unf d.Xo₂ d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r),
      IsUnf U₂ ∧ (∀ k, ModelW V hr (U₂.X k)) ∧
      ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
        (F : FamilyUnif d.Xo₂ (((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)).comp
            (IntermediateField.inclusion d.c₂.le).toRingHom)
          (fun j => relab d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) (e j).1))
        (ik : U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U₂.X k).Λ)
        (th : ∀ k, (U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
        (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U₂ V hr dict₂ ι e F ik φ th x₀ ∧
        ∀ (_ : d.IsLev) (_ : FnAlgClosed (Xo := d.Xo₂) (c := d.c₂)) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
          (_ : ∀ g : GA D V, (∃ w ∈ intAE D, ((Matrix.GeneralLinearGroup.det (finHom V g) :
            (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = d.l₂.M • w) →
            xi (Matrix.GeneralLinearGroup.det (finHom V g)) = 1)
          (_ : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
          (m : ℕ) (_ : 0 < m) (_ : ∀ g : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V g)) ^ m = 1)
          (_ : zeta m ∈ c.F),
          ∃ f : Rul d.Xo₂ d.c₂, ({ d with cδ := f } : DeltaDat Xo c n).IsLev ∧ f ^ m = 1 ∧
            ∀ h γ : GA D V, MarkBy U₂ V hr dict₂ ι F ik φ h γ →
              rdU U₂ f (dict₂ h).1 (dict₂ h).2 =
                1 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ) := by
  have hσ : d.c₂.F.val.toRingHom = (inC c).comp (d.eF.symm : d.c₂.F →+* c.F) := RingHom.ext fun _ => rfl
  have hg₂ : GoodEmb d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) := by
    rw [← hσ]; rfl
  obtain ⟨C, hC, hCι, hCx⟩ := (exists_ctx D H Dw d.l₂ d.Xo₂ d.c₂ _ V r hr ι hio hpos hA hg₂).2.2 x₀ hx₀
  obtain ⟨Kf, hKf⟩ := (PrincLevel.exists_levelK_and_nhds D V d.l₂.M).1
  obtain ⟨un, dict, mu, -, -, hP⟩ := exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1 ⟨continuous_const, fun _ => rfl⟩
    (fun _ => rfl)
  obtain ⟨g, e, F, ik, φ, th, hth, hdu, hdl⟩ := hP.dictLaws
  refine ⟨C.unf un, dict, hP.unf, hP.modelW, g, e, F, ik, φ, th, hth, ?_, ?_⟩
  · rw [← hCι, ← hCx]
    exact hdl
  intro hlev hcl xi h1 h2 m hm h3 hz
  obtain ⟨f, hf, hfm, -, hfx⟩ := GlobalTheory.XiFun.exists_sec_char_val D _ _ _ _ _ _ _ _ C.hr (C.unf un) dict C.ι g e F ik φ th C.x₀
    hC.iota hpos hA hg₂ hP.modelW hdl hdu.2.2.2.1 hcl xi
    (fun u _ hu => h1 u (by rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]; exact hu)) h2
    (fun h => ⟨⟨_, d.hF.symm ▸ GlobalTheory.NormOneChar.mem_of_pow_eq_one hm hz (by
      rw [← Units.val_pow_eq_pow_val, h3 h, Units.val_one])⟩, rfl⟩)
  have hfm' : f ^ m = 1 := hfm m h3
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, -, l9⟩ := hlev
  refine ⟨f, ⟨l1, l2, l3, l4, l5, l6, l7, hf, fun k _ _ _ y => ?_⟩, hfm', fun h γ hmk => ?_⟩
  · exact GlobalTheory.XiFun.evR_ne_zero_of_pow _ _ f d.cδ m hm hfm' k y (l9 k y)
  · rw [one_mul]
    rw [← hCι] at hmk
    exact hfx h γ hmk

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem halfIs_of_eq {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {t t' : T0}
    (e : R.Q t' = R.Q t) {Mb I : Ideal (𝓞 D.host.E)} (h : HalfIs R t' Mb I) : HalfIs R t Mb I := by
  unfold HalfIs at h ⊢
  rwa [e] at h

theorem xi_pow_eq_one (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (h : ChrEq c χ) (n : ℕ)
    (ho : χ.OrderDvd n) (x : (AE D)ˣ) : c x ^ n = 1 :=
  GlobalTheory.T.heckeChar_eq_one_of_trivial_finitePartOne D (c ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (GlobalTheory.T.idelicCharacter_pow_eq_one_finiteIdeles_of_orderDvd D c χ h n ho) x

def CoversRep (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (n : ℕ)
    (pd : T0 → ℕ) (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → Level T.Q.H) (rep : T0 → T0) (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) : Prop :=
  ∃ (d : T0 → DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n)
    (U : ∀ t, Unf (d t).Xo₂ (d t).c₂ ((inC c').comp ((d t).eF.symm : (d t).c₂.F →+* c'.F)) D.R.r)
    (dict : ∀ t, GA D (Wc D i) → Σ k, Frame ((U t).X k).Ψ D.R.r)
    (f : ∀ t, Rul (d (rep t)).Xo₂ (d (rep t)).c₂)
    (xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ),
    (∀ t, (d t).pd = pd t ∧ (d t).I = I t ∧ (d t).l₂ = l₂ t) ∧
    CovPin (T.Q.Xo ((i : ℕ) + 1)) c' (fun t => ({ d (rep t) with cδ := f t } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n)) ∧
    (∀ t, HalfIs R t T.Q.l.Mb (d (rep t)).I) ∧
    (∀ t, XiIs R i t (xi t)) ∧
    CXiVal (Wc D i) (rank_Wc i) (inC c') (fun t => ({ d (rep t) with cδ := f t } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n))
      (fun t => U (rep t)) (fun t => dict (rep t)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) (sOv T.toCore c' hle)) xi ∧
    (∀ t k, ModelW (Wc D i) (rank_Wc i) ((U (rep t)).X k))



theorem exists_covers_rep (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) {μ0 : T0} [Finite T0]
    (hT : LawsJ T) (hL : R.toLevCh.Is μ0) (i : Fin D.R.m) (n : ℕ)
    (pd : T0 → ℕ) (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → Level T.Q.H)
    (hl : ∀ t, IsCoverLevel T.Q.l (pd t) (I t) (l₂ t)) (hH : ∀ t, HalfIs R t T.Q.l.Mb (I t))
    (rep : T0 → T0) (hrep : ∀ t, R.Q (rep t) = R.Q t) :
    ∃ c₁ : Coeff T.Q.l, T.Q.c.F ≤ c₁.F ∧ D.what₂.embLL.toRatAlgHom.fieldRange ≤ c₁.F ∧
      (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ c₁.F) ∧
      ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F), c₁.F ≤ c'.F → CoversRep T R i n pd I l₂ rep c' hle := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hpq := (exists_iotaOK D T.Q hT.pins _ hj).2
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by omega
  have hX : ∀ t, ∃ (Xo₂ : Moduli (T.Q.Dw ((i : ℕ) + 1)) (l₂ t)) (c₀ : Coeff (l₂ t)),
      ∀ c'' : Coeff (l₂ t), c₀.F ≤ c''.F → FnAlgClosed (Xo := Xo₂) (c := c'') := fun t => by
    obtain ⟨Xo₂⟩ := GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.1 _ _ (T.Q.Dw ((i : ℕ) + 1)) (l₂ t) hpos
    obtain ⟨c₀, -⟩ := exists_coeff_ge (l₂ t) ⊥
    obtain ⟨c₁, -, h⟩ := (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Xo₂ c₀ hpos).2
    exact ⟨Xo₂, c₁, h⟩
  choose Xo₂ c₀ hc₀ using hX
  choose m hm ho using hL.xi_fin
  choose xi hx1 hx2 hx3 hx4 using fun t =>
    exists_xi D (Wc D i) (R.xi t) (R.xiH t) (hL.xi t) (m t) (hm t) (ho t) (hL.xi_triv t) (hL.xi_tame t)
  have := T.Q.c.fin
  have : ∀ t, FiniteDimensional ℚ (c₀ t).F := fun t => (c₀ t).fin
  have : ∀ t, FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta (m t)}) := fun t =>
    IntermediateField.adjoin.finiteDimensional
      ((Complex.isPrimitiveRoot_exp (m t) (hm t).ne').isIntegral (hm t)).tower_top
  have : FiniteDimensional ℚ D.what₂.embLL.toRatAlgHom.fieldRange :=
    LinearEquiv.finiteDimensional (D.what₂.embLL.toRatAlgHom.equivFieldRange).toLinearEquiv
  obtain ⟨c₁, hc₁⟩ := exists_coeff_ge T.Q.l ((T.Q.c.F ⊔ D.what₂.embLL.toRatAlgHom.fieldRange) ⊔
    ⨆ t, ((c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)}))
  have hsup₁ : ∀ t, (c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)} ≤ c₁.F := fun t =>
    ((le_iSup (fun t => (c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)}) t).trans le_sup_right).trans hc₁
  refine ⟨c₁, (le_sup_left.trans le_sup_left).trans hc₁, (le_sup_right.trans le_sup_left).trans hc₁, fun t x => ?_, fun c' hle hc' => ?_⟩
  · refine GlobalTheory.NormOneChar.mem_of_pow_eq_one (hm t) (hsup₁ t (le_sup_right (a := (c₀ t).F) (IntermediateField.mem_adjoin_simple_self ℚ _))) ?_
    rw [← Circle.coe_pow, xi_pow_eq_one D (R.xi t) (R.xiH t) (hL.xi t) (m t) (ho t) x]
    rfl
  have hsup : ∀ t, (c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)} ≤ c'.F := fun t => (hsup₁ t).trans hc'
  have hσ : GoodEmb T.Q.c (sOv T.toCore c' hle) := rfl
  obtain ⟨hio, hx₀⟩ := iotaOK_and_frame T hT _ hj _ hσ (Wc D i) (hT.spaceW _ hj _ hσ) (rank_Wc i)
  have key := fun t => by
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hl t
    have h0 : (c₀ t).F ≤ c'.F := le_sup_left.trans (hsup t)
    let c₂ : Coeff (l₂ t) := ⟨c'.F, c'.fin, c'.conj, h0 (c₀ t).zeta_mem, (c₀ t).le.trans h0⟩
    have hd := GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) c' hpos n (pd t) (I t) (l₂ t) (Xo₂ t) c₂ rfl
      l1 l2 l3 l4 l5
    have hd' : ∃ d : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n, d.pd = pd t ∧ d.I = I t ∧ d.l₂ = l₂ t ∧ d.IsLev ∧ d.l₂.A = 1 ∧
        FnAlgClosed (Xo := d.Xo₂) (c := d.c₂) ∧ ∃ _ : StarRing (𝓞 D.host.E), IsNab d.Xo₂ d.c₂ d.nab₂ := by
      obtain ⟨⟨pd', I', l₂', Xo₂', c₂', hF, r, mm, nab, cδ, φ₀⟩, a1, a2, a3, e₁, e₂, -, a4, a5⟩ := hd
      refine ⟨_, a1, a2, a3, a4, a3 ▸ l6, ?_, a5⟩
      dsimp only at a3 e₁ e₂ ⊢
      subst a3
      obtain rfl := eq_of_heq e₁
      obtain rfl := eq_of_heq e₂
      exact hc₀ t c₂ h0
    exact hd'
  choose d a1 a2 a3 a4 a5 a6 a7 using key
  have hM : ∀ t, ∀ PP ∈ R.Q t, (((d (rep t)).l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun t PP hPP => by
    refine (hH (rep t)).2.1 PP (by rw [hrep]; exact hPP) ?_
    have h1 : (((d (rep t)).l₂.M : ℕ) : 𝓞 D.host.E) ∈ (d (rep t)).l₂.Mb :=
      Ideal.mul_le_left ((d (rep t)).l₂.prod.ge (Ideal.mem_span_singleton_self _))
    rw [(a4 (rep t)).2.2.2.1, a2] at h1
    exact Ideal.mul_le_right h1
  choose U dict b3 using fun t => exists_fun_cover (d t) (Wc D i) (rank_Wc i) (iotaW T i) _ hio hpos hx₀ (a5 t)
  have b4 : ∀ t, ∃ f : Rul (d (rep t)).Xo₂ (d (rep t)).c₂,
      ({ d (rep t) with cδ := f } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n).IsLev ∧ f ^ m t = 1 ∧
      IsUnf (U (rep t)) ∧ (∀ k, ModelW (Wc D i) (rank_Wc i) ((U (rep t)).X k)) ∧
      ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw ((i : ℕ) + 1)).mult τ))
        (F : FamilyUnif (d (rep t)).Xo₂ (((inC c').comp ((d (rep t)).eF.symm : (d (rep t)).c₂.F →+* c'.F)).comp
            (IntermediateField.inclusion (d (rep t)).c₂.le).toRingHom)
          (fun j => relab (d (rep t)).c₂ ((inC c').comp ((d (rep t)).eF.symm : (d (rep t)).c₂.F →+* c'.F)) (e j).1))
        (ik : (U (rep t)).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((U (rep t)).X k).Λ)
        (th : ∀ k, ((U (rep t)).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
        (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
        DictLat (U (rep t)) (Wc D i) (rank_Wc i) (dict (rep t)) (iotaW T i) e F ik φ th (T.x₀ ((i : ℕ) + 1) (sOv T.toCore c' hle)) ∧
        ∀ h γ : GA D (Wc D i), MarkBy (U (rep t)) (Wc D i) (rank_Wc i) (dict (rep t)) (iotaW T i) F ik φ h γ →
          rdU (U (rep t)) f (dict (rep t) h).1 (dict (rep t) h).2 =
            1 * ((xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) (γ * h))) : ℂˣ) : ℂ) := fun t => by
    obtain ⟨u1, u2, g, e, F, ik, φ, th, v1, v2, v3⟩ := b3 (rep t)
    obtain ⟨f, f1, f2, f3⟩ := v3 (a4 (rep t)) (a6 (rep t)) (xi t)
      (hx2 t _ (d (rep t)).l₂.odd (unrAt_of_not_mem R hL t _ (hM t))) (hx3 t) (m t) (hm t) (hx4 t)
      (hsup t (le_sup_right (a := (c₀ t).F) (IntermediateField.mem_adjoin_simple_self ℚ _)))
    exact ⟨f, f1, f2, u1, u2, g, e, F, ik, φ, th, v1, v2, f3⟩
  choose f b1 b2 b5 using b4
  refine ⟨d, U, dict, f, xi, fun t => ⟨a1 t, a2 t, a3 t⟩, fun t => ⟨b1 t, a5 (rep t), a7 (rep t)⟩,
    fun t => ?_, hx1, ⟨1, ⟨1, one_pos, one_pow 1⟩, b5⟩, fun t => (b5 t).2.1⟩
  rw [a2]
  exact halfIs_of_eq R (hrep t) (hH (rep t))

end GlobalTheory.OneCover
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.CoverXiDet

theorem natM_mem_Mb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
  have h : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.subset_span rfl
  rw [← l.prod] at h
  exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h

theorem natM_mem_of_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l l₂ : Level H)
    (I P : Ideal (𝓞 E)) (h : l₂.Mb = l.Mb * I) (hI : I ≤ P) : ((l₂.M : ℕ) : 𝓞 E) ∈ P := by
  have h1 := natM_mem_Mb l₂
  rw [h] at h1
  exact hI (Ideal.mul_le_right (I := l.Mb) (J := I) h1)

end GlobalTheory.CoverXiDet

namespace GlobalTheory.CoverXiDet



theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (t : Tp) (u : GA D (Wc D i)), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ t).l₂.M : ℕ) • w) → M.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC _ i Tp tup M hM t u _ hw
  have hL := hC.lev
  have hN : ∀ PP ∈ R.Q (tup t), (((M.dδ t).l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hPP =>
    natM_mem_of_half _ _ _ _ ((hM.cov t).1).2.2.2.1 ((hM.tuple t).half.2.1 PP hPP)
  obtain ⟨xi', hxi1, hxi2, -, -⟩ := GlobalTheory.TupleCover.exists_xi D (Wc D i) (R.xi (tup t)) (R.xiH (tup t)) (hL.xi (tup t))
    (hL.xi_fin (tup t)).choose (hL.xi_fin (tup t)).choose_spec.1 (hL.xi_fin (tup t)).choose_spec.2 (hL.xi_triv (tup t))
    (hL.xi_tame (tup t))
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D (Wc D i) u
  have e1 := (hM.tuple t).xi u x hx
  have e2 := hxi1 u x hx
  have e3 : xi' (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1 := by
    refine hxi2 _ (M.dδ t).l₂.odd (GlobalTheory.TupleCover.unrAt_of_not_mem R hL (tup t) _ hN) u ?_
    obtain ⟨w, hw1, hw2⟩ := hw
    exact ⟨w, (GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers D).symm ▸ hw1, hw2⟩
  apply Units.ext
  rw [e1, ← e2, e3]

end GlobalTheory.CoverXiDet
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.schur_finiteHeisenberg_fockVacuumThetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ Φ : (WO S T → ℂ) → (WO S T → ℂ) → ℂ, (∀ (a : ℂ) (f f' g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f') → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (a • f + f') g = star a * Φ f g + Φ f' g) → (∀ (a : ℂ) (f g g' : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g') → Φ f (a • g + g') = a * Φ f g + Φ f g') → (∃ C : ℝ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → ‖Φ f g‖ ^ 2 ≤ C * (nrm2 μ 𝓕 f * nrm2 μ 𝓕 g)) → (∀ w : WO S T, w.map (infPart D) = 0 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (heisO ψ S T w f) (heisO ψ S T w g) = Φ f g) → ∃ c : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ f g = c * thetaIP μ 𝓕 f g := by
  first | exact @GlobalTheory.VacSchurFin.vacSchur | exact GlobalTheory.VacSchurFin.vacSchur | (intros; apply GlobalTheory.VacSchurFin.vacSchur <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverComp

theorem forms_mul_comp : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ N : ℕ, 0 < N → C.d.l₂.M ∣ N → (WeberIn T.Q.H C.d.c₂.F N ∨ CurveOver T.Q.H C.d.c₂.F N) → ∀ w : GA D (T.V j σ) → C.d.c₂.F, (∀ h h' : GA D (T.V j σ), finHom (T.V j σ) h = finHom (T.V j σ) h' → w h = w h') → (∀ γ ∈ GQ (T.V j σ), ∀ h, w (γ * h) = w h) → (∀ u : GA D (T.V j σ), gLat (T.V j σ) u = latHat (T.V j σ) → FinCong (T.V j σ) C.d.l₂.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ φ ∈ C.ratForms a n, (fun h => C.σ₂ (w h) * φ h) ∈ C.ratForms a n) ∧ ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), (∀ la ∈ S, ∀ h, la.valuation C.d.c₂.F (w h) ≤ 1) → ∀ φ ∈ C.intForms a n S, (fun h => C.σ₂ (w h) * φ h) ∈ C.intForms a n S := by
  intro D T hL j hj σ hσ C hU N hN hMN hW w hw1 hw2 hw3 a n
  obtain ⟨hlev, hA, hinc, hUnf, hdom, hr, g, e, F, ik, φ, th, hmod, hth, hdict⟩ := hU
  have hpq := (GlobalTheory.Member.exists_iotaOK D T.Q hL.pins j hj).2
  have hpos : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hio := (GlobalTheory.TupleCover.iotaOK_and_frame T hL j hj σ hσ (T.V j σ) rfl hr).1
  have hgood : GoodEmb C.d.c₂ C.σ₂ := by
    have h1 := hσ
    rw [← hinc] at h1
    exact h1
  have hMN' : C.d.l₂.M' ∣ N := by
    simpa [Level.M', hA] using hMN
  have key := GlobalTheory.T.coverSections_mul_stable_weberValues D T.Q hL.pins j hj C.d.l₂ C.d.Xo₂ C.d.c₂ C.σ₂ (T.V j σ) D.R.r hr C.U₂ C.dict₂
    (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) g e F ik φ th (T.x₀ j σ) hio hpos hA hgood hmod hdict hdom
    hUnf N hN hMN' hW w hw1 hw2 hw3 a n
  have hrd : ∀ f f' : Rul C.d.Xo₂ C.d.c₂,
      (∀ h, rdU C.U₂ f' (C.dict₂ h).1 (C.dict₂ h).2 = C.σ₂ (w h) * rdU C.U₂ f (C.dict₂ h).1 (C.dict₂ h).2) →
      C.rd a f' = fun h => C.σ₂ (w h) * C.rd a f h := by
    intro f f' hff
    funext h
    simp only [Cover.rd, Pi.smul_apply, smul_eq_mul]
    change _ * (_ * rdU C.U₂ f' (C.dict₂ h).1 (C.dict₂ h).2) = _ * (_ * (_ * rdU C.U₂ f (C.dict₂ h).1 (C.dict₂ h).2))
    rw [hff h]
    ring
  refine ⟨?_, ?_⟩
  · rintro _ ⟨f, ⟨hf, hc⟩, rfl⟩
    obtain ⟨f', hf', h1, h2, -⟩ := key f hf
    exact ⟨f', ⟨hf', h2 _ hc⟩, hrd f f' h1⟩
  · rintro S hS _ ⟨f, ⟨⟨hf, hc⟩, hv⟩, rfl⟩
    obtain ⟨f', hf', h1, h2, h3⟩ := key f hf
    exact ⟨f', ⟨⟨hf', h2 _ hc⟩, fun la hla v hvv => h3 la (hS la hla) (hv la hla) v hvv⟩, hrd f f' h1⟩

end GlobalTheory.CoverComp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.coefficient_vanishes_off_level_group_at_bad_prime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → thetaIP μ 𝓕 (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) = 0 := by
  first | exact @GlobalTheory.BadPlace.coef_bad_vanish | exact GlobalTheory.BadPlace.coef_bad_vanish | (intros; apply GlobalTheory.BadPlace.coef_bad_vanish <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.RealLowPf

theorem realLow : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, RealLow R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hP i t
  exact GlobalTheory.T.realLowestKType_of_extremalVectorCase D G Pl0 T A Ks R F hL hP i t (GlobalTheory.T.fockCoefficient_extremal_eq_discreteSeries D G Pl0 T A Ks R F hL hP i t)

end GlobalTheory.RawLift.RealLowPf

end
end
