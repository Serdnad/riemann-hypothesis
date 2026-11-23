module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulNonsingInvCancelRightGram
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle428
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle263
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle271
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle259
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle260
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlancherelSchrodingerIntertwiner
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle255
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle578
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle561
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle270
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle264
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle863
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle227
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle579
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.AlgStable

theorem isStable_span {D : D7} (θ : InfFam D) (X : HSp D) {Z : Type} (ρ : GA D X → Module.End ℂ (Z → ℂ))
    (s : Set (Z → ℂ)) (h1 : ∀ g ∈ GfC X, ∀ Φ ∈ s, ρ g Φ ∈ Submodule.span ℂ s)
    (h2 : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ s, ∃ Φ' ∈ Submodule.span ℂ s, GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsDer θ X ρ τ Y Φ Φ') :
    GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsStable θ X ρ (Submodule.span ℂ s) := by
  refine ⟨fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ => ?_⟩
  · have hle : Submodule.span ℂ s ≤ (Submodule.span ℂ s).comap (ρ g) := Submodule.span_le.2 (h1 g hg)
    exact hle hΦ
  · induction hΦ using Submodule.span_induction with
    | mem x hx => exact h2 τ Y hY x hx
    | zero =>
      refine ⟨0, zero_mem _, fun z => ?_⟩
      simp only [map_zero]
      exact hasDerivAt_const _ _
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', dx⟩ := hx
      obtain ⟨y', hy', dy⟩ := hy
      refine ⟨x' + y', add_mem hx' hy', fun z => ?_⟩
      simp only [map_add (f := _)]
      exact (dx z).add (dy z)
    | smul a x _ hx =>
      obtain ⟨x', hx', dx⟩ := hx
      refine ⟨a • x', Submodule.smul_mem _ a hx', fun z => ?_⟩
      simp only [map_smul]
      exact (dx z).const_mul a

theorem isVacF_om {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} (A : Fr S)
    (B : Fr T) {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {g : GA D S} (hg : g ∈ GfC S) {h : GA D T} (hh : h ∈ GfC T) {f : WO S T → ℂ}
    (hf : IsVacF ψ θ A B f) : IsVacF ψ θ A B (om (g, h) f) := by
  have e : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (om (g, h) f) =
      om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
    intro τ z
    rw [GlobalTheory.OrientedHeis.om_dRho hW hθ g h τ z hf.1, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hh,
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S (inv_mem hg), Matrix.one_mul, Matrix.mul_one]
  refine ⟨hW.om_pres _ f hf.1, fun τ z => ?_⟩
  have h0 := hf.2 τ z
  unfold annih at h0 ⊢
  rw [e, e, ← map_smul, ← map_add (f := _), h0, map_zero]

theorem algF_isStable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (Am : Fr M) (Bx : Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ ε M X χ χ' ω →
      IsStable θ M (fun g => ω (g, 1)) (algF ψ θ ε Am Bx) ∧ IsStable θ X (fun h => ω (1, h)) (algF ψ θ ε Am Bx) := by
  intro D ψ θ _ hθ ε M X A B χ χ' ω hW
  have hW' : IsWeilDatumO ψ (sgn ε M) X χ χ' (ω.toSgn ε) := hW
  have hmem : ∀ f P, IsFinF ψ θ ε A B f → fockF ψ θ ε A B f P ∈ algF ψ θ ε A B :=
    fun f P hf => Submodule.subset_span ⟨f, P, hf, rfl⟩
  have e0 : ∀ (g : GA D (sgn ε M)) (h : GA D X), (ω.toSgn ε) (g, h) = ω (ofSgn ε M g, h) := fun _ _ => rfl
  have hfin : ∀ g ∈ GfC M, ∀ h ∈ GfC X, ∀ f P, IsFinF ψ θ ε A B f →
      ω (g, h) (fockF ψ θ ε A B f P) ∈ algF ψ θ ε A B := by
    intro g hg h hh f P hf
    have hg' : (ofSgn ε M).symm g ∈ GfC (sgn ε M) := by
      rw [GlobalTheory.SgnIdent.mem_GfC_sgn, MulEquiv.apply_symm_apply]; exact hg
    have ht := GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ (sgn ε M) X χ χ' (ω.toSgn ε) hW' θ hθ _ hg' h hh
      (frSgn ε A).cart B.cart A.onb B.onb f P hf.1
    have hv := isVacF_om hθ (frSgn ε A) B hW' hg' hh hf
    rw [e0, MulEquiv.apply_symm_apply] at ht hv
    have : ω (g, h) (fockF ψ θ ε A B f P) = fockF ψ θ ε A B (ω (g, h) f) P := ht
    rw [this]
    exact hmem _ _ hv
  have hL := fun τ => GlobalTheory.LieFock.lieFockUpTo D (sgn ε M) X (frSgn ε A) B θ ψ χ χ' (ω.toSgn ε) τ hθ hW'
  refine ⟨isStable_span θ M _ _ ?_ ?_, isStable_span θ X _ _ ?_ ?_⟩
  · rintro g hg _ ⟨f, P, hf, rfl⟩
    exact hfin g hg 1 (one_mem _) f P hf
  · rintro τ Z hZ _ ⟨f, P, hf, rfl⟩
    obtain ⟨κS, κT, hκ⟩ := hL τ
    have hZ' : Z ∈ lieAt (sgn ε M) τ := by rw [GlobalTheory.SgnIdent.lieAt_sgn]; exact hZ
    have e : ∀ t : ℝ, (ω.toSgn ε) (oneP θ (sgn ε M) τ Z t, 1) = ω (oneP θ M τ Z t, 1) := by
      intro t
      rw [e0]
      unfold oneP
      rw [GlobalTheory.SgnIdent.atTau_sgn θ hθ]
    have h := (hκ f hf).1 Z hZ' P
    simp only [e] at h
    exact ⟨_, hmem f _ hf, h⟩
  · rintro h hh _ ⟨f, P, hf, rfl⟩
    exact hfin 1 (one_mem _) h hh f P hf
  · rintro τ Y hY _ ⟨f, P, hf, rfl⟩
    obtain ⟨κS, κT, hκ⟩ := hL τ
    have e1 : ∀ h : GA D X, (ω.toSgn ε) (1, h) = ω (1, h) := fun h => by rw [e0, map_one]
    have h := (hκ f hf).2 Y hY P
    simp only [e1] at h
    exact ⟨_, hmem f _ hf, h⟩

end GlobalTheory.AlgStable
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SuppLev

theorem supp_level : ∀ (D : D7) (S T : HSp D) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC T ΛT → IsFrame βT ΛT → T.rank ≤ S.rank → LT.Q = ∅ → IsIdemSum e Z → (∀ PP, PP ∈ Z ↔ PP ∈ LT.Pg ∨ PP ∈ Q) → ∀ g ∈ GfC T, ∀ x, levDatum S T βS βT LT Q m e x ≠ 0 → levDatum S T βS βT LT Q m e (actO S T 1 g x) ≠ 0 → ∃ k ∈ levG T βT LT, ∀ PP ∈ Z, projV T ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g = projV T ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) k := by
  classical
  intro D S T ΛT βS βT LT Q m Z e hsd hfr hrk hQ hZe hZ g hg x hx hx'
  have hu' := GlobalTheory.T.frameMatrixAdjoint_jointAction S T βS βT g x
  obtain ⟨hh, hI, hU, a, ha1, ha2, ha3⟩ := GlobalTheory.T.levelFiniteThetaDatum_ne_zero_frameAdjoint_spec S T βS βT LT Q m e x hx
  obtain ⟨-, hI', hU', b, hb1, hb2, hb3⟩ := GlobalTheory.T.levelFiniteThetaDatum_ne_zero_frameAdjoint_spec S T βS βT LT Q m e _ hx'
  simp only [hu'] at hI' hU' hb1
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hZe
  have hsupp := GlobalTheory.T.frameMatrixAdjoint_supported_of_conjHalf S T βS βT e x hee hh
  obtain ⟨h1, h2, hred⟩ := GlobalTheory.T.integral_idempotent_mul_of_unit_topBlock_reductions S.rank T.rank hrk Z e hZe _ _ hI hI' hsupp
    (fun PP hP => hU PP ((hZ PP).1 hP)) (fun PP hP => hU' PP ((hZ PP).1 hP))
  have hUA := GlobalTheory.LevSplit.finE_mem_UA T g
  obtain ⟨h3, h4⟩ := GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral T ΛT βT hsd hfr _ hUA _ rfl e h1 h2
  obtain ⟨hεε, hεc⟩ := GlobalTheory.T.idempotentSum_add_conj_idempotent_conj_fixed Z e hZe
  obtain ⟨k, hk, hmt⟩ := GlobalTheory.T.exists_idempotent_component_of_group_element T g (e + cA D e) hg hεε hεc
  refine ⟨k, ?_, fun PP hP => (GlobalTheory.T.localProjection_eq_of_idempotent_patch T _ g k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one Z e hZe PP hP) hmt).symm⟩
  have hfk := GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame T βT g k (e + cA D e) hmt
  obtain ⟨hSt, hR⟩ := GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction T.rank βT _ _ Z e hZe h1 h2 h3 h4 hfk
  refine ⟨hk, ?_⟩
  refine GlobalTheory.T.mem_level_of_type_place_reductions T βT LT _ hQ (GlobalTheory.LevSplit.finE_mem_UA T k) hSt a b ha2 hb2 ha3 hb3 fun PP => ?_
  apply Units.ext
  rw [Units.val_mul, hR PP.1 ((hZ PP.1).2 (Or.inl PP.2)), ha1, hb1]
  exact hred PP.1 ((hZ PP.1).2 (Or.inl PP.2))

end GlobalTheory.SuppLev
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HoweGlobal.FinPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_mem_UAt {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  have e : mat (1 : UA σ X.J) = 1 := rfl
  show u • (mat (1 : UA σ X.J) - 1) = 0
  rw [e, sub_self, smul_zero]

variable {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem exists_image (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin a × Fin (a + a') → Fv F v)) :
    ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ :=
  GlobalTheory.ThK.LocalOps.acts_exists (GlobalTheory.ThK.RealUniq.isPair_V hT) v (1, h) (one_mem_UAt _ _) hh φ hφ

def locOp (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    Module.End ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v)) where
  toFun φ := ⟨Classical.choose (exists_image hT v hh φ φ.2), (Classical.choose_spec (exists_image hT v hh φ φ.2)).1⟩
  map_add' φ ψ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hψ := (Classical.choose_spec (exists_image hT v hh ψ ψ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (φ + ψ : ↥(SB _)) (φ + ψ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 ψ.2 hφ hψ 1 1
    simp only [one_smul] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (φ + ψ).2 hs hl
  map_smul' c φ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (c • φ : ↥(SB _)) (c • φ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 φ.2 hφ hφ c 0
    simp only [zero_smul, add_zero] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (c • φ).2 hs hl

theorem locOp_acts (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : ↥(SB (Fin a × Fin (a + a') → Fv F v))) :
    Acts (evFin F v) (om (1, h)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ)
      ((locOp hT v hh φ : ↥(SB (Fin a × Fin (a + a') → Fv F v))) : (Fin a × Fin (a + a') → Fv F v) → ℂ) :=
  (Classical.choose_spec (exists_image hT v hh φ φ.2)).2

theorem locOp_mem (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    locOp hT v hh ∈ GlobalTheory.HoweGlobal.opFin G om v :=
  ⟨h, hh, locOp_acts hT v hh⟩

end GlobalTheory.HoweGlobal.FinPlace

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweGlobalPair.FinPlaceSmall

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_mem_UAt {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  have e : mat (1 : UA σ X.J) = 1 := rfl
  show u • (mat (1 : UA σ X.J) - 1) = 0
  rw [e, sub_self, smul_zero]

variable {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem exists_image (hT : IsTriple Bs G Xc om om') (v : Pl (F := F)) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin a' × Fin (a + a') → Fv F v)) :
    ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ :=
  GlobalTheory.ThK.LocalOps.acts_exists (GlobalTheory.ThK.RealUniq.isPair_V' hT) v (1, h) (one_mem_UAt _ _) hh φ hφ

def locOp (hT : IsTriple Bs G Xc om om') (v : Pl (F := F)) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    Module.End ℂ ↥(SB (Fin a' × Fin (a + a') → Fv F v)) where
  toFun φ := ⟨Classical.choose (exists_image hT v hh φ φ.2), (Classical.choose_spec (exists_image hT v hh φ φ.2)).1⟩
  map_add' φ ψ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hψ := (Classical.choose_spec (exists_image hT v hh ψ ψ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (φ + ψ : ↥(SB _)) (φ + ψ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om' (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 ψ.2 hφ hψ 1 1
    simp only [one_smul] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (φ + ψ).2 hs hl
  map_smul' c φ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (c • φ : ↥(SB _)) (c • φ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om' (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 φ.2 hφ hφ c 0
    simp only [zero_smul, add_zero] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (c • φ).2 hs hl

theorem locOp_acts (hT : IsTriple Bs G Xc om om') (v : Pl (F := F)) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : ↥(SB (Fin a' × Fin (a + a') → Fv F v))) :
    Acts (evFin F v) (om' (1, h)) (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ)
      ((locOp hT v hh φ : ↥(SB (Fin a' × Fin (a + a') → Fv F v))) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
  (Classical.choose_spec (exists_image hT v hh φ φ.2)).2

theorem locOp_mem (hT : IsTriple Bs G Xc om om') (v : Pl (F := F)) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    locOp hT v hh ∈ GlobalTheory.HoweGlobalPair.opFin om' v :=
  ⟨h, hh, locOp_acts hT v hh⟩

end GlobalTheory.HoweGlobalPair.FinPlaceSmall

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar




noncomputable section

namespace GlobalTheory.LiftMul

variable {D : D7}

theorem exists_den_AA (D : D7) :
    ∃ d : ℕ, 0 < d ∧ ∀ a ∈ D.host.AA, ∃ o : 𝓞 D.host.E, (d : D.host.E) * a = (o : D.host.E) := by
  obtain ⟨b, hb, hbI⟩ := D.host.AA.isFractional
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨Ideal.absNorm (Ideal.span {b}), Nat.pos_of_ne_zero ?_, fun a ha => ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
    obtain ⟨o, ho⟩ := hbI a ha
    refine ⟨c * o, ?_⟩
    show _ = algebraMap (𝓞 D.host.E) D.host.E (c * o)
    rw [map_mul, ho, Algebra.smul_def, ← mul_assoc, ← map_mul, hc, map_natCast]

def fA (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    WO S T →+ Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
  AddMonoidHom.mk' (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)

theorem gen_int (S T : HSp D) (ΛT : Lt D.host.E T.rank) (hsd : IsSelfDualC T ΛT)
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (hβS : Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank)) (hβT : Formalism.L2.DIV.IsFrame βT ΛT)
    {d : ℕ} {α : Af D.host.F} (hα : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {a : D.host.E} (ha : ∃ o : 𝓞 D.host.E, (d : D.host.E) * a = (o : D.host.E))
    {s : Fin S.rank → D.host.E} (hs : s ∈ stdL D.host.E S.rank) {t : Fin T.rank → D.host.E} (ht : t ∈ ΛT) :
    IsIntM (frMapAdj S T βS βT (incA D (d : D.host.E) • GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t))) := by
  obtain ⟨o, ho⟩ := ha
  have hc : toEAf D (incA D (d : D.host.E) * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [← map_mul, ho]
    exact GlobalTheory.IdemIntegral.eToEAf_int D o
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.ConjHalfInt.map_gen, GlobalTheory.ConjHalfInt.adj_shape, Matrix.mul_smul, Matrix.smul_mul]
  refine GlobalTheory.ConjHalfInt.isIntM_smul (GlobalTheory.PlaceVec.cF_mem_int (mul_mem hc hα)) ?_
  have hA : (S.gram⁻¹).map (eToEAf D) *
      ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      Matrix.of fun m (_ : Fin 1) => eToEAf D (s m) := by
    ext m z

    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
    GlobalTheory.ConjHalfInt.cF_eToEAf, ← map_mul, ← map_sum]
    rw [GlobalTheory.ConjHalfInt.gram_inv_star]
  have hB : ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D) =
      Matrix.of fun (_ : Fin 1) m => eToEAf D (∑ l, star (t l) * T.gram l m) := by
    ext z m

    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
    GlobalTheory.ConjHalfInt.cF_eToEAf, ← map_mul, ← map_sum]
  have e : (βS⁻¹).val * (S.gram⁻¹).map (eToEAf D) *
      (((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ *
        ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ) *
      (T.gram.map (eToEAf D) * βT.val) =
      ((βS⁻¹).val * ((S.gram⁻¹).map (eToEAf D) *
        ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ)) *
      ((((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D)) *
        βT.val) := by
    simp only [Matrix.mul_assoc]
  rw [e, hA, hB]
  exact GlobalTheory.ConjHalfInt.isIntM_mul (GlobalTheory.ConjHalfInt.frame_col_int hβS hs)
    (GlobalTheory.ConjHalfInt.pair_row_int hsd hβT ht)

theorem lat_int (S T : HSp D) (ΛT : Lt D.host.E T.rank) (hsd : IsSelfDualC T ΛT)
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (hβS : Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank)) (hβT : Formalism.L2.DIV.IsFrame βT ΛT)
    {d : ℕ} (hd : ∀ a ∈ D.host.AA, ∃ o : 𝓞 D.host.E, (d : D.host.E) * a = (o : D.host.E))
    {x : WO S T}
    (hx : x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) :
    IsIntM (frMapAdj S T βS βT (incA D (d : D.host.E) • x)) := by
  refine GlobalTheory.LatVac.latO_induction (p := fun u => IsIntM (frMapAdj S T βS βT (incA D (d : D.host.E) • u)))
    ?_ ?_ ?_ ?_ hx
  · intro α hα M hM
    have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      exact gen_int S T ΛT hsd βS βT hβS hβT hα' (hd a ha) hs ht
    | zero =>
      rw [GlobalTheory.LatVac.finTens_zero, smul_zero, GlobalTheory.ConjHalfInt.frMapAdj_zero]
      exact fun _ _ => zero_mem _
    | add M N _ _ hM hN =>
      rw [GlobalTheory.LatVac.finTens_add, smul_add, GlobalTheory.PlaceVec.frMapAdj_add]
      exact fun i j => add_mem (hM i j) (hN i j)
    | neg M _ hM =>
      rw [GlobalTheory.LatVac.finTens_neg, smul_neg, GlobalTheory.ConjHalfInt.frMapAdj_neg]
      exact fun i j => neg_mem (hM i j)
  · rw [smul_zero, GlobalTheory.ConjHalfInt.frMapAdj_zero]
    exact fun _ _ => zero_mem _
  · intro u v hu hv
    rw [smul_add, GlobalTheory.PlaceVec.frMapAdj_add]
    exact fun i j => add_mem (hu i j) (hv i j)
  · intro u hu
    rw [smul_neg, GlobalTheory.ConjHalfInt.frMapAdj_neg]
    exact fun i j => neg_mem (hu i j)

theorem red_nsmul {b a : ℕ} (PP : Formalism.L2.DIV.Pl D.host.E) {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N)
    {m : ℕ} (hm : (m : 𝓞 D.host.E) ∈ PP.asIdeal) : IsIntM (m • N) ∧ redM PP (m • N) = 0 := by
  have hI : IsIntM (m • N) := fun i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul]; exact mul_mem (natCast_mem _ m) (hN i j)
  refine ⟨hI, ?_⟩
  ext i j
  simp only [redM, dif_pos (hI i j), Matrix.zero_apply]
  have e : (⟨(m • N) i j, hI i j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      (m : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨N i j, hN i j⟩ := by
    apply Subtype.ext; simp [Matrix.smul_apply, nsmul_eq_mul]
  rw [e, map_mul, map_natCast]
  have h0 : (m : Formalism.L2.DIV.kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal) m]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
  rw [h0, zero_mul]

theorem nsmul_mem_liftL : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hne h2 e hidem
  obtain ⟨d, hd0, hd⟩ := exists_den_AA D
  set m2 : ℕ := ∏ PP ∈ Pg ∪ Q, Ideal.absNorm PP.asIdeal with hm2
  have hm2pos : 0 < m2 := Finset.prod_pos fun PP _ =>
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact PP.ne_bot)
  have hm2mem : ∀ PP ∈ Pg ∪ Q, (m2 : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hPP => by
    rw [hm2, Nat.cast_prod]
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hPP) (Ideal.absNorm_mem _)
  refine ⟨d * m2, Nat.mul_pos hd0 hm2pos, fun x hx hh => ?_⟩
  have hint := lat_int S T ΛT hsd βS βT hβS hβT hd hx
  have heq : frMapAdj S T βS βT ((d * m2) • x) = m2 • frMapAdj S T βS βT (incA D (d : D.host.E) • x) := by
    have hdx : d • x = incA D (d : D.host.E) • x := by rw [map_natCast, Nat.cast_smul_eq_nsmul]
    rw [mul_comm d m2, ← smul_smul, hdx]
    exact (fA S T βS βT).map_nsmul _ _
  show IsHalf (cA D e) ((d * m2) • x) ∧ IsIntM (frMapAdj S T βS βT ((d * m2) • x)) ∧
    ∀ PP ∈ Pg ∪ Q, redM PP (frMapAdj S T βS βT ((d * m2) • x)) = 0
  refine ⟨fun i j => ?_, ?_, fun PP hPP => ?_⟩
  · rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hh i j]
  · obtain ⟨PP, hPP⟩ := hne
    rw [heq]; exact (red_nsmul PP hint (hm2mem PP (Finset.mem_union_left _ hPP))).1
  · rw [heq]; exact (red_nsmul PP hint (hm2mem PP hPP)).2

end GlobalTheory.LiftMul

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise


theorem _root_.GlobalTheory.T.exists_classSum_schwartzProducts_gridPath : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → ∀ (n : Pl D.host.E → ℕ) {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → (GlobalTheory.FlipRun.edges p).Nodup → ∀ {U : Type} (K : (∀ w, (locGrid G t w).Args) → U → ℂ), (∀ (x z : ∀ w, (locGrid G t w).Args) (y : U), (∀ w ∈ locPl G t, ∀ b, z w b ∈ GlobalTheory.SplitFlip.matLat _ (unifAt w ^ n w • GlobalTheory.SplitFlip.stdLat (Kw w) _)) → K (x + z) y = K x y) → (∀ (x : ∀ w, (locGrid G t w).Args) (y : U), K x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b ∈ GlobalTheory.FlipRun.edges p, x w b ∈ GlobalTheory.SplitFlip.matLat _ (GlobalTheory.SplitFlip.stdLat (Kw w) _)) → ∃ (ι : Type) (s : Finset ι) (φ d : ι → PureT G p) (r : ι → GlobalTheory.FlipRun.ArgT G p), (∀ κ ∈ s, GlobalTheory.FlipRun.VecAll ρ e p (φ κ) (d κ)) ∧ ∀ (x : GlobalTheory.FlipRun.ArgT G p) (y : U), GlobalTheory.FlipRun.HalfAll e p x → K (fun w => GlobalTheory.FlipRun.pathArgs B t w p x) y = ∑ κ ∈ s, GlobalTheory.FlipRun.famProd p (φ κ) x * K (fun w => GlobalTheory.FlipRun.pathArgs B t w p (r κ)) y := by
  first | exact @GlobalTheory.FlipRun.exists_classes_path | exact GlobalTheory.FlipRun.exists_classes_path | (intros; apply GlobalTheory.FlipRun.exists_classes_path <;> assumption)
end
