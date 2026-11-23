module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle374
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle445
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle227
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle336
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle216
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle345
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle376
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle450
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPa
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle200
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle573
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle179
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle619
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalDoublingZetaFormSelfDualLatticeTransfer
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle452
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle550
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenBridge

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]

def toSum0 (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] : GL n k ≃* GL (n ⊕ Fin 0) k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k (Equiv.sumEmpty n (Fin 0)).symm).toMulEquiv

theorem toSum0_val (g : GL n k) :
    ((toSum0 k n g : GL (n ⊕ Fin 0) k) : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) =
      (g : Matrix n n k).reindex (Equiv.sumEmpty n (Fin 0)).symm (Equiv.sumEmpty n (Fin 0)).symm := rfl

end Local

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)}
  {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

theorem step_before_last_eq_s_succ (J : QJ a t) {j : ℕ} (hj : j + 1 = B.R.m) (i : Fin J.r) : j = (J.G i).s + 1 := by
  have h1 := (J.G i).hs
  have h2 : (I.rec7 l Z).R.m = B.R.m := rfl
  have h3 : (GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.m = B.R.m := rfl
  omega

def frJ (J : QJ a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) :
    Frame (J.G i).k ((I.rec7 l Z).sp.X j).rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1)) := by
  subst e
  exact (J.G i).FX _ le_rfl

def rdAt (J : QJ a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →*
      GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k :=
  (toSum0 (J.G i).k _).toMonoidHom.comp (GlobalTheory.LevIdx.locHom (J.G i).q _ (frJ J j i e))

def rd (J : QJ a t) (j : ℕ) (hj : j + 1 = B.R.m) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →*
      ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k) :=
  MonoidHom.pi fun i => rdAt J j i (step_before_last_eq_s_succ J hj i)

def plF (J : QJ a t) (p : GlobalTheory.FinPl.Pl (I.rec7 l Z)) : Prop := ∃ i, (J.G i).q.v = p

end GlobalTheory.PenBridge
end

namespace GlobalTheory.PenBridge

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]

theorem toSum0_mem_KO_iff (x : GL n k) : toSum0 k n x ∈ KO k (n ⊕ Fin 0) ↔ x ∈ KO k n := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Units.mapEquiv (Matrix.reindexAlgEquiv 𝒪[k] 𝒪[k] (Equiv.sumEmpty n (Fin 0))).toMulEquiv y, ?_⟩
    ext a b
    have := congrArg (fun g : GL (n ⊕ Fin 0) k => (g : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) (Sum.inl a) (Sum.inl b)) hy
    simpa [toSum0_val, Matrix.reindex_apply] using this
  · rintro ⟨y, rfl⟩
    refine ⟨Units.mapEquiv (Matrix.reindexAlgEquiv 𝒪[k] 𝒪[k] (Equiv.sumEmpty n (Fin 0)).symm).toMulEquiv y, ?_⟩
    ext a b
    simp [toSum0_val, Matrix.reindex_apply]

end Local

theorem relIndex_comap_conj {G : Type} [Group G] (H K : Subgroup G) {c : G} (hc : c ∈ K) :
    (H.comap (MulAut.conj c).toMonoidHom).relIndex K = H.relIndex K := by
  rw [Subgroup.relIndex_comap]
  congr 1
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact K.mul_mem (K.mul_mem hc hy) (K.inv_mem hc)
  · intro hx
    exact ⟨c⁻¹ * x * c, K.mul_mem (K.mul_mem (K.inv_mem hc) hx) hc, by group⟩

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)}
  {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

end GlobalTheory.PenBridge
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Classical

namespace GlobalTheory.ChainOnto.CoefSuppPf

theorem coefSupp : ∀ D : D7, CoefSupp D := by
  intro D _hgap c hc k _hk s s' hs hs' p hp m X hX φ g hg hnot
  obtain ⟨ξ, f₀, hvec⟩ := hp.vec
  have hthf : IsThetaFunO c.ψ s.V s'.V p.f := GlobalTheory.VecTheta.isThetaFunO_stepVec hvec
  obtain ⟨_hvac, e, he, hth⟩ := hvec
  obtain ⟨hr, ξL, hL⟩ := hs.lev
  have hQ : s.L.Q = ∅ := by rw [hL]; rfl
  have hPg : s.L.Pg = c.Pg := by rw [hL]; rfl
  have hrank : s.V.rank ≤ s'.V.rank := by
    rw [hs.rank, hs'.rank]
    show D.R.r + k * D.R.t ≤ D.R.r + (k + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ k)) _
  have hint : ∀ v, (∀ PP ∈ s.L.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v := by
    intro v hv
    apply hg v
    intro hmem
    simp only [Com.S, Finset.mem_image] at hmem
    obtain ⟨PP, hPP, hPPv⟩ := hmem
    exact hv PP (hPg ▸ hPP) hPPv
  have hsupp := fun x hx => by_contra fun h => hnot
    (GlobalTheory.T.finitePart_mem_level_of_thetaDatum_ne_zero D s.V s'.V s.Λ s.β s'.β s.L (c.chi (k + 1)) ξ e hs.selfDual hs.frame hrank hQ he g hint x hx h)
  have hsb := GlobalTheory.T.thetaChainStep_finiteDatum_isSchwartzBruhat_half D s.V s'.V s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ξ (s.L.Pg ∪ ∅) e
    hs.selfDual hs'.selfDual hs.frame hs'.frame he
  obtain ⟨n, a, y, hy, h1, h2⟩ := GlobalTheory.T.heisenberg_fix_and_kill_theta_off_support_move D c.ψ s.V s'.V hc.std s.Λ s'.Λ hs.selfDual hs'.selfDual
    (s.L.Pg ∪ ∅) e he f₀ _ p.f hsb hth g hsupp
  obtain ⟨H1, -⟩ := GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D c.ψ c.θ s.V s'.V hc.std hc.inf (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f hthf
    n a y (fun i => (hy i).1) φ
  obtain ⟨H2, H0⟩ := GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D c.ψ c.θ s.V s'.V hc.std hc.inf (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f hthf
    n (fun i => conj (a i)) (fun i => actO s.V s'.V g⁻¹ 1 (-(y i))) (fun i => (hy i).2) φ
  have R1 : ∑ i, a i • heisO c.ψ s.V s'.V (y i) (p.pt φ) = p.pt φ := by
    show ∑ i, a i • heisO c.ψ s.V s'.V (y i) (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f φ) = _
    rw [H1, h1]
    rfl
  have R2 : ∑ i, conj (a i) • heisO c.ψ s.V s'.V (actO s.V s'.V g⁻¹ 1 (-(y i))) (p.pt φ) = 0 := by
    show ∑ i, conj (a i) • heisO c.ψ s.V s'.V (actO s.V s'.V g⁻¹ 1 (-(y i)))
      (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f φ) = _
    rw [H2, h2, H0]
  exact GlobalTheory.T.weilMatrixCoefficient_eq_zero_of_heisenberg_relations D c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω hp.weil m X hX (p.pt φ) (hp.theta φ) g n a y R1 R2

end GlobalTheory.ChainOnto.CoefSuppPf
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ModelExtend

theorem isFullLattice_span {D : D7} {L : HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) :
    Submodule.IsFullLattice D.host.E (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) := by
  have hζ : ζ ≠ 0 := by
    rintro rfl
    exact h.2 (by simp)
  letI : Submodule.IsLattice D.host.E
      (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) :=
    Submodule.IsLattice.of_fg D.host.E (Submodule.fg_span_singleton ζ)
  refine ⟨?_⟩
  rw [Submodule.span_span_of_tower]
  exact (finrank_eq_one_iff_of_ne_zero ζ hζ).1 (by rw [Module.finrank_fin_fun, h.1])


open GlobalTheory.LocMod in
theorem exists_placeModel_ext : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S L'' : HSp D) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L'' ζ₀ → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (n : Type) [Fintype n] [DecidableEq n] (FS : GlobalTheory.LocMod.Frame k S.rank n) (FL'' : GlobalTheory.LocMod.Frame k L''.rank Unit) (TL : SB (Matrix Unit n k) →ₗ[ℂ] (WO S L'' → ℂ)), (GlobalTheory.LocMod.Place.ofSplitPt p).IsModel ψ FS FL'' TL → ∃ (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ ∧ IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ ∧ ∀ Φ, T₃ (GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FS FL'' Φ) = TL Φ := by
  intro D k _ _ _ _ p ψ hψ hU S L'' ζ₀ hζ LS hLS n _ _ FS FL'' TL hTL
  classical
  set P := GlobalTheory.LocMod.Place.ofSplitPt p with hP
  set Λ := latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v) with hΛ
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S LS hLS
  letI := isFullLattice_span hζ
  obtain ⟨hAo, hAc⟩ := GlobalTheory.T.splitPlace_homLattice_completion_openCompact D k p S L'' LS
    (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀}) inferInstance inferInstance Unit n FS FL''
  have hinj : Function.Injective (Witness.ext P FS FL'') := by
    intro Φ Ψ h
    apply Subtype.ext; funext x
    have := congrFun h (P.up FS FL'' x)
    rwa [Witness.ext_apply, Witness.ext_apply, if_pos (Witness.up_half P FS FL'' x),
      if_pos (Witness.up_half P FS FL'' x), Witness.down_up] at this
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective (Witness.ext P FS FL'') (LinearMap.ker_eq_bot.2 hinj)
  set T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ) := TL ∘ₗ G with hT₃d
  have hT₃ : ∀ Φ, T₃ (Witness.ext P FS FL'' Φ) = TL Φ := fun Φ => by
    change TL (G (Witness.ext P FS FL'' Φ)) = TL Φ
    rw [← LinearMap.comp_apply G, hG, LinearMap.id_apply]
  have hsb : ∀ Φ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Unit n k), Witness.ext P FS FL'' Φ' = Φ :=
    GlobalTheory.T.exists_schwartzBruhat_extByZero_of_splitPlaceHalf D k P S L'' Unit n FS FL'' Λ hAo hAc
  generalize hA : (Λ.comap (Witness.upH P FS FL'') : AddSubgroup (Matrix Unit n k)) = A at hAo hAc
  have hcl : IsClopen (A : Set (Matrix Unit n k)) := ⟨A.isClosed_of_isOpen hAo, hAo⟩
  let Φ₀ : SB (Matrix Unit n k) := ⟨(A : Set (Matrix Unit n k)).indicator 1,
    (LocallyConstant.charFn ℂ hcl).isLocallyConstant,
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _⟩
  have e1 : Witness.ext P FS FL'' Φ₀ = halfInd p.e Λ := by
    funext t
    rw [Witness.ext_apply, halfInd]
    change (if IsHalf p.e t then _ else _) = _
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht]
      change (A : Set (Matrix Unit n k)).indicator 1 _ = _
      rw [Set.indicator_apply, ← hA]
      refine if_congr ?_ rfl rfl
      change P.up FS FL'' (P.down FS FL'' t) ∈ Λ ↔ _
      rw [Witness.up_down P FS FL'' ht, and_iff_left ht]
    · rw [if_neg ht, if_neg fun h => ht h.2]
  refine ⟨TL Φ₀, T₃, hTL.theta Φ₀, ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩, hT₃⟩
  · obtain ⟨Φ', rfl⟩ := hsb Φ hΦ
    let Φ'' : SB (Matrix Unit n k) := ⟨fun s => Φ'.1 (s + P.down FS FL'' x),
      Φ'.2.1.comp_continuous (continuous_add_const _), Φ'.2.2.comp_homeomorph (Homeomorph.addRight _)⟩
    have e2 : (fun t => Witness.ext P FS FL'' Φ' (t + x)) = Witness.ext P FS FL'' Φ'' := by
      funext t
      rw [Witness.ext_apply, Witness.ext_apply, Witness.down_add]
      exact if_congr (Witness.half_add hx) rfl rfl
    rw [e2, hT₃, hT₃, hTL.trans (P.down FS FL'' x) Φ' Φ'' (fun t => rfl), Witness.up_down P FS FL'' hx]
  · obtain ⟨Φ', rfl⟩ := hsb Φ hΦ
    let Φ'' : SB (Matrix Unit n k) := ⟨fun s => ψ (symplO S L'' (P.up FS FL'' s) y) * Φ'.1 s,
      GlobalTheory.T.schwartzBruhat_mul_conjugateHalf_character_splitPlace D k P ψ hψ S L'' Unit n FS FL'' y hy Φ'.1 Φ'.2⟩
    have e2 : (fun t => ψ (symplO S L'' t y) * Witness.ext P FS FL'' Φ' t) = Witness.ext P FS FL'' Φ'' := by
      funext t
      rw [Witness.ext_apply, Witness.ext_apply]
      split_ifs with ht
      · change _ = ψ (symplO S L'' (P.up FS FL'' (P.down FS FL'' t)) y) * _
        rw [Witness.up_down P FS FL'' ht]
      · rw [mul_zero]
    rw [e2, hT₃, hT₃, hTL.modul y hy Φ' Φ'' (fun t => rfl)]
  · rw [one_smul, ← e1, hT₃]

end GlobalTheory.ModelExtend
end
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

namespace GlobalTheory.Core.Rk.WeylValue

variable {D : D7}

theorem integral_periodise {m n : ℕ} {ν : Measure (Mx D m n)} {𝓨 : Set (Mx D m n)}
    (hν : IsCovolOne (ratMx D m n) ν 𝓨) (φ F : Mx D m n → ℂ) (hφ : Integrable φ ν)
    (hF : ∀ x, HasSum (fun ξ : Matrix (Fin m) (Fin n) D.host.E => φ (x + rat ξ)) (F x)) :
    ∫ x in 𝓨, F x ∂ν = ∫ x, φ x ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := hν.1
  let e : Matrix (Fin m) (Fin n) D.host.E ≃ ratMx D m n :=
    Equiv.ofBijective (fun ξ => ⟨rat ξ, rat_mem ξ⟩)
      ⟨fun a b h => rat_injective (congrArg Subtype.val h), fun g => by
        obtain ⟨ξ, hξ⟩ := mem_ratMx.1 g.2
        exact ⟨ξ, Subtype.ext hξ⟩⟩
  have h1 : ∀ x, F x = ∑' g : ratMx D m n, φ (g +ᵥ x) := fun x => by
    rw [← (hF x).tsum_eq, ← e.tsum_eq]
    refine tsum_congr fun ξ => ?_
    show φ (x + rat ξ) = φ (rat ξ + x)
    rw [add_comm]
  simp only [h1]
  rw [hν.2.1.integral_eq_tsum'' φ hφ]
  refine integral_tsum (fun g => ?_) ?_
  · exact ((hφ.comp_add_left (g : Mx D m n)).aestronglyMeasurable).restrict
  · rw [← hν.2.1.lintegral_eq_tsum'' fun x => ‖φ x‖ₑ]
    exact hφ.2.ne

theorem pY_weyl (A : HSp D) {w : GA D (dblSp A)} (hw : IsWeyl A w) :
    ((dblDec A).pY ⬝ mt (dblSp A) w : Mx D A.rank (dblSp A).rank) = lowC A w ⬝ (dblDec A).pX := by
  have h0 : ((dblDec A).j0 ⬝ (dblDec A).p0 : Mx D (dblSp A).rank (dblSp A).rank) = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => Fin.elim0 k
  have h1 := (dblDec A).sum_eq_one
  rw [h0, add_zero] at h1
  have h2 := hw.2
  rw [← Matrix.mul_assoc] at h2
  rw [← Matrix.mul_one ((dblDec A).pY ⬝ mt (dblSp A) w), ← h1, Matrix.mul_add, ← Matrix.mul_assoc _ (dblDec A).jY, h2,
    Matrix.zero_mul, add_zero, lowC]
  simp only [Matrix.mul_assoc]

theorem swSec_weyl : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ w, IsWeyl A w → swSec A B omh ν 𝓨 f w = ∫ x, sch ψ A B ν 𝓨 f x ∂ν := by
  intro D ψ A B χB omh hω ν 𝓨 hν f hf w hw
  have hp := pY_weyl A hw
  have hm : lowC A w ∈ ratMx D A.rank A.rank :=
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff _ _).1 hw.1) (rat_mem _))
  let n : Mx D A.rank A.rank := (dblDec A).pX ⬝ (mt (dblSp A) w⁻¹ ⬝ (dblDec A).jY)
  have hn : n ∈ ratMx D A.rank A.rank :=
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff _ _).1 (inv_mem hw.1)) (rat_mem _))
  have hmn : lowC A w * n = 1 := by
    show lowC A w ⬝ ((dblDec A).pX ⬝ (mt (dblSp A) w⁻¹ ⬝ (dblDec A).jY)) = 1
    rw [← Matrix.mul_assoc, ← hp, Matrix.mul_assoc, ← Matrix.mul_assoc (mt (dblSp A) w), mt_mul_inv, Matrix.one_mul,
      HypDec.pY_jY]
  have h1 : ∀ z : WO A B, omh (w, 1) f (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B z) = f ((dblDec A).extX B (z ⬝ lowC A w)) := fun z => by
    rw [GlobalTheory.RatSubst.om_rat_left_apply D ψ _ _ _ _ omh hω f hf w hw.1, actO_eq, inv_inv, mt_one, Matrix.one_mul,
      ← extY_dblDec, HypDec.extY_apply, HypDec.extX_apply, Matrix.mul_assoc, hp, Matrix.mul_assoc]
  have hper : ∀ γ ∈ ratMx D B.rank A.rank, ∀ a, f ((dblDec A).extX B (γ + a)) = f ((dblDec A).extX B a) := by
    intro γ hγ a
    obtain ⟨δ, hδ⟩ : (dblDec A).extX B γ ∈ ratMx D _ _ := ratMx_mul hγ (rat_mem _)
    have h := hf.quasi δ ((dblDec A).extX B a)
    rw [show ratW B (dblSp A) δ = (dblDec A).extX B γ from hδ, HypDec.symplOH_extX_extX, neg_zero,
      AddChar.map_zero_eq_one, one_mul] at h
    rw [map_add (f := _), h]
  unfold swSec GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero
  simp only [h1]
  have hchange : ∫ a in 𝓨, f ((dblDec A).extX B (a * lowC A w)) ∂ν =
      ∫ a in 𝓨, f ((dblDec A).extX B a) ∂ν := by
    obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D B.rank A.rank
    let e : Mx D B.rank A.rank ≃+ Mx D B.rank A.rank :=
      { toFun := fun a => a * lowC A w
        invFun := fun a => a * n
        left_inv := fun a => by simp only [Matrix.mul_assoc, hmn, Matrix.mul_one]
        right_inv := fun a => by simp only [Matrix.mul_assoc, mul_eq_one_comm.1 hmn, Matrix.mul_one]
        map_add' := fun a b => Matrix.add_mul _ _ _ }
    have he : Continuous e := continuous_id.matrix_mul continuous_const
    have he' : Continuous e.symm := continuous_id.matrix_mul continuous_const
    have hr : ∀ x, e x ∈ ratMx D B.rank A.rank ↔ x ∈ ratMx D B.rank A.rank := fun x =>
      ⟨fun h => by
        have h2 := ratMx_mul h hn
        have h3 : e x * n = x := e.symm_apply_apply x
        rwa [h3] at h2,
       fun h => ratMx_mul h hm⟩
    obtain ⟨h1, hemb⟩ := GlobalTheory.Unf.ParCont.isCovolOne_map hν e he he' hr
    rw [← covolOne_integral_eq hν h1 (fun a => f ((dblDec A).extX B a)) hper,
      hemb.setIntegral_map, Set.preimage_image_eq _ e.injective]
    rfl
  refine hchange.trans ?_
  exact integral_periodise hν _ _ (GlobalTheory.T.doubledPairSchrodingerFunction_continuous_integrable D ψ hω.std A B ν 𝓨 hν f hf).2
    fun x => (GlobalTheory.T.doubledTheta_eq_sum_schrodingerFunction_periodisation D ψ hω.std A B ν 𝓨 hν f hf x).2

end GlobalTheory.Core.Rk.WeylValue
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP.VacFix

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ → ∀ v ∉ Sf, ∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram LA v, omh (emb D.sp.cm.sig (dblSp A).gram v k, 1) (delta A B Φ₁ Φ₂) = delta A B Φ₁ Φ₂ := by
  intro D ψ A B χB omh hW LA LB Sf Φ₁ Φ₂ h1 h2 hU v hv k hk
  have hstd := hW.std
  obtain ⟨hsd, hvac⟩ := GlobalTheory.T.doubling_sphericalVacua_to_doubled_lattice_vacuum D ψ A B LA LB hstd hU.sdA
  have hth := GlobalTheory.T.isThetaFunction_doublingSeesaw_of_standard_char D ψ A B hstd Φ₁ Φ₂ h1 h2
  have hlv := hvac Sf Φ₁ Φ₂ hU.sph₁ hU.sph₂ v hv
  have u1 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.UnramAt (1 : (AE D)ˣ →* Circle) v := fun _ _ _ _ => rfl
  have u2 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.UnramAt χB v := by
    obtain ⟨χ, hc⟩ := GlobalTheory.T.exists_heckeCharacter_of_unitary_tensorIdeles D χB hW.hecT
    refine GlobalTheory.UnramOver.unramAt_of_unrAt D χB χ hc v _ ?_ ?_
    · refine ⟨singleV _ v 1, rfl, ?_, ?_⟩
      · classical
        exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) v 1
      · intro v' hv'
        classical
        exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) 1 hv'
    · intro P hP
      exact (GlobalTheory.LFun.unrAt_iff_of_chrEq hc P).1 (hU.unr P (by
        simp only [GlobalTheory.LFun.above, Set.mem_setOf_eq, hP]
        exact_mod_cast hv))
  have key : ∀ C, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.VacuumFixedOn D C → C v →
      omh (emb D.sp.cm.sig (dblSp A).gram v k, 1) (delta A B Φ₁ Φ₂) = delta A B Φ₁ Φ₂ := by
    intro C hC hCv
    have := hC ψ (dblSp A) B 1 χB omh (sumLat finSumFinEquiv LA LA) LB hW hsd hU.sdB v hCv u1 u2 _ hth hlv k hk 1
      (one_mem _)
    rwa [map_one] at this
  by_cases hs : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsSplitPlace D v
  · exact key _ (GlobalTheory.PlaceTensor.splitVacuumFixed D) hs
  · exact key _ (GlobalTheory.PlaceTensor.inertVacuumFixed D) hs

end GlobalTheory.Core.Rk.IP.VacFix
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.global_doubling_zeta_form_selfDual_lattice_transfer : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' → GlobalFormAt A L → GlobalFormAt A L' := by
  first | exact @GlobalTheory.Core.Rk.GlobMove.globalFormAt_move | exact GlobalTheory.Core.Rk.GlobMove.globalFormAt_move | (intros; apply GlobalTheory.Core.Rk.GlobMove.globalFormAt_move <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.splitPlace_conjugate_stabilizer_keeps_movedFrameLattice : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}, Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y), (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) → ∀ (t : GA D S) (β : GL (Fin S.rank) (Lev.EAf D)) (e : Y ≃ Fin S.rank), GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) S t β (F.β.submatrix id e.symm) → ∀ g : GA D S, Lev.finE S (t⁻¹ * g * t) ∈ Formalism.L2.DIV.St β → GlobalTheory.FinPl.Moves S g L L (· = q.v) := by
  first | exact @GlobalTheory.LocMod.StMoves.moves_of_mem_St | exact GlobalTheory.LocMod.StMoves.moves_of_mem_St | (intros; apply GlobalTheory.LocMod.StMoves.moves_of_mem_St <;> assumption)
end
