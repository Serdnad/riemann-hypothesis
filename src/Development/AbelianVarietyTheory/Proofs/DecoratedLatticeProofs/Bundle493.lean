module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle476
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle177
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle178
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle477
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle118
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle484
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle212
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumBoxTensorLineOverVacuum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSliceLineSumEqIntertwinerImage
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle229
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle277
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle479
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle273
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle402
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLaws
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle485
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle416

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

namespace GlobalTheory.TopVol.InKConj

variable {D : D7}

theorem idAt_le_of {P : Pl D → Prop} {v : Pl D} (hv : P v) : idAt D (· = v) ≤ idAt D P := by
  intro a ha
  rw [idAt, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun h => w.2 (h ▸ hv)⟩⟩

theorem moves_at {V : HSp D} {g : GA D V} {M : Lat V} {P : Pl D → Prop} (h : Moves V g M M P) {v : Pl D} (hv : P v) :
    Moves V g M M (· = v) := by
  intro y hy
  have hy' : ∀ i, y i ∈ idAt D P := fun i => idAt_le_of hv (hy i)
  rw [KOpen.mem_latV_iff V M _ y hy, KOpen.mem_latV_iff V M _ _ (KOpen.supp_mulVec V _ g hy),
    ← KOpen.mem_latV_iff V M P y hy', ← KOpen.mem_latV_iff V M P _ (KOpen.supp_mulVec V P g hy')]
  exact h y hy'

theorem conj_mem_levG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ M : Lat V) (Ld : LevDat D.host.E ℂ V.rank)
    (P : Pl D → Prop) (t κ : GA D V) (hβ : IsFrame β Λ) (hΛ : IsSelfDualC V Λ) (ht : t ∈ GfC V)
    (hm : ∀ v, P v → Moves V t Λ M (· = v)) (hQ : Ld.Q = ∅)
    (hPg : ∀ PP ∈ Ld.Pg, ¬ P ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) (hκ : InK V M P κ) :
    t⁻¹ * κ * t ∈ Lev.levG V β Ld := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hfg : Λ.FG := Submodule.IsLattice.fg (A := D.host.E) Λ
  obtain ⟨hκf, hκ1⟩ := (KOpen.mem_grpAt_iff V P κ).1 hκ.1
  have hy : t⁻¹ * κ * t ∈ GfC V := (GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem ht) hκf) ht
  have hproj : ∀ v, ¬ P v → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (t⁻¹ * κ * t) = 1 := fun v hv => by
    rw [map_mul, map_mul, hκ1 v hv, mul_one, map_inv, inv_mul_cancel]
  have hSt : Lev.finE V (t⁻¹ * κ * t) ∈ St β := by
    rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ]
    intro v
    by_cases hv : P v
    · rw [← GlobalTheory.StMoves.moves_iff_stabLoc V Λ hfg v]
      exact (GlobalTheory.StMoves.moves_conj_iff κ (hm v hv)).2 (moves_at hκ.2 hv)
    · rw [hproj v hv]; exact Subgroup.one_mem _
  have hred : ∀ PP ∈ Ld.Pg, redFn β PP (Lev.finE V (t⁻¹ * κ * t)) = 1 := fun PP hP =>
    GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP hSt (hproj _ (hPg PP hP))
  refine ⟨hy, mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hSt, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩⟩
  · rw [hred PP hP]; exact Subgroup.one_mem _
  · rw [hQ] at hP; exact absurd hP (Finset.notMem_empty _)
  · have e : rTup β Ld (Lev.finE V (t⁻¹ * κ * t)) = 1 := by
      funext PP
      show upperLeftBlock Ld.hr (redFn β PP.1 _) = 1
      rw [hred PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
    rw [e]; exact Subgroup.one_mem _

end GlobalTheory.TopVol.InKConj

namespace GlobalTheory.TopVol.InKConj

end GlobalTheory.TopVol.InKConj
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.ZeroCongr
open Formalism.UG

theorem adFun_of_same {D : D7} {n : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} {T f T' f' : ℕ}
    {bad bad' : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (S' : StepLevel D.host.F D.host.E (sigD D) J T' f' bad')
    (hU : ∀ x, x ∈ S.U ↔ x ∈ S'.U) (hchi : ∀ (x : S.U) (x' : S'.U), x.1 = x'.1 → S.chi x = S'.chi x')
    (Ψ) (hΨ : Ψ ∈ AdFun S' (embT D)) : Ψ ∈ AdFun S (embT D) := by
  intro γ hγ x x' κ h y y' hy
  rw [hchi κ ⟨κ.1, (hU _).1 κ.2⟩ rfl]
  exact hΨ γ hγ x x' ⟨κ.1, (hU _).1 κ.2⟩ h y y' hy



theorem rdS_congr (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (n : ℕ) (hn : V.rank = n)
    (J : Matrix (Fin n) (Fin n) D.host.E) (hJ : J = V.gram.reindex (finCongr hn) (finCongr hn)) {T f T' f' : ℕ}
    {bad bad' : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (S' : StepLevel D.host.F D.host.E (sigD D) J T' f' bad')
    {cl cl' : Type} (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (yc' : cl' → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hb : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (hb' : Function.Bijective (fun c => (Quotient.mk'' (yc' c) : Cls S')))
    (lam : D.what₂.Tau → DomWeight n) (φ) (φ') (hφ' : φ' ∈ FiC S' (embT D) lam yc')
    (hU : ∀ x, x ∈ S.U ↔ x ∈ S'.U) (hchi : ∀ (x : S.U) (x' : S'.U), x.1 = x'.1 → S.chi x = S'.chi x')
    (hrep : ∀ c, ∃ c', ∃ κ : S.U, (yc' c').1 = (yc c).1 * κ.1 ∧ S.chi κ = 1 ∧ φ c = φ' c')
    (y : Frames (gramC J (embT D))) (g : GA D V) :
    rdS θ V hn S yc φ y g = rdS θ V hn S' yc' φ' y g := by
  obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hφ'
  have hA' := (Submodule.mem_inf.1 hΨ).1
  have hA := adFun_of_same S S' hU hchi Ψ hA'
  have e : φ = fun c => Ψ (yc c) := by
    funext c z
    obtain ⟨c', κ, hy, hχ, hφc⟩ := hrep c
    rw [hφc]
    have h1 : IsTr (atInf (embT D) ((1 : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) z z := fun τ => by
      show z.1 τ = _ * z.1 τ
      simp [atInf]
    have e3 := hA 1 (Subgroup.one_mem _) (yc c) (yc' c') κ (by rw [map_one, one_mul]; try exact hy) z z h1
    show Ψ (yc' c') z = Ψ (yc c) z
    rw [e3, hχ, Units.val_one, one_mul]
  subst e
  obtain ⟨⟨x, hx⟩, hu, hv⟩ := GlobalTheory.AdForm.rdS_val D θ hθ V n hn J hJ T f bad S cl yc hb Ψ hA y g
  obtain ⟨-, -, hv'⟩ := GlobalTheory.AdForm.rdS_val D θ hθ V n hn J hJ T' f' bad' S' cl' yc' hb' Ψ hA' y g
  let z : Frames (gramC J (embT D)) :=
    ⟨fun τ => infM θ V hn g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hu τ).mul (y.2 τ)⟩
  exact (hv x z hx (fun τ => rfl)).trans (hv' x z hx (fun τ => rfl)).symm

end GlobalTheory.AdForm.ZeroCongr

namespace GlobalTheory.Fam



theorem rd_zero_std : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ θ, IsInfFam θ → ∀ ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mram, ∀ y, A.rd θ 0 (Nat.zero_le _) β ((I.rec7 l Z).e0Tw u a ψ₀) y = (GlobalTheory.Core.Mi.chart0 (C.forms u).to0).rd θ ψ₀ y := by
  intro B X I hI hP l Z C hC u a Ch A hA β hβ θ hθ ψ₀ hψ y
  unfold GlobalTheory.AdForm.TwDat.rd GlobalTheory.AdForm.Chart.rd GlobalTheory.Core.Mi.chart0
  dsimp only
  have hfr : ((C.forms u).to0.val0.eY y) = (⟨y.1, y.2⟩ : Frames (gramC (gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (embT (I.rec7 l Z)))) :=
    Subtype.ext ((hC u).eY 0 (Nat.zero_le _) (Or.inl rfl) y)
  rw [hfr]
  funext g
  refine GlobalTheory.AdForm.ZeroCongr.rdS_congr (I.rec7 l Z) θ hθ _ _ _ _ ?hJ _ _ _ _ (A.K 0 (Nat.zero_le _) β).y_bij ((C.forms u).to0.cls0.toChart.y_bij) (lamT u 0) _ _ ?hφ ?hU ?hchi ?hrep _ g
  case hJ => rfl
  case hφ => exact ((C.forms u).to0.val0.Fi ψ₀).1 (((I.rec7 l Z).fm u).Fi_zero ▸ hψ.1)
  case hU => exact GlobalTheory.T.stepZeroChartLevel_standardBasePoint_eq_member I hI hP l Z C hC u a Ch A hA β hβ
  case hchi => exact GlobalTheory.T.levelZeroChartCharacter_eq_memberChartCharacter_stdBase I hI hP l Z C hC u a Ch A hA β hβ
  case hrep =>
    intro c
    obtain ⟨κ, h1, h2⟩ := GlobalTheory.T.stepZero_representative_differs_by_level I hI hP l Z C hC u a Ch A hA β hβ c
    refine ⟨(I.eCls0 l u a).symm c.1, κ, h1, h2, ?_⟩
    funext z
    have hz : (C.forms u).to0.val0.eY.symm z = ⟨z.1, z.2⟩ := by
      apply (C.forms u).to0.val0.eY.injective
      rw [Equiv.apply_symm_apply]
      exact Subtype.ext ((hC u).eY 0 (Nat.zero_le _) (Or.inl rfl) _).symm
    rw [hz]
    rfl

end GlobalTheory.Fam

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.exists_tupleAdelicData_standardBasePoints : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ (Ch : ℕ → Type) (_ : ∀ i, Fintype (Ch i)) (A : TwDat I l Z u a Ch), A.Is ∧ Nonempty (Unique (Ch B.R.m)) ∧ (∀ i, Nonempty (Idx I.sel (I.tup a) (I.idx a) i) → Nonempty (Ch i)) ∧ GlobalTheory.QTw.BaseCommon A ∧ (∀ i, i < B.R.m → ∀ β, A.kb i β = TC.kStd X u (B.R.N i)) ∧ ∀ i, i ≤ B.R.m → ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal → (i < B.R.m ∨ ¬ I.UnderQ a v) → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) (A.kb i β) = 1 ∧ ∀ i, i < B.R.m → ∀ β, A.kb i β = TC.kStd X u (B.R.N i) := by
  first | exact @GlobalTheory.AdForm.exists_twDat_baseStd | exact GlobalTheory.AdForm.exists_twDat_baseStd | (intros; apply GlobalTheory.AdForm.exists_twDat_baseStd <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

theorem _root_.GlobalTheory.T.splitPlace_datum_boxTensor_line_over_vacuum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S X T L'' : HSp D) (o'' : OrthDec X T L'') (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L'' ζ₀ → ∀ (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o'' ζ₀ γ γ₀ → ∀ (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → ∀ (f₂ F₂ : WO S T → ℂ) (Ψ₂ : Matrix n'' n k → ℂ), Over ψ β γ LS LT f₂ Ψ₂ F₂ → ∀ (b : (n → k) → ℂ) (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ → IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ → GlobalTheory.FinPl.tensRow Ψ₂ b ∈ SB (Matrix (n'' ⊕ Fin 1) n k) → ∃ g, Over ψ β γ₀ LS LX g (GlobalTheory.FinPl.tensRow Ψ₂ b) (o''.boxT S F₂ (T₃ (rowFun β ζ₀ b))) := by
  exact @GlobalTheory.FinPl.BoxDatum.over_boxT
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

theorem _root_.GlobalTheory.T.thetaSlice_lineSum_eq_intertwiner_image : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), a ≠ 0 → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ a) Ξ → ∀ u : WO A S, ∃ (g₁ : WO L S → ℂ) (T₁ : (WO L S → ℂ) →ₗ[ℂ] (WO L S → ℂ)), IsThetaFunO ψ L S g₁ ∧ IsPlaceModel ψ (symplO L S) (heisO ψ L S) p.e (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)) 1 g₁ T₁ ∧ T₁ (colFun β ζ a) = fun y => Ξ ((o.resS S).symm (u, y)) := by
  first | exact @GlobalTheory.LastTgtSlice.main | exact GlobalTheory.LastTgtSlice.main | (intros; apply GlobalTheory.LastTgtSlice.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SetCut

section Alg

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem mul_eq_add_sub_one (c : R) (a b : Matrix n n R) (ha : c • (a - 1) = a - 1) (hb : c • (b - 1) = 0) :
    a * b = a + b - 1 ∧ b * a = a + b - 1 := by
  have h1 : (a - 1) * (b - 1) = 0 := by rw [← ha, Matrix.smul_mul, ← Matrix.mul_smul, hb, Matrix.mul_zero]
  have h2 : (b - 1) * (a - 1) = 0 := by rw [← ha, Matrix.mul_smul, ← Matrix.smul_mul, hb, Matrix.zero_mul]
  have e1 : a * b = (a - 1) * (b - 1) + (a + b - 1) := by noncomm_ring
  have e2 : b * a = (b - 1) * (a - 1) + (a + b - 1) := by noncomm_ring
  exact ⟨by rw [e1, h1, zero_add], by rw [e2, h2, zero_add]⟩

theorem cut_sub_one (c : R) (g : Matrix n n R) : c • g + (1 - c) • (1 : Matrix n n R) - 1 = c • (g - 1) := by
  rw [smul_sub, sub_smul, one_smul]; abel

theorem cut_left (c : R) (a b : Matrix n n R) (ha : c • (a - 1) = a - 1) (hb : c • (b - 1) = 0) :
    c • (a * b) + (1 - c) • (1 : Matrix n n R) = a := by
  rw [← sub_left_inj (a := 1), cut_sub_one, (mul_eq_add_sub_one c a b ha hb).1,
    show a + b - 1 - 1 = (a - 1) + (b - 1) by abel, smul_add, ha, hb, add_zero]

theorem cut_right (c : R) (a b : Matrix n n R) (ha : c • (a - 1) = a - 1) (hb : c • (b - 1) = 0) :
    (1 - c) • (a * b) + (1 - (1 - c)) • (1 : Matrix n n R) = b := by
  rw [← sub_left_inj (a := 1), cut_sub_one, (mul_eq_add_sub_one c a b ha hb).1,
    show a + b - 1 - 1 = (a - 1) + (b - 1) by abel, sub_smul, one_smul, smul_add, ha, hb]
  abel

theorem cut_mul_cut (c : R) (hc : c * c = c) (g : Matrix n n R) :
    (c • g + (1 - c) • (1 : Matrix n n R)) * ((1 - c) • g + (1 - (1 - c)) • (1 : Matrix n n R)) = g := by
  have h0 : c * (1 - c) = 0 := by rw [mul_sub, mul_one, hc, sub_self]
  rw [(mul_eq_add_sub_one c _ _ (by rw [cut_sub_one, smul_smul, hc]) (by rw [cut_sub_one, smul_smul, h0, zero_smul])).1,
    sub_sub_cancel, sub_smul, sub_smul, one_smul, one_smul]
  abel

end Alg

variable {D : D7}

theorem mem_idOff_iff (P : Pl D → Prop) (a : AE D) : a ∈ idOff D P ↔ ∀ w, P w → GlobalTheory.FinPl.compAt D w a = 0 := by
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]

theorem mem_GfC_iff_entries (V : HSp D) (g : GA D V) :
    g ∈ GfC V ↔ ∀ i j, infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  rw [GlobalTheory.UnitaryIdemCut.mem_GfC_iff, Units.ext_iff]
  change (Formalism.L2.Theta.mt V g).map (infPart D) = 1 ↔ _
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero, Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]

theorem mem_grpAt_iff_parts (V : HSp D) (P : Pl D → Prop) (g : GA D V) :
    g ∈ grpAt V P ↔ ∀ i j, infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 ∧
      ∀ w, ¬ P w → GlobalTheory.FinPl.compAt D w ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  rw [grpAt, mem_congGrp_iff]
  exact forall_congr' fun i => forall_congr' fun j => mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D P _

theorem mem_grpOff_iff_parts (V : HSp D) (P : Pl D → Prop) (g : GA D V) :
    g ∈ grpOff V P ↔ ∀ i j w, P w → GlobalTheory.FinPl.compAt D w ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  rw [grpOff, mem_congGrp_iff]
  exact forall_congr' fun i => forall_congr' fun j => mem_idOff_iff P _

theorem grpAt_le_GfC (V : HSp D) (P : Pl D → Prop) : grpAt V P ≤ GfC V := fun g hg =>
  (mem_GfC_iff_entries V g).2 fun i j => ((mem_grpAt_iff_parts V P g).1 hg i j).1

theorem grpAt_le_grpOff (V : HSp D) (P P' : Pl D → Prop) (h : ∀ p, P p → ¬ P' p) : grpAt V P ≤ grpOff V P' := fun g hg =>
  (mem_grpOff_iff_parts V P' g).2 fun i j w hw => ((mem_grpAt_iff_parts V P g).1 hg i j).2 w fun h' => h w h' hw

theorem GfC_inf_grpOff (V : HSp D) (P : Pl D → Prop) : GfC V ⊓ grpOff V P = grpAt V fun p => ¬ P p := by
  ext g
  rw [Subgroup.mem_inf, mem_GfC_iff_entries, mem_grpOff_iff_parts, mem_grpAt_iff_parts]
  exact ⟨fun h i j => ⟨h.1 i j, fun w hw => h.2 i j w (not_not.1 hw)⟩,
    fun h => ⟨fun i j => (h i j).1, fun i j w hw => (h i j).2 w (not_not.2 hw)⟩⟩

abbrev eQ (D : D7) (Q : Finset (Pl D)) : AE D := algebraMap (AF D.host.F) (AE D) (idemQ D Q)

theorem eQ_mul_self (Q : Finset (Pl D)) : eQ D Q * eQ D Q = eQ D Q := by
  rw [← RingHom.map_mul, idemQ_mul_self]

theorem algebraMap_one_sub (c : AF D.host.F) :
    algebraMap (AF D.host.F) (AE D) (1 - c) = 1 - algebraMap (AF D.host.F) (AE D) c := by
  rw [RingHom.map_sub, RingHom.map_one]

theorem smul_of_mem_Q (V : HSp D) (Q : Finset (Pl D)) {a : GA D V} (ha : a ∈ grpAt V (· ∈ Q)) :
    eQ D Q • (Formalism.L2.Theta.mt V a - 1) = Formalism.L2.Theta.mt V a - 1 := by
  rw [grpAt, mem_congGrp_iff] at ha
  exact Matrix.ext fun i j => (mem_idAt_Q_iff Q _).1 (ha i j)

open Classical in
theorem smul_of_mem_Qc (V : HSp D) (Q : Finset (Pl D)) {b : GA D V} (hb : b ∈ grpAt V (· ∉ Q)) :
    eQ D Q • (Formalism.L2.Theta.mt V b - 1) = 0 := by
  rw [mem_grpAt_iff_parts] at hb
  exact Matrix.ext fun i j => (mem_idOff_iff_mul (· ∈ Q) _ (parts_idemQ Q).1 (parts_idemQ Q).2 _).1
    ((mem_idOff_iff _ _).2 fun w hw => (hb i j).2 w (not_not.2 hw))

theorem comm_Q (V : HSp D) (Q : Finset (Pl D)) {a b : GA D V} (ha : a ∈ grpAt V (· ∈ Q)) (hb : b ∈ grpAt V (· ∉ Q)) :
    a * b = b * a := by
  have h := mul_eq_add_sub_one _ _ _ (smul_of_mem_Q V Q ha) (smul_of_mem_Qc V Q hb)
  apply mt_injective V
  rw [mt_mul, mt_mul]
  exact h.1.trans h.2.symm

theorem cutG_left (V : HSp D) (Q : Finset (Pl D)) {a b : GA D V} (ha : a ∈ grpAt V (· ∈ Q)) (hb : b ∈ grpAt V (· ∉ Q)) :
    cutG V _ (idemQ_mul_self Q) (a * b) = a := by
  apply mt_injective V
  rw [mt_cutG, mt_mul]
  exact cut_left _ _ _ (smul_of_mem_Q V Q ha) (smul_of_mem_Qc V Q hb)

theorem cutG_right (V : HSp D) (Q : Finset (Pl D)) {a b : GA D V} (ha : a ∈ grpAt V (· ∈ Q)) (hb : b ∈ grpAt V (· ∉ Q)) :
    cutG V _ (one_sub_idemQ_mul_self Q) (a * b) = b := by
  apply mt_injective V
  rw [mt_cutG, mt_mul, algebraMap_one_sub]
  exact cut_right _ _ _ (smul_of_mem_Q V Q ha) (smul_of_mem_Qc V Q hb)

theorem cutG_mul_cutG (V : HSp D) (Q : Finset (Pl D)) (g : GA D V) :
    cutG V _ (idemQ_mul_self Q) g * cutG V _ (one_sub_idemQ_mul_self Q) g = g := by
  apply mt_injective V
  rw [mt_mul, mt_cutG, mt_cutG, algebraMap_one_sub]
  exact cut_mul_cut _ (eQ_mul_self Q) _

theorem cutG_mem_Q (V : HSp D) (Q : Finset (Pl D)) (g : GA D V) :
    cutG V _ (idemQ_mul_self Q) g ∈ grpAt V (· ∈ Q) := by
  rw [grpAt, mem_congGrp_iff]
  intro i j
  rw [mt_cutG, cut_sub_one, mem_idAt_Q_iff, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
  exact congrArg (· * _) (eQ_mul_self Q)

open Classical in
theorem cutG_mem_Qc (V : HSp D) (Q : Finset (Pl D)) {g : GA D V} (hg : g ∈ GfC V) :
    cutG V _ (one_sub_idemQ_mul_self Q) g ∈ grpAt V (· ∉ Q) := by
  rw [mem_grpAt_iff_parts]
  intro i j
  rw [mt_cutG, cut_sub_one, Matrix.smul_apply, smul_eq_mul, algebraMap_one_sub]
  refine ⟨?_, fun w hw => ?_⟩
  · rw [RingHom.map_mul, (mem_GfC_iff_entries V g).1 hg i j, mul_zero]
  · rw [RingHom.map_mul, RingHom.map_sub, RingHom.map_one, (parts_idemQ Q).2 w, if_pos (not_not.1 hw), sub_self, zero_mul]

theorem isClosed_of_idem (V : HSp D) (P : Pl D → Prop) (c : AF D.host.F)
    (hc : ∀ a, a ∈ idAt D P ↔ algebraMap (AF D.host.F) (AE D) c * a = a) : IsClosed (grpAt V P : Set (GA D V)) := by
  have h := (GlobalTheory.T.continuous_idempotentCut_and_isClosed_scaledKernel D V).2 (1 - c)
  convert h using 1
  ext g
  rw [SetLike.mem_coe, grpAt, mem_congGrp_iff, Set.mem_setOf_eq]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [hc, algebraMap_one_sub, sub_mul, one_mul, sub_eq_zero, eq_comm]

def splitHomeo (V : HSp D) (Q : Finset (Pl D)) : (grpAt V (· ∈ Q) × grpAt V (· ∉ Q)) ≃ₜ GfC V where
  toFun p := ⟨p.1.1 * p.2.1, mul_mem (grpAt_le_GfC V _ p.1.2) (grpAt_le_GfC V _ p.2.2)⟩
  invFun g := (⟨cutG V _ (idemQ_mul_self Q) g.1, cutG_mem_Q V Q g.1⟩,
    ⟨cutG V _ (one_sub_idemQ_mul_self Q) g.1, cutG_mem_Qc V Q g.2⟩)
  left_inv p := Prod.ext (Subtype.ext (cutG_left V Q p.1.2 p.2.2)) (Subtype.ext (cutG_right V Q p.1.2 p.2.2))
  right_inv g := Subtype.ext (cutG_mul_cutG V Q g.1)
  continuous_toFun := by
    haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
    exact Continuous.subtype_mk
      ((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)) _
  continuous_invFun :=
    (Continuous.subtype_mk (((GlobalTheory.T.continuous_idempotentCut_and_isClosed_scaledKernel D V).1 _ _).comp continuous_subtype_val) _).prodMk
      (Continuous.subtype_mk (((GlobalTheory.T.continuous_idempotentCut_and_isClosed_scaledKernel D V).1 _ _).comp continuous_subtype_val) _)

theorem grp_split : ∀ (D : D7) (V : HSp D) (Q : Finset (Pl D)), IsClosed (grpAt V (· ∈ Q) : Set (GA D V)) ∧ IsClosed (grpAt V (· ∉ Q) : Set (GA D V)) ∧ grpAt V (· ∈ Q) ≤ GfC V ∧ grpAt V (· ∉ Q) ≤ GfC V ∧ (∀ a ∈ grpAt V (· ∈ Q), ∀ b ∈ grpAt V (· ∉ Q), a * b = b * a) ∧ (∃ e : (grpAt V (· ∈ Q) × grpAt V (· ∉ Q)) ≃ₜ GfC V, ∀ p, (e p : GA D V) = p.1 * p.2) ∧ (∀ P P' : Pl D → Prop, (∀ p, P p → ¬ P' p) → grpAt V P ≤ grpOff V P') ∧ (∀ P : Pl D → Prop, GfC V ⊓ grpOff V P = grpAt V fun p => ¬ P p) ∧ (∀ (L : Lat V), IsSelfDualC V L → ∀ P : Pl D → Prop, (∃ K : Subgroup (GA D V), (∀ g, g ∈ K ↔ InK V L P g) ∧ IsCompact (K : Set (GA D V)) ∧ IsOpen ((K.subgroupOf (grpAt V P) : Subgroup _) : Set (grpAt V P))) ∧ ∀ κ, InK V L P κ ↔ ∃ a b, InK V L (fun p => P p ∧ p ∈ Q) a ∧ InK V L (fun p => P p ∧ p ∉ Q) b ∧ κ = a * b) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), (∀ a ∈ grpAt V (· ∈ Q), ∀ b ∈ grpAt V (· ∉ Q), a * b ∈ jacGrp d → a ∈ jacGrp d ∧ b ∈ jacGrp d) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∀ a ∈ grpAt V (· ∈ Q), ∀ b ∈ grpAt V (· ∉ Q), a * b ∈ besGrp d o → a ∈ besGrp d o ∧ b ∈ besGrp d o := by
  intro D V Q
  refine ⟨isClosed_of_idem V _ _ (mem_idAt_Q_iff Q), isClosed_of_idem V _ _ (mem_idAt_Qc_iff Q), grpAt_le_GfC V _,
    grpAt_le_GfC V _, fun a ha b hb => comm_Q V Q ha hb, ?_⟩
  refine ⟨⟨splitHomeo V Q, fun _ => rfl⟩, grpAt_le_grpOff V, GfC_inf_grpOff V, ?_, ?_⟩
  · intro L hL P
    exact ⟨GlobalTheory.T.exists_compactOpen_latticeStabilizerAtPlaces D V L hL P,
      GlobalTheory.T.inLatticeStabilizerAtPlaces_iff_placeSet_prod D V L P Q⟩
  · intro V₀ ρ d
    constructor
    · intro a ha b hb h
      exact ⟨cutG_left V Q ha hb ▸ (GlobalTheory.T.unitaryIdempotentCut_mem_fourierJacobi_besselGroup D V V₀ ρ d _ (idemQ_mul_self Q)).1 _ h,
        cutG_right V Q ha hb ▸ (GlobalTheory.T.unitaryIdempotentCut_mem_fourierJacobi_besselGroup D V V₀ ρ d _ (one_sub_idemQ_mul_self Q)).1 _ h⟩
    · intro A L o a ha b hb h
      exact ⟨cutG_left V Q ha hb ▸ (GlobalTheory.T.unitaryIdempotentCut_mem_fourierJacobi_besselGroup D V V₀ ρ d _ (idemQ_mul_self Q)).2 A L o _ h,
        cutG_right V Q ha hb ▸ (GlobalTheory.T.unitaryIdempotentCut_mem_fourierJacobi_besselGroup D V V₀ ρ d _ (one_sub_idemQ_mul_self Q)).2 A L o _ h⟩

end GlobalTheory.FinPl.SetCut

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistChainLevelProduct_inverse_scalar_laws : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∀ k ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h, ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ → t.om j (1, k) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧ t.om (j + 1) (k, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) = a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂ := by
  first | exact @GlobalTheory.QFinLaw.inverse_laws | exact GlobalTheory.QFinLaw.inverse_laws | (intros; apply GlobalTheory.QFinLaw.inverse_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.psi_primitive_of_inverseDifferent_lines : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L : Lat S) (M : Lat S₀) (μ : D.host.E) (v : GlobalTheory.FinPl.Pl D), μ ≠ 0 → LineAt z μ M v → (∀ i : Fin ρ, ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ incA D μ * a ∈ idV (dI D ^ (ρ - i.1)) v) → PrimAt ψ d L v ∧ LastAt ψ d z L M v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.primAt_lastAt_of_lines | exact GlobalTheory.Core.Mi.LatMatch.primAt_lastAt_of_lines | (intros; apply GlobalTheory.Core.Mi.LatMatch.primAt_lastAt_of_lines <;> assumption)
end
