module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle396
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFinGL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealCentreActsByCharacterOnIsotypicSlices
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle292
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle118
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle422
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LvSameZero
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle415
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle095
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle080
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle399
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.MvPolynomial
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam

theorem comb_smul_coef {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (κ : ℂ) (d : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (κ • d) f = κ • comb ψ S T d f := by
  by_cases hκ : κ = 0
  · subst hκ; simp [comb]
  · unfold comb
    rw [Finsupp.support_smul_eq hκ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, mul_smul]

theorem isRatDatum_const_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {e : AE D}
    {Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ} {f₀ f : WO S T → ℂ} (h : IsRatDatum ψ S T e Ξ f₀ f) (κ : ℂ) :
    IsRatDatum ψ S T e (fun z => κ * Ξ z) f₀ (κ • f) := by
  obtain ⟨Φ, hSB, hval, hth⟩ := h
  refine ⟨κ • Φ, ?_, fun γ => by simp [hval γ], ?_⟩
  · obtain ⟨hs, k, hk, hinv, hsupp⟩ := hSB
    refine ⟨fun t ht => hs t fun h0 => ht (by simp [h0]), k, hk, fun v hv hv' t => by simp [hinv v hv hv' t],
      fun t ht => hsupp t fun h0 => ht (by simp [h0])⟩
  · unfold IsThetaAt AllSome at hth ⊢
    refine ⟨hth.1, fun T hT => ?_⟩
    have h := hth.2 T hT
    simp only at h ⊢
    rw [h, map_smul]

def chartRescale {Ch : ℕ → Type} (m : ℕ) (cc : ℕ → ℂ) (b : ∀ j, Ch (j + 1) → ℂ) : ∀ j, Ch j → ℂ
  | 0 => fun _ => 1
  | j + 1 => fun γ => if j < m then cc j * b j γ else 1

theorem datRoot_ne_zero {x : ℂ} (h : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) : x ≠ 0 := by
  obtain ⟨n, hn, hx⟩ := h
  rintro rfl
  simp [zero_pow hn.ne'] at hx

theorem datRoot_mul {x y : ℂ} (hx : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) (hy : ∃ n : ℕ, 0 < n ∧ y ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ (x * y) ^ n = 1 := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hyb⟩ := hy
  refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
  rw [mul_pow, pow_mul, hxa, one_pow, mul_comm a b, pow_mul, hyb, one_pow, one_mul]

theorem datRoot_prod {ι : Type*} (s : Finset ι) (x : ι → ℂ) (h : ∀ i ∈ s, ∃ n : ℕ, 0 < n ∧ x i ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ (∏ i ∈ s, x i) ^ n = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact datRoot_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end GlobalTheory.Fam

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.RamCont

variable {D : D7}

theorem infM_mul' (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn (g * h) τ = infM θ V hn g τ * infM θ V hn h τ := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.infM_mul θ V g h τ

theorem infM_fin' (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GfC V) (τ : D.what₂.Tau) :
    infM θ V hn k τ = 1 := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.infM_fin θ V k hk τ

theorem continuous_infM' (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {n : ℕ} (hn : V.rank = n) (τ : D.what₂.Tau) :
    Continuous fun g : GA D V => infM θ V hn g τ := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.continuous_infM θ hθ V τ

theorem pf_mul (V : HSp D) (g h : GA D V) :
    GlobalTheory.AdForm.RdLaw.pf V (g * h) = GlobalTheory.AdForm.RdLaw.pf V g * GlobalTheory.AdForm.RdLaw.pf V h := by
  apply Subtype.ext
  show GlobalTheory.AdForm.RdLaw.PGL D V.rank (matHom V (g * h)) =
    GlobalTheory.AdForm.RdLaw.PGL D V.rank (matHom V g) * GlobalTheory.AdForm.RdLaw.PGL D V.rank (matHom V h)
  rw [map_mul, map_mul]

theorem pf_inv (V : HSp D) (g : GA D V) : GlobalTheory.AdForm.RdLaw.pf V g⁻¹ = (GlobalTheory.AdForm.RdLaw.pf V g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pf_mul, inv_mul_cancel, GlobalTheory.AdForm.RdLaw.pf_one]

theorem pf_inv_mul_mem (V : HSp D) (g : GA D V) : (GlobalTheory.AdForm.RdLaw.pf V g)⁻¹ * g ∈ GinfC V := by
  rw [GlobalTheory.CentreTarget.mem_GinfC, ← pf_inv, GlobalTheory.CentreTarget.mt_mul, Matrix.map_mul, GlobalTheory.AdForm.RdLaw.mt_pf,
    GlobalTheory.AdForm.RdLaw.PM_map, GlobalTheory.AdForm.RdLaw.finPart_eps, RingHom.map_sub, RingHom.map_one,
    GlobalTheory.AdForm.RdLaw.finPart_eps, sub_self, zero_smul, add_zero, one_smul, ← Matrix.map_mul,
    ← GlobalTheory.CentreTarget.mt_mul, inv_mul_cancel]
  show (matHom V 1).1.map _ = 1
  rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem infM_mul_pf (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k d : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn (k * ((GlobalTheory.AdForm.RdLaw.pf V d)⁻¹ * d)) τ = infM θ V hn k τ * infM θ V hn d τ := by
  rw [infM_mul' θ V hn k, infM_mul' θ V hn _ d, infM_fin' θ V hn _ (inv_mem (GlobalTheory.AdForm.RdLaw.pf_fin V d)), one_mul]

end GlobalTheory.AdForm.RamCont

namespace GlobalTheory.AdForm.RamCont

theorem rd_continuous : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ b y, Continuous (A.rd θ j hj b φ y) := by
  classical
  intro B X I hI hPins l Z u a Ch A hA θ hθ j hj φ hφ b y
  obtain ⟨hreps, -, -⟩ := GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hI hPins l Z u a Ch A hA j hj b
  have hchi := GlobalTheory.T.continuous_chartLevelCharacters_adelic_tuple I hI hPins l Z u a Ch A hA j hj b
  obtain ⟨hval, hrd⟩ := GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hI hPins l Z u a Ch A hA θ hθ j hj φ hφ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X j).gram
  rw [continuous_iff_continuousAt]
  intro g0
  obtain ⟨γ, hγ, c, k, hk, κ, hκ, e0⟩ := hreps.dec g0
  obtain ⟨P, -, hP⟩ := hval c.1
  let V := (I.rec7 l Z).sp.X j
  let hn := rankN (I.rec7 l Z) j hj
  have hpc : Continuous fun g : GA (I.rec7 l Z) V => GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) :=
    (GlobalTheory.AdForm.RdLaw.continuous_pf V).comp (continuous_const_mul g0⁻¹)
  let p : GA (I.rec7 l Z) V → GfC V := fun g => ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), GlobalTheory.AdForm.RdLaw.pf_fin V _⟩
  have hp : Continuous p := hpc.subtype_mk _
  let O : Set (GA (I.rec7 l Z) V) := {g | GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b}
  have hO : IsOpen O := by
    have h1 := hreps.opn.preimage hp
    have e : O = p ⁻¹' (((A.U j b).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) := by
      ext g
      show GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b ↔ p g ∈ (A.U j b).subgroupOf (GfC V)
      rw [Subgroup.mem_subgroupOf]
    rw [e]; exact h1
  have hg0 : g0 ∈ O := by
    show GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g0) ∈ A.U j b
    rw [inv_mul_cancel, GlobalTheory.AdForm.RdLaw.pf_one]; exact one_mem _
  let G : GA (I.rec7 l Z) V → ℂ := fun g =>
    if h : GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b then ((A.chi j b ⟨_, h⟩ : ℂˣ) : ℂ) else 0
  have hG : ContinuousAt G g0 := by
    have hc : ContinuousOn G O := by
      rw [continuousOn_iff_continuous_restrict]
      have e : (fun x : O => G x.1) = fun x : O => ((A.chi j b ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * x.1), x.2⟩ : ℂˣ) : ℂ) := by
        funext x
        exact dif_pos x.2
      show Continuous fun x : O => G x.1
      rw [e]
      exact hchi.comp ((hpc.comp continuous_subtype_val).subtype_mk _)
    exact hc.continuousAt (hO.mem_nhds hg0)
  let M : GA (I.rec7 l Z) V → (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ :=
    fun g τ => (show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ V hn k τ * infM θ V hn (g0⁻¹ * g) τ) * y.1 τ
  have hMu : ∀ g τ, IsUnit (M g τ).det := fun g τ => by
    simp only [M]
    erw [det_mul, det_mul]
    exact ((GlobalTheory.AdForm.RdVal.infM_unit θ V hn k τ).mul (GlobalTheory.AdForm.RdVal.infM_unit θ V hn _ τ)).mul (y.2 τ)
  have hM : ∀ τ, Continuous fun g =>
      (1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) τ * M g τ := by
    intro τ
    have h1 : Continuous fun g : GA (I.rec7 l Z) V => infM θ V hn (g0⁻¹ * g) τ :=
      (continuous_infM' θ hθ V hn τ).comp (continuous_const_mul g0⁻¹)
    show Continuous fun g : GA (I.rec7 l Z) V => (1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) τ * ((show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ V hn k τ * infM θ V hn (g0⁻¹ * g) τ) * y.1 τ)
    exact continuous_const.matrix_mul ((continuous_const.matrix_mul h1).matrix_mul continuous_const)
  let Φ : GA (I.rec7 l Z) V → ℂ := fun g =>
    (∏ τ, ((1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) τ * M g τ).det ^
      shiftOf (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j) τ) *
    MvPolynomial.eval (fun q : (I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N j) × Fin ((I.rec7 l Z).R.N j) =>
      ((1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) q.1 * M g q.1) q.2.1 q.2.2) P
  have hΦ : Continuous Φ := by
    refine Continuous.mul (continuous_finsetProd _ fun τ _ => ((hM τ).matrix_det).zpow₀ _ fun g => Or.inl ?_) ?_
    · rw [Pi.one_apply, one_mul]; exact (hMu g τ).ne_zero
    · exact (MvPolynomial.continuous_eval P).comp (continuous_pi fun q => (hM q.1).matrix_elem q.2.1 q.2.2)
  refine ContinuousAt.congr (f := fun g => ((A.chi j b ⟨κ, hκ⟩ : ℂˣ) : ℂ) * G g * Φ g)
    ((continuousAt_const.mul hG).mul hΦ.continuousAt) ?_
  filter_upwards [hO.mem_nhds hg0] with g hg
  have hU : GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b := hg
  have hδi : (GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g) ∈ GinfC V := pf_inv_mul_mem V _
  have hδf : GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ GfC V := GlobalTheory.AdForm.RdLaw.pf_fin V _
  have hκf : κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ GfC V := mul_mem (hreps.le hκ) hδf
  have eg : g = γ * (A.h j b c * (k * ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g)))) *
      (κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g)) := by
    have hc := Formalism.IndefR.Eqv.Act.comm_inf_fin hδi hκf
    calc g = g0 * (GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) * ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g))) := by group
      _ = γ * (A.h j b c * k) * ((κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g)) *
          ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g))) := by rw [e0]; group
      _ = γ * (A.h j b c * k) * (((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g)) *
          (κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))) := by rw [hc]
      _ = _ := by group
  let y' : (I.chain l u a).Y j := ⟨M g, hMu g⟩
  have htr : IsTr (G := fun _ => 1) (infM θ V hn (k * ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g)))) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := by
    intro τ
    rw [infM_mul_pf θ V hn k (g0⁻¹ * g) τ]
    rfl
  have key := hrd b y γ hγ c _ (mul_mem hk hδi) ⟨κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), mul_mem hκ hU⟩ y' htr
  rw [show A.rd θ j hj b φ y g = _ from (congrArg (A.rd θ j hj b φ y) eg).trans key]
  have e1 : (⟨κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), mul_mem hκ hU⟩ : A.U j b) =
      ⟨κ, hκ⟩ * ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), hU⟩ := rfl
  have e2 : G g = ((A.chi j b ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), hU⟩ : ℂˣ) : ℂ) := dif_pos hU
  have e3 : Φ g = φ c.1 y' := congrFun hP ⟨M g, hMu g⟩
  rw [e1, map_mul, Units.val_mul, e2, e3, mul_assoc]

end GlobalTheory.AdForm.RamCont
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.RepZero

open _root_.Formalism.L2.Col GlobalTheory.Mem.Col2.StepZero

theorem chr_of_down_eq_one {X : Fields} {n : ℕ} {ST SG Q : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers X.E))}
    {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
    (pref : DecoF X.E n ST SG Q → Prop) {Λ₀ : LevFam X.E X.K n SG} (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q)
    (b : β) (g : (stepY ST y β Λ Θ pref).G b) (h : down pref hΛ b g = 1) : (stepY ST y β Λ Θ pref).chr b g = 1 := by
  show (Λ b).chr g.2.1 * (Θ b).chr g.2.2 = 1
  rw [chr_eq_one (hΘ b), mul_one, chr_congr (hΛ b)]
  have e : (⟨g.2.1.1, hΛ b ▸ g.2.1.2⟩ : Λ₀.grp) = (down pref hΛ b g).2 := rfl
  rw [e, h]
  exact map_one _

theorem exists_lift_one {X : Fields} {n : ℕ} {ST SG Q : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers X.E))}
    {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
    (pref : DecoF X.E n ST SG Q → Prop) {Λ₀ : LevFam X.E X.K n SG} (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (b : β) (p q : (stepY ST y β Λ Θ pref).D b) (h : p.1.1.deco = q.1.1.deco) :
    ∃ g : (stepY ST y β Λ Θ pref).G b, (stepY ST y β Λ Θ pref).gam b g = 1 ∧ g • p = q ∧ (stepY ST y β Λ Θ pref).chr b g = 1 := by
  obtain ⟨g, h2, h3⟩ := exists_lift pref hy hΛ hΘ b p q 1 (by rw [one_smul]; exact h)
  exact ⟨g, (congrArg (fun g => ufGL X.E n g.1) h2).trans (map_one _), h3, chr_of_down_eq_one pref hΛ hΘ b g h2⟩

end GlobalTheory.Fam.RepZero


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Fam.rep_zero_std : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ c : {c // A.chOf 0 c = β}, ∃ κ : (A.K 0 (Nat.zero_le _) β).lev.U, ((C.forms u).to0.cls0.y ((I.eCls0 l u a).symm c.1)).1 = ((A.K 0 (Nat.zero_le _) β).y c).1 * κ.1 ∧ (A.K 0 (Nat.zero_le _) β).lev.chi κ = 1 := by
  set_option maxHeartbeats 4000000 in
    intro B X I hI _ l Z C hC u a Ch A hA β hk c
    obtain ⟨c, rfl⟩ := c
    set c' := (I.eCls0 l u a).symm c with hc'
    have hR := hA.reads 0 (Nat.zero_le _)
    have hyS : ((C.forms u).to0.cls0.y c').1 = I.yStd u 0 c' := (hC u).yE 0 (Nat.zero_le _) (Or.inl rfl) c'
    have hS := MemChart.yStd_spec I hI u 0 c'
    set yc : TC.GA B (B.R.N 0) := ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1 with hyc
    have hd : Disjoint (B.primes X).vGs (I.Q a) := (LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a)
    let q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0 := extTo (I.Q a) (extTo I.SQ ((I.stp u I.mu0 0).rep c').1.1)
    have hq : TC.PtOf (yc * (yc⁻¹ * I.yStd u 0 c') * A.kb 0 (A.chOf 0 c)) q := by
      rw [mul_inv_cancel_left, hk]
      exact IsPtOf.extTo (I.Q_subset_SQ a) hd hS
    have hL := hI.idx_ok a
    have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
    have hΛ := StepZero.levGAt_zero (I.Tp a) hL
    have hΘ := StepZero.levQAt_zero (I.Tp a) hL
    have e : ((I.stp u a 0).rep c).1.1.deco = ((I.stp u I.mu0 0).rep c').1.1.deco := by
      have := TC.StepZero.rep_eCls0 I hI l u a c'
      rwa [hc', Equiv.apply_symm_apply] at this
    obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
    obtain ⟨g, hgam, h3, hchr⟩ := RepZero.exists_lift_one ((I.Tp a).pref u 0) hy hΛ hΘ c.1 ((I.stp u a 0).rep c) p
      (by rw [hp]; exact e)
    have hact : ((I.stp u a 0).act c.1 g ((I.stp u a 0).rep c)).1.1 = q :=
      (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp
    have hmem : yc⁻¹ * I.yStd u 0 c' ∈ (A.K 0 (Nat.zero_le _) (A.chOf 0 c)).lev.U :=
      (hR.lev c _ q hq).2 ⟨g, hgam, hact, TC.Chart0.cos0 I _ _⟩
    refine ⟨⟨yc⁻¹ * I.yStd u 0 c', hmem⟩, ?_, ?_⟩
    · show _ = yc * (yc⁻¹ * I.yStd u 0 c')
      rw [hyS, mul_inv_cancel_left]
    · have hpt2 : TC.PtOf (yc * (yc⁻¹ * I.yStd u 0 c') * A.kb 0 (A.chOf 0 c))
          ((I.stp u a 0).act c.1 g ((I.stp u a 0).rep c)).1.1 := by
        rw [hact]
        exact hq
      have hc := hR.chr c ⟨yc⁻¹ * I.yStd u 0 c', hmem⟩ g hgam hpt2
      apply Units.ext
      refine hc.trans ?_
      rw [hchr]
      simp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharRoot

theorem sigR_sigR (D : D7) (w : Formalism.L2.Theta.AE D) :
    sigR (AF D.host.F) D.sp.cm.sig (sigR (AF D.host.F) D.sp.cm.sig w) = w := by
  have hσ : ∀ z : D.host.E, D.sp.cm.sig (D.sp.cm.sig z) = z := fun z => star_star z
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => simp [sigR, hσ]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]

theorem exists_idF_eq_mul_sigR (D : D7) (x : (Formalism.L2.Theta.AE D)ˣ) :
    ∃ t : (AF D.host.F)ˣ, ((idF D t : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = (x : Formalism.L2.Theta.AE D) * sigR (AF D.host.F) D.sp.cm.sig (x : Formalism.L2.Theta.AE D) := by
  have hσ : ∀ z : D.host.E, D.sp.cm.sig (D.sp.cm.sig z) = z := fun z => star_star z
  have htr : ∀ z : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = z + D.sp.cm.sig z := by
    intro z
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add (f := _), hσ, add_comm]
  obtain ⟨t, ht⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr
    (x * Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom x) (by
      rw [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_mul, sigR_sigR, mul_comm])
  refine ⟨t, ?_⟩
  convert congrArg Units.val ht using 1
  · rfl
  · rfl

theorem pow_eq_one_of_isDetRoot (D : D7) (V : HSp D) (g : GA D V) (x : (Formalism.L2.Theta.AE D)ˣ) (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (n : ℕ)
    (hn : 0 < n) (hbase : ∀ t, c (idF D t) ^ n = 1) (hcont : Continuous c) (hR : IsDetRoot V g x)
    (d : (Formalism.L2.Theta.AE D)ˣ) (hd : (d : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det)
    (hfu : Formalism.L2.Pj.FinUnit d) : ∃ N : ℕ, 0 < N ∧ c x ^ N = 1 := by
  obtain ⟨t, ht⟩ := exists_idF_eq_mul_sigR D x
  have hxx : x * x = d * idF D t := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ht, hd]
    unfold IsDetRoot at hR
    unfold Formalism.L2.Theta.mt
    nth_rewrite 1 [hR]
    ring
  obtain ⟨N, -, -, m, hm, hord⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hcont
  refine ⟨2 * (m * n), by positivity, ?_⟩
  rw [pow_mul, sq, ← map_mul, hxx, map_mul, mul_pow, pow_mul, hord _ hfu, one_pow, one_mul, mul_comm m n, pow_mul, hbase t,
    one_pow]

theorem infPart_det_of_mem_GfC : ∀ (D : D7) (V : HSp D) (g : GA D V), g ∈ GfC V →
    infPart D (Formalism.L2.Theta.mt V g).det = 1 := by
  intro D V g hg
  have h : infHom V g = 1 := hg
  have h2 := congrArg (fun z : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => Matrix.det z.1) h
  simp only [Units.val_one, Matrix.det_one] at h2
  rw [← h2]
  unfold infHom Formalism.L2.Theta.mt Formalism.UG.bc
  rw [RingHom.map_det]
  rfl

theorem finUnit_det_of_carries : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) (k : GL (Fin n) (EF D)),
    g ∈ GfC V → finM V hn g = k.1 →
    Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat D.host.E n) (Formalism.L2.Col.stdLat D.host.E n) →
    ∃ d : (Formalism.L2.Theta.AE D)ˣ, (d : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det ∧ Formalism.L2.Pj.FinUnit d := by
  intro D V n hn g k hg hk hc
  obtain ⟨h1, h2⟩ := GlobalTheory.T.integral_entries_of_carries_standardLattice D.host.F D.host.E n k hc
  have hu : IsUnit (Formalism.L2.Theta.mt V g).det := by
    unfold Formalism.L2.Theta.mt
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  obtain ⟨f1, f2⟩ := GlobalTheory.T.det_integralUnitIdele_of_integral_finitePart D V n hn g k hk h1 h2 hu.unit hu.unit_spec
  refine ⟨hu.unit, hu.unit_spec, ?_, f1, f2⟩
  rw [hu.unit_spec]
  exact infPart_det_of_mem_GfC D V g hg

end GlobalTheory.CharRoot

theorem GlobalTheory.CharRoot.chr_xr_pow_eq_one : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ j, j < B.R.m → ∀ i, i ≤ B.R.m → ∀ β, ∃ n : ℕ, 0 < n ∧ A.chr (j + 1) (A.xr i β) ^ n = 1 := by
  intro B X I hI hP l Z u a Ch₀ A hA j hj i hi β
  have hc : ChrEq (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (A.chr (j + 1)) (I.C.mu0 ⟨j, hj⟩ * I.xi a) := hA.chr ⟨j, hj⟩
  obtain ⟨hG, hF, hR⟩ := hA.kA i hi β
  have hb := hA.base i hi β

  obtain ⟨n, hn, hξ⟩ : ∃ n : ℕ, 0 < n ∧ I.xi a ^ n = 1 := by
    have hx := hI.xi_reads a
    have ht : IsOfFinOrder (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) := (I.tup a).2.1.1.1.2
    obtain ⟨n, hn, hpow⟩ := ht.exists_pow_eq_one
    refine ⟨n, hn, ?_⟩
    apply Subtype.ext
    ext y
    have h1 := hx y
    simp only [SubgroupClass.coe_pow, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, OneMemClass.coe_one, MonoidHom.one_apply, Units.val_one]
    rw [h1, ← map_pow, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hpow]
    simp

  have hpow : ∀ k : ℕ, ChrEq (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (A.chr (j + 1) ^ (k + 1)) ((I.C.mu0 ⟨j, hj⟩ * I.xi a) ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simpa using hc
    | succ k ih =>
      rw [pow_succ (A.chr (j + 1)) (k + 1), pow_succ _ (k + 1)]
      exact GlobalTheory.AdelicLiftCompare.chrEq_mul ih hc
  have hbase : ∀ t, A.chr (j + 1) (idF (I.rec7 l Z) t) ^ n = 1 := by
    intro t
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h1 := hpow k
    rw [mul_pow, hξ, mul_one] at h1
    have h2 := GlobalTheory.GridWeil.triv_base h1 (PsiExist.trivOn_pow (I.C.isMu0 ⟨j, hj⟩).triv (k + 1)) t
    simpa using h2

  have hcar : Formalism.L2.Herm.Carries (A.kb i β) (Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) (Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) := by
    obtain ⟨h1, h2⟩ := hb
    have h := h1.lat
    erw [h2] at h
    exact h
  obtain ⟨d, hd, hfu⟩ := GlobalTheory.CharRoot.finUnit_det_of_carries (I.rec7 l Z) _ _ _ (A.kA i β) (A.kb i β) hG hF hcar
  exact GlobalTheory.CharRoot.pow_eq_one_of_isDetRoot (I.rec7 l Z) _ (A.kA i β) (A.xr i β) (A.chr (j + 1)) n hn hbase hc.1.1 hR d hd hfu
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem _root_.GlobalTheory.T.seesawCombinations_composite_ne_zero_of_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (Lp : Fin n → LocPl ψ S T M M'), (Function.Injective fun i => (Lp i).q.v) → ∀ g, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) g → g ≠ 0 → (List.finRange n).foldr (fun i g' => comb ψ S T (Lp i).o g') g ≠ 0 := by
  first | exact @GlobalTheory.CombNonzero.main | exact GlobalTheory.CombNonzero.main | (intros; apply GlobalTheory.CombNonzero.main <;> assumption)
end
