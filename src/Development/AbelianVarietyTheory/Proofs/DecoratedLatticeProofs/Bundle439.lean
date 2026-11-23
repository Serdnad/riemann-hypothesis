module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle392
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle052
public import Formalism.LocalToGlobal.Columns.Bundle032
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

def basY (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Module.Basis (Fin (D.sp.Y 0).rank) D.host.E (VS D).V :=
  X.bas.reindex (finCongr (rank_eq X h)).symm

theorem cY_eq_basY (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (z : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h z = (basY X h).equivFun z := by
  funext k
  simp [GlobalTheory.Core.SBesEx.cY, HidaSetting.crd, crdOf, basY, Module.Basis.repr_reindex]

theorem mem_hermitianCoordinateLattice_iff (S : HSp D) (y : Fin S.rank → D.host.E) :
    y ∈ Formalism.L2.Herm.crdLat S S.L0 ↔ S.frame.equivFun.symm y ∈ S.L0 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [Formalism.L2.Herm.crd] using hw
  · intro hy
    exact ⟨_, hy, S.frame.equivFun.apply_symm_apply y⟩

theorem mem_rowLatticeYZeroFrame_iff_basis_sum (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (hId : ∀ x : I.E, HEq (ιE x) x) (bas : Module.Basis (Fin I.n) D.host.E (VS D).V)
    (hL : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ (∑ i, ιE (x i) • bas i) ∈ (VS D).L0) (hn : (D.sp.Y 0).rank = I.n)
    (y : Fin (D.sp.Y 0).rank → D.host.E) :
    y ∈ latS D ↔ (∑ k, y k • bas (Fin.cast hn k)) ∈ (VS D).L0 := by
  subst hI
  have hι : ∀ x, ιE x = x := fun x => eq_of_heq (hId x)
  have e1 := hL y
  have e2 : (∑ i, ιE (y i) • bas i) = ∑ k, y k • bas (Fin.cast hn k) :=
    Finset.sum_congr rfl fun i _ => congrArg (· • bas i) (hι (y i))
  refine Iff.trans ?_ (e1.trans (Eq.to_iff (congrArg (· ∈ (VS D).L0) e2)))
  rw [mem_hermitianCoordinateLattice_iff]
  show _ ↔ y ∈ Formalism.L2.SG.InstExistsPf.Lv D
  rw [Formalism.L2.SG.InstExistsPf.mem_Lv, Module.Basis.equivFun_symm_apply]

theorem mem_latS (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : _root_.GlobalTheory.Core.Mi.IdE X)
    (y : Fin (D.sp.Y 0).rank → D.host.E) :
    y ∈ latS D ↔ (basY X h).equivFun.symm y ∈ (VS D).L0 := by
  rw [mem_rowLatticeYZeroFrame_iff_basis_sum X.B.I h X.ιE hId X.bas X.L_eq (rank_eq X h), Module.Basis.equivFun_symm_apply]
  simp [basY]

theorem cY_mem_latS (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : _root_.GlobalTheory.Core.Mi.IdE X) (z : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h z ∈ latS D ↔ z ∈ (VS D).L0 := by
  rw [mem_latS X h hId, cY_eq_basY, LinearEquiv.symm_apply_apply]

theorem hT_swap (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := by
  have := (VS D).herm.eq x y
  rw [← this]
  rfl

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

theorem hT_fY_mem (X : HidaSetting D) (i : Fin D.R.rS) {Y : (VS D).V} (hY : Y ∈ (VS D).L0) :
    (VS D).hT (X.fY i) Y ∈ aaD D i := by
  have key : (VS D).L0 ≤ (aaD D i : Submodule (𝓞 D.host.E) D.host.E).comap
      (((VS D).hT (X.fY i)).restrictScalars (𝓞 D.host.E)) := by
    rw [X.Lam_split]
    refine sup_le (sup_le ?_ ?_) ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show (VS D).hT (X.fY i) (x • X.eX a) ∈ (aaD D i : Submodule (𝓞 D.host.E) D.host.E)
      rw [map_smul, smul_eq_mul, hT_swap, X.ef]
      by_cases hai : a = i
      · subst hai; simpa using hx
      · simp [hai]
    · intro x hx
      show (VS D).hT (X.fY i) x ∈ (aaD D i : Submodule (𝓞 D.host.E) D.host.E)
      rw [((X.Lb_perp x hx) i).2]; exact zero_mem _
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show (VS D).hT (X.fY i) (x • X.fY a) ∈ (aaD D i : Submodule (𝓞 D.host.E) D.host.E)
      rw [map_smul, X.ff, smul_zero]; exact zero_mem _
  exact key hY

theorem hT_eX_mem (X : HidaSetting D) (i : Fin D.R.rS) {Y : (VS D).V} (hY : Y ∈ (VS D).L0) :
    (VS D).hT (X.eX i) Y ∈ (aaD D i)⁻¹ := by
  have key : (VS D).L0 ≤ (((aaD D i)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E).comap (((VS D).hT (X.eX i)).restrictScalars (𝓞 D.host.E)) := by
    rw [X.Lam_split]
    refine sup_le (sup_le ?_ ?_) ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show (VS D).hT (X.eX i) (x • X.eX a) ∈ (((aaD D i)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E)
      rw [map_smul, X.ee, smul_zero]; exact zero_mem _
    · intro x hx
      show (VS D).hT (X.eX i) x ∈ (((aaD D i)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E)
      rw [((X.Lb_perp x hx) i).1]; exact zero_mem _
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show (VS D).hT (X.eX i) (x • X.fY a) ∈ (((aaD D i)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E)
      rw [map_smul, smul_eq_mul, X.ef]
      by_cases hai : i = a
      · subst hai; simpa using hx
      · simp [hai]
  exact key hY

theorem smul_eX_mem_iff (X : HidaSetting D) (i : Fin D.R.rS) (c : D.host.E) :
    c • X.eX i ∈ (VS D).L0 ↔ c ∈ aaD D i := by
  constructor
  · intro hc
    have := hT_fY_mem X i hc
    rwa [map_smul, smul_eq_mul, hT_swap, X.ef, if_pos rfl, star_one, mul_one] at this
  · intro hc
    rw [X.Lam_split]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨i, c, hc, rfl⟩))

theorem smul_fY_mem_iff (X : HidaSetting D) (i : Fin D.R.rS) (c : D.host.E) :
    c • X.fY i ∈ (VS D).L0 ↔ c ∈ (aaD D i)⁻¹ := by
  constructor
  · intro hc
    have := hT_eX_mem X i hc
    rwa [map_smul, smul_eq_mul, X.ef, if_pos rfl, mul_one] at this
  · intro hc
    rw [X.Lam_split]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, c, hc, rfl⟩)

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

theorem star_smul_dotProduct {n : ℕ} (c : D.host.E) (v w : Fin n → D.host.E) :
    star (c • v) ⬝ᵥ w = star c * (star v ⬝ᵥ w) := by
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum, mul_assoc]

theorem qX_mulVec_apply {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (y : Fin S.rank → D.host.E) (i : Fin ρ) :
    (d.qX *ᵥ y) i = star (fun r => d.e' r i) ⬝ᵥ (S.gram *ᵥ y) := by
  rw [HypDec.qX, ← Matrix.mulVec_mulVec]; rfl

theorem qY_mulVec_apply {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (y : Fin S.rank → D.host.E) (i : Fin ρ) :
    (d.qY *ᵥ y) i = star (fun r => d.e r i) ⬝ᵥ (S.gram *ᵥ y) := by
  rw [HypDec.qY, ← Matrix.mulVec_mulVec]; rfl

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem latS_rescaled_frame : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μ lam : D.host.E), GlobalTheory.Core.Mi.IdE X → B.FrameAt μ lam → IsSelfDualC (D.sp.Y 0) (latS D) ∧ (∀ y ∈ latS D, ∀ i, (fun r => (B.d.qX *ᵥ y) i * B.d.e r i) ∈ latS D ∧ (fun r => (B.d.qY *ᵥ y) i * B.d.e' r i) ∈ latS D) ∧ (∀ (i : Fin D.R.rS) (t : D.host.E), t • (fun r => B.d.e r i) ∈ latS D ↔ GlobalTheory.Core.SBesEx.scl μ lam i * t ∈ aaD D i) ∧ ∀ (i : Fin D.R.rS) (t : D.host.E), t • (fun r => B.d.e' r i) ∈ latS D ↔ (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ * t ∈ (aaD D i)⁻¹ := by
  intro D X h u ψ A B μ lam hId hF
  have hcY_smul : ∀ (c : D.host.E) (z : (VS D).V), c • GlobalTheory.Core.SBesEx.cY X h z = GlobalTheory.Core.SBesEx.cY X h (c • z) := by
    intro c z; rw [cY_eq_basY, cY_eq_basY, map_smul]
  have hcol_e : ∀ i, (fun r => B.d.e r i) = GlobalTheory.Core.SBesEx.scl μ lam i • GlobalTheory.Core.SBesEx.cY X h (X.eX i) := by
    intro i; funext r; rw [hF.e]; rfl
  have hcol_e' : ∀ i, (fun r => B.d.e' r i) =
      (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ • GlobalTheory.Core.SBesEx.cY X h (X.fY i) := by
    intro i; funext r; rw [hF.e']; rfl
  have colE : ∀ i (t : D.host.E), t • (fun r => B.d.e r i) ∈ latS D ↔ GlobalTheory.Core.SBesEx.scl μ lam i * t ∈ aaD D i := by
    intro i t
    rw [hcol_e, smul_smul, hcY_smul, cY_mem_latS X h hId, smul_eX_mem_iff, mul_comm]
  have colE' : ∀ i (t : D.host.E), t • (fun r => B.d.e' r i) ∈ latS D ↔
      (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ * t ∈ (aaD D i)⁻¹ := by
    intro i t
    rw [hcol_e', smul_smul, hcY_smul, cY_mem_latS X h hId, smul_fY_mem_iff, mul_comm]
  have hdot := @star_smul_dotProduct D (D.sp.Y 0).rank
  have hqX := qX_mulVec_apply B.d
  have hqY := qY_mulVec_apply B.d
  refine ⟨GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D (D.sp.Y 0), ?_, colE, colE'⟩
  intro y hy i
  have hY : (basY X h).equivFun.symm y ∈ (VS D).L0 := (mem_latS X h hId y).1 hy
  have hyY : y = GlobalTheory.Core.SBesEx.cY X h ((basY X h).equivFun.symm y) := by
    rw [cY_eq_basY, LinearEquiv.apply_symm_apply]
  set Y := (basY X h).equivFun.symm y
  constructor
  · have hq : (B.d.qX *ᵥ y) i = (GlobalTheory.Core.SBesEx.scl μ lam i)⁻¹ * (VS D).hT (X.fY i) Y := by
      rw [hqX, hcol_e', hdot, hyY, GlobalTheory.Core.SBesEx.cY_isom D X h hId Y (X.fY i), star_inv₀, star_star]
    show (B.d.qX *ᵥ y) i • (fun r => B.d.e r i) ∈ latS D
    rw [colE, hq]
    by_cases hs : GlobalTheory.Core.SBesEx.scl μ lam i = 0
    · rw [hs, zero_mul]; exact FractionalIdeal.mem_coe.mp (zero_mem _)
    · rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]; exact hT_fY_mem X i hY
  · have hq : (B.d.qY *ᵥ y) i = star (GlobalTheory.Core.SBesEx.scl μ lam i) * (VS D).hT (X.eX i) Y := by
      rw [hqY, hcol_e, hdot, hyY, GlobalTheory.Core.SBesEx.cY_isom D X h hId Y (X.eX i)]
    show (B.d.qY *ᵥ y) i • (fun r => B.d.e' r i) ∈ latS D
    rw [colE', hq]
    by_cases hs : star (GlobalTheory.Core.SBesEx.scl μ lam i) = 0
    · rw [hs, _root_.inv_zero, zero_mul]; exact FractionalIdeal.mem_coe.mp (zero_mem _)
    · rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]; exact hT_eX_mem X i hY

end GlobalTheory.Core.Mi.LatMatch

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch



open GlobalTheory.FinPl.FrameLat in
theorem exists_normOneAt_pr (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (c₀ : k) (hc₀ : c₀ ≠ 0) :
    ∃ c : AE D, NormOneAt p.v c ∧ p.pr c = c₀ := by
  have hf : ∀ x : k, (p.e + cA D p.e) * p.sec x = p.sec x := fun x => (idem_iff p _).1 (sec_mem_idAt p x)
  have hcf : ∀ x : k, (p.e + cA D p.e) * cA D (p.sec x) = cA D (p.sec x) :=
    fun x => (idem_iff p _).1 (csec_mem_idAt (p := p) x)
  have hee : p.e * cA D p.e = 0 := p.split.2.1
  have hce : cA D p.e * p.e = 0 := cAe_mul_e p
  have hecs : ∀ x : k, p.e * cA D (p.sec x) = 0 := by
    intro x
    rw [← e_mul_sec p x, map_mul, ← mul_assoc, hee, zero_mul]
  have hsc : ∀ x y : k, p.sec x * cA D (p.sec y) = 0 := by
    intro x y
    rw [← e_mul_sec p x, mul_comm p.e, mul_assoc, hecs, mul_zero]
  have hprc : ∀ x : k, p.pr (cA D (p.sec x)) = 0 := by
    intro x
    have h1 : p.sec (p.pr (cA D (p.sec x))) = 0 := by rw [p.sec_pr, hecs]
    have h2 := congrArg p.pr h1
    rwa [p.pr_sec, map_zero] at h2
  have hcc : ∀ z : AE D, cA D (cA D z) = z := fun z => cA_cA z
  have he1 : p.sec 1 = p.e := sec_one p
  obtain ⟨f, hfdef⟩ : ∃ f : AE D, f = p.e + cA D p.e := ⟨_, rfl⟩
  have hfm : f ∈ idAt D (· = p.v) := hfdef ▸ sum_mem_idAt p
  have hff : f * f = f := by
    have := (idem_iff p f).1 hfm; rwa [← hfdef] at this
  have hf' : ∀ x : k, f * p.sec x = p.sec x := fun x => hfdef ▸ hf x
  have hcf' : ∀ x : k, f * cA D (p.sec x) = cA D (p.sec x) := fun x => hfdef ▸ hcf x

  obtain ⟨u, hu⟩ : ∃ u : AE D, u = 1 - f := ⟨_, rfl⟩
  have huf : u * f = 0 := by rw [hu, sub_mul, one_mul, hff, sub_self]
  have hus : ∀ x : k, u * p.sec x = 0 := by intro x; rw [← hf' x, ← mul_assoc, huf, zero_mul]
  have hucs : ∀ x : k, u * cA D (p.sec x) = 0 := by intro x; rw [← hcf' x, ← mul_assoc, huf, zero_mul]
  have huu : u * u = u := by nth_rewrite 2 [hu]; rw [mul_sub, mul_one, huf, sub_zero]
  have hcu : cA D u = u := by
    rw [hu, hfdef, map_sub, map_one, map_add (f := _), hcc, add_comm]
  refine ⟨u + p.sec c₀ + cA D (p.sec c₀⁻¹), ⟨?_, ?_⟩, ?_⟩
  · have hconj : cA D (u + p.sec c₀ + cA D (p.sec c₀⁻¹)) = u + cA D (p.sec c₀) + p.sec c₀⁻¹ := by
      rw [map_add (f := _), map_add (f := _), hcu, hcc]
    show _ * cA D _ = 1
    rw [hconj]
    have e1 : p.sec c₀ * p.sec c₀⁻¹ = p.e := by rw [← sec_mul p, mul_inv_cancel₀ hc₀, he1]
    have e2 : cA D (p.sec c₀⁻¹) * cA D (p.sec c₀) = cA D p.e := by
      rw [← map_mul (cA D), ← sec_mul p, inv_mul_cancel₀ hc₀, he1]
    have s1 : p.sec c₀ * u = 0 := by rw [mul_comm (p.sec c₀) u]; exact hus _
    have s2 : cA D (p.sec c₀⁻¹) * u = 0 := by rw [mul_comm (cA D (p.sec c₀⁻¹)) u]; exact hucs _
    have s3 : cA D (p.sec c₀⁻¹) * p.sec c₀⁻¹ = 0 := by rw [mul_comm (cA D (p.sec c₀⁻¹)) (p.sec c₀⁻¹)]; exact hsc _ _
    have s4 : p.sec c₀ * cA D (p.sec c₀) = 0 := hsc _ _
    have expand : (u + p.sec c₀ + cA D (p.sec c₀⁻¹)) * (u + cA D (p.sec c₀) + p.sec c₀⁻¹)
        = u * u + u * cA D (p.sec c₀) + u * p.sec c₀⁻¹ + p.sec c₀ * u + p.sec c₀ * cA D (p.sec c₀)
          + p.sec c₀ * p.sec c₀⁻¹ + cA D (p.sec c₀⁻¹) * u + cA D (p.sec c₀⁻¹) * cA D (p.sec c₀)
          + cA D (p.sec c₀⁻¹) * p.sec c₀⁻¹ := by ring
    rw [expand, huu, hucs, hus, s1, s4, e1, s2, e2, s3, hu, hfdef]
    ring
  · have : u + p.sec c₀ + cA D (p.sec c₀⁻¹) - 1 = -f + p.sec c₀ + cA D (p.sec c₀⁻¹) := by rw [hu]; ring
    rw [this]
    refine add_mem (add_mem (neg_mem hfm) (sec_mem_idAt p _)) (csec_mem_idAt (p := p) _)
  · rw [map_add (f := _), map_add (f := _), hprc, add_zero, hu, hfdef, map_sub, map_one, map_add (f := _), ← he1, hprc, p.pr_sec, p.pr_sec]
    ring

end GlobalTheory.Core.Mi.LatMatch
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.FinPl.FrameLat



theorem sMoves_of_wComp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (L L' : Lat S) (c : AE D) (g : GA D S), IsSelfDualC S L → IsSelfDualC S L' → NormOneAt p.v c → (∀ x : Fin S.rank → k, (fun i => p.sec (x i)) ∈ latV S L (· = p.v) ↔ (fun i => p.sec ((p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x)) i)) ∈ latV S L' (· = p.v)) → SMoves S c g L L' p.v := by
  intro D k _ _ _ _ p S L L' c g hL hL' hc hw
  have hpc : p.pr c * p.pr (cA D c) = 1 := by rw [← map_mul, hc.1, map_one]
  have hGinv : ∀ x : Fin S.rank → k,
      (Formalism.L2.Theta.mt S g).map p.pr *ᵥ ((Formalism.L2.Theta.mt S g⁻¹).map p.pr *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
      show Formalism.L2.Theta.mt S g * Formalism.L2.Theta.mt S g⁻¹ = Formalism.L2.Theta.mt S (g * g⁻¹) from rfl, mul_inv_cancel,
      show Formalism.L2.Theta.mt S 1 = 1 from rfl, Matrix.map_one p.pr (map_zero _) (map_one _), Matrix.one_mulVec]
  have hsec : ∀ u : Fin S.rank → k, Formalism.L2.Theta.mt S g *ᵥ (fun i => p.sec (u i)) =
      fun i => p.sec (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) := by
    intro u
    funext i

    simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, e_mul_sec]
  have hc1 : ∀ a : k, c * p.sec a = p.sec (p.pr c * a) := by
    intro a; rw [mul_comm, sec_mul_right, mul_comm]
  have hc2 : ∀ b : k, c * cA D (p.sec b) = cA D (p.sec (p.pr (cA D c) * b)) := by
    intro b
    have h : c * cA D (p.sec b) = cA D (cA D c * p.sec b) := by rw [map_mul, cA_cA]
    rw [h, mul_comm, sec_mul_right, mul_comm]
  have hB : ∀ x z : Fin S.rank → k,
      ∑ i, ∑ j, (p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x)) i * p.pr (cA D (incA D (S.gram i j))) *
          (p.pr (cA D c) • ((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a)) *ᵥ z)) j =
        ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * z j := by
    intro x z
    rw [← pairing_inv (p := p) g x z]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) *
      (((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a)) *ᵥ z) j)) * hpc
  intro y hy
  have hyd : y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
    funext i
    simp only [Pi.add_apply, p.sec_pr]
    rw [map_mul, cA_cA, ← add_mul]
    exact ((idem_iff p _).1 (hy i)).symm
  obtain ⟨u, z, rfl⟩ : ∃ u z : Fin S.rank → k, y = (fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))) :=
    ⟨_, _, hyd⟩
  have himg : c • (Formalism.L2.Theta.mt S g *ᵥ ((fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))))) =
      (fun i => p.sec ((p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u)) i)) +
        (fun i => cA D (p.sec ((p.pr (cA D c) • ((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a)) *ᵥ z)) i))) := by
    funext i
    have h1 := congrFun (hsec u) i
    have h2 := congrFun (mt_csec (p := p) g z) i
    have h3 : (Formalism.L2.Theta.mt S g *ᵥ ((fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))))) i =
        p.sec (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) +
          cA D (p.sec ((((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a))) *ᵥ z) i)) := by
      rw [Matrix.mulVec_add, Pi.add_apply, h1, h2]
    have h4 : c * (p.sec (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) +
          cA D (p.sec ((((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a))) *ᵥ z) i))) =
        p.sec (p.pr c * ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) +
          cA D (p.sec (p.pr (cA D c) * (((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a))) *ᵥ z) i)) := by
      rw [mul_add, hc1, hc2]
    show c * (Formalism.L2.Theta.mt S g *ᵥ ((fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))))) i = _
    refine (congrArg (c * ·) h3).trans (h4.trans ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [himg, decomp hL, decomp hL']
  refine and_congr (hw u) ?_
  rw [csec_mem_iff hL, csec_mem_iff hL']
  constructor
  · intro h x' hx'
    have hx : p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ
        (p.pr (cA D c) • ((Formalism.L2.Theta.mt S g⁻¹).map p.pr *ᵥ x'))) = x' := by
      rw [Matrix.mulVec_smul, smul_smul, hpc, one_smul, hGinv]
    have hmem := (hw (p.pr (cA D c) • ((Formalism.L2.Theta.mt S g⁻¹).map p.pr *ᵥ x'))).2 (by rw [hx]; exact hx')
    rw [← hx, hB]
    exact h _ hmem
  · intro h x hx
    have h5 := h _ ((hw x).1 hx)
    rwa [hB] at h5

end GlobalTheory.Core.Mi.LatMatch

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

namespace GlobalTheory.Fam.LevelFrames


open _root_.Formalism.L2.Col in
theorem redV_eq_of_near {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    {f : Sp E n ≃ₗ[E] Sp E n} (hf : ∀ i j : Fin n, P.valuation E (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) < 1)
    {y : Sp E n} (hy : y ∈ stdAt E n P) : redV P (f y) = redV P y := by
  funext i
  have hy' := GlobalTheory.TopStep.mem_stdAt.1 hy
  have e : f y i - y i = ∑ j, (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) * y j := by
    simp only [_root_.sub_mul, Finset.sum_sub_distrib, ← Fin.ext_iff, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    congr 1

    conv_lhs => rw [pi_eq_sum_univ' y, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  have h : P.valuation E (f y i - y i) < 1 := by
    rw [e]
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' ((GlobalTheory.AtTypeExists.intAt_iff _ _).1 (hy' j))) (hf i j)
  obtain ⟨h1, h2⟩ := twRed0_of_val P h
  have h3 := reduction_add h1 (hy' i)
  rw [sub_add_cancel, h2, zero_add] at h3
  exact h3


end GlobalTheory.Fam.LevelFrames
end
