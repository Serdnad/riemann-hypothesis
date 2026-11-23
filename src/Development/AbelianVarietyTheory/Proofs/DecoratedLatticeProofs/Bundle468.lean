module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle023
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle174
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle379
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle328
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle348
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle270
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle448
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle457
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle447
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle451
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle404
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle378
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle449
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.GSuppFirst

theorem gsupp1_at : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp1 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ (x : GA D (c.V (j + 1))), SuppAt Gi.q.e (c.V (j + 1)) x → flatBF (t.sBF j (σ + 1) h) (t.om j (1, x) (comb c.ψ _ _ (Gi.eg j) F)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, SuppAt Gi.q.e (c.V (j + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  intro D c v hc hv hG t ht Gi hch j σ h F hF x hx hflat
  have hs := Gi.hs
  obtain ⟨Tm, hTm, hTmO⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Gi.k Gi.q Gi.unit _ _ (c.V j) (c.V (j + 1))
    (Gi.FY j (2 * σ + 1 + 1 + 1) (by omega)) (Gi.FY (j + 1) (2 * σ + 1 + 1) (by omega)) c.ψ Gi.S.ψ hc.std Gi.char Gi.S.cond
    (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) (Gi.latY j _ _) (Gi.latY (j + 1) _ _)).2 F hF
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Gi.k)
    (Y := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
    (Y' := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (2 * σ + 1 + 1 + 1))
  have H2 : j + (2 * σ + 1 + 1) = Gi.s := by omega
  let Φ : GlobalTheory.SplitWeil.SB _ := ⟨_, (GModel.phi_sb Gi).1 j (2 * σ + 1 + 1) H2⟩
  have hcomb : Tm Φ = comb c.ψ _ _ (Gi.eg j) F := by
    rw [← hTmO O hO]; exact (Gi.eg_is j (2 * σ + 1 + 1) H2).2 Tm hTm O Φ hO rfl
  obtain ⟨μ, hμt, hμu, hBF, -⟩ := hch
  have hW := MuUnits.withMu_eq Gi.k Gi.s D.R.k Gi.S (Fin D.R.t) μ hμt hμu
  let Fd : GlobalTheory.LocMod.Dbl (GlobalTheory.LocMod.ofSplit Gi.q) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1)) (2 * σ) :=
    { s := Gi.sc j
      s_ne := fun h0 => by have := Gi.sc_unit j; rw [h0, map_zero] at this; exact zero_ne_one this
      F₀ := Gi.FX j (by omega)
      F₁ := Gi.FX (j + 1) (by omega)
      F₂ := Gi.FX (j + 1 + 1) (by omega)
      G₀ := Gi.FY j (2 * σ + 1 + 1 + 1) (by omega)
      G₁ := Gi.FY (j + 1) (2 * σ + 1 + 1) (by omega)
      G₂ := Gi.FY (j + 1 + 1) (2 * σ + 1) (by omega)
      bes := Gi.bes j (σ + 1) h _ _
      jac := Gi.jac j (σ + 1) h _ _
      bes' := by rw [← Gi.sc_step j]; exact Gi.bes (j + 1 + 1) σ (idx_step h) _ _ }
  have hΦ : Φ.1 = ((withMu Gi.S μ hμt).T (Fin D.R.t)).Phi j (2 * σ + 1 + 1) (by omega) := (hW.1 j _ _).symm
  have hflat' : flatBF (t.sBF j (σ + 1) h) ((t.sBF j (σ + 1) h).om (1, x) (Tm Φ)) ≠ 0 := by
    rw [(ht.sBF j (σ + 1) h).1, hcomb]; exact hflat
  obtain ⟨r, hr, hrs, u, uk, hloc, huk, hxr⟩ := hG Gi.k (GlobalTheory.LocMod.ofSplit Gi.q) Gi.s D.R.k (withMu Gi.S μ hμt) (Fin D.R.t) c.ψ
    Gi.char j (2 * σ) (by omega) σ _ _ _ Fd (t.sBF j (σ + 1) h) (hBF j (σ + 1) h).1 Tm hTm Φ hΦ x hx hflat'
  refine ⟨r, hr, hrs, u, uk, hloc, ?_, hxr⟩
  rw [← (hW.2 (j + 1) (2 * σ + 1 + 1) (by omega)).1]; exact huk

end GlobalTheory.SeeSaw.GSuppFirst
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section
namespace GlobalTheory.VacComb

variable {D : D7}

theorem isThetaFunO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T 0 := {
  quasi _ _ := by simp
  level := ⟨⊤, isOpen_univ, fun _ _ _ => funext fun _ => by simp [heisO]⟩
  cont := continuous_const
  smooth _ _ _ _ _ := by simpa using (contDiff_const : ContDiff ℝ _ fun _ : Fin _ → ℝ => (0 : ℂ)) }

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : heisO ψ S T u 0 = 0 :=
  funext fun _ => by simp [heisO]

theorem isModel_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) :
    p.IsModel ψ FS FT (0 : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)) := {
  theta _ := isThetaFunO_zero ψ S T
  trans _ _ _ _ := by simp [heisO_zero]
  modul _ _ _ _ _ := by simp [heisO_zero] }

theorem model_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {Y Y' : Type} [Fintype Y]
    [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {FS : Frame k S.rank Y'} {FT : Frame k T.rank Y} {Tm}
    (hTm : p.IsModel ψ FS FT Tm) {Φ₀ : SB (Matrix Y Y' k)} (h₀ : Tm Φ₀ ≠ 0) {O : SB (Matrix Y Y' k)} (hO : O ≠ 0) :
    Tm O ≠ 0 := by
  intro h
  have := (GlobalTheory.T.localSchrodingerModel_uniq_transport_exists D k p Y Y' S T FS FT ψ hψ).1 Tm 0 hTm (isModel_zero p ψ FS FT) O hO (by simpa using h)
  exact h₀ (by rw [this]; rfl)

end GlobalTheory.VacComb

namespace GlobalTheory.VacComb

theorem exists_adapted_frame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (M : GlobalTheory.FinPl.Lat S), IsSelfDualC S M → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y), ∃ G : Frame k S.rank Y, ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((G.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S M (· = q.v) := by
  intro D k _ _ _ _ q S M hM Y _ _ F
  obtain ⟨gl, h1, h2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D k q S Y F.β F.γ F.βγ F.γβ
  let α : GlobalTheory.FinPl.Frame q S Y := ⟨F.β, F.γ, F.βγ, F.γβ, gl, h1, h2⟩
  obtain ⟨Λ, hΛ, hα, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k q S Y α M hM
  have : Λ.IsFullLattice k := by
    refine { toIsLattice := hΛ, span_eq_top := eq_top_iff.mpr fun x _ => ?_ }
    obtain ⟨m, s, c, hs, hc, -⟩ := GlobalTheory.FinPl.FrameLat.exists_gen (p := q) hM
    have hx := congrArg (F.γ *ᵥ ·) (hc (F.β *ᵥ x))
    simp only [Matrix.mulVec_mulVec, F.γβ, Matrix.one_mulVec, Matrix.mulVec_sum,
      Matrix.mulVec_smul] at hx
    rw [hx]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    apply (hα _).2
    change (fun i => q.sec ((F.β *ᵥ (F.γ *ᵥ fun a => q.pr (incA D (s l a)))) i)) ∈ _
    rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
    exact GlobalTheory.FinPl.FrameLat.sec_inc_mem (p := q) (hs l)
  obtain ⟨g, hg⟩ := GlobalTheory.LatPair.exists_smul_lat (GlobalTheory.LatPair.stdLat k Y) Λ
  have hgg : g.1 * (g⁻¹).1 = 1 := by rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hgg' : (g⁻¹).1 * g.1 = 1 := by rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  refine ⟨⟨F.β * g.1, (g⁻¹).1 * F.γ, ?_, ?_⟩, fun y => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc g.1, hgg, Matrix.one_mul, F.βγ]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, hgg']
  · have e1 : (∀ i, y i ∈ 𝒪[k]) ↔ g • y ∈ Λ := by
      rw [← hg, GlobalTheory.LatPair.mem_smul_iff, inv_smul_smul, GlobalTheory.LatPair.mem_stdLat]
    rw [e1, hα (g • y)]
    show _ ∈ _ ↔ _ ∈ _
    have e2 : F.β *ᵥ (g • y) = (F.β * g.1) *ᵥ y := by
      rw [← Matrix.mulVec_mulVec]; rfl
    change (fun i => q.sec ((F.β *ᵥ (g • y)) i)) ∈ _ ↔ _
    rw [e2]

end GlobalTheory.VacComb

namespace GlobalTheory.VacComb

variable {D : D7}

theorem down_up {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : Matrix Y Y' k) : p.down FS FT (p.up FS FT x) = x := by
  unfold Place.down Place.up
  have h : ((FT.β * x * FS.γ).map p.ι : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π = FT.β * x * FS.γ := by
    ext i j; simp [p.π_ι]
  rw [h, Matrix.mul_assoc FT.β, ← Matrix.mul_assoc FT.γ, FT.γβ, Matrix.one_mul, Matrix.mul_assoc, FS.γβ, Matrix.mul_one]

theorem exists_model_vac : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ G, GlobalTheory.FinPl.Vac ψ S T M M' (· = q.v) G → ∃ Tm, (ofSplit q).IsModel ψ FS FT Tm ∧ ∀ Φ₀ : SB (Matrix Y Y' k), Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) (· = q.v)} (fun _ => 1) → Tm Φ₀ = G := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT ψ hψ M M' hM hM' G hG
  obtain ⟨GS, hGS⟩ := exists_adapted_frame D k q S M hM Y' FS
  obtain ⟨GT, hGT⟩ := exists_adapted_frame D k q T M' hM' Y FT
  obtain ⟨ψk, hch, hcond⟩ := GlobalTheory.SplitWeilChar.weil_char_conductor_one D k q ψ hψ hU
  obtain ⟨Tm', hTm', hO'⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D k q hU Y Y' S T GS GT ψ ψk hψ hch hcond M M' hM hM' hGS hGT).2 G hG
  obtain ⟨Tm, hTm, hrel⟩ := GlobalTheory.LocMod.Place.exists_isModel_chg D k (ofSplit q) Y Y' S T GS GT Y Y' FS FT ψ Tm' hTm'
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  refine ⟨Tm, hTm, fun Φ₀ h₀ => ?_⟩
  rw [hrel O Φ₀ ?_, hO' O hO]
  intro x
  have hup : (ofSplit q).up FS FT (FT.γ * GT.β * x * (GS.γ * FS.β)) = (ofSplit q).up GS GT x :=
    GlobalTheory.LocMod.Place.up_chg (ofSplit q) GS GT FS FT x
  rw [hO, h₀]
  by_cases hx : ∀ r s, x r s ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (show x ∈ {x : Matrix Y Y' k | ∀ r s, x r s ∈ 𝒪[k]} from hx), Set.indicator_of_mem]
    show (ofSplit q).up FS FT (FT.γ * GT.β * x * (GS.γ * FS.β)) ∈ latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) (· = q.v)
    rw [hup]
    exact GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D k q hU Y Y' S T GS GT M M' hM hM' hGS hGT x hx
  · rw [Set.indicator_of_notMem (show x ∉ {x : Matrix Y Y' k | ∀ r s, x r s ∈ 𝒪[k]} from hx), Set.indicator_of_notMem]
    intro hmem
    change (ofSplit q).up FS FT (FT.γ * GT.β * x * (GS.γ * FS.β)) ∈ latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) (· = q.v) at hmem
    rw [hup] at hmem
    obtain ⟨x', hx', he⟩ := GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D k q hU Y Y' S T GS GT M M' hM hM' hGS hGT _ hmem
      (GlobalTheory.LocMod.Witness.up_half (ofSplit q) GS GT x)
    have : x = x' := by rw [← down_up (ofSplit q) GS GT x, he, down_up]
    exact hx (this ▸ hx')

end GlobalTheory.VacComb

namespace GlobalTheory.VacComb

variable {D : D7}

theorem comb_o_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M')
    (L : LocPl ψ S T M M') {G : WO S T → ℂ} (hG : GlobalTheory.FinPl.Vac ψ S T M M' (· = L.q.v) G) (hG0 : G ≠ 0) :
    comb ψ S T L.o G ≠ 0 := by
  obtain ⟨Tm, hTm, hTG⟩ := exists_model_vac D L.k L.q L.unit L.Y L.Y' S T L.FS L.FT ψ hψ M M' hM hM' G hG
  obtain ⟨Φ₀, h₀⟩ := GlobalTheory.SeeSaw.LocPlModel.exists_latInd L.q L.unit L.FS L.FT hM hM'
  obtain ⟨O, hO, hO0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := L.k) (Y := L.Y) (Y' := L.Y')
  have hO' : O ≠ 0 := by rintro rfl; simp at hO0
  rw [← hTG Φ₀ h₀, ← L.o_is Tm hTm Φ₀ O hO h₀]
  exact model_ne_zero _ hψ hTm (by rwa [hTG Φ₀ h₀]) hO'

theorem combAt_o {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (L : LocPl ψ S T M M') : GlobalTheory.FinPl.CombAt (· = L.q.v) L.o := fun u hu r c =>
  (GlobalTheory.FinPl.FrameLat.idem_iff L.q _).2 (L.o_at u hu r c)

theorem foldr_comb_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ F, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) F → F ≠ 0 → (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F ≠ 0 := by
  intro D ψ hψ S T M M' hM hM' n L hL F hF hF0
  have hI := fun P P' hd => GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D ψ hψ S T P P' hd
  let g : Fin n → (WO S T → ℂ) → (WO S T → ℂ) := fun i f => comb ψ S T (L i).o f
  have key : ∀ l : List (Fin n), l.Nodup → l.foldr g F ≠ 0 ∧
      ∀ j, j ∉ l → GlobalTheory.FinPl.Vac ψ S T M M' (· = (L j).q.v) (l.foldr g F) := by
    intro l
    induction l with
    | nil =>
      intro _
      exact ⟨hF0, fun j _ => GlobalTheory.GSuppComb.vac_mono (fun _ _ => trivial) hF⟩
    | cons a l ih =>
      intro hl
      obtain ⟨ha, hl'⟩ := List.nodup_cons.1 hl
      obtain ⟨h0, hv⟩ := ih hl'
      have hdisj : ∀ j, j ≠ a → ∀ p, p = (L a).q.v → ¬ p = (L j).q.v := fun j hj p hp hq =>
        hj (hL (hq.symm.trans hp))
      refine ⟨comb_o_ne_zero hψ hM hM' (L a) (hv a ha) h0, fun j hj => ?_⟩
      have hja : j ≠ a := fun h => hj (h ▸ List.mem_cons_self)
      have hjl : j ∉ l := fun h => hj (List.mem_cons_of_mem _ h)
      exact ((hI _ _ (hdisj j hja)).2.1 _ (combAt_o (L a))).2 M M' _ (hv j hjl)
  exact (key _ (List.nodup_finRange n)).1

end GlobalTheory.VacComb
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.FinPl.idV_principal_at : ∀ (D : D7) (v : Pl D) (𝔞 : FI D), 𝔞 ≠ 0 → ∃ g ∈ idV 𝔞 v, ∃ g' ∈ idAt D (· = v), (∀ s ∈ idAt D (· = v), g' * g * s = s) ∧ ∀ s, s ∈ idV 𝔞 v ↔ s ∈ idAt D (· = v) ∧ g' * s ∈ intAt D (· = v) := by
  intro D v 𝔞 h𝔞
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.T.fractionalIdealCompletion_locally_principal D v 𝔞 h𝔞
  obtain ⟨ε, hεε, -, hεint, hεid, -⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).1
  have hεI : ε ∈ idAt D (· = v) := hεint.1
  have hxx : incA D x⁻¹ * incA D x = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  refine ⟨incA D x * ε, ?_, incA D x⁻¹ * ε, Ideal.mul_mem_left _ _ hεI, ?_, ?_⟩
  · rw [hx]
    refine ⟨?_, Ideal.mul_mem_left _ _ hεI⟩
    rw [← mul_assoc, hxx, one_mul]; exact hεint
  · intro s hs
    have : incA D x⁻¹ * ε * (incA D x * ε) = ε * ε := by
      calc incA D x⁻¹ * ε * (incA D x * ε) = (incA D x⁻¹ * incA D x) * (ε * ε) := by ring
        _ = ε * ε := by rw [hxx, one_mul]
    rw [this, hεε]; exact (hεid s).1 hs
  · intro s
    rw [hx]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [mul_assoc, (hεid s).1 h2]; exact h1
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      rw [mul_assoc, (hεid s).1 h2] at h1; exact h1
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

namespace GlobalTheory.QPl

variable {D : D7} {c : Comm D} {v : VCom c} {t : Tup c}

def QFam.pinTup (F : QFam v t) (sc cT : ℕ → ℂ) : VTup t where
  Q := Finset.univ.image fun i => (F.Q i).q.v
  sc := sc
  eQ := fun j => if j + 1 < D.R.m then aconv (List.ofFn fun i => (F.Q i).eL j) else 0
  eQT := fun j h => aconv (List.ofFn fun i => (F.Q i).eT j h)
  dQ := fun j α γ => if j < D.R.m then
    (∏ i, (F.Q i).wt j (F.eqv j α i)) • aconv (List.ofFn fun i => (F.Q i).dL j (F.eqv j α i) (F.eqv (j + 1) γ i)) else 0
  ε := fun j α => if (∃ ρ, j + 2 * ρ + 2 = D.R.m) ∨ j = 0 then
    (∏ i, (F.Q i).wt j (F.eqv j α i)) • conv (List.ofFn fun i => (F.Q i).εL j (F.eqv j α i)) else 0
  εT := fun n _ β => Finsupp.single 1 (∏ i, (F.Q i).wt n (F.eqv n β i))
  FX := fun _ _ => Set.univ
  FY := fun j => {f | ∀ i, (F.Q i).Typed j f}
  FT := Set.univ
  cQ := fun j => ∏ i, (((F.Q i).idx (j + 1) : ℂ) * ((F.Q i).idx (j + 1 + 1) : ℂ))⁻¹
  cT := cT

end GlobalTheory.QPl

namespace GlobalTheory.Fam

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}

variable (a : GeoAll W u) (J : ∀ t, QJ a t)

end GlobalTheory.Fam

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

namespace GlobalTheory.QPl

theorem exchange_posOne_last : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m) (s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h)), s₁.χW = χ Q.s → ∀ α (Tm : SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k) →ₗ[ℂ] (WO (c.V Q.s) (c.V (Q.s + 1)) → ℂ)), (ofSplit Q.q).IsModel c.ψ (Q.FY Q.s (0 + 1) (by omega)) (Q.FY (Q.s + 1) 0 (by omega)) Tm → ∀ Φ Φα : SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k), Φ.1 = Q.T.Phi Q.s 0 rfl → Φα.1 = om (Q.T.mu (Q.s + 1)) (Q.rep Q.s 0 rfl α) 1 (Q.T.Phi Q.s 0 rfl) → ∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (Tm Φ) = Tm Φα := by
  intro D c v χ Q _ h s₁ hχ α Tm hTm Φ Φα hΦ hΦα
  obtain ⟨⟨ρ', hρ'⟩, hsm⟩ := GlobalTheory.PosOne.isSrc_exists_isSmoothRep Q.k (Q.X Q.s ⊕ Fin (0 + 1)) (Q.X (Q.s + 1) ⊕ Fin 0)
    (Q.T.mu (Q.s + 1)) (Q.mu Q.s (by omega)).2
  have hsmooth := hsm ρ' hρ'
  obtain ⟨e, he, heL⟩ := Q.εL_at Q.s 0 h 0 rfl α
  obtain ⟨μS, hμS⟩ := GlobalTheory.LocMod.Witness.exists_isComp (ofSplit Q.q) s₁.χV
  have hμT : (ofSplit Q.q).IsComp s₁.χW (Q.T.mu (Q.s + 1))⁻¹ := by
    intro x a hxa
    have := (Q.mu Q.s (by omega)).1 x a hxa
    rw [hχ, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, this]
    simp
  have hloc1 : (ofSplit Q.q).IsLoc (Q.FY (Q.s + 1) 0 (by omega)) 1 1 := by
    have := Q.gl_loc (Q.s + 1) 0 (by omega) 1
    rwa [map_one] at this
  have key : ∀ g, s₁.om (Q.gl Q.s (0 + 1) (by omega) g, 1) (Tm Φ) = Tm (ρ' g Φ) := by
    intro g
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) c.ψ _ _ s₁.χV s₁.χW s₁.om s₁.weil μS _ hμS hμT _ _ _ _ Tm hTm
      _ g 1 1 (Q.gl_loc Q.s (0 + 1) (by omega) g) hloc1 Φ (ρ' g Φ) ?_
    rw [hρ']
    funext x
    have hu : (((μS * Q.T.mu (Q.s + 1)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((μS⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        = ((Q.T.mu (Q.s + 1) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
      rw [← Units.val_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_comm (μS _), mul_assoc, mul_inv_cancel, mul_one]
    simp only [om, Pi.smul_apply, smul_eq_mul, map_one, inv_one, Units.val_one, inv_inv]
    rw [← hu]
    ring
  have hN : ∀ g ∈ N Q.k (Q.X Q.s) (0 + 1) (0 + 1), g = 1 := by
    intro g hg
    have hle : N Q.k (Q.X Q.s) (0 + 1) (0 + 1) ≤ ⊥ := by
      refine (Subgroup.closure_le _).2 fun g' hg' => ?_
      rw [SetLike.mem_coe, Subgroup.mem_bot]
      ext r s
      refine hg' r s ?_
      rcases r with r | r <;> rcases s with s | s <;> simp [GlobalTheory.RootEx.lev, Fin.val_eq_zero]
    exact Subgroup.mem_bot.1 (hle hg)
  let lx : Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k →
      (SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k) →ₗ[ℂ] ℂ) :=
    fun x => (LinearMap.proj x).comp (SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k)).subtype
  have hsum : Φα = e.sum (fun g a => a • ρ' g Φ) := by
    apply Subtype.ext
    funext x
    have h1 := he _ ρ' hsmooth (lx x) (fun g hg w => by
        rw [hN g hg]
        simp [GlobalTheory.RootEx.simpleSum]) Φ (fun j => by
        apply Subtype.ext
        rw [hρ', Submodule.coe_smul, hΦ, (Q.laws.1 Q.s 0 rfl).1 j])
    have h2 : (Φα : Matrix _ _ _ → ℂ) x = lx x (ρ' (Q.rep Q.s 0 rfl α) Φ) := by
      simp only [lx, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply, hΦα]
      rw [hρ', hΦ]
    have h3 : ((e.sum fun g a => a • ρ' g Φ : SB _) : Matrix _ _ _ → ℂ) x = lx x (e.sum fun g a => a • ρ' g Φ) := rfl
    rw [h2, h3, map_finsuppSum]
    refine h1.trans ?_
    simp [GlobalTheory.PosOne.comb, map_smul]
  rw [heL]
  show (Finsupp.mapDomain _ e).sum (fun g a => a • s₁.om (g, 1) (Tm Φ)) = Tm Φα
  rw [Finsupp.sum_mapDomain_index (h := fun g (a : ℂ) => a • s₁.om (g, 1) (Tm Φ)) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  rw [hsum, map_finsuppSum]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [map_smul, key]

end GlobalTheory.QPl
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.inverseDifferentPow_completion_trivial_at_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k), p.UnitAA → ∀ (n : ℕ) (a : AE D), (a ∈ idV (dI D ^ n) p.v ↔ a ∈ intAt D (· = p.v)) ∧ (a ∈ idV (dI D ^ n)⁻¹ p.v ↔ a ∈ intAt D (· = p.v)) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit | exact GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit | (intros; apply GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainStep_vector_twoLevel_law : ∀ D : D7, ForStep D fun _ _ s s' p => VecLaw p.ω (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) (Lev.levG s'.V s'.β s'.L) (fun κ => (Lev.levChi s'.V s'.β s'.L κ)⁻¹) p.f := by
  first | exact @GlobalTheory.ChainOnto.StepVecLawBoth.vecLaw | exact GlobalTheory.ChainOnto.StepVecLawBoth.vecLaw | (intros; apply GlobalTheory.ChainOnto.StepVecLawBoth.vecLaw <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_combination_rebase_vacuumLattices_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M N : GlobalTheory.FinPl.Lat S) (M' N' : GlobalTheory.FinPl.Lat T) (Q : Finset (GlobalTheory.FinPl.Pl D)), IsSelfDualC S M → IsSelfDualC S N → IsSelfDualC T M' → IsSelfDualC T N' → (∀ p ∈ Q, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p)) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p))) → (∀ p, p ∉ Q → GlobalTheory.FinPl.latV S M (· = p) = GlobalTheory.FinPl.latV S N (· = p) ∧ GlobalTheory.FinPl.latV T M' (· = p) = GlobalTheory.FinPl.latV T N' (· = p)) → ∃ o : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· ∈ Q) o ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) f → GlobalTheory.FinPl.Vac ψ S T N N' (fun _ => True) (comb ψ S T o f) ∧ (f ≠ 0 → comb ψ S T o f ≠ 0) := by
  first | exact @GlobalTheory.VacRebase.rebase_vac | exact GlobalTheory.VacRebase.rebase_vac | (intros; apply GlobalTheory.VacRebase.rebase_vac <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.supportedTranslatesCombination_commutes_schrodinger : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (Pg : Finset (Pl D.host.E)) (P' : GlobalTheory.FinPl.Pl D → Prop), IsIdemSum e Pg → (∀ PP ∈ Pg, ¬ P' ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) → ∀ (d : WO S T →₀ ℂ), GlobalTheory.FinPl.CombAt P' d → ∀ (f₁ : WO S T → ℂ) (T₁ T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₁ T₁ → (∀ Φ, T₂ Φ = comb ψ S T d (T₁ Φ)) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (comb ψ S T d f₁) T₂ := by
  first | exact @GlobalTheory.PlaceModelComb.main | exact GlobalTheory.PlaceModelComb.main | (intros; apply GlobalTheory.PlaceModelComb.main <;> assumption)
end
