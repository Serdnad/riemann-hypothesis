module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle497
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle284
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle285
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle476
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle495
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle352
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle311
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle324
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle498
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TorusEntryRatioIntegralAtUnramifiedPlace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw.LevIntProof

variable {D : D7}

theorem pet_tr {c : Com D} {s : PiLocalization₂ D} (hc : c.Is) {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (hM : IsMet c s ipD ip) (u₁ u₂ : s.CC c) (v : s.M.Vec) (b : GinfC s.V)
    (κ : GA D s.V) (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v)) =
      Lev.levChi s.V s.β s.L κ * ip u₁ u₂ *
        ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  have hmem := (mem_multT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) (u₁ : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))).1 u₁.2
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
  obtain ⟨w, hw, hU⟩ := GlobalTheory.ChainOnto.mult_equiv_real D c.θ s.V s.par s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) hc.inf v b
  have hUw := hU _ hmem
  have ev : ∀ x : s.M.Vec, PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.lift.symm (u₁ : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) x := by
    intro x; simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
  have key : rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) =
      Lev.levChi s.V s.β s.L κ • PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ w) := by
    funext g
    rw [ev, ev, hUw]
    simp only [rTr, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc]
    exact hmap.lev v κ hκ (g * (b : GA D s.V))
  have hsch : s.pet (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ w)) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v)) =
      ip u₁ u₂ * ipD (PiTensorProduct.tprod ℂ w) (PiTensorProduct.tprod ℂ v) := hM.schur u₁ u₂ _ _
  rw [key, GlobalTheory.ChainOnto.PetCoef.pet_smul_left, hsch, hM.pure w v]
  simp only [hw, mul_assoc]

theorem leftInv_conj {V : HSp D} {F : GA D V → ℂ} (h : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) F) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (fun x => conj (F x)) :=
  fun γ hγ x => by simp only [h γ hγ x]

theorem rcoef_conj {s : PiLocalization₂ D} (hh : s.ν.IsHaarMeasure) (hf : IsFundamentalDomain (GQ s.V) s.fd s.ν)
    {F₁ F₂ : GA D s.V → ℂ} (h₁ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) F₁) (h₂ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) F₂) (g : GA D s.V) :
    GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F₁ x)) (fun x => conj (F₂ x)) g = conj (s.pet (rTr s.V g F₁) F₂) := by
  haveI := hh
  have hl : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) (rTr s.V g fun x => conj (F₁ x)) := (leftInv_conj h₁).mul_right g
  show GlobalTheory.AutomorphicL2Unitary.pet (GQ s.V) s.ν (rTr s.V g fun x => conj (F₁ x)) (fun x => conj (F₂ x)) = _
  rw [GlobalTheory.AutomorphicL2Unitary.pet_eq hf hl (leftInv_conj h₂)]
  show _ = conj (∫ x in s.fd, rTr s.V g F₁ x * starRingEnd ℂ (F₂ x) ∂s.ν)
  rw [← integral_conj]
  congr 1
  funext x
  simp [rTr]

theorem leftInv_val {c : Com D} {s : PiLocalization₂ D} (u : s.CC c) (v : s.M.Vec) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) := by
  have hmem := (mem_multT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))).1 u.2
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
  have e : PiLocalization₂.val u (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v := by
    simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
  rw [e]
  exact GlobalTheory.AutomorphicL2Unitary.leftInv_of_isAutFun (hmap.aut v).toIsAutFun

end GlobalTheory.ChainTw.LevIntProof

namespace GlobalTheory.ChainTw.LevIntProof

variable {D : D7}

theorem hgtL_real_lev {s : PiLocalization₂ D} (hsd : IsSelfDualC s.V s.Λ) {a : GL (Fin s.V.rank) (AE D)}
    (hmaj : GlobalTheory.Doubling.IsMaj s.V a) (b : GinfC s.V) (κ : GA D s.V) (hκf : κ ∈ GfC s.V)
    (hpr : ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) :
    GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a ((b : GA D s.V) * κ) = GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V) ∧
      ((GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V) : ℝ)) =
        ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V)) := by
  obtain ⟨_, h2, h3⟩ := GlobalTheory.ChainOnto.hgt_one_components D s.V s.Λ hsd
  obtain ⟨_, _, hoff⟩ := GlobalTheory.Core.Rk.IP.hgtL_props D s.V s.Λ a hsd hmaj
  have hb : (b : GA D s.V) ∈ GlobalTheory.Core.Rk.IP.openOff s.V s.Λ ∅ := fun v _ => by
    rw [h3 b b.2 v]; exact one_mem _
  have hbk : (b : GA D s.V) * κ ∈ GlobalTheory.Core.Rk.IP.openOff s.V s.Λ ∅ := fun v _ => by
    rw [map_mul, h3 b b.2 v, one_mul]; exact hpr v
  have e1 := (hoff ∅).2 _ hb
  have e2 := (hoff ∅).2 _ hbk
  simp only [Finset.prod_empty, mul_one] at e1 e2
  have hA : ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w ((b : GA D s.V) * κ) =
      GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V) := fun w => by
    rw [map_mul, h2 κ hκf w, mul_one]
  simp only [hA] at e2
  exact ⟨NNReal.coe_injective (e2.trans e1.symm), e1⟩

theorem flatInt_mul_lev {c : Com D} {s s' : PiLocalization₂ D} (hc : c.Is) (hh : s.ν.IsHaarMeasure)
    (hf : IsFundamentalDomain (GQ s.V) s.fd s.ν) (hsd : IsSelfDualC s.V s.Λ) {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (hM : IsMet c s ipD ip) (p : Step c s s') (m : Measure (WO s.V s'.V))
    (X : Set (WO s.V s'.V)) {a : GL (Fin s.V.rank) (AE D)} (hmaj : GlobalTheory.Doubling.IsMaj s.V a)
    (φ : PolF D s'.V.rank s.V.rank) (v : s.M.Vec)
    (hlaw : ∀ κ ∈ Lev.levG s.V s.β s.L, (p.ω (κ, 1)) (p.pt φ) = Lev.levChi s.V s.β s.L κ • p.pt φ)
    (hstab : ∀ κ ∈ Lev.levG s.V s.β s.L, ‖Lev.levChi s.V s.β s.L κ‖ = 1 ∧
      ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v)
    (u₁ u₂ : s.CC c) (z : ℂ) (b : GinfC s.V) (κ : GA D s.V) (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    flatInt p m X a φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v)) z
        ((b : GA D s.V) * κ) =
      conj (ip u₁ u₂) * (zReal p m X φ v b *
        GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) (z - GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V)) := by
  have hκf : κ ∈ GfC s.V := (Subgroup.mem_inf.mp hκ).1
  obtain ⟨hn, hpr⟩ := hstab κ hκ
  have hn' : Lev.levChi s.V s.β s.L κ * conj (Lev.levChi s.V s.β s.L κ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; norm_num
  unfold flatInt GlobalTheory.Core.Rk.IP.integrand
  rw [show GlobalTheory.Core.Rk.IP.wcoef p.ω m X (p.pt φ) (p.pt φ) ((b : GA D s.V) * κ) =
      coefW p.ω m X (p.pt φ) ((b : GA D s.V) * κ) from rfl,
    GlobalTheory.ChainOnto.ZetaNeProof.coefW_mul_lev p m X φ hlaw _ κ hκ,
    rcoef_conj hh hf (leftInv_val u₁ v) (leftInv_val u₂ v), pet_tr hc hM u₁ u₂ v b κ hκ,
    (hgtL_real_lev hsd hmaj b κ hκf hpr).1]
  unfold zReal
  simp only [map_mul]
  linear_combination (coefW p.ω m X (p.pt φ) (b : GA D s.V) *
    GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) (z - GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V) *
    conj (ip u₁ u₂) *
    conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) * hn'

theorem levInt : ∀ D : D7, LevelLawQ D → LevInt D := by
  intro D hLaw hng c w hw k hk s s' hs hs' p hp ipD ip hM m X hcov mR hmR φ v hRC a hmaj
  have hc : c.Is := hw.com
  obtain ⟨hr, _, hfl⟩ := id hs
  obtain ⟨hr', _, hfl'⟩ := id hs'
  have hrk : s.V.rank = D.R.rankY k := hfl.rank
  have hrk' : s'.V.rank = D.R.rankY (k + 1) := hfl'.rank
  have hsz : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V = (D.R.t : ℂ) / 2 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero
    rw [hrk, hrk']
    simp only [Formalism.BasicNotions.Ranks.rankY]
    push_cast; ring
  have hh : s.ν.IsHaarMeasure := hfl.haar
  have hfd : IsFundamentalDomain (GQ s.V) s.fd s.ν := hfl.fund
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  obtain ⟨_, _, _, _, hstab, _⟩ := GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D c w hw k hk.le s hs
  have hlaw := (hLaw hng c w hw k hk s s' hs hs' p hp φ).1
  obtain ⟨_, hI⟩ := hRC
  obtain ⟨s₁, hs₁, hI₁⟩ := hI a hmaj
  have hmj : GlobalTheory.Doubling.IsMaj s.V a := hmaj.1
  obtain ⟨hcont, hpos, _⟩ := GlobalTheory.Core.Rk.IP.hgtL_props D s.V s.Λ a hsd hmj
  have hreal : ∀ b : GinfC s.V, ((GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V) : ℝ)) =
      ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V)) := fun b =>
    (hgtL_real_lev hsd hmj b 1 (one_mem _) fun v => by rw [map_one]; exact one_mem _).2
  have hint : ∀ z : ℝ, s₁ ≤ z → Integrable (fun b : GinfC s.V => zReal p m X φ v b *
      GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) ((z : ℂ) - (D.R.t : ℂ) / 2)) mR := by
    intro z hz
    have h0 : Integrable (fun b : GinfC s.V => zReal p m X φ v b *
        GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) ((s₁ : ℂ) - (D.R.t : ℂ) / 2)) mR := by
      refine hI₁.congr (ae_of_all _ fun b => ?_)
      simp only [GlobalTheory.Doubling.npow, hreal b]
    have hm : AEStronglyMeasurable (fun b : GinfC s.V =>
        GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) ((z : ℂ) - s₁)) mR := by
      have hme : Measurable fun b : GinfC s.V =>
          ((GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V) : ℝ) : ℂ) ^ ((z : ℂ) - s₁) :=
        (Complex.measurable_ofReal.comp
          (NNReal.continuous_coe.comp (hcont.comp continuous_subtype_val)).measurable).pow_const _
      exact hme.aestronglyMeasurable
    have hb : ∀ᵐ b : GinfC s.V ∂mR, ‖GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) ((z : ℂ) - s₁)‖ ≤ 1 :=
      ae_of_all _ fun b => by
        obtain ⟨h1, h2⟩ := hpos (b : GA D s.V)
        unfold GlobalTheory.Doubling.npow
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr h1)]
        apply Real.rpow_le_one (NNReal.coe_nonneg _) (by exact_mod_cast h2)
        simp only [Complex.sub_re, Complex.ofReal_re]
        linarith
    refine (h0.mul_bdd hm hb).congr (ae_of_all _ fun b => ?_)
    simp only
    rw [mul_assoc, ← GlobalTheory.Doubling.npow_add (hpos _).1]
    congr 2
    ring
  refine ⟨s₁, hs₁, fun u₁ u₂ => ?_⟩
  have hF : ∀ z : ℝ, s₁ ≤ z →
      IntegrableOn (flatInt p m X a φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v)) z)
        (levSet s) s.ν ∧
      ∫ g in levSet s, flatInt p m X a φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v))
        z g ∂s.ν = ∫ b, conj (ip u₁ u₂) * (zReal p m X φ v b *
          GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) ((z : ℂ) - (D.R.t : ℂ) / 2)) ∂mR := by
    intro z hz
    refine hmR.2 _ _ ((hint z hz).const_mul _) fun b κ hκ => ?_
    rw [flatInt_mul_lev hc hh hfd hsd hM p m X hmj φ v hlaw hstab u₁ u₂ _ b κ hκ, hsz]
  refine ⟨fun z hz => (hF z hz).1, ?_⟩
  rw [(hF ((D.R.t : ℝ) / 2) hs₁.le).2, integral_const_mul, mul_comm]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun b => ?_)
  simp only
  rw [show (((D.R.t : ℝ) / 2 : ℝ) : ℂ) - (D.R.t : ℂ) / 2 = 0 by push_cast; ring, GlobalTheory.Doubling.npow_zero, mul_one]

end GlobalTheory.ChainTw.LevIntProof

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.ContrKernel

variable {D : D7}

theorem continuous_ofAdj (S T : HSp D) : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T) := by
  have h : Continuous fun z : Mx D S.rank T.rank => giA T ⬝ (adj z ⬝ gA S) :=
    continuous_const.matrix_mul
      ((GlobalTheory.MixModel.continuous_adj (D := D) (m := S.rank) (n := T.rank)).matrix_mul continuous_const)
  exact h.const_smul (incA D (-D.host.xi0⁻¹))

theorem continuous_kappa {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ')
    (S : HSp D) : Continuous (l.κ S) :=
  (continuous_ofAdj B.L S).comp (continuous_const.matrix_mul continuous_id)

theorem integrable_of_cont_bdd {m n : ℕ} (μ : Measure (Mx D m n)) [IsFiniteMeasure μ] (f : Mx D m n → ℂ)
    (hc : Continuous f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) : Integrable f μ := by
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem symm_resS_symm {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (u : WO B T) (v : WO A T) :
    (o.symm.resS T).symm (u, v) = (o.resS T).symm (v, u) := by
  rw [OrthDec.resS_symm_apply, OrthDec.resS_symm_apply, add_comm]; rfl

theorem symm_resT_symm {T A B : HSp D} (o : OrthDec T A B) (S : HSp D) (u : WO S B) (v : WO S A) :
    (o.symm.resT S).symm (u, v) = (o.resT S).symm (v, u) := by
  rw [OrthDec.resT_symm_apply, OrthDec.resT_symm_apply, add_comm]; rfl

theorem kernel_doubleStep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (χA χA' χz : ((AE D)ˣ →* Circle)) (oma : Om B.A J.W₀) (omz : Om B.L J.W₀) (omb : Om J.W₀ B'.A) (omz' : Om J.W₀ B'.L), s₁.χV = χA * χz → s₂.χW = χA' * χz → IsWeilDatumO ψ B.A J.W₀ χA s₁.χW oma → IsWeilDatumO ψ B.L J.W₀ χz s₁.χW omz → IsWeilDatumO ψ J.W₀ B'.A s₂.χV χA' omb → IsWeilDatumO ψ J.W₀ B'.L s₂.χV χz omz' → ∀ (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ₁ → IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂ → ∀ h₀ h₁ h₂, ∫ w in vL.𝓕, s₂.om₀ (h₁, B'.o.emb (h₂, 1)) Ξ₂ ((B'.o.resT J.W₀).symm (0, w)) * s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) ∂vL.μ = omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) 0 := by
  intro D ψ σ B J B' s₁ s₂ l vL χA χA' χz oma omz omb omz' hV hW hoa hoz hob hoz' Ξ₁ Ξ₂ hΞ₁ hΞ₂ h₀ h₁ h₂
  have hstd : IsStdChar D ψ (-1) := hoa.std
  have TS := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hstd B.V₀ B.A B.L B.o J.W₀
  have TT := GlobalTheory.T.thetaTensorRule_targetOrthogonalSum D ψ hstd B'.V₀ B'.A B'.L B'.o J.W₀
  have hw₁ : IsWeilDatumO ψ B.V₀ J.W₀ (χA * χz) s₁.χW s₁.om₀ := hV ▸ s₁.weil₀
  have hw₂ : IsWeilDatumO ψ J.W₀ B'.V₀ s₂.χV (χA' * χz) s₂.om₀ := hW ▸ s₂.weil₀
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
  haveI : BorelSpace (WO J.W₀ B'.L) := ⟨rfl⟩
  haveI : BorelSpace (WO B.L J.W₀) := ⟨rfl⟩

  have hS₁ : ∀ u, IsThetaFunO ψ B.L J.W₀ fun z => Ξ₁ ((B.o.resS J.W₀).symm (u, z)) := (TS.slice_theta Ξ₁ hΞ₁).2
  have hS₂ : ∀ v, IsThetaFunO ψ J.W₀ B'.L fun w => Ξ₂ ((B'.o.resT J.W₀).symm (v, w)) := (TT.slice_theta Ξ₂ hΞ₂).2

  obtain ⟨Hf, hHf⟩ : ∃ Hf : WO B.A J.W₀ → WO B.L J.W₀ → ℂ,
      Hf = fun u z => omz (1, h₁) (fun z' => Ξ₁ ((B.o.resS J.W₀).symm (u, z'))) z := ⟨_, rfl⟩
  obtain ⟨Gf, hGf⟩ : ∃ Gf : WO J.W₀ B'.A → WO J.W₀ B'.L → ℂ,
      Gf = fun v w => omz' (h₁, 1) (fun w' => Ξ₂ ((B'.o.resT J.W₀).symm (v, w'))) w := ⟨_, rfl⟩
  obtain ⟨F₁, hF₁d⟩ : ∃ F₁ : WO B.V₀ J.W₀ → ℂ, F₁ = fun x => Hf (B.o.resS J.W₀ x).1 (B.o.resS J.W₀ x).2 := ⟨_, rfl⟩
  obtain ⟨F₂, hF₂d⟩ : ∃ F₂ : WO J.W₀ B'.V₀ → ℂ, F₂ = fun x => Gf (B'.o.resT J.W₀ x).1 (B'.o.resT J.W₀ x).2 :=
    ⟨_, rfl⟩
  have hF₁s : ∀ u z, F₁ ((B.o.resS J.W₀).symm (u, z)) = Hf u z := by
    intro u z; rw [hF₁d]; simp only [AddEquiv.apply_symm_apply]
  have hF₂s : ∀ v w, F₂ ((B'.o.resT J.W₀).symm (v, w)) = Gf v w := by
    intro v w; rw [hF₂d]; simp only [AddEquiv.apply_symm_apply]

  have hF₁ : IsThetaFunO ψ B.V₀ J.W₀ F₁ := by
    have h := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.L B.A J.W₀ B.o.symm χz s₁.χW omz hoz Ξ₁ hΞ₁ Unit 0 (fun _ => 0) (fun _ => 0)
      measurable_const (integrable_zero _ _ _) (1, h₁)).1
    have e : F₁ = fun x => omz (1, h₁) (fun u => Ξ₁ ((B.o.symm.resS J.W₀).symm (u, (B.o.symm.resS J.W₀ x).2)))
        (B.o.symm.resS J.W₀ x).1 := by
      funext x; rw [hF₁d, hHf]; simp only [symm_resS_symm]; rfl
    rw [e]; exact h
  have hF₂ : IsThetaFunO ψ J.W₀ B'.V₀ F₂ := by
    have h := (GlobalTheory.T.weilRep_commutes_slice_superposition_target D ψ B'.V₀ B'.L B'.A J.W₀ B'.o.symm s₂.χV χz omz' hoz' Ξ₂ hΞ₂ Unit 0 (fun _ => 0) (fun _ => 0)
      measurable_const (integrable_zero _ _ _) (h₁, 1)).1
    have e : F₂ = fun x => omz' (h₁, 1) (fun u => Ξ₂ ((B'.o.symm.resT J.W₀).symm (u, (B'.o.symm.resT J.W₀ x).2)))
        (B'.o.symm.resT J.W₀ x).1 := by
      funext x; rw [hF₂d, hGf]; simp only [symm_resT_symm]; rfl
    rw [e]; exact h

  obtain ⟨b₁, hb₁d⟩ : ∃ b₁ : WO J.W₀ B'.L → ℂ, b₁ = fun w => oma (h₀, h₁) (fun u => Hf u (l.κ J.W₀ w)) 0 := ⟨_, rfl⟩
  have hA : ∀ w, s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) = b₁ w := by
    intro w
    rw [(TS.om_slice χA χz s₁.χW s₁.om₀ oma omz hw₁ hoa hoz h₀ 1 h₁ Ξ₁ hΞ₁ (l.κ J.W₀ w)).2 0, hb₁d, hHf]
  have hB : ∀ w, s₂.om₀ (h₁, B'.o.emb (h₂, 1)) Ξ₂ ((B'.o.resT J.W₀).symm (0, w)) = omb (h₁, h₂) (fun v => Gf v w) 0 := by
    intro w
    rw [(TT.om_slice s₂.χV χA' χz s₂.om₀ omb omz' hw₂ hob hoz' h₁ h₂ 1 Ξ₂ hΞ₂ w).2 0, hGf]

  have hb₁int : Integrable b₁ (vL.μ.restrict vL.𝓕) := by
    have th := hw₁.om_pres (B.o.emb (h₀, 1), h₁) Ξ₁ hΞ₁
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded B.V₀ J.W₀ ψ hstd _ th
    have e : b₁ = fun w => s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) :=
      funext fun w => (hA w).symm
    rw [e]
    exact integrable_of_cont_bdd _ _ (th.cont.comp ((B.o.continuous_resS_symm J.W₀).comp
      (continuous_const.prodMk (continuous_kappa l J.W₀)))) ⟨C, fun w => hC _⟩
  have hGint : ∀ v, Integrable (Gf v) (vL.μ.restrict vL.𝓕) := by
    intro v
    have th := hoz'.om_pres (h₁, 1) _ (hS₂ v)
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded J.W₀ B'.L ψ hstd _ th
    have e : Gf v = omz' (h₁, 1) (fun w' => Ξ₂ ((B'.o.resT J.W₀).symm (v, w'))) := by rw [hGf]
    rw [e]
    exact integrable_of_cont_bdd _ _ th.cont ⟨C, hC⟩

  have hLine : ∀ u v, ∫ w, Gf v w * Hf u (l.κ J.W₀ w) ∂(vL.μ.restrict vL.𝓕) = contr l J.W₀ vL Ξ₁ Ξ₂ u v := by
    intro u v
    have hrank : B.L.rank = B'.L.rank := B.line.1.trans B'.line.1.symm
    have hgram := (GlobalTheory.T.besselLineLink_gram_similitude_bijective D (σ + 1) B B'.L B'.ζ B'.line l).1
    have CL := GlobalTheory.T.weilRep_conj_sourceLine_eq_targetLine D ψ B.L B'.L J.W₀ l.τ hrank hgram χz s₁.χW s₂.χV omz omz' hoz hoz'
      (fun z => Ξ₁ ((B.o.resS J.W₀).symm (u, z))) (hS₁ u)
    have CU := GlobalTheory.T.weilDatum_preserves_thetaFundamentalDomainPairing D ψ J.W₀ B'.L s₂.χV χz omz' hoz' vL (h₁, 1) _ _ (hS₂ v) CL.1
    rw [CL.2 h₁] at CU
    simp only [thPair, star_star] at CU
    rw [hGf, hHf]
    exact CU

  have hInner : ∀ v, oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0 =
      ∫ w, b₁ w * F₂ ((B'.o.resT J.W₀).symm (v, id w)) ∂(vL.μ.restrict vL.𝓕) := by
    intro v
    have e : (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) =
        fun u => ∫ w, Gf v w * F₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w)) ∂(vL.μ.restrict vL.𝓕) := by
      funext u; rw [← hLine u v]; simp only [hF₁s]
    rw [e, (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.A B.L J.W₀ B.o χA s₁.χW oma hoa F₁ hF₁ (WO J.W₀ B'.L) (vL.μ.restrict vL.𝓕)
      (l.κ J.W₀) (Gf v) (continuous_kappa l J.W₀).measurable (hGint v) (h₀, h₁)).2 0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hF₁s, hF₂s, id, hb₁d]
    exact mul_comm _ _
  have hOuter := (GlobalTheory.T.weilRep_commutes_slice_superposition_target D ψ B'.V₀ B'.A B'.L J.W₀ B'.o s₂.χV χA' omb hob F₂ hF₂ (WO J.W₀ B'.L)
    (vL.μ.restrict vL.𝓕) id b₁ measurable_id hb₁int (h₁, h₂)).2 0
  have e : (fun v => oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) =
      fun v => ∫ w, b₁ w * F₂ ((B'.o.resT J.W₀).symm (v, id w)) ∂(vL.μ.restrict vL.𝓕) := funext hInner
  rw [e, hOuter]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [hA, hB, hF₂s, id]
  exact mul_comm _ _

end GlobalTheory.ContrKernel

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.SeeLastPf

theorem ofAdj_zero (D : D7) (L S : HSp D) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S 0 = 0 := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]

theorem seeLast : ∀ D : D7, SeeLast D := by
  intro D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ χA χz χS χS' χT om₁ oma omz omX omT omz'' h₁ ha hz hX hT hz'' Ξ Φ₂ hΞ hΦ₂
  have hψ : IsStdChar D ψ (-1) := h₁.std
  have hsrc := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hψ V₀ A L o S
  have htgt := GlobalTheory.T.thetaTensorRule_targetOrthogonalSum D ψ hψ X T L'' o'' S
  have hτ' : τᴴ ⬝ (L.gram ⬝ τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L''.gram := by
    rw [hτ]; simp
  have hrk : L.rank = L''.rank := hL.trans hL''.symm
  have hline := fun u => GlobalTheory.T.weilRep_sourceLine_eq_opposite_targetLine D ψ L L'' S τ hrk hτ' χz χS χS' omz omz'' hz hz''
    (fun v => Ξ ((o.resS S).symm (u, v))) ((hsrc.slice_theta Ξ hΞ).2 u)
  refine ⟨fun u => (hline u).1, ?_⟩
  intro h₀ h h'
  have e1 : ∀ u, omX (h, o''.emb (h', 1)) (o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm
      (u, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) ⬝ w)))) 0 =
      omT (h, h') Φ₂ 0 * omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))) 0 := by
    intro u
    rw [htgt.om_box χS' χT χz⁻¹ omX omT omz'' hX hT hz'' h h' 1 Φ₂ _ hΦ₂ (hline u).1, htgt.box_zero,
      (hline u).2 h]
    beta_reduce
    congr 1
    exact congrArg (omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))))
      ((congrArg (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S) (Matrix.mul_zero _)).trans (ofAdj_zero D L S))
  have e2 := (hsrc.om_slice χA χz χS om₁ oma omz h₁ ha hz h₀ 1 h Ξ hΞ 0).2 0
  have e0 : (o.resS S).symm (0, 0) = 0 := by
    rw [← Prod.zero_eq_mk, map_zero]
  rw [e0] at e2
  simp only [e1]
  rw [e2]
  have : (fun u => omT (h, h') Φ₂ 0 * omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))) 0) =
      omT (h, h') Φ₂ 0 • (fun u' => omz (1, h) (fun v' => Ξ ((o.resS S).symm (u', v'))) 0) := by
    funext u; simp
  rw [this, map_smul]
  simp

end GlobalTheory.SeeLastPf

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselToJacobiFlatMap_support_reduces_to_torus : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ n ∈ flagN J.d, n ∈ grpAt J.W (· = v) → ∀ t : GL (Fin ρ) (AE D), ∀ γ ∈ grpAt J.W₀ (· = v), ∀ κ, InK J.W LW (· = v) κ → 𝔉 (s.om (1, n * J.d.levi t * J.d.emb0 γ * κ) f) ≠ 0 → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 := by
  first | exact @GlobalTheory.FinPl.oneBF_red_torus | exact GlobalTheory.FinPl.oneBF_red_torus | (intros; apply GlobalTheory.FinPl.oneBF_red_torus <;> assumption)
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.torusEntryRatio_integral_at_unramified_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i j : Fin ρ, j.1 = i.1 + 1 → t.1 i i * (t⁻¹).1 j j - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.RatioStep.ratio_int | exact GlobalTheory.FinPl.RatioStep.ratio_int | (intros; apply GlobalTheory.FinPl.RatioStep.ratio_int <;> assumption)
end
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.jacobiToBesselFlatMapSupport_proof : ∀ D : D7, GlobalTheory.FinPl.SupportShift D := by
  first | exact @GlobalTheory.FinPl.supportShift | exact GlobalTheory.FinPl.supportShift | (intros; apply GlobalTheory.FinPl.supportShift <;> assumption)
end
