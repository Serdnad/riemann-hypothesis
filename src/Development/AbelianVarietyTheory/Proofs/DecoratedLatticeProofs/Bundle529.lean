module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle304
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle378
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle448
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle451
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle452
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle524
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle482
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle474
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle521
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle514
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.Reindex

variable {D : D7}

theorem exists_rat_block {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {γ : GA D V} (hq : γ ∈ GQ V)
    (hn : γ ∈ flagN d) : ∃ (u : UX D ρ) (u₀ : Matrix (Fin ρ) (Fin ρ) D.host.E),
      blockX d γ = u.1.1 ∧ rat u₀ = u.1.1 := by
  obtain ⟨u, hu, h⟩ := GlobalTheory.JacClosed.flagN_le d hn
  have hb : blockX d γ = u.1 := by rw [blockX, h, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
  have hr : blockX d γ ∈ ratMx D ρ ρ :=
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff V γ).1 hq) (rat_mem _))
  obtain ⟨u₀, hu₀⟩ := mem_ratMx.1 hr
  exact ⟨⟨u, hu⟩, u₀, hb, hu₀.trans hb⟩

theorem det_eq_one {ρ : ℕ} (u : UX D ρ) (u₀ : Matrix (Fin ρ) (Fin ρ) D.host.E) (h : rat u₀ = u.1.1) :
    u₀.det = 1 := by
  have h0 : ∀ i j : Fin ρ, j < i → u₀ i j = 0 := fun i j hij => incA_injective (by
    rw [map_zero]
    have := congrFun (congrFun h i) j
    change incA D (u₀ i j) = _ at this
    rw [this]; exact ((mem_UX.1 u.2) i j).1 hij)
  have h1 : ∀ i : Fin ρ, u₀ i i = 1 := fun i => incA_injective (by
    rw [map_one]
    have := congrFun (congrFun h i) i
    change incA D (u₀ i i) = _ at this
    rw [this]; exact ((mem_UX.1 u.2) i i).2)
  rw [Matrix.det_of_upperTriangular (fun i j (hij : j < i) => h0 i j hij)]
  simp [h1]

theorem gramQ_mul (W : HSp D) {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) (u₀ : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    gramQ W (x * u₀) = u₀ᴴ * gramQ W x * u₀ := by
  simp only [gramQ, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.Unf.Reindex


open GlobalTheory.Unf.Reindex in
theorem GlobalTheory.Unf.tsum_offBase_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ γ ∈ GQ V, γ ∈ flagN d → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS (om (γ, 1) Φ) x.1 = ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS Φ x.1 := by
  intro D ψ V V₀ W ρ d χV χW om om' hV hV₀ vS x₀ hx₀ γ hq hn Φ hΦ
  obtain ⟨u, u₀, hb, hu₀⟩ := exists_rat_block d hq hn
  have hdet : IsUnit u₀.det := by rw [det_eq_one u u₀ hu₀]; exact isUnit_one
  have hdet' : IsUnit u₀ᴴ.det := by rw [Matrix.det_conjTranspose, det_eq_one u u₀ hu₀, star_one]; exact isUnit_one
  set G₀ := gramQ W x₀
  have hG : u₀ᴴ * G₀ * u₀ = G₀ := by
    apply rat_injective
    have := hx₀.2 u.1 u.2
    rw [rat_mul, rat_mul, rat_conjTranspose, hu₀]
    rw [Matrix.mul_assoc]; exact this
  have key : ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, gramQ W (x * u₀) = G₀ ↔ gramQ W x = G₀ := by
    intro x
    rw [gramQ_mul]
    constructor
    · intro h
      have h2 : u₀ᴴ * gramQ W x * u₀ = u₀ᴴ * G₀ * u₀ := h.trans hG.symm
      have h3 := congrArg (fun M => (u₀ᴴ)⁻¹ * M * u₀⁻¹) h2
      simp only [Matrix.mul_assoc] at h3
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet', Matrix.mul_nonsing_inv _ hdet] using h3
    · intro h; rw [h, hG]
  have hinv : u₀ * u₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hinv' : u₀⁻¹ * u₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  let e : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀} ≃
      {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀} :=
    { toFun := fun x => ⟨x.1 * u₀, fun h => x.2 ((key x.1).1 h)⟩
      invFun := fun x => ⟨x.1 * u₀⁻¹, fun h => x.2 (by
        have := (key (x.1 * u₀⁻¹)).2 h
        rwa [Matrix.mul_assoc, hinv', Matrix.mul_one] at this)⟩
      left_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hinv, Matrix.mul_one])
      right_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hinv', Matrix.mul_one]) }
  have hterm : ∀ x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀},
      term ψ d W vS (om (γ, 1) Φ) x.1 = term ψ d W vS Φ (e x).1 := by
    intro x
    refine (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hV hV₀ vS Φ hΦ).2.1 γ hq hn x.1 (x.1 * u₀) ?_
    rw [rat_mul, hu₀, hb]
  rw [tsum_congr hterm]
  exact Equiv.tsum_eq e (fun y => term ψ d W vS Φ y.1)

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.LatShape

theorem coreFrame_beta_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n)
    {F F' : Frame k B.V₀.rank (n ⊕ Unit)} (h : p.IsCoreFrame B s FA F) (h' : p.IsCoreFrame B s FA F') : F.β = F'.β := by
  ext r (a | u)
  · rw [h.1, h'.1]
  · cases u
    rw [h.2, h'.2]

theorem exists_shape_integral_in_normal_frames : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∃ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (dT : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (M : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀) (β₀ : ∀ j ρ h i, GlobalTheory.FinPl.Frame (o.p i) (y.bes j ρ h).V₀ (Fin (D.sp.X j).rank ⊕ Fin 1)), ShapeOff { v with N := N, dT := dT, RamAd := o.Ram } { o with M := M, β₀ := β₀ } ∧ (∀ j, GlobalTheory.FinPl.CombAt (· ∈ v.tP) (dT j)) ∧ (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) ∧ ∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N j) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP a y m b₀ k _ _ _ _ ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY
  have hfin := GlobalTheory.T.level_places_finite W hP
  have hsep := GlobalTheory.T.level_places_under_eq W hP
  have hsc : ∀ PP hP j, sc PP hP j ≠ 0 := by
    intro PP hP j h0
    have := (hFY PP hP).1 j
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hxi : ∀ PP hP, (ofSplit (l PP hP).q).xi ≠ 0 := by
    intro PP hP h0
    have e := (hFY PP hP).2.1 0
    have v2 := (hFY PP hP).1 (0 + 1 + 1)
    rw [e, h0, mul_zero, map_zero] at v2
    exact zero_ne_one v2
  let I := {PP : Pl D.host.E // PP ∈ (pk W).Pg ∨ QAll W PP}
  haveI : Finite I := hfin.to_subtype
  have hinj : ∀ i i' : I, (l i.1 i.2).q.v = (l i'.1 i'.2).q.v → i = i' := by
    intro i i' e
    rw [(l i.1 i.2).under, (l i'.1 i'.2).under] at e
    exact Subtype.ext (hsep _ _ i.2 i'.2 e)
  have hA : ∀ j, ∃ N' : GlobalTheory.FinPl.Lat (Yc D j), (j < D.R.m → IsSelfDualC (Yc D j) N') ∧
      ∀ PP h c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) N' := by
    intro j
    by_cases hj : j < D.R.m
    · obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.exists_self_dual_lattice_chain W hP j hj
      obtain ⟨N', hsd, hint⟩ := GlobalTheory.T.exists_move_selfDual_lattice_split_frames D (Yc D j) L₀ hL₀ I (fun i => (l i.1 i.2).k) (fun i => (l i.1 i.2).q)
        (fun _ => XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (D.R.m - 1 - j))
        (fun i => FY i.1 i.2 j (D.R.m - 1 - j) (by have := (l i.1 i.2).hs; omega)) hinj
      refine ⟨N', fun _ => hsd, fun PP h c hc => ?_⟩
      obtain rfl : c = D.R.m - 1 - j := by have := (l PP h).hs; omega
      exact hint ⟨PP, h⟩
    · refine ⟨⊥, fun h => absurd h hj, fun PP h c hc => ?_⟩
      exfalso
      have := (l PP h).hs
      omega
  choose N₁ hN₁sd hN₁int using hA
  have hB : ∀ j ρ h, ∃ M' : GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀, IsSelfDualC (y.bes j ρ h).V₀ M' ∧
      ∀ PP hP (hj : j ≤ (l PP hP).s + 1)
        (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)),
        (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ →
        IntIn (l PP hP).q _ F₀ M' := by
    intro j ρ h
    obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.local_component_measure_relation W u hP a y m b₀ k ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY j ρ h
    have hj : ∀ i : I, j ≤ (l i.1 i.2).s + 1 := fun i => by have := (l i.1 i.2).hs; omega
    have hex : ∀ i : I, ∃ F : Frame (l i.1 i.2).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit),
        (ofSplit (l i.1 i.2).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc i.1 i.2 j) ((l i.1 i.2).FX j (hj i)) F := by
      intro i
      exact ((@GlobalTheory.LocMod.normalFrames_and_basePoint_exist D (l i.1 i.2).k _ _ _ _ (ofSplit (l i.1 i.2).q)
        (hxi i.1 i.2)).1 _ ρ _ _ _ (hsc i.1 i.2 j)).1
    choose F hF using hex
    obtain ⟨M', hsd, hint⟩ := GlobalTheory.T.exists_move_selfDual_lattice_split_frames D (y.bes j ρ h).V₀ L₀ hL₀ I (fun i => (l i.1 i.2).k) (fun i => (l i.1 i.2).q)
      (fun _ => XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit) F hinj
    refine ⟨M', hsd, fun PP hP hj' F₀ hF₀ => ?_⟩
    have e := coreFrame_beta_eq _ _ _ _ (hF ⟨PP, hP⟩) hF₀
    intro z
    rw [← e]
    exact hint ⟨PP, hP⟩ z
  choose M₁ hM₁sd hM₁int using hB
  have hoffT := GlobalTheory.T.local_component_measure_value W u hP a y m b₀ k ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY
  have hbf := GlobalTheory.T.local_component_measure_bound W u hP a y m b₀ k ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY N₁ M₁ hN₁sd (fun PP h j c hc => hN₁int j PP h c hc) hM₁sd (fun PP hP j ρ h hj F₀ hF₀ => hM₁int j ρ h PP hP hj F₀ hF₀)
  have hfb := GlobalTheory.T.local_component_measure_scalar W u hP a y m b₀ k ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY N₁ M₁ hN₁sd (fun PP h j c hc => hN₁int j PP h c hc) hM₁sd (fun PP hP j ρ h hj F₀ hF₀ => hM₁int j ρ h PP hP hj F₀ hF₀)
  have hsp := GlobalTheory.T.local_component_measure_equation W u hP a y m b₀ k ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY N₁ M₁ hN₁sd (fun PP h j c hc => hN₁int j PP h c hc) hM₁sd (fun PP hP j ρ h hj F₀ hF₀ => hM₁int j ρ h PP hP hj F₀ hF₀)
  let G' : Finset (GlobalTheory.FinPl.Pl D) := hfin.toFinset.image (fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))
  have hG' : ∀ x, x ∈ G' ↔ ∃ PP, (PP ∈ (pk W).Pg ∨ QAll W PP) ∧ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = x := by
    intro x
    simp only [G', Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hdisj' : Disjoint G' v.tP := by
    rw [Finset.disjoint_left]
    intro x hx hxT
    obtain ⟨PP, hPP, rfl⟩ := (hG' x).1 hx
    rcases hPP with hg | hq
    · exact Finset.disjoint_left.1 hdisj ((hgP _).2 ⟨PP, hg, rfl⟩) hxT
    · exact hoffT PP hq hxT
  obtain ⟨N, dT, M, β₀, hN, -, hC, hS⟩ := GlobalTheory.T.seeSawLatticeShapeExists_proof D (commOf (pk W) u (mkGeo m b₀)) { v with gP := G', N := N₁ } k ι
    { o with M := M₁ } hc hdisj' (by show IsSelfDualC D.sp.X' v.NT; rw [hvNT]; exact hLT)
    ⟨hPre.nodup, hPre.all, hPre.inj, hPre.tP, hPre.char, hPre.latT, hPre.line, hPre.tau, hPre.lam, hPre.normT, hPre.topT⟩
    hN₁sd (fun x hx => by
      obtain ⟨PP, hPP, rfl⟩ := (hG' x).1 hx
      exact ⟨⟨hbf PP hPP, hfb PP hPP⟩, ⟨(hsp PP hPP).core, (hsp PP hPP).top⟩⟩)
    (fun n h x hx => by
      obtain ⟨LZ, h1, h2⟩ := hLZ n h x hx
      refine ⟨LZ, h1, ?_⟩
      show GlobalTheory.FinPl.OrthAt _ _ v.NT LZ x
      rw [hvNT]
      exact h2)
  refine ⟨N, dT, M, β₀, ?_, hC, fun j hj => (hN j hj).1, ?_⟩
  · exact ⟨⟨hS.pre.nodup, hS.pre.all, hS.pre.inj, hS.pre.tP, hS.pre.char, hS.pre.latT, hS.pre.line, hS.pre.tau, hS.pre.lam,
      hS.pre.normT, hS.pre.topT⟩, fun x => ⟨(hS.good x).bf, (hS.good x).fb⟩,
      fun x hx => ⟨(hS.split x hx).core, (hS.split x hx).top⟩, hS.glued, hS.rep, hS.ram⟩
  · intro PP h j c hc
    have hj : j < D.R.m := by have := (l PP h).hs; omega
    have hx : (l PP h).q.v ∈ G' := by rw [(l PP h).under]; exact (hG' _).2 ⟨PP, h, rfl⟩
    have e : GlobalTheory.FinPl.latV (Yc D j) (N j) (· = (l PP h).q.v) = GlobalTheory.FinPl.latV (Yc D j) (N₁ j) (· = (l PP h).q.v) :=
      (hN j hj).2 _ hx
    intro z
    rw [e]
    exact hN₁int j PP h c hc z

end GlobalTheory.Fam.LatShape

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

noncomputable section

namespace GlobalTheory.LastDbl

variable {D : D7}

theorem ker_smul {A S X : HSp D} (oma : Om A S) (omX : Om S X) (a : ℂ) (C : WO A S → WO S X → ℂ) (h₀ : GA D A)
    (h₁ : GA D S) (h₂ : GA D X) :
    GlobalTheory.SeeSmallPf.ker oma omX (a • C) h₀ h₁ h₂ = a * GlobalTheory.SeeSmallPf.ker oma omX C h₀ h₁ h₂ := by
  unfold GlobalTheory.SeeSmallPf.ker
  have e1 : (fun v => oma (h₀, h₁) (fun u => (a • C) u v) 0) = a • fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v
    have e : (fun u => (a • C) u v) = a • fun u => C u v := by
      funext u; simp only [Pi.smul_apply]
    rw [e, map_smul]; simp only [Pi.smul_apply]
  rw [e1, map_smul]; simp only [Pi.smul_apply, smul_eq_mul]

theorem biLift_smul {A S X : HSp D} (oma : Om A S) (omX : Om S X) (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) (a : ℂ)
    (C : WO A S → WO S X → ℂ) (h₂ : GA D X) :
    biLift oma omX vA vS φ (a • C) h₂ = a * biLift oma omX vA vS φ C h₂ := by
  rw [GlobalTheory.SeeSmallPf.biLift_eq, GlobalTheory.SeeSmallPf.biLift_eq]
  have e : ∀ h₀ h₁, φ h₀ * GlobalTheory.SeeSmallPf.ker oma omX (a • C) h₀ h₁ h₂ =
      a * (φ h₀ * GlobalTheory.SeeSmallPf.ker oma omX C h₀ h₁ h₂) := fun h₀ h₁ => by rw [ker_smul]; ring
  simp only [e, integral_const_mul]

theorem theta_smul {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (a : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (a • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hi => ?_⟩
    have e : heisO ψ S T u (a • f) = a • heisO ψ S T u f := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, hU u hu hi]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := (contDiff_const.mul (hf.smooth k L hL hfin w)) }

theorem sum_fin {G M : Type} [AddCommMonoid M] (s : Finset G) (F : G → M) :
    ∑ g ∈ s, F g = ∑ i : Fin s.card, F (s.equivFin.symm i) := by
  rw [← Finset.sum_coe_sort s F]
  exact (Equiv.sum_comp s.equivFin.symm (fun x => F x)).symm

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c), c.Is → t.Is → WeilOK (t := t) v → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (Y : WO (c.V (j + 1)) c.T → ℂ), IsThetaFunO c.ψ _ _ Y → ∀ φ, IsContAut (c.X j) φ → (∀ X : WO (c.V j) (c.V (j + 1)) → ℂ, IsThetaFunO c.ψ _ _ X → ∀ f, IsContAut c.T f → IntegrableOn (fun h' => f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) X Y) ((c.oT (j + 1 + 1) h).emb (h', 1))) c.volT.𝓕 c.volT.μ) ∧ ∀ (G : Type) (s : Finset G) (a : G → ℂ) (X : G → WO (c.V j) (c.V (j + 1)) → ℂ), (∀ g, IsThetaFunO c.ψ _ _ (X g)) → ∑ g ∈ s, a g • c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (X g) Y) = c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ s, a g • X g) Y) := by
  intro D c v t hc ht hW j h Y hY φ hφ
  obtain ⟨χA, χz, χS', χT, omz, omT, omz'', hχV, hWa, hWz, hWX, hWT, hWTb, hWz''⟩ := hW.last j h
  have hB : BiAct D := GlobalTheory.SeeSaw.biAct_all D
  have hA : CoCpt (c.X j) := (hc.x j (by omega)).cpt
  have hS : CoCpt (c.X (j + 1)) := (hc.x (j + 1) (by omega)).cpt
  have hτ := (hW.tau j h).2
  obtain ⟨-, -, hthS, -⟩ := GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D c.ψ (c.V (j + 1)) (c.X (j + 1)) c.T (c.jac j 0 h).d hc.std
  have hY' : IsThetaFunO c.ψ (c.X (j + 1)) c.T (fun w => Y ((c.jac j 0 h).d.ext0 c.T w)) := (hthS Y).2 hY
  have hC : ∀ Z : WO (c.V j) (c.V (j + 1)) → ℂ, IsThetaFunO c.ψ _ _ Z →
      IsBiTheta c.ψ (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1)) (c.lst j h (v.τ j h) (t.sBF j 0 h) Z Y) := by
    intro Z hZ
    have hZ' : IsThetaFunO c.ψ (c.B j 0 h).V (c.J j 0 h).W Z := hZ
    obtain ⟨hΞ, -⟩ := GlobalTheory.LastRed.val_zero (t.sBF j 0 h) hZ'
    exact GlobalTheory.LastRed.lastBi_biTheta D c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz
      (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) hτ (flatBF (t.sBF j 0 h) Z) _ hΞ hY'
  refine ⟨fun X hX f hf => GlobalTheory.SeeSmallPf.outer hB hWa hWX (hC X hX) hA hS hc.cpt (c.x j).vol (c.x (j + 1)).vol c.volT
    (c.oT (j + 1 + 1) h) hφ hf, fun G s a X hX => ?_⟩
  have hsum : ∀ (Z : G → WO (c.V j) (c.V (j + 1)) → ℂ), c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ s, a g • Z g) Y =
      ∑ g ∈ s, a g • c.lst j h (v.τ j h) (t.sBF j 0 h) (Z g) Y := by
    intro Z
    funext u w
    simp only [Comm.lst, GlobalTheory.FinPl.lastBi, OrthDec.boxT, GlobalTheory.LastRed.flatBF_rankZero, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring
  have hsm : ∀ (b : ℂ) (Z : WO (c.V j) (c.V (j + 1)) → ℂ), c.lst j h (v.τ j h) (t.sBF j 0 h) (b • Z) Y =
      b • c.lst j h (v.τ j h) (t.sBF j 0 h) Z Y := by
    intro b Z
    funext u w
    simp only [Comm.lst, GlobalTheory.FinPl.lastBi, OrthDec.boxT, GlobalTheory.LastRed.flatBF_rankZero, Pi.smul_apply, smul_eq_mul]
    ring
  funext h₂
  rw [hsum, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have e1 : ∀ g, a g * c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (X g) Y) h₂ =
      c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (a g • X g) Y) h₂ := fun g => by
    rw [hsm]; exact (biLift_smul _ _ _ _ _ _ _ _).symm
  simp only [e1]
  rw [sum_fin s, sum_fin s]
  have e2 : (∑ i : Fin s.card, a (s.equivFin.symm i) • c.lst j h (v.τ j h) (t.sBF j 0 h) (X (s.equivFin.symm i)) Y) =
      ∑ i : Fin s.card, c.lst j h (v.τ j h) (t.sBF j 0 h) (a (s.equivFin.symm i) • X (s.equivFin.symm i)) Y :=
    Finset.sum_congr rfl fun i _ => (hsm _ _).symm
  rw [e2]
  exact (GlobalTheory.SeeSmallPf.biLift_sum hB hWa hWX hA hS (c.x j).vol (c.x (j + 1)).vol hφ
    (fun i => c.lst j h (v.τ j h) (t.sBF j 0 h) (a (s.equivFin.symm i) • X (s.equivFin.symm i)) Y)
    (fun i => hC _ (theta_smul _ (hX _))) h₂).symm

end GlobalTheory.LastDbl

end
end
