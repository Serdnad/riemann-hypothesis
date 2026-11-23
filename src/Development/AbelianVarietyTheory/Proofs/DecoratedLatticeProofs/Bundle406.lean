module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle377
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle245
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle200
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle207
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle379
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle214
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle381

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitLineSim

open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_not_int : ∃ x : k, x ∉ 𝒪[k] := by
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  refine ⟨r⁻¹, fun h => ?_⟩
  have h1 : valuation k r⁻¹ ≤ 1 := h
  have hr : r ≠ 0 := hr0
  have : (1 : ValueGroupWithZero k) ≤ valuation k r := by
    calc (1 : ValueGroupWithZero k) = valuation k (r * r⁻¹) := by rw [mul_inv_cancel₀ hr, map_one]
      _ = valuation k r * valuation k r⁻¹ := map_mul _ _ _
      _ ≤ valuation k r * 1 := by gcongr
      _ = valuation k r := mul_one _
  exact absurd hr1 (not_lt.2 this)

theorem mul_sec' (q : SplitPt D k) (a : AE D) (b : k) : a * q.sec b = q.sec (q.pr a * b) := by
  rw [mul_comm, FrameLat.sec_mul_right, mul_comm]

theorem mul_csec (q : SplitPt D k) (a : AE D) (b : k) :
    a * cA D (q.sec b) = cA D (q.sec (q.pr (cA D a) * b)) := by
  rw [← mul_sec', map_mul, Formalism.L2.Theta.cA_cA]

theorem mulVec_sec' (q : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (A : Fin n → k) :
    (M *ᵥ fun i => q.sec (A i)) = fun j => q.sec ((M.map q.pr *ᵥ A) j) := by
  funext j

  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_sec', map_sum]

theorem mulVec_csec (q : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (B : Fin n → k) :
    (M *ᵥ fun i => cA D (q.sec (B i))) = fun j => cA D (q.sec ((M.map (fun a => q.pr (cA D a)) *ᵥ B) j)) := by
  funext j

  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_csec, map_sum]

theorem pr_cA_sec (q : SplitPt D k) (c : k) : q.pr (cA D (q.sec c)) = 0 := by
  have he : q.pr (cA D q.e) = 0 := by
    have h1 : q.pr (cA D q.e * q.e) = 0 := by rw [FrameLat.cAe_mul_e, map_zero]
    have pe : q.pr q.e = 1 := by rw [← FrameLat.sec_one, q.pr_sec]
    rwa [map_mul, pe, mul_one] at h1
  rw [← FrameLat.e_mul_sec q c, map_mul, map_mul, he, zero_mul]

theorem pr_cA_xi_int (q : SplitPt D k) (h : q.UnitAA) : q.pr (cA D (incA D D.host.xi0)) ∈ 𝒪[k] := by
  have hid : cA D (q.sec 1) ∈ idAt D (· = q.v) := FrameLat.csec_mem_idAt (p := q) 1
  have hc : cA D (q.sec 1) ∈ intAt D (· = q.v) := by
    refine (GlobalTheory.SplitIntComp.mem_intAt_iff q hid).2 ⟨?_, ?_⟩
    · rw [pr_cA_sec]; exact zero_mem _
    · rw [Formalism.L2.Theta.cA_cA, q.pr_sec]; exact one_mem _
  have h2 := (h.1 _ hc).1
  have h3 := ((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.1).1 h2).2
  rwa [map_mul, Formalism.L2.Theta.cA_cA, map_mul, q.pr_sec, mul_one] at h3

theorem pr_xi_int (q : SplitPt D k) (h : q.UnitAA) : q.pr (incA D D.host.xi0) ∈ 𝒪[k] :=
  (GlobalTheory.SplitIntComp.val_xi q h).le

end GlobalTheory.SplitLineSim

namespace GlobalTheory.SplitLineSim
open GlobalTheory.FinPl

theorem line_sim_maps : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (L L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (LL : GlobalTheory.FinPl.Lat L) (LZ : GlobalTheory.FinPl.Lat L'') (zL : Fin L.rank → k) (z₀ : Fin L''.rank → k) (u : k), q.UnitAA → IsSelfDualC L LL → IsSelfDualC L'' LZ → L.rank = 1 → L''.rank = 1 → (∀ y : k, y ∈ 𝒪[k] ↔ (fun i => q.sec (zL i * y)) ∈ GlobalTheory.FinPl.latV L LL (· = q.v)) → (∀ y : k, y ∈ 𝒪[k] ↔ (fun i => q.sec (z₀ i * y)) ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v)) → valuation k u = 1 → τ.map (ofSplit q).pr *ᵥ z₀ = u • zL → τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ y ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v), (rat τ : Mx D L.rank L''.rank) *ᵥ y ∈ GlobalTheory.FinPl.latV L LL (· = q.v) := by
  intro D k _ _ _ _ q L L'' τ LL LZ zL z₀ u hU hLL hLZ hr hr'' hcL hcZ hu hτz hτ y hy
  haveI : Unique (Fin L.rank) := ⟨⟨⟨0, by omega⟩⟩, fun j => Fin.ext (by have := j.2; omega)⟩
  haveI : Unique (Fin L''.rank) := ⟨⟨⟨0, by omega⟩⟩, fun j => Fin.ext (by have := j.2; omega)⟩
  set j0 : Fin L.rank := default with hj0
  set i0 : Fin L''.rank := default with hi0
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  have hu_int : u ∈ 𝒪[k] := hu.le
  have hui_int : u⁻¹ ∈ 𝒪[k] := by
    show valuation k u⁻¹ ≤ 1
    rw [map_inv₀, hu, inv_one]

  have h1 : q.pr (incA D (τ j0 i0)) * z₀ i0 = u * zL j0 := by
    have := congrFun hτz j0
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_unique, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hzL : zL j0 ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_not_int (k := k)
    apply hx
    rw [hcL]
    have : (fun i => q.sec (zL i * x)) = 0 := by
      funext i
      rw [Subsingleton.elim i j0, h0, zero_mul, map_zero]
      rfl
    rw [this]
    exact zero_mem _
  have hz0 : z₀ i0 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact hzL ((mul_eq_zero.1 h1.symm).resolve_left hu0)

  have hyS : ∀ i, y i ∈ idAt D (· = q.v) := FrameLat.latV_supp hy
  set A : Fin L''.rank → k := fun i => q.pr (y i) with hA
  set B : Fin L''.rank → k := fun i => q.pr (cA D (y i)) with hB
  have hyAB : y = (fun i => q.sec (A i)) + fun i => cA D (q.sec (B i)) := by
    funext i
    exact GlobalTheory.SplitIntComp.eq_sec_add_csec q (hyS i)
  rw [hyAB] at hy
  obtain ⟨hyA, hyB⟩ := (FrameLat.decomp hLZ A B).1 hy
  rw [hyAB, Matrix.mulVec_add, mulVec_sec', mulVec_csec]
  refine (FrameLat.decomp hLL _ _).2 ⟨?_, ?_⟩
  ·
    set c : k := A i0 / z₀ i0 with hc
    have hcA : ∀ i, z₀ i * c = A i := fun i => by
      rw [Subsingleton.elim i i0, hc, mul_div_cancel₀ _ hz0]
    have hcint : c ∈ 𝒪[k] := (hcZ c).2 (by simpa only [hcA] using hyA)
    have : (fun j => q.sec ((((rat τ : Mx D L.rank L''.rank)).map q.pr *ᵥ A) j)) =
        fun j => q.sec (zL j * (u * c)) := by
      funext j
      rw [Subsingleton.elim j j0]
      congr 1
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_unique]
      rw [← hcA i0]
      change q.pr (incA D (τ j0 i0)) * (z₀ i0 * c) = _
      rw [← mul_assoc, h1]
      ring
    rw [this]
    exact (hcL _).1 (mul_mem hu_int hcint)
  ·
    rw [FrameLat.csec_mem_iff hLL]
    intro x hx
    have h00 : star (τ j0 i0) * (L.gram j0 j0 * τ j0 i0) = -(D.host.xi0 * star D.host.xi0) * L''.gram i0 i0 := by
      have := congrFun (congrFun hτ i0) i0
      rw [Matrix.mul_apply, Fintype.sum_unique, Matrix.mul_apply, Fintype.sum_unique,
        Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul] at this
      exact this
    let φ : D.host.E →+* k := (q.pr.comp (cA D)).comp (incA D)
    have hφs : ∀ t : D.host.E, φ (star t) = q.pr (incA D t) := fun t => by
      show q.pr (cA D (incA D (star t))) = _
      rw [FrameLat.cA_incA, star_star]

    have e3 : q.pr (incA D (τ j0 i0)) * (q.pr (cA D (incA D (L.gram j0 j0))) * q.pr (cA D (incA D (τ j0 i0)))) =
        -(q.pr (cA D (incA D D.host.xi0)) * q.pr (incA D D.host.xi0)) * q.pr (cA D (incA D (L''.gram i0 i0))) := by
      have h2 := congrArg φ h00
      rw [map_mul, map_mul, map_mul, map_neg, map_mul, hφs (τ j0 i0), hφs D.host.xi0] at h2
      exact h2
    have hcw_int : -(q.pr (cA D (incA D D.host.xi0)) * q.pr (incA D D.host.xi0)) ∈ 𝒪[k] :=
      neg_mem (mul_mem (pr_cA_xi_int q hU) (pr_xi_int q hU))
    obtain ⟨c', hc'⟩ : ∃ c' : k, c' = x j0 / zL j0 := ⟨_, rfl⟩
    have hxc : ∀ j, zL j * c' = x j := fun j => by
      rw [Subsingleton.elim j j0, hc', mul_div_cancel₀ _ hzL]
    have hc'int : c' ∈ 𝒪[k] := (hcL c').2 (by simpa only [hxc] using hx)

    have hz1 : (fun i => q.sec (z₀ i)) ∈ latV L'' LZ (· = q.v) := by
      simpa only [mul_one] using (hcZ 1).1 (one_mem _)
    have hZB := (FrameLat.csec_mem_iff hLZ B).1 hyB z₀ hz1
    simp only [Fintype.sum_unique] at hZB
    have hinv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
    have e0 : ((((rat τ : Mx D L.rank L''.rank)).map (fun a => q.pr (cA D a)) *ᵥ B) j0) =
        q.pr (cA D (incA D (τ j0 i0))) * B i0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_unique]
      rfl
    simp only [Fintype.sum_unique]
    rw [e0, ← hxc j0]
    have key : zL j0 * c' * q.pr (cA D (incA D (L.gram j0 j0))) * (q.pr (cA D (incA D (τ j0 i0))) * B i0) =
        c' * u⁻¹ * (-(q.pr (cA D (incA D D.host.xi0)) * q.pr (incA D D.host.xi0))) *
          (z₀ i0 * q.pr (cA D (incA D (L''.gram i0 i0))) * B i0) := by
      linear_combination (c' * u⁻¹ * z₀ i0 * B i0) * e3 -
        (c' * u⁻¹ * q.pr (cA D (incA D (L.gram j0 j0))) * q.pr (cA D (incA D (τ j0 i0))) * B i0) * h1 -
        (c' * q.pr (cA D (incA D (L.gram j0 j0))) * q.pr (cA D (incA D (τ j0 i0))) * B i0 * zL j0) * hinv
    rw [key]
    exact mul_mem (mul_mem (mul_mem hc'int hui_int) hcw_int) hZB

end GlobalTheory.SplitLineSim
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.QParL

theorem seg_eq_segL : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP →
    ∀ (x : (AE D)ˣ) (ϖ : (Fv D.host.F v)ˣ), IsLocUnif φ x ϖ → ∀ z t, GlobalTheory.LFun.seg PP z t = GlobalTheory.ParHecke.segL ϖ z t := by
  intro D v φ PP hφ x ϖ hx z t
  obtain ⟨-, hq⟩ := GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ
  obtain ⟨e, -, -, -, hϖ⟩ := hx
  have hn := GlobalTheory.GLDoubling.nabs_unif hϖ
  unfold GlobalTheory.LFun.seg GlobalTheory.ParHecke.segL
  refine Multiset.map_congr rfl fun n _ => ?_
  congr 1
  ext
  rw [GlobalTheory.SmGL.val_absPow, hn, hq, GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), ← Complex.cpow_neg]
  congr 1
  ring

theorem qPar_succ {D : D7} (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) :
    qPar c PP x (k + 1) = (qPar c PP x k).map (· * (Circle.toUnits (c.chS (k + 1) x) * (Circle.toUnits (c.chT (k + 1) x))⁻¹)) +
      GlobalTheory.LFun.seg PP (Circle.toUnits (c.chS (k + 1) x)) D.R.t := rfl

theorem card_qPar {D : D7} (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) : (qPar c PP x k).card = k * D.R.t := by
  induction k with
  | zero => simp [qPar]
  | succ k ih => rw [qPar_succ, Multiset.card_add, Multiset.card_map, ih, GlobalTheory.LFun.card_seg]; ring

theorem seg_map_mul {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (z u : ℂˣ) (t : ℕ) :
    (GlobalTheory.LFun.seg w z t).map (· * u) = GlobalTheory.LFun.seg w (z * u) t := by
  simp only [GlobalTheory.LFun.seg, Multiset.map_map, Function.comp_def]
  exact Multiset.map_congr rfl fun i _ => mul_right_comm _ _ _

theorem sum_map_mul {ι : Type} (s : Finset ι) (f : ι → Multiset ℂˣ) (u : ℂˣ) :
    (∑ i ∈ s, f i).map (· * u) = ∑ i ∈ s, (f i).map (· * u) :=
  map_sum (Multiset.mapAddMonoidHom (· * u)) f s

theorem qPar_closed {D : D7} (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) :
    qPar c PP x k = ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.seg PP (Circle.toUnits ((c.μ i * c.eps k) x)) D.R.t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [qPar_succ, ih, sum_map_mul, Finset.sum_Icc_succ_top (by omega)]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [seg_map_mul, ← GlobalTheory.ChainOnto.ParClosed.eps_succ]
      congr 1
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
      ext
      simp only [Units.val_mul]
      ring
    · rw [GlobalTheory.ChainOnto.ParClosed.chS_succ]

theorem qPar_twist {D : D7} (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) :
    (qPar c PP x k).map (· * (Circle.toUnits (c.chT (k + 1) x))⁻¹) =
      ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.seg PP (Circle.toUnits ((c.μ i * (c.μ (k + 1))⁻¹) x)) D.R.t := by
  rw [qPar_closed, sum_map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [seg_map_mul, GlobalTheory.ChainOnto.ParClosed.chT_succ]
  congr 1
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
  rw [_root_.mul_inv_rev]
  group

theorem invNormFactor_eq (q t k : ℕ) :
    GlobalTheory.GLDoubling.invNormFactor q (k * t) ((t : ℂ) / 2) =
      ((∏ n ∈ Finset.Ioc t ((k + 1) * t), (1 - ((q : ℝ) ^ n)⁻¹) : ℝ) : ℂ) := by
  unfold GlobalTheory.GLDoubling.invNormFactor
  push_cast
  rw [show (k + 1) * t = t + k * t by ring]
  generalize k * t = m
  have h1 : Finset.Ioc t (t + m) = (Finset.Icc 1 m).map (addLeftEmbedding t) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_Icc, addLeftEmbedding_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨n - t, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩; constructor <;> omega
  rw [h1, Finset.prod_map]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : (2 * ((t : ℂ) / 2) + (i : ℂ)) = ((addLeftEmbedding t i : ℕ) : ℂ) := by
    simp only [addLeftEmbedding_apply]; push_cast; ring
  rw [this, Complex.cpow_neg, Complex.cpow_natCast]

end GlobalTheory.QParL

open GlobalTheory.QParL in
theorem GlobalTheory.ChainTw.qPar_twist_lFactor : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ k < D.R.m, ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ x ϖ, IsLocUnif φ x ϖ → (∀ z t, GlobalTheory.LFun.seg PP z t = GlobalTheory.ParHecke.segL ϖ z t) ∧ (qPar c PP x k).card = k * D.R.t ∧ ∀ α : Fin (k * D.R.t) → ℂˣ, Finset.univ.val.map α = (qPar c PP x k).map (· * (Circle.toUnits (c.chT (k + 1) x))⁻¹) → (∀ i, ‖(α i : ℂ)‖ ≤ (Ideal.absNorm PP.asIdeal : ℝ) ^ (((D.R.t : ℝ) - 1) / 2) ∧ ‖(α i : ℂ)‖⁻¹ ≤ (Ideal.absNorm PP.asIdeal : ℝ) ^ (((D.R.t : ℝ) - 1) / 2)) ∧ GlobalTheory.GLDoubling.lFactor (Ideal.absNorm PP.asIdeal) α ((D.R.t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.lFactor (Ideal.absNorm PP.asIdeal) α⁻¹ ((D.R.t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.invNormFactor (Ideal.absNorm PP.asIdeal) (k * D.R.t) ((D.R.t : ℂ) / 2) = blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ) := by
  intro D c w hw k hk PP hPP v φ hφ x ϖ hx
  refine ⟨seg_eq_segL D v φ PP hφ x ϖ hx, card_qPar c PP x k, fun α hα => ?_⟩
  rw [qPar_twist] at hα
  have hz : ∀ i ∈ Finset.Icc 1 k, Circle.toUnits ((c.μ i * (c.μ (k + 1))⁻¹) x) =
      GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) PP := fun i hi =>
    GlobalTheory.T.unramifiedHeckeChar_at_uniformizerIdele_eq_value D v φ PP hφ x ϖ hx _ (GlobalTheory.T.hecke_char_quotient_unramified_at_twist_place D c w hw PP hPP i (k + 1) (Finset.mem_Icc.1 hi).1
      (by have := (Finset.mem_Icc.1 hi).2; omega) (by omega) (by omega))
  have hα' : Finset.univ.val.map α = ∑ i ∈ Finset.Icc 1 k,
      GlobalTheory.LFun.seg PP (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) PP) D.R.t := by
    rw [hα]; exact Finset.sum_congr rfl fun i hi => by rw [hz i hi]
  obtain ⟨hb, hL⟩ := GlobalTheory.T.segments_bounds_and_doubling_lFactor PP k D.R.t (k * D.R.t)
    (fun i => GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) PP) (fun i => GlobalTheory.LFun.norm_val _ _) α hα'
  refine ⟨hb, ?_⟩
  rw [hL, invNormFactor_eq, blockL, zinv]

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

namespace GlobalTheory.QPl.SphOne

theorem isOneComb_sph_level : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ), 1 ≤ P → P ≤ c → ∀ (ψ : AddChar k Circle), Continuous ψ → HasConductor ψ 1 → ∀ ν : Measure k, IsUnitVol ν → ∀ (L : Level (GL (n ⊕ Fin c) k)), L.J = KO k _ → (∀ j, L.lam j = 1) → IsOneComb ψ ν P L 1 (Finsupp.single 1 1) ∧ prX (Cgrp L.J 1) = KO k n := by
  intro k _ _ _ _ _ _ n _ _ c P h1 h2 ψ _ hψ ν hν L hJ hlam
  obtain ⟨J, lam⟩ := L
  dsimp only at hJ hlam
  subst hJ
  have e : lam = 1 := MonoidHom.ext fun j => hlam j
  subst e
  refine ⟨?_, GlobalTheory.QPl.PinTest.prX_KO⟩
  exact GlobalTheory.QPl.PinTest.isOneComb_sph hψ hν h1 h2

end GlobalTheory.QPl.SphOne
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

namespace GlobalTheory.QVal.InnerSupp

variable {D : D7}

theorem placeIdem_self {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) : ε * ε = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have hαα : α * α = α := by
    apply RestrictedProduct.ext
    intro w
    change evalV D.host.F w (α * α) = evalV D.host.F w α
    rw [map_mul]
    by_cases hw : w = v
    · subst hw; rw [h1, mul_one]
    · rw [h0 w hw, zero_mul]
  show ((0 : Ainf D.host.F), α) * ((0 : Ainf D.host.F), α) = ((0 : Ainf D.host.F), α)
  rw [Prod.mk_mul_mk, mul_zero, hαα]

theorem idem_sq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) :
    (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by
  obtain ⟨ε, hε, heq⟩ := q.above
  rw [heq, ← map_mul, placeIdem_self hε]

theorem support_aconv {G : Type} [AddMonoid G] (P : G → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b)) :
    ∀ l : List (G →₀ ℂ), (∀ c ∈ l, ∀ u ∈ c.support, P u) → ∀ u ∈ (aconv l).support, P u := by
  classical
  intro l
  induction l with
  | nil =>
    intro _ u hu
    have h := Finsupp.support_single_subset (show u ∈ (Finsupp.single (0 : G) (1 : ℂ)).support from hu)
    rw [Finset.mem_singleton] at h
    subst h
    exact h0
  | cons e l ih =>
    intro hl u hu
    have hu' : u ∈ (e.sum fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b)).support := hu
    have h1 := Finsupp.support_sum hu'
    rw [Finset.mem_biUnion] at h1
    obtain ⟨g, hg, h2⟩ := h1
    have h3 := Finsupp.support_sum h2
    rw [Finset.mem_biUnion] at h3
    obtain ⟨h, hh, h4⟩ := h3
    have h5 := Finsupp.support_single_subset h4
    rw [Finset.mem_singleton] at h5
    subst h5
    exact hadd g h (hl e (List.mem_cons.2 (Or.inl rfl)) g hg)
      (ih (fun c hc => hl c (List.mem_cons.2 (Or.inr hc))) h hh)

theorem side {A T : HSp D} (E₀ : AE D) (hc : cA D E₀ = E₀) (hsq : E₀ * E₀ = E₀) (c₀ : WO A T →₀ ℂ)
    (l : List (WO A T →₀ ℂ)) (h₀ : ∀ x ∈ c₀.support, IsHalf E₀ x)
    (hl : ∀ c ∈ l, ∀ u ∈ c.support, (∀ a b, E₀ * u a b = 0) ∧ u.map (infPart D) = 0) :
    IsFinComb (aconv l) ∧ (∀ u ∈ (aconv l).support, IsHalf (1 - E₀) u) ∧
      ∀ x ∈ c₀.support, ∀ y ∈ (aconv l).support, symplO A T x y = 0 := by
  have key := support_aconv (fun u : WO A T => (∀ a b, E₀ * u a b = 0) ∧ u.map (infPart D) = 0)
    ⟨fun a b => by rw [Matrix.zero_apply, mul_zero], by ext a b; simp⟩
    (fun u u' hu hu' => ⟨fun a b => by rw [Matrix.add_apply, mul_add, hu.1 a b, hu'.1 a b, add_zero], by
      ext a b
      have e1 := congrFun (congrFun hu.2 a) b
      have e2 := congrFun (congrFun hu'.2 a) b
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.add_apply] at e1 e2 ⊢
      rw [map_add, e1, e2, add_zero]⟩) l hl
  have half : ∀ u ∈ (aconv l).support, IsHalf (1 - E₀) u := fun u hu a b => by
    rw [sub_mul, one_mul, (key u hu).1 a b, sub_zero]
  refine ⟨fun u hu => (key u hu).2, half, fun x hx y hy => ?_⟩
  exact GlobalTheory.HeisComb.symplO_half A T E₀ (1 - E₀) x y hc (by rw [mul_sub, mul_one, hsq, sub_self]) (h₀ x hx) (half y hy)

end GlobalTheory.QVal.InnerSupp


open GlobalTheory.QVal.InnerSupp in
theorem GlobalTheory.QVal.inner_supp : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → (IsFinComb (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)) ∧ (Q 0).Away (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)) ∧ ∀ x ∈ (Q 0).D₁.support, ∀ y ∈ (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)).support, symplO _ _ x y = 0) ∧ (IsFinComb (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)) ∧ (Q 0).Away (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)) ∧ ∀ x ∈ (Q 0).D₂.support, ∀ y ∈ (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)).support, symplO _ _ x y = 0) := by
  intro D ψ σ S r Q hinj
  have hv : ∀ i : Fin r, (Q 0).q.v ≠ (Q i.succ).q.v := fun i h => Fin.succ_ne_zero i (hinj h).symm
  obtain ⟨hc, -, horth⟩ := GlobalTheory.PlaceIdemFacts.idem_facts D (Q 0).k (Q 0).q
  have hsq := idem_sq (Q 0).q
  have kill : ∀ (i : Fin r) {m n : ℕ} (u : Mx D m n), IsHalf ((Q i.succ).q.e + cA D (Q i.succ).q.e) u →
      (∀ a b, ((Q 0).q.e + cA D (Q 0).q.e) * u a b = 0) ∧ u.map (infPart D) = 0 := by
    intro i m n u hu
    obtain ⟨-, hinf, -⟩ := GlobalTheory.PlaceIdemFacts.idem_facts D (Q i.succ).k (Q i.succ).q
    refine ⟨fun a b => ?_, (hinf (fun _ => True) trivial m n u hu).2⟩
    rw [← hu a b, ← mul_assoc, horth (Q i.succ).k (Q i.succ).q (hv i), zero_mul]
  refine ⟨side _ hc hsq (Q 0).D₁ _ (fun x hx => (Q 0).dat₁.1 x hx) ?_, side _ hc hsq (Q 0).D₂ _ (fun x hx => (Q 0).dat₂.1 x hx) ?_⟩
  · intro c hc' u hu
    simp only [List.mem_ofFn] at hc'
    obtain ⟨i, rfl⟩ := hc'
    exact kill i u ((Q i.succ).dat₁.1 u hu)
  · intro c hc' u hu
    simp only [List.mem_ofFn] at hc'
    obtain ⟨i, rfl⟩ := hc'
    exact kill i u ((Q i.succ).dat₂.1 u hu)

end
end
