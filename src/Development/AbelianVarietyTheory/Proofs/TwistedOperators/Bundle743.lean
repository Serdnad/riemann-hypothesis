module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle729
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle445
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle732
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingExpansionProductFunctionFixedByKplus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle410
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle495
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle621
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle653
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle636
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle737
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle726
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


open GlobalTheory.SeeSaw (idV FI dI) in
theorem GlobalTheory.AscFin.coef_superdiag : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m)
    (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))) (𝔠 : GlobalTheory.SeeSaw.FI D), 𝔠 ≠ 0 →
    ∀ v : GlobalTheory.FinPl.Pl D, (∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV 𝔠 v,
      s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v)) → ∀ i j : Fin ρ, j.1 = i.1 + 1 →
    GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈
      GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ D.host.xi0 * G.pl.stAbar sc * 𝔠⁻¹) v := by
  intro D hD T L μ0 hL sc G W M0 hM0 F hF ρ h M 𝔠 h𝔠 v hM i j hij
  obtain ⟨-, f2, -, -, -, -, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D W.ψ W.ψ_std v
  have hmono : MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v :=
    ((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W M0 hM0 F hF).2.1 ρ h).2.1 v |>.2
  obtain ⟨hcB, heB, -⟩ := hF.hB ρ h
  obtain ⟨hcJ, heJ, -⟩ := hF.hJ ρ h
  have hlatB := G.sp.colLat (2 * ρ + 2) (by omega) h
  have hlatJ := G.sp.colLat (2 * ρ + 1) (by omega) (by omega)
  have hx : ∀ n : ℕ, (-D.host.xi0) ^ n ≠ 0 := fun n => pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)
  let 𝔟B : Fin ρ → FI D := fun p => FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
    stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) (Fin.castLE (by omega) p)
  let 𝔟J : Fin ρ → FI D := fun p => FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
    stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p)
  have lineB : ∀ (p : Fin ρ) (a : AE D), GlobalTheory.FinPl.colMul (F.dB ρ h).jX p a ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v) ↔
      a ∈ idV (𝔟B p) v := by
    intro p a
    have e1 : GlobalTheory.FinPl.colMul (F.dB ρ h).jX p a = fun k => a * incA D ((-D.host.xi0) ^ (p.1 + 1) *
        (G.colDec (2 * ρ + 2) (by omega) h).a k (Fin.castLE (by omega) p)) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, heB, colsOf]
    rw [e1]
    have e2 : G.Λ (.grid (2 * ρ + 2) 0) = _ := hlatB
    rw [e2]
    exact GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega) (hx _) v a
  have lineJ : ∀ (p : Fin ρ) (a : AE D), GlobalTheory.FinPl.colMul (F.dJ ρ h).jX p a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) ↔
      a ∈ idV (𝔟J p) v := by
    intro p a
    have e1 : GlobalTheory.FinPl.colMul (F.dJ ρ h).jX p a = fun k => a * incA D ((-D.host.xi0) ^ (p.1 + 1) *
        (G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p)) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, heJ, colsOf]
    rw [e1]
    have e2 : G.Λ (.grid (2 * ρ + 1) 0) = _ := hlatJ
    rw [e2]
    exact GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega) (hx _) v a
  have hN : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hN' : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.AscFin.PrimStd.modulBar_ne_bot G.pl sc)
  have hA : G.pl.stA sc ≠ 0 := mul_ne_zero (GlobalTheory.CuspCharLattice.host_AA_ne_zero _) (inv_ne_zero hN')
  have hAb : G.pl.stAbar sc ≠ 0 := mul_ne_zero (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (inv_ne_zero hN)
  have hsp : ∀ n : ℕ, FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((-D.host.xi0) ^ n)⁻¹) ≠ 0 := fun n => by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact inv_ne_zero (hx _)
  have hb0B : ∀ p, 𝔟B p ≠ 0 := fun p => mul_ne_zero (hsp _) (by
    unfold stairId; exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hAb)))
  have hb0J : ∀ p, 𝔟J p ≠ 0 := fun p => mul_ne_zero (hsp _) (by
    unfold stairId; exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hAb)))
  have hrat : 𝔟J i * (𝔟B j)⁻¹ = FractionalIdeal.spanSingleton _ D.host.xi0 * G.pl.stAbar sc := by
    rw [mul_inv_eq_iff_eq_mul₀ (hb0B j)]
    have hneg : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (-D.host.xi0) = FractionalIdeal.spanSingleton _ D.host.xi0 :=
      FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, by simp⟩
    have e2 : ((-D.host.xi0) ^ (i.1 + 1))⁻¹ = -D.host.xi0 * ((-D.host.xi0) ^ (j.1 + 1))⁻¹ := by
      have hξ : -D.host.xi0 ≠ 0 := neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero
      rw [hij]
      field_simp
      ring
    show FractionalIdeal.spanSingleton _ _ * stairId _ _ _ _ = _ * (FractionalIdeal.spanSingleton _ _ * stairId _ _ _ _)
    rw [e2, ← FractionalIdeal.spanSingleton_mul_spanSingleton, hneg]
    unfold stairId
    simp only [Fin.coe_castLE]
    have e3 : 2 * ρ + 1 - 1 - i.1 = 2 * ρ + 2 - 1 - j.1 := by omega
    rw [e3, hij, pow_succ (G.pl.stAbar sc) (i.1 + 1), mul_inv]
    conv_lhs => rw [show (G.pl.stAbar sc ^ (i.1 + 1))⁻¹ = G.pl.stAbar sc * ((G.pl.stAbar sc ^ (i.1 + 1))⁻¹ * (G.pl.stAbar sc)⁻¹) by
      rw [mul_comm ((G.pl.stAbar sc ^ (i.1 + 1))⁻¹), ← mul_assoc, mul_inv_cancel₀ hAb, one_mul]]
    ring
  have hxA : GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  rw [← hrat]
  refine (f2 𝔠 _ h𝔠 (mul_ne_zero (hb0J i) (inv_ne_zero (hb0B j))) _ hxA).1 ?_
  intro s hs
  have hsA : s ∈ idAt D (· = v) := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ s hs
  refine (f2 (𝔟B j) (𝔟J i) (hb0B j) (hb0J i) _ (Ideal.mul_mem_right _ _ hxA)).1 ?_
  intro c hc
  have hcA : c ∈ idAt D (· = v) := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ c hc
  have h1 := hM _ ((lineB j c).2 hc) s hs
  have h3 := ((hmono _).1 h1).1 i
  rw [Matrix.mulVec_smul, GlobalTheory.FinPl.PsiUnit.mulVec_colMul, GlobalTheory.FinPl.PsiUnit.mulVec_colMul] at h3
  have h4 := (lineJ i _).1 h3
  have e4 : ((s • GlobalTheory.FinPl.colMul ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) j c) i) =
      GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j * s * c := by
    rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.FinPl.colMul]
    have hc' := (GlobalTheory.FinPlLoc.mem_idAt_iff _ c).1 hcA
    calc s * (c * _) = s * ((GlobalTheory.FinPlLoc.idem D (· = v) * c) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) := by rw [hc']
      _ = _ := by ring
  rwa [e4] at h4
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.CorePiece

variable {D : D7}

theorem proj_mem_adelic_lattice_of_mono {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {P : GlobalTheory.FinPl.Pl D → Prop}
    (hL₀ : Submodule.IsLattice D.host.E L₀) (hm : ∀ v, P v → MonoAt d L L₀ v) {z : Fin S.rank → AE D}
    (hz : z ∈ latA S L P) : d.p0 *ᵥ z ∈ latA S₀ L₀ P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hu
    have hu' : u ∈ latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have heq : d.p0 *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (d.p0 *ᵥ u) k := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hu]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
      rw [h1]; ring
    rw [heq]
    exact GlobalTheory.FinPl.VacFlat.smul_mem_latA ha (GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits d hL₀ hm hu')
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem mem_lattice_of_extend_inclusion {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {LV : Lat V} {LV₀ : Lat V₀} {LW : Lat W} {LW₀ : Lat W₀}
    (hV : IsSelfDualC V LV) (hV₀ : IsSelfDualC V₀ LV₀) (hW₀ : IsSelfDualC W₀ LW₀)
    (hmV : ∀ v, MonoAt dV LV LV₀ v) (hmW : ∀ v, MonoAt dW LW LW₀ v) {u : WO V₀ W₀}
    (hu : dV.ext0 W (dW.inc0 V₀ u) ∈ latO V W (LV : Set _) (LW : Set _) fun _ => True) :
    u ∈ latO V₀ W₀ (LV₀ : Set _) (LW₀ : Set _) fun _ => True := by
  have hE : dV.ext0 W (dW.inc0 V₀ u) = dW.j0 * u * dV.p0 := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply]
  rw [hE] at hu
  have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  have hu0 : dW.p0 * (dW.j0 * u * dV.p0) * dV.j0 = u := by
    simp only [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    simp only [Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one]
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D V₀ W₀ LV₀ LW₀ hV₀ hW₀ _ u).2 ⟨?_, fun y hy => ?_⟩
  · rw [← hu0]
    intro i j
    rw [Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine sum_mem fun k _ => ?_
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hx k l))
  · have key : (show Matrix (Fin W₀.rank) (Fin V₀.rank) (AE D) from u) *ᵥ y =
        dW.p0 *ᵥ ((dW.j0 * u * dV.p0) *ᵥ (dV.j0 *ᵥ y)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu0]
    rw [key]
    exact proj_mem_adelic_lattice_of_mono dW hW₀.1 (fun v _ => hmW v)
      (GlobalTheory.FinPl.LatMem.latO_maps hV hu (GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace dV hV.1 (fun v _ => hmV v) hy))

theorem core_fin_vac : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m),
    (∀ u ∈ (pcBF W F ρ h).Γ₀, MxAt (fun _ => True) (show Mx D (G.V (.core (2 * ρ + 1))).rank (F.V₀ ρ).rank from u)) ∧
      ∃ f, VacG W.ψ (F.V₀ ρ) (G.V (.core (2 * ρ + 1))) (pcBF W F ρ h).Γ₀ f ∧ f ≠ 0 := by
  intro D hOff T L μ0 hL sc G W M hM F hF ρ h
  obtain ⟨-, hB, -⟩ := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hOff T L μ0 hL sc G W M hM F hF
  obtain ⟨hsd0, hmono, -, -⟩ := hB ρ h
  have hV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ (fun j hj => by injection hj with h1 h2; omega)).sd
  have hW₀ : IsSelfDualC (G.V (.core (2 * ρ + 1))) (G.Λ (.core (2 * ρ + 1))) :=
    (G.isV (X := .core (2 * ρ + 1)) (show 2 * ρ + 1 ≤ D.R.m by omega) (fun j hj => Node.noConfusion hj)).sd
  have hle : (pcBF W F ρ h).Γ₀ ≤ latO (F.V₀ ρ) (G.V (.core (2 * ρ + 1))) (lat0 F ρ h : Set _)
      (G.Λ (.core (2 * ρ + 1)) : Set _) fun _ => True := by
    intro u hu
    refine mem_lattice_of_extend_inclusion (F.dB ρ h) (F.dJ ρ h) hV hsd0 hW₀ (fun v => (hmono v).1) (fun v => (hmono v).2) ?_
    exact GlobalTheory.RowLoc.mem_latO_negSp.1 (AddSubgroup.mem_comap.1 hu).1
  exact ⟨fun u hu => GlobalTheory.FinPl.LatMem.latO_mxAt (hle hu), GlobalTheory.T.exists_ne_zero_latticeVacuum_selfDual D W.ψ W.ψ_std _ _ _ _ hsd0 hW₀ _ hle⟩

end GlobalTheory.AscFin.CorePiece

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.PcFBVac

variable {D : D7}

theorem mxAt_mul_mul {P : GlobalTheory.FinPl.Pl D → Prop} {k l m n : ℕ} (b : Mx D k l) {a : Mx D l m} (c : Mx D m n)
    (ha : MxAt P a) : MxAt P (b * a * c) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun r _ => Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun s _ => Ideal.mul_mem_left _ _ (ha s r))

theorem pcFB_vac : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∃ f, VacG W.ψ _ _ (pcFB W F σ h h').Γ₀ f ∧ f ≠ 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨-, H2, -⟩ := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF
  have sdT : IsSelfDualC (F.V₀ σ) (lat0 F σ h') := (H2 σ h').1
  have monoB : ∀ v, MonoAt (F.dB σ h') (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v := fun v => ((H2 σ h').2.1 v).1
  have monoJ : ∀ v, MonoAt (F.dJ (σ + 1) h) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.core (2 * (σ + 1) + 1))) v :=
    fun v => ((H2 (σ + 1) h).2.1 v).2
  have sdC := GlobalTheory.CosetRow.selfDual_chi hL G (2 * σ + 2) (by omega)
  have sdS : IsSelfDualC (G.V (.core (2 * (σ + 1) + 1))) (G.Λ (.core (2 * (σ + 1) + 1))) :=
    (node_isV G hL (X := .core (2 * (σ + 1) + 1)) (show 2 * (σ + 1) + 1 ≤ D.R.m by omega)).sd
  have sdV : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    (node_isV G hL (X := .grid (2 * (σ + 1) + 1) 0) (show 2 * (σ + 1) + 1 ≤ D.R.m ∧ 0 ≤ D.R.m by omega)).sd
  refine GlobalTheory.T.exists_ne_zero_latticeVacuum_selfDual D W.ψ W.ψ_std _ _ (G.Λ (.core (2 * (σ + 1) + 1))) (lat0 F σ h') sdS sdT _ ?_
  intro u hu
  have hw := (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ sdC.1 sdC.2 (fun _ => True) _).1 hu.1
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ sdS sdT]
  have hu' : u = (F.dB σ h').p0 * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) * (F.dJ (σ + 1) h).j0 := by
    simp only [Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one]
    rw [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
  refine ⟨?_, fun y hy => ?_⟩
  · rw [hu']
    exact mxAt_mul_mul _ _ hw.1
  · have hj : (F.dJ (σ + 1) h).j0 *ᵥ y ∈ latV (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) fun _ => True :=
      GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace (F.dJ (σ + 1) h) sdV.1 (fun v _ => monoJ v) hy
    have h2 := hw.2 _ hj
    have e : ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) *ᵥ ((F.dJ (σ + 1) h).j0 *ᵥ y) = (F.dB σ h').j0 *ᵥ (u *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    change ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) *ᵥ ((F.dJ (σ + 1) h).j0 *ᵥ y) ∈ _ at h2
    rw [e] at h2
    have h3 := GlobalTheory.FinPl.ColSplitA.mulVec_mem_latA (F.dB σ h').p0
      (fun z hz => GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits _ sdT.1 (fun v _ => monoB v) hz) h2
    rw [Matrix.mulVec_mulVec, HypDec.p0_j0, Matrix.one_mulVec] at h3
    exact h3

end GlobalTheory.AscFin.PcFBVac

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LineCompLat

variable {D : D7}

theorem rat_mulVec_tmul {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (t : AF D.host.F) (x : Fin n → D.host.E) :
    rat M *ᵥ (fun l => t ⊗ₜ[D.host.F] (1 * x l)) = fun k => t ⊗ₜ[D.host.F] (1 * (M *ᵥ x) k) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, one_mul, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] M k l) * (t ⊗ₜ[D.host.F] x l) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem rat_mulVec_latV {S S' : HSp D} {L : Lat S} {L' : Lat S'} {P : GlobalTheory.FinPl.Pl D → Prop}
    (M : Matrix (Fin S'.rank) (Fin S.rank) D.host.E) (hM : ∀ x ∈ L, M *ᵥ x ∈ L')
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : rat M *ᵥ y ∈ latV S' L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [rat_mulVec_tmul]
    exact AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, M *ᵥ x, hM x hx, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem mxAt_mul_left {P : GlobalTheory.FinPl.Pl D → Prop} {k m n : ℕ} (B : Mx D k m) {A : Mx D m n} (hA : MxAt P A) :
    MxAt P (B * A) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hA l j)

theorem mxAt_mul_right {P : GlobalTheory.FinPl.Pl D → Prop} {k m n : ℕ} {A : Mx D k m} (hA : MxAt P A) (C : Mx D m n) :
    MxAt P (A * C) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hA i l)

end GlobalTheory.LineCompLat

open GlobalTheory.LineCompLat

theorem GlobalTheory.AscFin.BoxBF.lineComp_mem_latO : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 ∈ latO (negSp F.Lz) (G.V (.core (2 * ρ + 1))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) : Set _) (G.Λ (.core (2 * ρ + 1)) : Set _) fun _ => True := by
  intro D hD T L μ0 hL sc G W Mv hM F hF ρ h u hu
  obtain ⟨hsd0, hloc, hsdM, horth⟩ := (GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W Mv hM F hF).2.1 ρ h
  have sdV : IsSelfDualC (negSp (G.V (.grid (2 * ρ + 1 + 1) 0))) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    isSelfDualC_neg (G.sp.V_is (2 * ρ + 1 + 1) 0 (by omega) h (by omega)).sd
  have sdW : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (G.sp.V_is (2 * ρ + 1) 0 (by omega) (by omega) (by omega)).sd
  have sdC : IsSelfDualC (G.V (.core (2 * ρ + 1))) (G.Λ (.core (2 * ρ + 1))) :=
    (G.sp.P_is (2 * ρ + 1) (by omega)).sd
  have hU1 : (F.dJ ρ h).j0 * u * (F.dB ρ h).p0 ∈ latRow G (2 * ρ + 1) := hu
  have hU := hU1.1
  dsimp only [GridData.pS, GridData.pT, GridData.latS, GridData.latT] at hU
  clear hU1 hu
  have hu' : u = (F.dJ ρ h).p0 * ((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) * (F.dB ρ h).j0 := by
    simp only [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    rw [Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [OrthDec.resS_apply]
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ hsdM sdC _ _).2 ⟨?_, fun z hz => ?_⟩
  · rw [hu']
    exact mxAt_mul_right (mxAt_mul_right (mxAt_mul_left _ (GlobalTheory.FinPl.LatMem.latO_mxAt hU)) _) _
  have h1 : (F.oB ρ h).jB *ᵥ z ∈ latV (F.V₀ ρ) (lat0 F ρ h) fun _ => True := by
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latV_of_local hsdM.1 hsd0.1 (F.oB ρ h).jB (fun v _ y hy => ?_) hz
    refine ((horth v) _).2 ⟨?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, OrthDec.pA_jB, Matrix.zero_mulVec]; exact zero_mem _
    · rw [Matrix.mulVec_mulVec, OrthDec.pB_jB, Matrix.one_mulVec]; exact hy
  have h2 : (F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z) ∈
      latV (negSp (G.V (.grid (2 * ρ + 1 + 1) 0))) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) fun _ => True :=
    rat_mulVec_latV (F.dB ρ h).i₀ (fun x hx => hx) h1
  have h3 := GlobalTheory.FinPl.LatMem.latO_maps sdV hU h2
  have h4 : (F.dJ ρ h).p0 *ᵥ (((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) *ᵥ ((F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z))) ∈
      latA _ (G.Λ (.core (2 * ρ + 1))) fun _ => True := by
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latA (F.dJ ρ h).p0 (fun y hy => ?_) h3
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latV_of_local sdW.1 sdC.1 (F.dJ ρ h).p0 (fun v _ y' hy' => ?_) hy
    exact (((hloc v).2 y').1 hy').2.2
  have e : (F.dJ ρ h).p0 *ᵥ (((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) *ᵥ ((F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z))) =
      (u * (F.oB ρ h).jB) *ᵥ z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    rw [Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [← e]
  exact h4
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

theorem exists_locAt_big : Big fun ch => ∃ s, LocAt ch s :=
  GlobalTheory.RowReal.big_mono (fun ch h => by
               obtain ⟨⟨⟨s, hP⟩, hC⟩, hL⟩ := h
               exact ⟨s, hL s hP hC⟩)
    (Big.and (Big.and GlobalTheory.T.exists_sign_flatDictionaryAtOnePlace_largeDepth GlobalTheory.T.unfoldedProduct_depends_on_dataProduct) GlobalTheory.T.flat_dictionary_relative_base_vacua_large_depth)

end GlobalTheory.RowVal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.unfoldingExpansion_productFunction_fixed_by_Kplus : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ k : FinPt G (.top 0), finG (G.V (.top 0)) k ∈ G.Kplus →
    ∀ z : ∀ l : Arr D, WO (G.pS (arrP t l)) (G.pT (arrP t l)),
      (τ.sum fun d b => b * ∏ l, moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d) l (z l)) =
        τ.sum fun d b => b * ∏ l, vecsOf S d l (z l) := by
  first | exact @GlobalTheory.TopZeroFirst.product_invariant | exact GlobalTheory.TopZeroFirst.product_invariant | (intros; apply GlobalTheory.TopZeroFirst.product_invariant <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

theorem _root_.GlobalTheory.T.psiE_at_S0_column_pair : All fun {D} _ _ {sc} {G} W _ => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))), u ∈ latRow G (2 * σ + 2) → ∀ (p : Fin (σ + 1)) (v : GlobalTheory.FinPl.Pl D), v ∈ G.pl.S0 → psiE W.ψ (GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev))) = 1 := by
  first | exact @GlobalTheory.CharXFB.HeisenbergPairBadPlaces.traceCharacter_trivial_heisenbergPair_at_badPlaces | exact GlobalTheory.CharXFB.HeisenbergPairBadPlaces.traceCharacter_trivial_heisenbergPair_at_badPlaces | (intros; apply GlobalTheory.CharXFB.HeisenbergPairBadPlaces.traceCharacter_trivial_heisenbergPair_at_badPlaces <;> assumption)
end
