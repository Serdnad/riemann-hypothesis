module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle486
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle442
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle621
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle652
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle733
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle729
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle241
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle732
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle730
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle718
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle674
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle343
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle734
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle450
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle449
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle691

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.inv_AA_multiple_depth_lattice_maps_completion : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ v : GlobalTheory.FinPl.Pl D, ∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹) v, s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
  first | exact @GlobalTheory.AscFin.RowAAUnit.smul_mulVec_mem_latV | exact GlobalTheory.AscFin.RowAAUnit.smul_mulVec_mem_latV | (intros; apply GlobalTheory.AscFin.RowAAUnit.smul_mulVec_mem_latV <;> assumption)
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

namespace GlobalTheory.AscFin.GridLat

theorem lattices_grid : OnStd fun {D} _ _ {sc} {G} W F => (∀ i, i < D.R.m → FinLat (latRow G i) ∧ FinLat (latCore G i) ∧ FinLat (latBig G i) ∧ IsSelfDualC (G.V (.grid i 0)) (idLat (shiftId G) (G.Λ (.grid i 0)))) ∧ (∀ ρ h, IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) ∧ (∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v ∧ MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v) ∧ IsSelfDualC (negSp F.Lz) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) ∧ ∀ v, OrthAt (F.oB ρ h) (lat0 F ρ h) (G.Λ (.core (2 * ρ + 2))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) v) ∧ ∀ ρ, IsSelfDualC (negSp F.Lz) (idLat (G.pl.stA sc ^ ρ * (G.pl.stAbar sc ^ ρ)⁻¹ * shiftId G) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  intro D hq T L μ0 hL sc G W M hM F hF
  have sdG : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := by
    intro i hi
    cases i with
    | zero =>
      obtain ⟨c, hc⟩ := (hL.βY 0 (by have := D.R.two_le_m; omega) : ∃ c, _)
      exact Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
    | succ i => exact (G.sp.V_is (i + 1) 0 (by omega) hi (by omega)).sd
  have sdP : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.core i)) (G.Λ (.core i)) := fun i hi => (G.sp.P_is i hi).sd
  have sdShift : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.grid i 0)) (idLat (shiftId G) (G.Λ (.grid i 0))) := by
    intro i hi
    obtain ⟨I', h1, h2⟩ := GlobalTheory.T.exists_conjugate_inverse_staircase_modulus_ideal G.pl sc 0 1
    simp only [pow_zero, pow_one, inv_one, one_mul] at h1 h2
    exact GlobalTheory.T.isSelfDual_fractionalIdealSmulLattice_of_norm_one _ _ _ I' (sdG i hi) h1 h2
  have sdLine : ∀ a b : ℕ, IsSelfDualC (negSp F.Lz) (idLat (G.pl.stA sc ^ a * (G.pl.stAbar sc ^ a)⁻¹ *
      (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b *
        (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹))
      (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
    intro a b
    obtain ⟨I', h1, h2⟩ := GlobalTheory.T.exists_conjugate_inverse_staircase_modulus_ideal G.pl sc a b
    exact GlobalTheory.T.isSelfDual_fractionalIdealSmulLattice_of_norm_one _ _ _ I' (GlobalTheory.T.isSelfDual_standardFrame_lineLattice F hF) h1 h2
  refine ⟨fun i hi => ⟨GlobalTheory.T.isFiniteAdelicMatrixLattice_depthLatticeOfPair G (.chi i 0) (isSelfDualC_neg (sdG (i + 1) hi)) (sdG i hi.le),
    GlobalTheory.T.isFiniteAdelicMatrixLattice_depthLatticeOfPair G (.core i) (isSelfDualC_neg (sdP (i + 1) hi)) (sdP i hi.le),
    GlobalTheory.T.isFiniteAdelicMatrixLattice_latO_selfDual _ _ _ _ (sdG (i + 1) hi) (sdShift i hi.le), sdShift i hi.le⟩,
    fun ρ h => ⟨GlobalTheory.T.isSelfDual_besselCoreVertexLattice F hF ρ h, fun v => ⟨GlobalTheory.T.bessel_vertex_lattice_splits_along_witt F hF ρ h v, GlobalTheory.T.fourierJacobiVertexLattice_splitsAlongWitt_at_place F hF ρ h v⟩, ?_, fun v => GlobalTheory.T.orthAt_oB_lat0_of_std F hF ρ h v⟩,
    fun ρ => ?_⟩
  · have := sdLine (ρ + 1) 0
    simpa only [pow_zero, inv_one, mul_one] using this
  · have := sdLine ρ 1
    simp only [pow_one] at this
    exact this

end GlobalTheory.AscFin.GridLat

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

namespace GlobalTheory.RowBig

theorem latRow_zero_le_latBig : All fun {D} _ _ _ {G} _ _ => 0 < D.R.m → latRow G 0 ≤ latBig G 0 := by
  intro D hq T L μ0 hL sc G W M hM him u hu
  have hS : IsSelfDualC (G.V (.grid (0 + 1) 0)) (G.Λ (.grid (0 + 1) 0)) :=
    (G.sp.V_is (0 + 1) 0 (by omega) him (by omega)).sd
  have hT : IsSelfDualC (G.V (.grid 0 0)) (G.Λ (.grid 0 0)) := by
    obtain ⟨c, hc⟩ := (hL.βY 0 (by have := D.R.two_le_m; omega) : ∃ c, _)
    exact Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
  have h1 := idLat_one (G.Λ (.grid 0 0))
  have hsh := isSelfDualC_idLat_shiftId G _ hT
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hu' : u ∈ latO (negSp (G.V (.grid (0 + 1) 0))) (G.V (.grid 0 0)) (G.Λ (.grid (0 + 1) 0) : Set _)
      (G.Λ (.grid 0 0) : Set _) (fun _ => True) ∧
      ∀ e : AE D, IsIdemSum e G.pl.W0 → e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (0 + 1) 0)) (G.Λ (.grid 0 0))) := hu
  have key := GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift hq μ0 hL G (G.Λ (.grid (0 + 1) 0)) 1 (G.Λ (.grid 0 0)) hS (by rw [h1]; exact hT)
    (by rw [one_mul]; exact hsh) u (by rw [h1]; exact GlobalTheory.RowLoc.mem_latO_negSp.1 hu'.1) ⟨e, he, by rw [h1]; exact hu'.2 e he⟩
  rw [one_mul] at key
  exact key

end GlobalTheory.RowBig

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

theorem _root_.GlobalTheory.T.depthLatticeGridRow_le_selfDualHomLatticeShift : All fun {D} _ _ _ {G} _ _ => ∀ i, 1 ≤ i → i < D.R.m → latRow G i ≤ latBig G i := by
  first | exact @GlobalTheory.RowBig.latRow_le_latBig | exact GlobalTheory.RowBig.latRow_le_latBig | (intros; apply GlobalTheory.RowBig.latRow_le_latBig <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.exists_nsmul_selfDual_hom_lattice_mem_depth_lattice : OnStd fun {D} _ _ {sc} {G} _ _ => ∀ i, i < D.R.m → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latBig G i, N • u ∈ latRow G i := by
  first | exact @GlobalTheory.BigRow.exists_nsmul_latBig_mem_latRow | exact GlobalTheory.BigRow.exists_nsmul_latBig_mem_latRow | (intros; apply GlobalTheory.BigRow.exists_nsmul_latBig_mem_latRow <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.exists_unfolding_flatMap_ne_zero_fullRank : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∃ Φ ∈ cls dV dW p (rat x₀) y ψ, flatS dV dW s (rat x₀) y Φ ≠ 0 := by
  first | exact @GlobalTheory.AscFinNe.flat_ne_zero | exact GlobalTheory.AscFinNe.flat_ne_zero | (intros; apply GlobalTheory.AscFinNe.flat_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.exists_unit_mem_modulusDivConjugateIdeal : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (v : GlobalTheory.FinPl.Pl D), v ∉ G.pl.S0 → ∃ d : 𝓞 D.host.F, d ∉ v.asIdeal ∧ ((d : D.host.F) : D.host.E) ∈ shiftId G ∧ ∀ x ∈ shiftId G, ∃ y : 𝓞 D.host.E, (y : D.host.E) = ((d : D.host.F) : D.host.E) * x := by
  first | exact @GlobalTheory.ShiftUnit.exists_d | exact GlobalTheory.ShiftUnit.exists_d | (intros; apply GlobalTheory.ShiftUnit.exists_d <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal.OneVac

theorem isBiVac_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (LA : Set (Fin A.rank → D.host.E))
    (LS : Set (Fin S.rank → D.host.E)) (LA' : Set (Fin A'.rank → D.host.E)) :
    IsBiVac ψ A S A' LA LS LA' 0 ∧ IsBiSmooth (0 : WO A S → WO S A' → ℂ) := by
  have hz : ∀ (X Y : HSp D) (u : WO X Y), heisO ψ X Y u (0 : WO X Y → ℂ) = 0 := fun X Y u => by
    simpa using GlobalTheory.SeeSaw.Scale.heisO_smul ψ X Y u 0 0
  have h : ∀ (X Y : HSp D) (Λ : AddSubgroup (WO X Y)),
      IsThetaFunO ψ X Y (0 : WO X Y → ℂ) ∧ IsLatVac (heisO ψ X Y) Λ (0 : WO X Y → ℂ) := fun X Y Λ =>
    ⟨⟨fun γ w => by simp, ⟨⊤, isOpen_univ, fun u _ _ => hz X Y u⟩, continuous_const, fun k L hL hf w => contDiff_const⟩,
      fun u _ => hz X Y _, fun e _ u _ _ => hz X Y u⟩
  exact ⟨⟨continuous_const, fun v => h A S _, fun u => h S A' _⟩, fun n L L' _ _ _ _ u v => contDiff_const⟩

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem vacAt_of (h₁ : VacReal ch) (h₂ : VacTw ch) : VacAt ch := by
  obtain ⟨hb, z, hz, htw⟩ := h₂
  refine ⟨hb, z, hz, fun P p hp => ?_⟩
  by_cases hex : ∃ (t : T) (M : Vol ch.G), M.Is t
  · obtain ⟨t₀, M₀, hM₀⟩ := hex
    obtain ⟨b₀, hb₀⟩ := hb t₀
    refine ⟨fun j => ((z t₀ j : ℂ)⁻¹) • conAt ch.W hM₀ (fockD ch.W t₀ (fun j => ch.rm.vT D.R.m j) P) (p * b₀) j,
      fun j hj hj' => ?_, fun t M hM b hbt j hj hj' => ?_⟩
    · obtain ⟨hv, hs⟩ := h₁ t₀ M₀ hM₀ b₀ hb₀ P p hp j hj hj'
      exact ⟨GlobalTheory.SeeSaw.Scale.isBiVac_smul _ hv, GlobalTheory.SeeSaw.Scale.isBiSmooth_smul _ hs⟩
    · have e := htw t t₀ M M₀ hM hM₀ b b₀ hbt hb₀ P p hp j hj hj'
      rw [smul_comm, ← e, smul_smul, inv_mul_cancel₀ (z t₀ j).ne_zero, one_smul]
  · exact ⟨0, fun j _ _ => isBiVac_zero _ _ _ _ _ _ _, fun t M hM => absurd ⟨t, M, hM⟩ hex⟩

theorem big_vacAt : Big fun ch => VacAt ch :=
  GlobalTheory.RowReal.big_mono (Q := fun ch => VacReal ch ∧ VacTw ch) (fun ch h => vacAt_of ch h.1 h.2)
    (Big.and GlobalTheory.T.unfoldedVacuaAreRealDatum_largeDepth GlobalTheory.T.unfoldedVacua_differ_by_twist_values_largeDepth)

end GlobalTheory.RowVal.OneVac

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowWt

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem wtAt_big : Big fun ch => ∀ s, WtAt ch s := by
  refine GlobalTheory.RowReal.big_mono ?_ (GlobalTheory.T.rowTest_tupleTerm_measures_differ_by_scalars.and GlobalTheory.T.unfolding_cell_mass_eq_const_mul_local_coefficients)
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h s ρ μ hH
  obtain ⟨hA, hC⟩ := h
  have hc := hC s ρ μ hH
  classical
  let cf : ℕ → ℂ := fun j => if hj : j ∈ idx D then (hc j hj).choose else 1
  refine ⟨((idx D).map cf).prod, fun t Φ β b hb M M' hM hM' => ?_⟩
  obtain ⟨x, hx, hx1⟩ := hA t Φ β M M' hM hM'
  refine ⟨x, hx, ?_⟩
  have hlt : ∀ j ∈ idx D, 1 ≤ j ∧ j + 2 ≤ D.R.m := fun j hj => by
    rw [idx, List.mem_range'_1] at hj; omega
  have hgf : ∀ j ∈ idx D, b j ∈ GfC _ := fun j hj => by
    obtain ⟨δ, r, -, -, hf⟩ := hb.2 j hj (by have := hlt j hj; omega)
    exact hf.1
  have hfac : ∀ j ∈ idx D, (if h : b j ∈ GfC _ then cellWt (ρ j) (μ j) ((latGrp ch.G j).subgroupOf _) ⟨b j, h⟩ else 0) *
      ((x (.top j) : ℝ) : ℂ) = cf j * (colCoef ch t β j : ℂ) := fun j hj => by
    rw [dif_pos (hgf j hj)]
    have hs := hx (.top j) (show j ≤ D.R.m by have := hlt j hj; omega) (by simp only [ne_eq, Node.top.injEq]; have := hlt j hj; omega)
    have e := (hc j hj).choose_spec t Φ β b hb M M' hM hM' (x (.top j)) hs (hgf j hj)
    simp only [cf, dif_pos hj]
    exact e
  have hsP : sProd D x = ((idx D).map fun j => ((x (.top j) : ℝ) : ℂ)).prod := by
    have h2 : ∏ i ∈ Finset.range (D.R.m + 1), ((x (.grid i D.R.m) : ℝ) : ℂ) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      rw [hx1 (.grid i D.R.m) ⟨by simp at hi; omega, rfl⟩ (by simp) (fun j _ => by simp)]
      simp
    rw [sProd, h2, mul_one, ← List.prod_toFinset _ (show (idx D).Nodup from List.nodup_range')]
    symm
    refine Finset.prod_subset (fun j hj => ?_) (fun j hj0 hj => ?_)
    · rw [List.mem_toFinset] at hj
      have := hlt j hj
      exact Finset.mem_range.2 (by omega)
    · rw [List.mem_toFinset] at hj
      have hj1 := Finset.mem_range.1 hj0
      rw [hx1 (.top j) (show j ≤ D.R.m by omega) (by simp only [ne_eq, Node.top.injEq]; omega) (fun j' hj' e => by cases e; exact hj hj')]
      simp
  have hwt : GlobalTheory.RowVal.wt ρ μ b = ((idx D).map fun j => if h : b j ∈ GfC _ then cellWt (ρ j) (μ j) ((latGrp ch.G j).subgroupOf _) ⟨b j, h⟩
      else 0).prod := by
    unfold GlobalTheory.RowVal.wt
    congr 1
  rw [hwt, hsP, ← List.prod_map_mul, List.map_congr_left hfac, List.prod_map_mul, coef_prod]

end GlobalTheory.RowWt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVacScalar

private theorem map_mt_one_eq_one {D : D7} (V : HSp D) : (Formalism.L2.Theta.mt V 1).map (finPart D) = 1 := by
  rw [Formalism.L2.Theta.mt, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem scalars_eq_edgeFactors : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ (c₁ c₂ : ℂ),
    W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) →
    W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) =
      c₂ • S.Z.vac (.chi (j + 1) D.R.m) →
    c₁ * c₂ = ∏ w : locPl G t, ((oppositePath D.R.m).map ((locGrid G t w.1).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w.1 (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w.1
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  intro D T L sc G W U S μ₀ hL t ht j hj k hk c₁ c₂ h₁ h₂
  obtain ⟨hA, hB, hC, hD⟩ := GlobalTheory.RowMovedLat.moved_pair_stab S ht j hj k hk
  have e₁ := GlobalTheory.RowVacScalar.vacScalar_eq_prod S hL t j hj.le _ hA ?g₁ hB ?l₁ c₁ h₁
  have e₂ := GlobalTheory.RowVacScalar.vacScalar_eq_prod S hL t (j + 1) hj _ ?g₂ hC ?l₂ hD c₂ h₂
  · rw [e₁, e₂, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact GlobalTheory.T.splitPlaceScalars_mul_eq_oppositePath_edgeFactors S ht j hj k hk w.1 w.2 ⟨_, GlobalTheory.RowVacScalar.isIdemAt_idemAt hL G t w.2⟩
  case g₁ =>
    dsimp only [GridData.toPair]
    exact one_mem _
  case l₁ =>
    intro y
    dsimp only [GridData.toPair]
    rw [map_mt_one_eq_one, Matrix.one_mulVec]
  case g₂ =>
    dsimp only [GridData.toPair]
    rw [map_one]
    exact one_mem _
  case l₂ =>
    intro y
    dsimp only [GridData.toPair]
    rw [map_one, map_mt_one_eq_one, Matrix.one_mulVec]

end GlobalTheory.RowVacScalar
end
end
