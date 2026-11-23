module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle495
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle745
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle254
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle736
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle665
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle653
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle672
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle746
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle486
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle451
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle241
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntertwinesCoreHeisenbergOperators
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle606
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle643
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle639
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle328
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle747
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle702
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle737
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecOfEqIntertwiner
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

theorem GlobalTheory.AscFin.psiE_superdiag_S0 : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → ∀ v : GlobalTheory.FinPl.Pl D, v ∈ G.pl.S0 → ∀ o ∈ intAt D (· = v), psiE W.ψ (o * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) = 1 := by
  intro D hQ T L μ0 hL sc G W Mv hM F hF ρ h M hMr i j hij v hv o ho
  have hAA : (D.host.AA : GlobalTheory.SeeSaw.FI D) ≠ 0 := GlobalTheory.HostAAPartition.host_AA_ne_zero D
  have hm : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.AscFin.PrimStd.modulBar_ne_bot G.pl sc)
  have hsh : shiftId G ≠ 0 := mul_ne_zero hm (inv_ne_zero hmB)
  have h1 := GlobalTheory.T.besselJacobi_superdiagonal_entries_at_place D hQ T L μ0 hL sc G W Mv hM F hF ρ h M _ (inv_ne_zero hAA) v
    (GlobalTheory.T.inv_AA_multiple_depth_lattice_maps_completion D hQ T L μ0 hL sc G W Mv hM F hF ρ h M hMr v) i j hij
  have h2 := GlobalTheory.T.besselJacobi_superdiagonal_entries_at_place D hQ T L μ0 hL sc G W Mv hM F hF ρ h M _ (mul_ne_zero (inv_ne_zero hAA) (inv_ne_zero hsh)) v
    (GlobalTheory.T.besselStep_depthLattice_mulVec_mem_completion D hQ T L μ0 hL sc G W Mv hM F hF ρ h M hMr v) i j hij
  have e1 : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * G.pl.stAbar sc * (D.host.AA : GlobalTheory.SeeSaw.FI D)⁻¹⁻¹ =
      GlobalTheory.SeeSaw.dI D * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := by
    unfold Places.stAbar GlobalTheory.SeeSaw.dI
    rw [inv_inv]
    ring
  have e2 : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * G.pl.stAbar sc *
      ((D.host.AA : GlobalTheory.SeeSaw.FI D)⁻¹ * (shiftId G)⁻¹)⁻¹ =
      GlobalTheory.SeeSaw.dI D * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := by
    unfold Places.stAbar GlobalTheory.SeeSaw.dI shiftId
    rw [mul_inv, inv_inv, inv_inv]
    field_simp
  rw [e1] at h1
  rw [e2] at h2
  have hx := GlobalTheory.T.mem_completion_of_mem_modulus_and_conj_quotients G.pl sc v _ _ h1 h2
  have hxA : GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  have hψ := ((GlobalTheory.T.fractionalIdealCompletion_properties_at_place D W.ψ W.ψ_std v).2.2.2.2.1 _ hxA).1 hx o ho
  have ho' : GlobalTheory.FinPlLoc.idem D (· = v) * o = o := (GlobalTheory.FinPlLoc.mem_idAt_iff _ o).1 ho.1
  rw [← ho']
  rw [← hψ]
  congr 1
  ring

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

namespace GlobalTheory.AscFin

theorem pcBF_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h
  refine ⟨fun u hu => ?_⟩
  have e1 := ((F.dB ρ h).coordS (G.V (.grid (2 * ρ + 1) 0))).symm_apply_apply u
  have e2 := ((F.dJ ρ h).coordT (F.V₀ ρ)).symm_apply_apply (u ⬝ (F.dB ρ h).j0)
  obtain ⟨s1, -, s3⟩ := GlobalTheory.T.bessel_depth_lattice_splits_along_source_witt D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  obtain ⟨f4, i4⟩ := GlobalTheory.T.depthLatticeGridRow_dualPart_finite_pairs_trivially D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  have b := GlobalTheory.T.depth_lattice_core_parts_mem_selfDual_lattice D hq T L μ0 hL sc G W M hM F hF ρ h _ s3
  refine ⟨u ⬝ (F.dB ρ h).jX, s1, u ⬝ (F.dB ρ h).jY, AddSubgroup.subset_closure ⟨f4, i4⟩,
    (F.dJ ρ h).pX ⬝ (u ⬝ (F.dB ρ h).j0), b.1, (F.dJ ρ h).pY ⬝ (u ⬝ (F.dB ρ h).j0), b.2,
    (F.dJ ρ h).p0 ⬝ (u ⬝ (F.dB ρ h).j0), GlobalTheory.T.bessel_depth_lattice_core_splits_along_target_witt D hq T L μ0 hL sc G W M hM F hF ρ h _ s3, ?_,
    GlobalTheory.T.base_point_character_trivial_on_depth_lattice D hq T L μ0 hL sc G W M hM F hF ρ h u hu, GlobalTheory.T.besselSecondBasePoint_character_trivial_depthLattice D hq T L μ0 hL sc G W M hM F hF ρ h u hu⟩
  have e2' : (F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ (u ⬝ (F.dB ρ h).j0)) + (F.dJ ρ h).incY (F.V₀ ρ) ((F.dJ ρ h).pY ⬝ (u ⬝ (F.dB ρ h).j0)) + (F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 ⬝ (u ⬝ (F.dB ρ h).j0)) = (u ⬝ (F.dB ρ h).j0) := by
    simp only [HypDec.coordT, AddEquiv.coe_mk, Equiv.coe_fn_mk, AddEquiv.symm_mk, Equiv.coe_fn_symm_mk] at e2
    exact (add_right_comm _ _ _).trans e2
  have e1' : (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jX) + (F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY) + (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).j0) = u := by
    simp only [HypDec.coordS, AddEquiv.coe_mk, Equiv.coe_fn_mk, AddEquiv.symm_mk, Equiv.coe_fn_symm_mk] at e1
    exact (add_right_comm _ _ _).trans e1
  rw [e2', e1']

end GlobalTheory.AscFin
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BoxFB

theorem isHalf_mul_left {D : D7} {k m n : ℕ} {e : AE D} (a : Mx D k m) {u : Mx D m n} (hu : IsHalf e u) :
    IsHalf e (a * u) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, hu l j]

theorem vacG_boxT {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {T A B S : HSp D} (d : OrthDec T A B)
    {Γ : AddSubgroup (WO S T)} {ΓA : AddSubgroup (WO S A)} {ΓB : AddSubgroup (WO S B)}
    (hA : ∀ u ∈ Γ, (d.resT S u).1 ∈ ΓA) (hB : ∀ u ∈ Γ, (d.resT S u).2 ∈ ΓB)
    {fA : WO S A → ℂ} {fB : WO S B → ℂ} (vA : VacG ψ S A ΓA fA) (vB : VacG ψ S B ΓB fB) :
    VacG ψ S T Γ (d.boxT S fA fB) := by
  refine ⟨d.isThetaFunO_boxT vA.1 vB.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · rw [d.heisO_boxT, map_nsmul, Prod.smul_fst, Prod.smul_snd, vA.2.1 _ (hA u hu), vB.2.1 _ (hB u hu)]
  · rw [d.heisO_boxT, vA.2.2 e he _ (hA u hu) (by rw [d.resT_apply]; exact isHalf_mul_left _ hh),
      vB.2.2 e he _ (hB u hu) (by rw [d.resT_apply]; exact isHalf_mul_left _ hh)]

end GlobalTheory.BoxFB

namespace GlobalTheory.BoxFB

theorem core_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).1 ∈ latCore G (2 * σ + 2) := GlobalTheory.T.jacobi_step_core_component_mem_core_depth_lattice

theorem line_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).2 ∈ lineLat F (σ + 1) := GlobalTheory.T.fourierJacobi_depth_lattice_line_components_mem

theorem vacG_boxT_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ Ξ₁ Φ₀, VacG W.ψ _ _ (latCore G (2 * σ + 2)) Ξ₁ → VacG W.ψ _ _ (lineLat F (σ + 1)) Φ₀ → VacG W.ψ _ _ (pcFB W F σ h h').Γ₀ ((F.oB σ h').boxT _ Ξ₁ Φ₀) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h' Ξ₁ Φ₀ hΞ hΦ
  exact vacG_boxT (F.oB σ h') (core_mem D hD T L μ0 hL sc G W M hM F hF σ h h')
    (line_mem D hD T L μ0 hL sc G W M hM F hF σ h h') hΞ hΦ

end GlobalTheory.BoxFB

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowFlatAsm

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)

theorem evT_combC_smul (c : Combs G) (a : ℕ → ℂ) (C C' : BiFam G) (h : ∀ j, Even j → j < D.R.m → C j = a j • C' j)
    (f : SchRow G) (u : ColPt G) (y : RowPt G) :
    evT (combC W c C) f u y = (∏ k ∈ Finset.range (D.R.m / 2), a (2 * k)) * evT (combC W c C') f u y := by
  simp only [evT]
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : 2 * k < D.R.m := by have := Finset.mem_range.1 hk; omega
  simp only [combC]
  rw [h _ (even_two_mul k) hk', GlobalTheory.SeeSaw.Scale.biComb_smul]
  rfl

theorem isRealFam_smul (a : ℕ → ℂ) {C : BiFam G} (h : IsRealFam W C) : IsRealFam W fun j => a j • C j :=
  fun j hj hm => ⟨GlobalTheory.SeeSaw.Scale.isBiVac_smul _ (h j hj hm).1, GlobalTheory.SeeSaw.Scale.isBiSmooth_smul _ (h j hj hm).2⟩

theorem prod_ite_zero (κ : ℂ) :
    ∏ k ∈ Finset.range (D.R.m / 2), (if 2 * k = 0 then κ else 1) = κ := by
  have hm : 0 ∈ Finset.range (D.R.m / 2) := by have := D.R.two_le_m; exact Finset.mem_range.2 (by omega)
  rw [Finset.prod_eq_single_of_mem 0 hm fun k _ hk => if_neg (by omega)]
  exact if_pos rfl


variable {W} in
theorem isExpansion_zero {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (hβ : β ∉ S.supp t Φ)
    {τ : PureDat G t →₀ ℂ} (h : S.IsExpansion t Φ β τ) : S.IsExpansion t Φ β 0 := by
  obtain ⟨e, he, -, -⟩ := h
  refine ⟨e, he, fun d hd => by simp at hd, fun x y _ _ => ?_⟩
  simp only [GridChoice.supp, Set.mem_setOf_eq, not_forall, unfSupport, not_not] at hβ
  obtain ⟨w, hw⟩ := hβ
  rw [Finsupp.sum_zero_index]
  refine (Finset.prod_eq_zero (Finset.mem_univ w) ?_).symm
  simp only [GridChoice.term]
  rw [hw]
  rfl

end Grid

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem flatAt_of (s : ℤˣ) (hl : LocAt ch s) (hv : VacAt ch) (ho : OneAt ch) : FlatAt ch s := by
  obtain ⟨κ, z₁, hz₁, hl⟩ := hl
  obtain ⟨hb, z₂, hz₂, hv⟩ := hv
  refine ⟨fun t => z₁ t * (∏ k ∈ Finset.range (D.R.m / 2), z₂ t (2 * k))⁻¹,
    fun t => mul_mem (hz₁ t) (inv_mem (prod_mem fun k _ => hz₂ t _)), fun P p hp => ?_⟩
  obtain ⟨C₀, hC₀, hC⟩ := hv P p hp
  refine ⟨fun j => (if j = 0 then κ else 1) • C₀ j, isRealFam_smul ch.W _ hC₀,
    fun t Φ τ hτ M hM β b hβ τ' c hτ' hc => ?_⟩
  obtain ⟨b₀, hb₀⟩ := hb t
  by_cases hs : Stair t β
  · refine ⟨_, fun _ => rfl, fun u y => ?_⟩
    obtain ⟨ζ, hζ, e⟩ := hl t Φ τ hτ M hM β b b₀ hβ hb₀ τ' c hτ' hc
    rw [e P p hp u y, hζ hs, Finsupp.mul_sum, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun d _ => ?_
    rw [evT_combC_smul ch.W (c d) (fun j => (z₂ t j : ℂ)) _ C₀ (hC t M hM b₀ hb₀),
      evT_combC_smul ch.W (c d) (fun j => if j = 0 then κ else 1) _ C₀ (fun _ _ _ => rfl), prod_ite_zero]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_prod, _root_.mul_inv_rev, inv_inv]
    ring
  · refine ⟨0, fun h => absurd h hs, fun u y => ?_⟩
    obtain ⟨ζ, -, e⟩ := hl t Φ τ hτ M hM β b b₀ hβ hb₀ 0 c
      (isExpansion_zero _ t Φ β (fun h => hs (ho t Φ β h)) hτ') (fun d hd => by simp at hd)
    rw [e P p hp u y, Finsupp.sum_zero_index, mul_zero, zero_mul]

theorem flatAt_big : Big fun ch => ∃ s, FlatAt ch s :=
  big_mono (fun ch ⟨⟨⟨s, hl⟩, hv⟩, ho⟩ => ⟨s, flatAt_of ch s hl hv ho⟩) ((GlobalTheory.T.flat_dictionary_base_vacua_large_depth.and GlobalTheory.T.unfolded_vacua_real_up_to_twist_large_depth).and GlobalTheory.T.rowTest_support_families_staircase_cosets)

end GlobalTheory.RowFlatAsm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.UpBessel

theorem upBF : ∀ D : D7, UpBF D := by
  intro D ψ ρ B J s 𝒮 Γ₀ K hL L' ζ' hζ' l χA χz χ' oma omz hχ hWa hWz φ G hφ hG hK Ξ₁ Ξ₂ hΞ₁ hΞ₂ hbox hJ
  by_contra hnone
  push_neg at hnone

  have hstd : IsStdChar D ψ (-1) := s.weil.std
  have hℓ : Tame ψ B.V₀ J.W₀ (J.perAll ψ B s.om₀ φ G) :=
    GlobalTheory.T.fourierJacobiPeriod_all_data_isTameThetaFunctional D ψ ρ ρ B J s.χV s.χW s.om₀ s.weil₀ φ G hφ hG

  have hkill : ∀ Φ ∈ 𝒮, J.perAll ψ B s.om₀ φ G (flBF s Φ) = 0 :=
    GlobalTheory.T.vanishing_descends_bessel_to_fourierJacobi D ψ ρ B J s 𝒮 Γ₀ K hL φ G hφ hG hK hnone
  obtain ⟨Φ₁, hΦ₁, hΦ₁ne⟩ := hL.ne

  have hall : ∀ f, VacG ψ B.V₀ J.W₀ Γ₀ f → J.perAll ψ B s.om₀ φ G f = 0 := by
    refine GlobalTheory.T.tame_functional_vacuum_irreducibility D ψ hstd B.V₀ J.W₀ Γ₀ _ hℓ (flBF s Φ₁) (hL.vac Φ₁ hΦ₁) hΦ₁ne ?_
    intro w hw
    have hcomm := (GlobalTheory.FlatHeis.flatAt_heisO D ψ hstd B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU
      (xZero J.d) (yZero B.V₀ ρ (vecB B.o B.ζ)) Φ₁ (hL.theta Φ₁ hΦ₁)).2.1 w
    have hflat : flBF s (heisO ψ B.V J.W (B.d.ext0 J.W (J.d.inc0 B.V₀ w)) Φ₁) =
        heisO ψ B.V₀ J.W₀ w (flBF s Φ₁) := hcomm
    rw [← hflat]
    exact hkill _ (hL.core Φ₁ hΦ₁ w hw)

  have h0 := hall _ hbox
  rw [GlobalTheory.T.periodAllData_products_eq_fourierJacobiPeriod D ψ ρ B J s L' ζ' hζ' l χA χz χ' oma omz hχ hWa hWz φ G Ξ₁ Ξ₂ hΞ₁ hΞ₂] at h0
  exact hJ h0

end GlobalTheory.UpBessel
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowVertexInv

theorem sum_prod_moveV_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)), (τ.sum fun d c => c * ∏ a, moveV S j hj k (vecOf S d) a (z a)) = τ.sum fun d c => c * ∏ a, vecOf S d a (z a) := by
  intro D T L sc G W U S t Φ β τ μ₀ hμ hq hQ hU hβ hE hv j hj k hk z
  obtain ⟨c₁, c₂, Tm, h1, h2, hT⟩ := GlobalTheory.RowVertexInv.FactorTheta.vecOf_eq_intertwiner S hE hv j hj k hk
  have hB := GlobalTheory.T.sum_prod_expansion_functions_rowVertex_invariant S hμ hq hQ hU hβ hE hv j hj k hk c₁ c₂ h1 h2
  let M : MultilinearMap (RingHom.id ℂ) (fun a : Fin D.R.m ⊕ Fin D.R.m => ↥(⊤ : Submodule ℂ (FactorFn G t a))) ℂ :=
    (MultilinearMap.mkPiAlgebra ℂ (Fin D.R.m ⊕ Fin D.R.m) ℂ).compLinearMap fun a =>
      (LinearMap.proj (z a)) ∘ₗ Tm a ∘ₗ (⊤ : Submodule ℂ (FactorFn G t a)).subtype
  have key := GlobalTheory.finsupp_sum_multilinear_eq_of_prod_eq (X := fun a => WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)))
    (fun a => ⊤) M τ τ (fun d a => ⟨scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a, trivial⟩)
    (fun d a => ⟨fnOf d a, trivial⟩) hB
  simp only [smul_eq_mul] at key
  convert key using 1
  · refine Finsupp.sum_congr fun d hd => ?_
    congr 1
    simp only [M, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, LinearMap.proj_apply]
    exact Finset.prod_congr rfl fun a _ => by rw [(hT d hd a).2]
  · refine Finsupp.sum_congr fun d hd => ?_
    congr 1
    simp only [M, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, LinearMap.proj_apply]
    exact Finset.prod_congr rfl fun a _ => by rw [(hT d hd a).1]

end GlobalTheory.RowVertexInv
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.expansionTensorSum_invariant_gridRowLevel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)), (τ.sum fun d c => c * ∏ a, moveV S j hj k (vecOf S d) a (z a)) = τ.sum fun d c => c * ∏ a, vecOf S d a (z a) := by
  first | exact @GlobalTheory.RowVertexInv.sum_prod_moveV_eq | exact GlobalTheory.RowVertexInv.sum_prod_moveV_eq | (intros; apply GlobalTheory.RowVertexInv.sum_prod_moveV_eq <;> assumption)

end
end
