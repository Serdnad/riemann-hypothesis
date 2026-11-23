module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle384
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386

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

namespace GlobalTheory.OneCosetBF

variable {D : D7}

theorem one_quot_apply {n : ℕ} (I : Ideal (AE D)) (i j : Fin n) :
    (1 : Matrix (Fin n) (Fin n) (AE D ⧸ I)) i j = Ideal.Quotient.mk I ((1 : Matrix (Fin n) (Fin n) (AE D)) i j) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]

theorem mem_congGrp_iff {V : HSp D} {I : Ideal (AE D)} {g : GA D V} :
    g ∈ GlobalTheory.FinPl.congGrp V I ↔
      ∀ i j, Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  simp only [GlobalTheory.FinPl.congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff, Units.val_one]
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rw [one_quot_apply] at this
    exact Ideal.Quotient.eq.1 this
  · intro h
    ext i j
    rw [one_quot_apply]
    exact Ideal.Quotient.eq.2 (h i j)

end GlobalTheory.OneCosetBF

namespace GlobalTheory.OneCosetBF

variable {D : D7}

open GlobalTheory.FinPl in
theorem idAt_mono {P Q : Pl D → Prop} (h : ∀ w, P w → Q w) : idAt D P ≤ idAt D Q := by
  intro a ha
  simp only [idAt, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun hp => w.2 (h _ hp)⟩⟩

open GlobalTheory.FinPl in
theorem idOff_mono {P Q : Pl D → Prop} (h : ∀ w, Q w → P w) : idOff D P ≤ idOff D Q := by
  intro a ha
  simp only [idOff, Ideal.mem_iInf] at ha ⊢
  exact fun w => ha ⟨w.1, h _ w.2⟩

open GlobalTheory.FinPl in
theorem idAt_le_idOff {P Q : Pl D → Prop} (h : ∀ w, Q w → ¬ P w) : idAt D P ≤ idOff D Q := by
  intro a ha
  simp only [idAt, idOff, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢
  exact fun w => ha.2 ⟨w.1, h _ w.2⟩

open GlobalTheory.FinPl in
theorem idAt_inf_idOff {P Q R : Pl D → Prop} (h : ∀ w, P w → ¬ Q w → R w) : idAt D P ⊓ idOff D Q ≤ idAt D R := by
  intro a ha
  simp only [idAt, idOff, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢
  refine ⟨ha.1.1, fun w => ?_⟩
  by_cases hq : Q w.1
  · exact ha.2 ⟨w.1, hq⟩
  · exact ha.1.2 ⟨w.1, fun hp => w.2 (h _ hp hq)⟩

theorem congGrp_mono {V : HSp D} {I J : Ideal (AE D)} (h : I ≤ J) : GlobalTheory.FinPl.congGrp V I ≤ GlobalTheory.FinPl.congGrp V J :=
  fun _ hg => mem_congGrp_iff.2 fun i j => h (mem_congGrp_iff.1 hg i j)

theorem congGrp_inf {V : HSp D} {I J : Ideal (AE D)} {g : GA D V} (hI : g ∈ GlobalTheory.FinPl.congGrp V I)
    (hJ : g ∈ GlobalTheory.FinPl.congGrp V J) : g ∈ GlobalTheory.FinPl.congGrp V (I ⊓ J) :=
  mem_congGrp_iff.2 fun i j => ⟨mem_congGrp_iff.1 hI i j, mem_congGrp_iff.1 hJ i j⟩

theorem mul_sub_mem {I : Ideal (AE D)} {k m n : ℕ} {M : Matrix (Fin m) (Fin m) (AE D)}
    (hM : ∀ i j, M i j - (1 : Matrix (Fin m) (Fin m) (AE D)) i j ∈ I) (N : Matrix (Fin k) (Fin m) (AE D))
    (Y : Matrix (Fin m) (Fin n) (AE D)) (i : Fin k) (j : Fin n) : (N * M * Y - N * Y) i j ∈ I := by
  have e : N * M * Y - N * Y = N * (M - 1) * Y := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  rw [e]
  simp only [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ ?_)
  simpa only [Matrix.sub_apply] using hM q l

variable {W : HSp D} {ρ : ℕ}

theorem off_left {P : GlobalTheory.FinPl.Pl D → Prop} {gv g' : GA D W} (hg' : g' ∈ GlobalTheory.FinPl.congGrp W (GlobalTheory.FinPl.idOff D P))
    {X x a : Mx D W.rank ρ} (h : MxOff P (Formalism.L2.Theta.mt W (gv * g')⁻¹ * X - x - a)) :
    MxOff P (Formalism.L2.Theta.mt W gv⁻¹ * X - x - a) := by
  intro i j
  have h1 := mul_sub_mem (mem_congGrp_iff.1 (inv_mem hg')) (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) (Formalism.L2.Theta.mt W gv⁻¹ * X) i j
  simp only [Matrix.one_mul] at h1
  have e : Formalism.L2.Theta.mt W gv⁻¹ * X - x - a =
      (Formalism.L2.Theta.mt W (gv * g')⁻¹ * X - x - a) -
        (Formalism.L2.Theta.mt W g'⁻¹ * (Formalism.L2.Theta.mt W gv⁻¹ * X) - Formalism.L2.Theta.mt W gv⁻¹ * X) := by
    rw [_root_.mul_inv_rev, mt_mul, Matrix.mul_assoc]; abel
  rw [e, Matrix.sub_apply]
  exact Ideal.sub_mem _ (h i j) h1

theorem off_right {P : GlobalTheory.FinPl.Pl D → Prop} {gv g' : GA D W} (hgv : gv ∈ GlobalTheory.FinPl.congGrp W (GlobalTheory.FinPl.idOff D P))
    {X x a : Mx D W.rank ρ} (h : MxOff P (Formalism.L2.Theta.mt W (gv * g')⁻¹ * X - x - a)) :
    MxOff P (Formalism.L2.Theta.mt W g'⁻¹ * X - x - a) := by
  intro i j
  have h1 := mul_sub_mem (mem_congGrp_iff.1 (inv_mem hgv)) (Formalism.L2.Theta.mt W g'⁻¹) X i j
  have e : Formalism.L2.Theta.mt W g'⁻¹ * X - x - a =
      (Formalism.L2.Theta.mt W (gv * g')⁻¹ * X - x - a) -
        (Formalism.L2.Theta.mt W g'⁻¹ * Formalism.L2.Theta.mt W gv⁻¹ * X - Formalism.L2.Theta.mt W g'⁻¹ * X) := by
    rw [_root_.mul_inv_rev, mt_mul]; abel
  rw [e, Matrix.sub_apply]
  exact Ideal.sub_mem _ (h i j) h1

theorem mxOff_mono {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ w, Q w → P w) {m n : ℕ} {y : Mx D m n} (hy : MxOff P y) :
    MxOff Q y := fun i j => idOff_mono h (hy i j)

end GlobalTheory.OneCosetBF

namespace GlobalTheory.OneCosetBF

variable {D : D7}

theorem assemble (W : HSp D) {ρ : ℕ} (x : Mx D W.rank ρ) (A : AddSubgroup (Mx D W.rank ρ)) (K : Subgroup (GA D W))
    (t : Finset (GlobalTheory.FinPl.Pl D)) (ht : t.Nonempty)
    (loc : ∀ v ∈ t, ∀ g ∈ grpAt W (· = v),
      (∃ u : UX D ρ, ∃ a ∈ A, MxOff (· = v) (Formalism.L2.Theta.mt W g⁻¹ * (x * u.1.1) - x - a)) →
        ∃ r ∈ Rgrp W x, r ∈ grpAt W (· = v) ∧ ∃ k ∈ K, k ∈ grpAt W (· = v) ∧ g = r * k) :
    ∀ g ∈ grpAt W (· ∈ t),
      (∃ u : UX D ρ, ∃ a ∈ A, MxOff (· ∈ t) (Formalism.L2.Theta.mt W g⁻¹ * (x * u.1.1) - x - a)) →
        ∃ r ∈ Rgrp W x, r ∈ grpAt W (· ∈ t) ∧ ∃ k ∈ K, k ∈ grpAt W (· ∈ t) ∧ g = r * k := by
  revert loc
  induction ht using Finset.Nonempty.cons_induction with
  | singleton v =>
    intro loc g hg hc
    simp only [Finset.mem_singleton] at hg hc loc ⊢
    exact loc v rfl g hg hc
  | cons v t hv ht ih =>
    intro loc g hg hc
    obtain ⟨u, a, ha, hc⟩ := hc
    obtain ⟨gv, hgv, g', hg', rfl⟩ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).1 g
    have hcomm := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).2.1
    have hsub : ∀ w, w ∈ t → ¬ (w = v) := fun w hw e => hv (e ▸ hw)
    have hvt : grpAt W (· = v) ≤ grpAt W (· ∈ Finset.cons v t hv) :=
      congGrp_mono (idAt_mono fun w hw => hw ▸ Finset.mem_cons_self v t)
    have htt : grpAt W (· ∈ t) ≤ grpAt W (· ∈ Finset.cons v t hv) :=
      congGrp_mono (idAt_mono fun w hw => Finset.mem_cons.2 (Or.inr hw))
    have ht_off : grpAt W (· ∈ t) ≤ grpOff W (· = v) :=
      congGrp_mono (idAt_le_idOff fun w hw hwt => hsub w hwt hw)
    have hv_off : grpAt W (· = v) ≤ grpOff W (· ∈ t) :=
      congGrp_mono (idAt_le_idOff fun w hw hwv => hsub w hw hwv)
    have hg'1 : g' ∈ grpAt W (· ∈ t) := by
      have h1 : g' ∈ grpAt W (· ∈ Finset.cons v t hv) := by
        have := mul_mem (inv_mem (hvt hgv)) hg
        rwa [inv_mul_cancel_left] at this
      exact congGrp_mono (idAt_inf_idOff fun w hw hnv => (Finset.mem_cons.1 hw).resolve_left hnv)
        (congGrp_inf h1 hg')
    have hcv : MxOff (· = v) (Formalism.L2.Theta.mt W gv⁻¹ * (x * u.1.1) - x - a) :=
      off_left hg' (mxOff_mono (fun w hw => hw ▸ Finset.mem_cons_self v t) hc)
    have hct : MxOff (· ∈ t) (Formalism.L2.Theta.mt W g'⁻¹ * (x * u.1.1) - x - a) :=
      off_right (hv_off hgv) (mxOff_mono (fun w hw => Finset.mem_cons.2 (Or.inr hw)) hc)
    obtain ⟨rv, hrv, hrv', kv, hkv, hkv', rfl⟩ := loc v (Finset.mem_cons_self v t) gv hgv ⟨u, a, ha, hcv⟩
    obtain ⟨r', hr', hr'', k', hk', hk'', rfl⟩ :=
      ih (fun w hw => loc w (Finset.mem_cons.2 (Or.inr hw))) g' hg'1 ⟨u, a, ha, hct⟩
    refine ⟨rv * r', mul_mem hrv hr', mul_mem (hvt hrv') (htt hr''), kv * k', mul_mem hkv hk',
      mul_mem (hvt hkv') (htt hk''), ?_⟩
    have hc' := hcomm kv hkv' r' (ht_off hr'')
    calc rv * kv * (r' * k') = rv * (kv * r') * k' := by simp only [mul_assoc]
      _ = rv * (r' * kv) * k' := by rw [hc']
      _ = rv * r' * (kv * k') := by simp only [mul_assoc]

end GlobalTheory.OneCosetBF
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

namespace GlobalTheory.AscFin.BesIso

theorem symplO_negSp_eq {D : D7} (S T : HSp D) (x y : WO S T) : symplO (negSp S) T x y = -symplO S T x y := by
  have hinv : (-S.gram)⁻¹ = -S.gram⁻¹ :=
    Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul _ (gram_isUnit_det S)])
  have h : hO (negSp S) T x y = -hO S T x y := by
    simp only [hO, negSp_gram, hinv, Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  rw [symplO_eq, symplO_eq, h, mul_neg, map_neg]

theorem hO_extX_eq {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (a : Mx D T.rank ρ) (u : WO S T) :
    hO S T (d.extX T a) u = hO S T (d.extX T a) (d.extY T (u ⬝ d.jY)) := by
  have hu : u = d.extX T (u ⬝ d.jX) + d.ext0 T (u ⬝ d.j0) + d.extY T (u ⬝ d.jY) := ((d.coordS T).symm_apply_apply u).symm
  have h1 := d.hO_ext T a (u ⬝ d.jX) 0 (u ⬝ d.jY) 0 (u ⬝ d.j0)
  have h2 := d.hO_ext T a 0 0 (u ⬝ d.jY) 0 0
  simp only [map_zero, add_zero, zero_add] at h1 h2
  rw [← hu] at h1
  rw [h1, h2]
  simp [pairS, hO]

end GlobalTheory.AscFin.BesIso


open GlobalTheory.AscFin.BesIso in
theorem GlobalTheory.AscFin.BesIso.splits_iso : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), MxAt (fun _ => True) (u ⬝ (F.dB ρ h).jY) ∧ ∀ a, (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a ∈ latRow G (2 * ρ + 1) → W.ψ (symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) ((F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a) ((F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY))) = 1 := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  have sd : ∀ i, i ≤ D.R.m → 1 ≤ i → IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := fun i hi h1 =>
    (G.isV (X := .grid i 0) ⟨hi, Nat.zero_le _⟩ (fun j hj => by injection hj with e1 e2; omega)).sd
  have sdV := isSelfDualC_neg (sd (2 * ρ + 2) h (by omega))
  have sdW := sd (2 * ρ + 1) (by omega) (by omega)
  have hmx : ∀ w, w ∈ latRow G (2 * ρ + 1) → MxAt (fun _ => True) w := fun w hw =>
    ((GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ sdV sdW (fun _ => True) w).1 hw.1).1
  refine ⟨fun i j => ?_, fun a ha => ?_⟩
  · simp only [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hmx u hu i k)
  · have key := (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdV sdW (fun _ => True) _ (hmx _ ha)).1 ha.1 u hu.1
    rw [symplO_negSp_eq, AddChar.map_neg_eq_inv, inv_eq_one] at key
    rw [symplO_eq] at key ⊢
    rw [← hO_extX_eq]
    exact key
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AdjSrcZero

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem AAbar_ne_zero (D : D7) : D.host.AAbar ≠ 0 := by
  obtain ⟨⟨hAA, hbar⟩, -⟩ := GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D
  intro h0
  apply hAA
  rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
  intro x hx
  have h1 : star x ∈ D.host.AAbar := (hbar _).2 (by rwa [star_star])
  have h2 := h0 _ h1
  simpa using congrArg star h2

theorem AAbar_mul_st (G : GridData L sc) :
    D.host.AAbar * (G.pl.stA sc ^ (0 + 1) * (G.pl.stAbar sc ^ (0 + 1))⁻¹) = D.host.AA * shiftId G := by
  have hA := AAbar_ne_zero D
  simp only [zero_add, pow_one, Places.stA, Places.stAbar, shiftId, mul_inv, inv_inv]
  calc _ = (D.host.AAbar * D.host.AAbar⁻¹) * (D.host.AA *
        (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) *
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hA, one_mul]

theorem star_smul_mem_span : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {n : ℕ}
    (Λ₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), ∀ a ∈ D.host.AA,
    ∀ s ∈ idLat (G.pl.stA sc ^ (0 + 1) * (G.pl.stAbar sc ^ (0 + 1))⁻¹) Λ₀,
    star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'} := by
  intro D T L sc G n Λ₀ a ha s hs
  obtain ⟨⟨-, hbar⟩, -⟩ := GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D
  have key : ∀ b ∈ D.host.AA * shiftId G, ∀ y ∈ Λ₀, b • y ∈
      Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'} := by
    intro b hb y hy
    refine FractionalIdeal.mul_induction_on (C := fun b => b • y ∈
      Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'}) hb ?_ ?_
    · intro i hi j hj
      refine Submodule.subset_span ⟨i, hi, j • y, Submodule.subset_span ⟨j, hj, y, hy, rfl⟩, ?_⟩
      rw [smul_smul]
    · intro x z hx hz
      rw [add_smul]
      exact add_mem hx hz
  have hsa : star a ∈ D.host.AAbar := (hbar _).2 (by rwa [star_star])
  unfold idLat at hs
  refine Submodule.span_induction (p := fun z _ => star a • z ∈
      Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'}) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨i, hi, y, hy, rfl⟩
    rw [smul_smul]
    exact key _ (AAbar_mul_st G ▸ FractionalIdeal.mul_mem_mul hsa hi) y hy
  · simp
  · intro x z _ _ hx hz
    rw [smul_add]
    exact add_mem hx hz
  · intro c x _ hx
    rw [smul_comm]
    exact Submodule.smul_mem _ c hx

end GlobalTheory.AdjSrcZero
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

namespace GlobalTheory.HeisTranslCR

open GlobalTheory.FockCompare GlobalTheory.VacUnique

theorem deriv_twisted_line_at {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] (F : R → ℂ) (hF : Differentiable ℝ F)
    (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (a w u : R) :
    deriv (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (om a (t • u) : ℂ)) * F (w + t • u)) 0 =
      fderiv ℝ F w u - Real.pi * Complex.I * (om a u : ℂ) * F w := by
  have h1 : HasDerivAt (fun t : ℝ => w + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add w
  have h2 : HasDerivAt (fun t : ℝ => F (w + t • u)) (fderiv ℝ F w u) 0 := by
    have h := (hF (w + (0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    simpa [Function.comp_def] using h
  have h3 : HasDerivAt (fun t : ℝ => -(Real.pi * Complex.I) * (om a (t • u) : ℂ))
      (-(Real.pi * Complex.I) * (om a u : ℂ)) 0 := by
    have e : (fun t : ℝ => -(Real.pi * Complex.I) * (om a (t • u) : ℂ)) =
        fun t : ℝ => (t : ℂ) * (-(Real.pi * Complex.I) * (om a u : ℂ)) := by
      funext t
      rw [LinearMap.map_smul, smul_eq_mul, Complex.ofReal_mul]
      ring
    rw [e]
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (-(Real.pi * Complex.I) * (om a u : ℂ))
  have h4 := (h3.cexp.mul h2).deriv
  refine Eq.trans h4 ?_
  simp only [zero_smul, map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, add_zero, one_mul]
  ring

theorem differentiable_phase {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (a : R) :
    Differentiable ℝ fun w : R => Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) := by
  have h : Differentiable ℝ fun w : R => ((om a w : ℝ) : ℂ) :=
    Complex.ofRealCLM.differentiable.comp (LinearMap.toContinuousLinearMap (om a)).differentiable
  exact ((differentiable_const _).mul h).cexp

theorem fderiv_phase_mul {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (F : R → ℂ)
    (hF : Differentiable ℝ F) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (a w u : R) :
    fderiv ℝ (fun w : R => Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) * F w) w u =
      Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) *
        (fderiv ℝ F w u - Real.pi * Complex.I * (om a u : ℂ) * F w) := by
  have hG : Differentiable ℝ fun w : R => Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) * F w :=
    (differentiable_phase om a).mul hF
  have h1 : HasDerivAt (fun t : ℝ => w + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add w
  have h2 := (hG (w + (0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  simp only [zero_smul, add_zero, Function.comp_def] at h2
  rw [← h2.deriv]
  have e : (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (om a (w + t • u) : ℂ)) * F (w + t • u)) =
      fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) *
        (Complex.exp (-(Real.pi * Complex.I) * (om a (t • u) : ℂ)) * F (w + t • u)) := by
    funext t
    rw [LinearMap.map_add (f := _), Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  rw [e, deriv_const_mul_field, deriv_twisted_line_at F hF om a w u]

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}

theorem heisO_real_at (h : Chart θ σ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (f : WO S T → ℂ) (y : WO S T) (w : RW T S) :
    heisO ψ S T (iotaW σ T S w) f y =
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S y) w : ℂ)) * f (y + iotaW σ T S w) := by
  unfold heisO
  rw [GlobalTheory.OrientedChar.char_symplOH D θ ψ h.inf hψ S T _ _ (Or.inr (h.real_iota T S w)), h.pi_iota]


open Classical in
theorem dRho_eq_at (h : Chart θ σ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (f : WO S T → ℂ) (y : WO S T) (hF : Differentiable ℝ fun v : RW T S => f (y + iotaW σ T S v)) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : RW T S) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f (y + iotaW σ T S w) =
      fderiv ℝ (fun v : RW T S => f (y + iotaW σ T S v)) w (Pi.single τ z) -
        Real.pi * Complex.I * (omO S T (piW θ T S y + w) (Pi.single τ z) : ℂ) * f (y + iotaW σ T S w) := by
  refine Eq.trans ?_ (deriv_twisted_line_at _ hF (omO S T) (piW θ T S y + w) w (Pi.single τ z))
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [GlobalTheory.VacUnique.Ann.lineAt_eq h S T τ z t, heisO_real_at h hψ, (piW θ T S).map_add, h.pi_iota, add_assoc,
    ← (iotaW σ T S).map_add]


open Classical in
theorem heis_translate_cauchy_riemann : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (f : WO S T → ℂ), GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ y : WO S T, Differentiable ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) ∧ ∀ w z : GlobalTheory.FockCompare.RW T S, fderiv ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) w z + Complex.I * fderiv ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) w (GlobalTheory.VacUnique.jO S T A.cart B.cart z) = (Real.pi : ℂ) * Complex.I * ((GlobalTheory.VacUnique.omO S T w z : ℂ) + Complex.I * (GlobalTheory.VacUnique.omO S T w (GlobalTheory.VacUnique.jO S T A.cart B.cart z) : ℂ)) * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y := by
  intro D θ σ h ψ hψ S T A B f hf y
  have hF : Differentiable ℝ fun v : RW T S => f (y + iotaW σ T S v) :=
    (GlobalTheory.OrientedHeis.theta_sm h hf.1 y).differentiable (by simp)
  have hG : (fun w : RW T S => heisO ψ S T (iotaW σ T S w) f y) = fun w : RW T S =>
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S y) w : ℂ)) * f (y + iotaW σ T S w) := by
    funext w
    exact heisO_real_at h hψ S T f y w
  rw [hG]
  refine ⟨(differentiable_phase (omO S T) (piW θ T S y)).mul hF, fun w z => ?_⟩
  rw [fderiv_phase_mul _ hF, fderiv_phase_mul _ hF]
  rw [heisO_real_at h hψ S T f y w]
  set a := piW θ T S y with ha
  set Fd := fderiv ℝ (fun v : RW T S => f (y + iotaW σ T S v)) w with hFd
  set Fw := f (y + iotaW σ T S w) with hFw
  let L : RW T S →+ ℂ :=
    { toFun := fun s => Fd s - Real.pi * Complex.I * (omO S T (a + w) s : ℂ) * Fw
      map_zero' := by simp
      map_add' := fun x x' => by
        rw [ContinuousLinearMap.map_add (f := _), LinearMap.map_add (f := _), Complex.ofReal_add]
        ring }
  have hL : L z + Complex.I * L (jO S T A.cart B.cart z) = 0 := by

    rw [← Finset.univ_sum_single z, map_sum, map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun τ _ => ?_
    have h1 := congrFun (hf.2 τ (z τ)) (y + iotaW σ T S w)
    have h2 : Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z τ) f (y + iotaW σ T S w) +
        Complex.I * Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO (A.cart τ) (B.cart τ) (z τ)) f
          (y + iotaW σ T S w) = 0 := h1
    have h3 := dRho_eq_at h hψ S T f y hF τ (z τ) w
    have h4 := dRho_eq_at h hψ S T f y hF τ (cplxO (A.cart τ) (B.cart τ) (z τ)) w
    have h5 := GlobalTheory.VacUnique.Ann.jO_single S T A.cart B.cart τ (z τ)
    have h6 : L (Pi.single τ (z τ)) + Complex.I * L (Pi.single τ (cplxO (A.cart τ) (B.cart τ) (z τ))) = 0 :=
      (congrArg₂ (fun a b : ℂ => a + Complex.I * b) h3 h4).symm.trans h2
    exact (congrArg (fun b => L (Pi.single τ (z τ)) + Complex.I * L b) h5).trans h6
  have e1 : L z = Fd z - Real.pi * Complex.I * ((omO S T a z : ℂ) + (omO S T w z : ℂ)) * Fw := by
    show Fd z - Real.pi * Complex.I * (omO S T (a + w) z : ℂ) * Fw = _
    rw [LinearMap.map_add (f := _), LinearMap.add_apply, Complex.ofReal_add]
  have e2 : L (jO S T A.cart B.cart z) = Fd (jO S T A.cart B.cart z) - Real.pi * Complex.I *
      ((omO S T a (jO S T A.cart B.cart z) : ℂ) + (omO S T w (jO S T A.cart B.cart z) : ℂ)) * Fw := by
    show Fd _ - Real.pi * Complex.I * (omO S T (a + w) _ : ℂ) * Fw = _
    rw [LinearMap.map_add (f := _), LinearMap.add_apply, Complex.ofReal_add]
  rw [e1, e2] at hL
  linear_combination (Complex.exp (-(Real.pi * Complex.I) * (omO S T a w : ℂ))) * hL

end GlobalTheory.HeisTranslCR
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mixedModelThetaTerms_summable_heightBound : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ A d : ℕ, ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ K : ℝ, ∀ (g : GA D V) (h : GA D W) (F : WO V W → ℂ), IsThetaFunO ψ V W F → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V W (actO V W g h u) F = F) → ∑' y : Matrix (Fin W.rank) (Fin r) D.host.E, ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) F) 0‖ₑ ≤ ENNReal.ofReal (K * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A) * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) d F := by
  first | exact @GlobalTheory.MixedTerm.mixed_terms_bound | exact GlobalTheory.MixedTerm.mixed_terms_bound | (intros; apply GlobalTheory.MixedTerm.mixed_terms_bound <;> assumption)
end
