module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FlagMove

variable {D : D7}

theorem Xsp_eq_Xflag {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : Xsp F = Xflag F D.R.rS := by
  unfold Xsp Xflag
  simp only [Formalism.MainNotions.S.FlagG.X, Formalism.MainNotions.S.FlagG.Xa]
  congr 1
  ext v
  simp

private lemma finrank_Xflag {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (j : ℕ) :
    Module.finrank D.host.E (Xflag F j) = Fintype.card {i : Fin D.R.rS // i.1 < j} := by
  have h : Xflag F j = Submodule.span D.host.E
      (Set.range (fun i : {i : Fin D.R.rS // i.1 < j} => F.fl.e i.1)) := by
    unfold Xflag
    simp only [Formalism.MainNotions.S.FlagG.Xa]
    congr 1
    ext v
    simp
  rw [h, finrank_span_eq_card]
  exact F.fl.e_indep.comp _ Subtype.val_injective

theorem finrank_Xflag_eq {T T0 : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F0 : LFlag (D.sp.Y 0) D.R.rS T0) (j : ℕ) :
    Module.finrank D.host.E (Xflag F j) = Module.finrank D.host.E (Xflag F0 j) := by
  rw [finrank_Xflag, finrank_Xflag]

theorem orth_iff {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {U U' : Submodule D.host.E (VS D).V} (hU : ∀ x, β x ∈ U' ↔ x ∈ U) (y : (VS D).V) :
    β y ∈ orth (VS D) U' ↔ y ∈ orth (VS D) U := by
  have hiso : ∀ x y, (VS D).hT (β x) (β y) = (VS D).hT x y := hi
  unfold orth
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h x hx
    rw [← hiso]
    exact h (β x) ((hU x).2 hx)
  · intro h x hx
    have hx' : β.symm x ∈ U := (hU _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hx)
    have h' := h _ hx'
    rw [← hiso, LinearEquiv.apply_symm_apply] at h'
    exact h'

private lemma frame_mem_Xflag {T0 : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T0) (j : ℕ)
    (a : Fin (D.R.rS + 1)) (ha : a.1 < j) (hr : a.1 < D.R.rS) : frame F0 a ∈ Xflag F0 j := by
  have e : a = Fin.castSucc ⟨a.1, hr⟩ := Fin.ext rfl
  rw [e]
  unfold frame Xflag
  simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, Formalism.MainNotions.S.FlagG.Xa]
  exact Submodule.subset_span ⟨⟨a.1, hr⟩, ha, rfl⟩

theorem map_Xflag_le {T T0 : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F0 : LFlag (D.sp.Y 0) D.R.rS T0)
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hU : IsUpUni U) (hf : ∀ b, σ (frame F b) = ∑ a, U a b • frame F0 a) (j : ℕ) :
    ∀ x ∈ Xflag F j, σ x ∈ Xflag F0 j := by
  intro x hx
  have key : Submodule.span D.host.E (F.fl.e '' {i | i.1 < j}) ≤
      (Xflag F0 j).comap (σ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i.1 < j := hi
    show σ (F.fl.e i) ∈ Xflag F0 j
    have he : F.fl.e i = frame F (Fin.castSucc i) := by
      unfold frame
      simp [Formalism.MainNotions.S.FlagG.fvec]
    rw [he, hf]
    refine Submodule.sum_mem _ (fun a _ => ?_)
    by_cases hab : Fin.castSucc i < a
    · rw [(hU a (Fin.castSucc i)).1 hab, zero_smul]
      exact Submodule.zero_mem _
    · have h1 : a.1 ≤ i.1 := by
        simpa [Fin.lt_def] using hab
      have h2 := i.2
      exact Submodule.smul_mem _ _ (frame_mem_Xflag F0 j a (by omega) (by omega))
  exact key hx

theorem mem_Xflag_iff {T T0 : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F0 : LFlag (D.sp.Y 0) D.R.rS T0)
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hU : IsUpUni U) (hf : ∀ b, σ (frame F b) = ∑ a, U a b • frame F0 a) (j : ℕ) (x : (VS D).V) :
    σ x ∈ Xflag F0 j ↔ x ∈ Xflag F j := by
  have hle : (Xflag F j).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag F0 j := by
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    exact map_Xflag_le F F0 σ U hU hf j y hy
  have hfin : FiniteDimensional D.host.E (Xflag F0 j) := by
    show FiniteDimensional D.host.E (Submodule.span D.host.E (F0.fl.e '' {i | i.1 < j}))
    exact FiniteDimensional.span_of_finite D.host.E ((Set.toFinite _).image _)
  have heq : (Xflag F j).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag F0 j := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    exact le_of_eq ((finrank_Xflag_eq F0 F j).trans (LinearEquiv.finrank_map_eq σ (Xflag F j)).symm)
  constructor
  · intro h
    rw [← heq, Submodule.mem_map] at h
    obtain ⟨y, hy, hyx⟩ := h
    have hyx' : y = x := σ.injective hyx
    rw [hyx'] at hy
    exact hy
  · exact map_Xflag_le F F0 σ U hU hf j x

theorem nrat_conj_iff : ∀ (D : D7) {T : D.host.E} (F F0 : LFlag (D.sp.Y 0) D.R.rS T)
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E),
    σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → IsUpUni U → (∀ b, σ (frame F b) = ∑ a, U a b • frame F0 a) →
    ∀ n, n ∈ NRat F ↔ σ * n * σ⁻¹ ∈ NRat F0 := by
  intro D T F F0 σ U hσ hU hf n
  have hX : ∀ j x, σ x ∈ Xflag F0 j ↔ x ∈ Xflag F j := fun j x => mem_Xflag_iff F F0 σ U hU hf j x
  have hS : ∀ x, σ x ∈ Xsp F0 ↔ x ∈ Xsp F := by
    intro x
    rw [Xsp_eq_Xflag, Xsp_eq_Xflag]
    exact hX _ x
  have hO : ∀ x, σ x ∈ orth (VS D) (Xsp F0) ↔ x ∈ orth (VS D) (Xsp F) := orth_iff hσ hS
  have hc : ∀ x, (σ * n * σ⁻¹) (σ x) = σ (n x) := by
    intro x
    show σ (n (σ.symm (σ x))) = σ (n x)
    rw [LinearEquiv.symm_apply_apply]
  have hsub : ∀ x, σ (n x) - σ x = σ (n x - x) := fun x => (map_sub σ _ _).symm
  unfold NRat
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨mul_mem (mul_mem hσ h1) (inv_mem hσ), ?_, ?_⟩
    · intro j x hx
      obtain ⟨y, rfl⟩ := σ.surjective x
      rw [hc, hsub, hX]
      exact h2 j y ((hX _ y).1 hx)
    · intro x hx
      obtain ⟨y, rfl⟩ := σ.surjective x
      rw [hc, hsub, hS]
      exact h3 y ((hO y).1 hx)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · have e : n = σ⁻¹ * (σ * n * σ⁻¹) * σ := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hσ) h1) hσ
    · intro j x hx
      have h' := h2 j (σ x) ((hX _ x).2 hx)
      rw [hc, hsub, hX] at h'
      exact h'
    · intro x hx
      have h' := h3 (σ x) ((hO x).2 hx)
      rw [hc, hsub, hS] at h'
      exact h'

end GlobalTheory.FlagMove
end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.NmlCoset

variable {D : D7} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)

theorem mem_orth_iff (U : Submodule D.host.E (VS D).V) (y : (VS D).V) :
    y ∈ orth (VS D) U ↔ ∀ x ∈ U, (VS D).hT x y = 0 := by
  unfold orth
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]

theorem X_iso : ∀ x ∈ Xsp F, ∀ y ∈ Xsp F, (VS D).hT x y = 0 := by
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨b, rfl⟩ := hy; exact F.fl.e_iso a b
    | zero => simp
    | add y y' _ _ h1 h2 => simp [map_add (f := _), h1, h2]
    | smul c y _ h => simp [map_smul, h]
  | zero => simp
  | add x x' _ _ h1 h2 => simp [map_add (f := _), h1, h2]
  | smul c x _ h => simp [h]

theorem X_le_orth : Xsp F ≤ orth (VS D) (Xsp F) := by
  intro y hy
  rw [mem_orth_iff]
  intro x hx
  exact X_iso F x hx y hy

theorem Xa_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  apply Submodule.span_mono
  apply Set.image_mono
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

instance Xa_fd (j : ℕ) : FiniteDimensional D.host.E (Xflag F j) :=
  FiniteDimensional.span_of_finite _ (Set.Finite.image _ (Set.toFinite _))

theorem maps_Xa {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) (j : ℕ) :
    ∀ x ∈ Xflag F (j + 1), n x ∈ Xflag F (j + 1) := by
  intro x hx
  have h := hn.2.1 j x hx
  have : n x = (n x - x) + x := by abel
  rw [this]
  exact (Xflag F (j + 1)).add_mem (Xa_mono F j h) hx

theorem maps_X {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) :
    ∀ x ∈ Xsp F, n x ∈ Xsp F := by
  intro x hx
  have h := hn.2.2 x (X_le_orth F hx)
  have : n x = (n x - x) + x := by abel
  rw [this]
  exact (Xsp F).add_mem h hx

theorem maps_orth {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) :
    ∀ x ∈ orth (VS D) (Xsp F), n x ∈ orth (VS D) (Xsp F) := by
  intro x hx
  have h := hn.2.2 x hx
  have : n x = (n x - x) + x := by abel
  rw [this]
  exact (orth (VS D) (Xsp F)).add_mem (X_le_orth F h) hx

theorem symm_mem_Xa {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) (j : ℕ) :
    ∀ x ∈ Xflag F (j + 1), n.symm x ∈ Xflag F (j + 1) := by
  intro x hx
  have hle : (Xflag F (j + 1)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag F (j + 1) := by
    rintro _ ⟨y, hy, rfl⟩
    exact maps_Xa F hn j y hy
  have heq := Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq n _)
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : n.symm x = y := by rw [← hyx]; simp
  rw [this]; exact hy

theorem one_mem : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, ?_, ?_⟩
  · intro j x _; simp
  · intro x _; simp

theorem mul_mem {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) (hm : m ∈ NRat F) :
    n * m ∈ NRat F := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hn.1 hm.1, ?_, ?_⟩
  · intro j x hx
    show n (m x) - x ∈ Xflag F j
    have e : n (m x) - x = (n (m x) - m x) + (m x - x) := by abel
    rw [e]
    exact (Xflag F j).add_mem (hn.2.1 j (m x) (maps_Xa F hm j x hx)) (hm.2.1 j x hx)
  · intro x hx
    show n (m x) - x ∈ Xsp F
    have e : n (m x) - x = (n (m x) - m x) + (m x - x) := by abel
    rw [e]
    exact (Xsp F).add_mem (hn.2.2 (m x) (maps_orth F hm x hx)) (hm.2.2 x hx)

theorem inv_mem {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) : n⁻¹ ∈ NRat F := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hn.1, ?_, ?_⟩
  · intro j x hx
    show n.symm x - x ∈ Xflag F j
    have hy := symm_mem_Xa F hn j x hx
    have h := hn.2.1 j (n.symm x) hy
    rw [LinearEquiv.apply_symm_apply] at h
    have e : n.symm x - x = -(x - n.symm x) := by abel
    rw [e]; exact (Xflag F j).neg_mem h
  · intro x hx
    show n.symm x - x ∈ Xsp F
    have hy : n.symm x ∈ orth (VS D) (Xsp F) := by
      rw [mem_orth_iff] at hx ⊢
      intro v hv
      have hi := hn.1 v (n.symm x)
      rw [LinearEquiv.apply_symm_apply] at hi
      rw [← hi]
      exact hx _ (maps_X F hn v hv)
    have h := hn.2.2 (n.symm x) hy
    rw [LinearEquiv.apply_symm_apply] at h
    have e : n.symm x - x = -(x - n.symm x) := by abel
    rw [e]; exact (Xsp F).neg_mem h

end GlobalTheory.HL.NmlCoset

namespace GlobalTheory.HL


open GlobalTheory.HL.NmlCoset in
theorem nmlOf_eq_iff_lin : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ t₀ t : TauC Y u u', nmlOf Y u u' t = nmlOf Y u u' t₀ ↔
      ∃ n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧
        t.lin = n⁻¹ * t₀.lin * m := by
  intro D X Y u u' _ t₀ t
  constructor
  · intro h
    have ht : t.lin ∈ nmlOf Y u u' t := ⟨1, one_mem _, 1, one_mem _, by simp⟩
    rw [h] at ht
    obtain ⟨n, hn, n', hn', e⟩ := ht
    exact ⟨n⁻¹, n', inv_mem _ hn, hn', by simpa using e⟩
  · rintro ⟨n, m, hn, hm, e⟩
    ext δ
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a * n⁻¹, mul_mem _ ha (inv_mem _ hn), m * b, mul_mem _ hm hb, ?_⟩
      rw [e]; simp only [mul_assoc]
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a * n, mul_mem _ ha hn, m⁻¹ * b, mul_mem _ (inv_mem _ hm) hb, ?_⟩
      rw [e]; group

end GlobalTheory.HL
end

end

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.doubleCoset_eq_iff_isometry_unipotent_translate : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ t₀ t : TauC Y u u', nmlOf Y u u' t = nmlOf Y u u' t₀ ↔ ∃ n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m := by
  first | exact @GlobalTheory.HL.nmlOf_eq_iff_lin | exact GlobalTheory.HL.nmlOf_eq_iff_lin | (intros; apply GlobalTheory.HL.nmlOf_eq_iff_lin <;> assumption)

end
end

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_unipotent_conj_iff_of_unitriangular_isometry : ∀ (D : D7) {T : D.host.E} (F F0 : LFlag (D.sp.Y 0) D.R.rS T) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → IsUpUni U → (∀ b, σ (frame F b) = ∑ a, U a b • frame F0 a) → ∀ n, n ∈ NRat F ↔ σ * n * σ⁻¹ ∈ NRat F0 := by
  first | exact @GlobalTheory.FlagMove.nrat_conj_iff | exact GlobalTheory.FlagMove.nrat_conj_iff | (intros; apply GlobalTheory.FlagMove.nrat_conj_iff <;> assumption)

end
end
