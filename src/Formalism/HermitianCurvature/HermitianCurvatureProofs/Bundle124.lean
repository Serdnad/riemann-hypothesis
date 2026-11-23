module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockRelationTwistedHeight
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle009
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle038
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftDerivativeCurves
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

section comp

variable {V V' V'' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V'']
  [Module ℂ V''] {T : V →ₗ[ℂ] V'} {T' : V' →ₗ[ℂ] V''}

theorem rel_comp {A : Pr V} {A' : Pr V'} {A'' : Pr V''} (h : Rel T A A') (h' : Rel T' A' A'') :
    Rel (T' ∘ₗ T) A A'' := by
  refine ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩
  · have h1 := LinearMap.congr_fun h.1 v
    have h2 := LinearMap.congr_fun h'.1 (T v)
    simp only [LinearMap.comp_apply] at h1 h2 ⊢
    rw [h2, h1]
  · have h1 := LinearMap.congr_fun h.2 v
    have h2 := LinearMap.congr_fun h'.2 (T v)
    simp only [LinearMap.comp_apply] at h1 h2 ⊢
    rw [h2, h1]

theorem mrel_comp {M : Matrix (Fin 2) (Fin 2) (Pr V)} {M' : Matrix (Fin 2) (Fin 2) (Pr V')}
    {M'' : Matrix (Fin 2) (Fin 2) (Pr V'')} (h : MRel T M M') (h' : MRel T' M' M'') : MRel (T' ∘ₗ T) M M'' :=
  fun a b => rel_comp (h a b) (h' a b)

variable {S : Type} [Fintype S] [DecidableEq S]

end comp

section bT

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
  {S : Type} [Fintype S] [DecidableEq S]

theorem mrel_Ts {σ : Wd.Site (Pr V)} {σ' : Wd.Site (Pr V')} (hp : Rel T σ.p σ'.p) (hc : Rel T σ.c σ'.c)
    (hci : Rel T σ.ci σ'.ci) (Y : ℂ) : MRel T (Wd.Ts σ Y) (Wd.Ts σ' Y) := by
  unfold Wd.Ts; exact mrel_Tm Y hp hc hci

theorem arel_bT {σ : Wd.Site (Pr V)} {σ' : Wd.Site (Pr V')} (hp : Rel T σ.p σ'.p) (hc : Rel T σ.c σ'.c)
    (hci : Rel T σ.ci σ'.ci) : ∀ w : List (Wd.Letter ℂ S), ARel T (Wd.bT σ w) (Wd.bT σ' w)
  | [] => by unfold Wd.bT; exact arel_one
  | l :: w => by
    unfold Wd.bT Wd.vlet
    refine arel_mul (arel_ins _ (brel_lift0 ?_)) (arel_bT hp hc hci w)
    split_ifs
    · exact mrel_Ts hp hc hci _
    · intro a b
      rw [Matrix.map_apply, Matrix.map_apply]
      exact rel_star (mrel_Ts hp hc hci _ a b)

end bT

section one

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem site_ops {t : ℂ} (ht : t ≠ 0)
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (l : Fin ρ) :
    Rel (trL ht z z' π π') (L.p (shS l)) (Ls.p l) ∧ Rel (trL ht z z' π π') (L.c (shS l)) (Ls.c l) ∧
      Rel (trL ht z z' π π') (L.ci (shS l)) (Ls.ci l) := by
  have hop := fun (i : Fin 6) Φ => op_tr ht X Xs l i Φ
  refine ⟨?_, ?_, ?_⟩
  · rw [hL.1, hLs.1]
    exact rel_mk (fun v => hop 0 v) (fun v => by simp only [LinearMap.neg_apply, hop 3, map_neg])
  · rw [hL.2.2.1, hLs.2.2.1]
    exact rel_mk (fun v => hop 1 v) (fun v => hop 4 v)
  · rw [hL.2.2.2.1, hLs.2.2.2.1]
    exact rel_mk (fun v => hop 2 v) (fun v => hop 5 v)

theorem qqi_rel_n {t : ℂ} (ht : t ≠ 0) (hz : inWb k ρ z) (hz' : inWb k ρ z')
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {st : Fr.Start (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'))}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    {sts : Fr.Start (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))))} {s : ℂ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y) (n : ℕ) (hn : n ≤ ρ) (Y : ℂ) :
    MRel (trL ht z z' π π') (P5.QQi L st ⟨n + 1, by omega⟩ Y) (P5.QQi Ls sts ⟨n, by omega⟩ Y) := by
  have hQ : MRel (trL ht z z' π π') (st.QQ Y) (sts.QQ Y) := by
    rw [hst, hsts]
    exact mrel_smul s fun a b => rel_mk (fun v => t_tr ht hz hz' X Xs Y a b v) (fun v => t_tr ht hz hz' X Xs _ b a v)
  unfold P5.QQi
  exact mrel_mul (mrel_mul (mrel_conjTranspose (tprod_rel ht hL hLs _ _ n rfl)) hQ) (tprod_rel ht hL hLs _ _ n rfl)

end one

end Formalism.FourierDecayAlt.P.PTieB

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PTieB

end Formalism.FourierDecayAlt.P
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {k r : ℕ}

def mk3 (k : ℕ) {n : ℕ} (v0 : Fin n → ℂ) (F : Fin (k - 1) → Fin n → ℂ) (zz : Fin n → ℂ) : Fin (k + 1) → Fin n → ℂ :=
  fun a => if h0 : a.val = 0 then v0 else if hk : a.val = k then zz else F ⟨a.val - 1, by have := a.isLt; omega⟩

theorem three_part_frame_zero {n : ℕ} {v0 zz : Fin n → ℂ} {F : Fin (k - 1) → Fin n → ℂ} {a : Fin (k + 1)} (h : a.val = 0) :
    mk3 k v0 F zz a = v0 := by
  unfold mk3; rw [dite_eq_left h]

theorem three_part_frame_last {n : ℕ} {v0 zz : Fin n → ℂ} {F : Fin (k - 1) → Fin n → ℂ} (hk : 1 ≤ k) {a : Fin (k + 1)}
    (h : a.val = k) : mk3 k v0 F zz a = zz := by
  unfold mk3; rw [dite_eq_right (by omega), dite_eq_left h]

theorem three_part_frame_middle {n : ℕ} {v0 zz : Fin n → ℂ} {F : Fin (k - 1) → Fin n → ℂ} {a : Fin (k + 1)} (h0 : a.val ≠ 0)
    (hk : a.val ≠ k) : mk3 k v0 F zz a = F ⟨a.val - 1, by have := a.isLt; omega⟩ := by
  unfold mk3; rw [dite_eq_right h0, dite_eq_right hk]

theorem three_part_frame_orthonormal (hk : 2 ≤ k) {v0 zz : Fin (2 * r + k + 1) → ℂ} {F : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    (hv0 : inWb k r v0) (hzz : inWb k r zz) (hF : ∀ j, inWb k r (F j))
    (h00 : herm (Hpk k r) v0 v0 = 1) (hzz1 : herm (Hpk k r) zz zz = -1) (h0z : herm (Hpk k r) v0 zz = 0)
    (hF0 : ∀ j, herm (Hpk k r) (F j) v0 = 0) (hFz : ∀ j, herm (Hpk k r) (F j) zz = 0)
    (hFF : ∀ i j, herm (Hpk k r) (F i) (F j) = if i = j then 1 else 0) : ONb k r (mk3 k v0 F zz) := by
  have hz0 : herm (Hpk k r) zz v0 = 0 := by rw [DU.hswap, h0z, map_zero]
  have h0F : ∀ j, herm (Hpk k r) v0 (F j) = 0 := fun j => by rw [DU.hswap, hF0 j, map_zero]
  have hzF : ∀ j, herm (Hpk k r) zz (F j) = 0 := fun j => by rw [DU.hswap, hFz j, map_zero]
  constructor
  · intro a
    by_cases h0 : a.val = 0
    · rw [three_part_frame_zero h0]; exact hv0
    · by_cases hl : a.val = k
      · rw [three_part_frame_last (by omega) hl]; exact hzz
      · rw [three_part_frame_middle h0 hl]; exact hF _
  · intro a b
    by_cases ha0 : a.val = 0
    · rw [three_part_frame_zero ha0]
      by_cases hb0 : b.val = 0
      · rw [three_part_frame_zero hb0, h00, if_pos (Fin.ext (by omega)), if_neg (by omega)]
      · rw [if_neg (fun h => hb0 (by rw [← h]; exact ha0))]
        by_cases hbl : b.val = k
        · rw [three_part_frame_last (by omega) hbl, h0z]
        · rw [three_part_frame_middle hb0 hbl, h0F]
    · by_cases hal : a.val = k
      · rw [three_part_frame_last (by omega) hal]
        by_cases hb0 : b.val = 0
        · rw [three_part_frame_zero hb0, hz0, if_neg (fun h => ha0 (by rw [h]; exact hb0))]
        · by_cases hbl : b.val = k
          · rw [three_part_frame_last (by omega) hbl, hzz1, if_pos (Fin.ext (by omega)), if_pos hal]
          · rw [three_part_frame_middle hb0 hbl, hzF, if_neg (fun h => hbl (by rw [← h]; exact hal))]
      · rw [three_part_frame_middle ha0 hal]
        by_cases hb0 : b.val = 0
        · rw [three_part_frame_zero hb0, hF0, if_neg (fun h => ha0 (by rw [h]; exact hb0))]
        · by_cases hbl : b.val = k
          · rw [three_part_frame_last (by omega) hbl, hFz, if_neg (fun h => hal (by rw [h]; exact hbl))]
          · rw [three_part_frame_middle hb0 hbl, hFF]
            by_cases hab : a = b
            · subst hab; rw [if_pos rfl, if_pos rfl, if_neg hal]
            · have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
              rw [if_neg (fun h => hv (by have := congrArg Fin.val h; simp at this; omega)), if_neg hab]

section pt

variable {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

theorem pt_facts (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    inWb k r (SSn.nu0 k r z z' μsec ζ) ∧ herm (Hpk k r) (SSn.nu0 k r z z' μsec ζ) z = 0 ∧
    herm (Hpk k r) (SSn.nu0 k r z z' μsec ζ) (SSn.nu0 k r z z' μsec ζ) = 1 ∧
    SSn.prWv k r z (SSn.nu0 k r z z' μsec ζ) = SSn.nu0 k r z z' μsec ζ ∧
    inWb k r (SSn.nu0' k r z z' μsec ζ) ∧ herm (Hpk k r) (SSn.nu0' k r z z' μsec ζ) z' = 0 ∧
    herm (Hpk k r) (SSn.nu0' k r z z' μsec ζ) (SSn.nu0' k r z z' μsec ζ) = 1 ∧
    SSn.prWv k r z' (SSn.nu0' k r z z' μsec ζ) = SSn.nu0' k r z z' μsec ζ := by
  obtain ⟨h1, h2, h3, h4⟩ := DU.base hz hz' hT hT' hsec hζ
  have hG := NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ)
  have hGi := FrameEntries.glev_inv hG
  have hy : inWb k r (NF.muZ k r μsec ζ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hyi : inWb k r ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) := Qx8.inWb_mulVec hGi hz
  have hνW : inWb k r (SSn.nu0 k r z z' μsec ζ) := by
    show inWb k r (SSn.unitH k r (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνW' : inWb k r (SSn.nu0' k r z z' μsec ζ) := by
    show inWb k r (SSn.unitH k r (SSn.prWv k r z' ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z)))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz' hyi) _
  refine ⟨hνW, ?_, h2, h1, hνW', ?_, h4, h3⟩
  · rw [← h1]; exact DU.prWv_perp hT hνW
  · rw [← h3]; exact DU.prWv_perp hT' hνW'

theorem mu_frame (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ)
    {m : ℕ} {Fr : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hFr : Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr) :
    (∀ j, inWb k r (NF.muZ k r μsec ζ *ᵥ Fr j)) ∧
    (∀ i j, herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ Fr i) (NF.muZ k r μsec ζ *ᵥ Fr j) = if i = j then 1 else 0) ∧
    (∀ j, herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ Fr j) z = 0) ∧
    ∀ j, herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ Fr j) (SSn.nu0 k r z z' μsec ζ) = 0 := by
  obtain ⟨-, -, hνν, -, -, -, hν'ν', -⟩ := pt_facts hz hz' hT hT' hsec hζ
  set μ := NF.muZ k r μsec ζ with hμ
  have hG := NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ)
  have hU : μ ∈ UH (Hpk k r) := hG.1
  have hGi := FrameEntries.glev_inv hG
  have hy : inWb k r (μ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hyi : inWb k r (μ⁻¹ *ᵥ z) := Qx8.inWb_mulVec hGi hz
  have hFz' : ∀ j, herm (Hpk k r) (Fr j) z' = 0 := fun j => hFr.2.2 j z' (by simp)
  have hFν' : ∀ j, herm (Hpk k r) (Fr j) (SSn.nu0' k r z z' μsec ζ) = 0 := fun j => hFr.2.2 j _ (by simp)

  have hz0 : ∀ j, herm (Hpk k r) (μ *ᵥ Fr j) z = 0 := by
    intro j
    rw [FrameEntries.herm_inv hU]
    set t : ℂ := (((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z' (μ⁻¹ *ᵥ z)) (SSn.prWv k r z' (μ⁻¹ *ᵥ z))).re)⁻¹ : ℝ) : ℂ)
      with ht
    have hν' : SSn.nu0' k r z z' μsec ζ = t • SSn.prWv k r z' (μ⁻¹ *ᵥ z) := rfl
    have ht0 : t ≠ 0 := by
      intro h0
      rw [hν', h0, zero_smul] at hν'ν'
      simp [herm] at hν'ν'
    have h1 := hFν' j
    rw [hν', DU.hsmul_r] at h1
    have h2 : herm (Hpk k r) (Fr j) (SSn.prWv k r z' (μ⁻¹ *ᵥ z)) = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd ((map_eq_zero (starRingEnd ℂ)).1 h) ht0
      · exact h
    rw [DU.prWv_of hyi, DU.hadd_r, DU.hsmul_r, hFz' j, mul_zero, add_zero] at h2
    exact h2
  refine ⟨fun j => Qx8.inWb_mulVec hG (hFr.1 j), fun i j => by rw [Qx2.herm_uh hU]; exact hFr.2.1 i j, hz0, ?_⟩
  intro j
  set s : ℂ := (((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z (μ *ᵥ z')) (SSn.prWv k r z (μ *ᵥ z'))).re)⁻¹ : ℝ) : ℂ)
  have hν : SSn.nu0 k r z z' μsec ζ = s • SSn.prWv k r z (μ *ᵥ z') := rfl
  rw [hν, DU.hsmul_r, DU.prWv_of hy, DU.hadd_r, DU.hsmul_r, hz0 j, Qx2.herm_uh hU, hFz' j]
  simp

theorem frame'_exists (hk : 2 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    ∃ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr := by
  obtain ⟨-, -, -, -, hW', hz'0, h11, -⟩ := pt_facts hz hz' hT hT' hsec hζ
  exact Topx1.typ_frame_exists k r (by omega) z' _ hz' hT' hW' hz'0 h11

end pt

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT
end

section

namespace Formalism.FourierDecayAlt.P.CutBP.TNM

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Matrix

noncomputable section

section cov

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : B.Mat k r → (W →L[ℂ] W)}

theorem tc_dOp_conj (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {g : B.Mat k r}
    (hg : g ∈ UWset k r z) {X : B.Mat k r} (hX : P.QrD.InLieW k r z X)
    (hY : P.QrD.InLieW k r z (g * X * g⁻¹)) :
    (P.QrD.dOp π (g * X * g⁻¹)).comp (π g) = (π g).comp (P.QrD.dOp π X) := by
  have hiU := WeylGroupFacts.uh_inv hg.1
  have ug := WeylGroupFacts.isUnit_of_uh hg.1
  have key : ∀ t : ℝ, (π (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)))).comp (π g) =
      (π g).comp (π (NormedSpace.exp ((t : ℂ) • X))) := by
    intro t
    have hE := P.QrD.exp_uw hX t
    have hE' := P.QrD.exp_uw hY t
    have hconj : NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) * g = g * NormedSpace.exp ((t : ℂ) • X) := by
      have h := P.LeftDerivativeCurves.exp_swap hiU X t
      rw [Matrix.nonsing_inv_nonsing_inv _ ug] at h
      calc NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) * g
          = g * (g⁻¹ * NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) * g := by
            rw [← Matrix.mul_assoc g, Matrix.mul_nonsing_inv _ ug, Matrix.one_mul]
        _ = g * (NormedSpace.exp ((t : ℂ) • X) * g⁻¹) * g := by rw [h]
        _ = g * NormedSpace.exp ((t : ℂ) • X) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ug, Matrix.mul_one]
    rw [← hπ.2 _ hE' _ hg, ← hπ.2 _ hg _ hE, hconj]
  have hd1 := P.QrD.dOp_hasDeriv hπ hc hX
  have hd2 := P.QrD.dOp_hasDeriv hπ hc hY
  let L1 : (W →L[ℂ] W) →L[ℂ] (W →L[ℂ] W) := ContinuousLinearMap.compL ℂ W W W (π g)
  let L2 : (W →L[ℂ] W) →L[ℂ] (W →L[ℂ] W) := (ContinuousLinearMap.compL ℂ W W W).flip (π g)
  have h1 := (L1.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd1
  have h2 := (L2.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd2
  have hfun : ((L2.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)))) =
      ((L1.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) := by
    funext t
    exact key t
  rw [hfun] at h2
  exact h2.unique h1

theorem tc_inWb {g : B.Mat k r} (hg : g ∈ UWset k r z) {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) :
    inWb k r (g *ᵥ w) := by
  obtain ⟨hU, hme, hms, -⟩ := P.Dx2.VV.uw_parts hg
  exact P.Dx2.DF.m0_mulVec_mem_orthogonal g hU hme hms hw

theorem tc_ecOp_conj (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {g : B.Mat k r}
    (hg : g ∈ UWset k r z) {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [z] Bs)
    (a b : Fin m) :
    (P.QrD.ecOp π (Q.unitB (Hpk k r) (fun a => g *ᵥ Bs a) a b)).comp (π g) =
      (π g).comp (P.QrD.ecOp π (Q.unitB (Hpk k r) Bs a b)) := by
  have ug := WeylGroupFacts.isUnit_of_uh hg.1
  have hgB : Q.IsFrameOf k r [z] (fun a => g *ᵥ Bs a) :=
    P.Topx1.vecw_frame_map hg.1 (fun w hw => tc_inWb hg hw) (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      exact ⟨1, z, by simp, by rw [hv, one_smul, hg.2.2]⟩) hB
  obtain ⟨e1, e2, e3⟩ := P.Topx1.vecw_conj_eq hg.1 ug Bs a b
  have lY := P.QrD.frame_lie hgB a b
  have lX := P.QrD.frame_lie hB a b
  rw [e1, e2, e3] at lY
  unfold P.QrD.ecOp
  rw [e1, e2, e3, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul, tc_dOp_conj hπ hc hg lX.1 lY.1, tc_dOp_conj hπ hc hg lX.2 lY.2]

theorem tc_capRep_conj (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {g : B.Mat k r}
    (hg : g ∈ UWset k r z) {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [z] Bs)
    (w : ℂ) (v : W) :
    Q.capRep k r π (fun a => g *ᵥ Bs a) w (π g v) = π g (Q.capRep k r π Bs w v) := by
  have hgB : Q.IsFrameOf k r [z] (fun a => g *ᵥ Bs a) :=
    P.Topx1.vecw_frame_map hg.1 (fun w hw => tc_inWb hg hw) (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      exact ⟨1, z, by simp, by rw [hv, one_smul, hg.2.2]⟩) hB
  unfold Q.capRep
  refine P.Topx1.vecw_qmF (π g).toLinearMap _ _ (fun i j y => ?_) id id w v
  have lY := P.QrD.frame_lie hgB i j
  have lX := P.QrD.frame_lie hB i j
  simp only [ContinuousLinearMap.coe_coe]
  rw [P.QrD.ecRep_eq hπ hc lY.1 lY.2, P.QrD.ecRep_eq hπ hc lX.1 lX.2]
  have h := congrArg (fun L : W →L[ℂ] W => L y) (tc_ecOp_conj hπ hc hg hB i j)
  simpa using h

end cov

theorem type_commutation_holds : TypeComm := by
  intro PP Wp _ _ _ π z e TP hπ hc hu hk hz hTz he hez hee g hg l hl ρ
  have ug := WeylGroupFacts.isUnit_of_uh hg.1
  have hgi : g⁻¹ ∈ UWset PP.k PP.r z := WeylGroupFacts.uw_inv hg
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hl
    have : e = 0 := by
      rw [← Matrix.one_mulVec e, ← Matrix.nonsing_inv_mul _ ug, ← Matrix.mulVec_mulVec, hl, Matrix.mulVec_zero]
    rw [this] at hee
    simp [herm] at hee
  have hli : g⁻¹ *ᵥ e = l⁻¹ • e := by
    calc g⁻¹ *ᵥ e = g⁻¹ *ᵥ (l⁻¹ • (l • e)) := by rw [smul_smul, inv_mul_cancel₀ hl0, one_smul]
      _ = l⁻¹ • (g⁻¹ *ᵥ (g *ᵥ e)) := by rw [hl, Matrix.mulVec_smul]
      _ = l⁻¹ • e := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ug, Matrix.one_mulVec]
  obtain ⟨Bs₀, hB₀⟩ := Formalism.FourierDecayAlt.P.Topx1.typ_frame_exists PP.k PP.r hk z e hz hTz he hez hee
  have hB₀z : Q.IsFrameOf PP.k PP.r [z] Bs₀ := Formalism.FourierDecayAlt.P.Topx1.vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB₀

  have keep : ∀ h ∈ UWset PP.k PP.r z, ∀ c : ℂ, c ≠ 0 → h *ᵥ e = c • e →
      ∀ v, TP.E ρ (π h (TP.E ρ v)) = π h (TP.E ρ v) := by
    intro h hh c hc0 hce v
    have hB1 : Q.IsFrameOf PP.k PP.r [z, e] (fun a => h *ᵥ Bs₀ a) :=
      Formalism.FourierDecayAlt.P.Topx1.vecw_frame_map hh.1 (fun w hw => tc_inWb hh hw) (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact ⟨1, v, by simp, by rw [one_smul, hh.2.2]⟩
        · exact ⟨c⁻¹, v, by simp, by rw [hce, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩) hB₀
    refine TP.full _ hB1 ρ _ fun w => ?_
    rw [tc_capRep_conj hπ hc hh hB₀z w, TP.eigen Bs₀ hB₀ ρ w v, map_smul]
  have kg := keep g hg l hl0 hl
  have kgi := keep g⁻¹ hgi l⁻¹ (inv_ne_zero hl0) hli

  let large₂ : Wp →ₗᵢ[ℂ] Wp := { toLinearMap := (π g : Wp →ₗ[ℂ] Wp), norm_map' := hu g hg }
  have hinn : ∀ x y, inner ℂ (π g x) (π g y) = inner ℂ x y := fun x y => large₂.inner_map_map x y
  have hgg : ∀ y, π g (π g⁻¹ y) = y := by
    intro y
    rw [← ContinuousLinearMap.comp_apply, ← hπ.2 _ hg _ hgi, Matrix.mul_nonsing_inv _ ug, hπ.1]
    rfl
  set E := TP.E ρ with hE
  have hEE : ∀ x, E (E x) = x - (x - E x) := by
    intro x; simp only [sub_sub_cancel]
    exact congrArg (fun L : Wp →L[ℂ] Wp => L x) (TP.idem ρ)
  have hker : ∀ y, E y = 0 → E (π g y) = 0 := by
    intro y hy
    have horth : ∀ u, inner ℂ (π g y) (E u) = 0 := by
      intro u
      calc inner ℂ (π g y) (E u) = inner ℂ (π g y) (π g (π g⁻¹ (E u))) := by rw [hgg]
        _ = inner ℂ y (π g⁻¹ (E u)) := hinn _ _
        _ = inner ℂ y (E (π g⁻¹ (E u))) := by rw [kgi u]
        _ = inner ℂ (E y) (π g⁻¹ (E u)) := (TP.selfAdj ρ _ _).symm
        _ = 0 := by rw [hy, inner_zero_left]
    have hidem : E (E (π g y)) = E (π g y) := congrArg (fun L : Wp →L[ℂ] Wp => L (π g y)) (TP.idem ρ)
    have h0 : inner ℂ (E (π g y)) (E (π g y)) = 0 := by
      rw [TP.selfAdj ρ, hidem, horth]
    exact inner_self_eq_zero.1 h0
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  have hidem : E (E x) = E x := congrArg (fun L : Wp →L[ℂ] Wp => L x) (TP.idem ρ)
  have hsplit : x = E x + (x - E x) := by abel
  have hy : E (x - E x) = 0 := by rw [map_sub, hidem, sub_self]
  conv_lhs => rw [hsplit, map_add (f := _), map_add (f := _), hker _ hy, add_zero, kg x]

end

end Formalism.FourierDecayAlt.P.CutBP.TNM
end
